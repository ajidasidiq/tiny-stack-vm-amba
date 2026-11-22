// Amba Stack VM: a fast interpreter for make.fun's tiny stack ISA v1.
// One run answers a whole set, writing /output/<id>/stdout.bin and
// /output/<id>/exit.txt per instance. Table-driven dispatch over fixed
// Int32Array stacks/memory; each step checks the ISA's trap rules in order.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// [opcode, immediate bytes, pops, pushes]
const SPEC: ReadonlyArray<readonly [number, number, number, number]> = [
  [0, 0, 0, 0], [1, 1, 0, 1], [2, 4, 0, 1], [3, 0, 1, 0],
  [4, 0, 1, 2], [5, 0, 2, 2], [6, 0, 2, 3], [7, 0, 3, 3],
  [16, 0, 2, 1], [17, 0, 2, 1], [18, 0, 2, 1], [19, 0, 2, 1],
  [20, 0, 2, 1], [21, 0, 2, 1], [22, 0, 2, 1], [23, 0, 1, 1],
  [24, 0, 2, 1], [25, 0, 2, 1], [26, 0, 2, 1], [27, 0, 1, 1],
  [28, 0, 2, 1], [29, 0, 2, 1], [30, 0, 2, 1], [32, 0, 2, 1],
  [33, 0, 2, 1], [34, 0, 2, 1], [48, 2, 0, 0], [49, 2, 1, 0],
  [50, 2, 1, 0], [51, 2, 0, 0], [52, 0, 0, 0], [64, 0, 1, 1],
  [65, 0, 2, 0], [80, 0, 1, 0], [81, 0, 1, 0], [82, 0, 0, 1],
  [83, 0, 1, 0],
];
const IMM = new Uint8Array(256).fill(255);
const POPS = new Uint8Array(256);
const PUSHES = new Uint8Array(256);
for (const [op, imm, pops, pushes] of SPEC) {
  IMM[op] = imm; POPS[op] = pops; PUSHES[op] = pushes;
}

const DIGITS = new Uint8Array(12); // PRINT's decimal digits, built backwards

function run(prog: Uint8Array, input: Uint8Array): { out: Uint8Array; code: number } {
  const n = prog.length;
  const data = new Int32Array(256);
  const calls = new Int32Array(64);
  const mem = new Int32Array(256);
  const out = new Uint8Array(65536);
  let sp = 0, cp = 0, olen = 0, ipos = 0, pc = 0, steps = 0;
  const end = (code: number) => ({ out: out.subarray(0, olen), code });

  for (;;) {
    if (steps === 1e6) return end(10);
    if (pc < 0 || pc >= n) return end(9);
    const op = prog[pc];
    const imm = IMM[op];
    if (imm === 255) return end(5);
    if (pc + imm >= n) return end(9);
    steps++;
    const next = pc + 1 + imm;
    const pops = POPS[op];
    if (sp < pops) return end(2);
    if (sp - pops + PUSHES[op] > 256) return end(3);
    pc = next;

    switch (op) {
      case 0: return end(0);
      case 1: data[sp++] = (prog[pc - 1] << 24) >> 24; break;
      case 2:
        data[sp++] = prog[pc - 4] | (prog[pc - 3] << 8) | (prog[pc - 2] << 16) | (prog[pc - 1] << 24);
        break;
      case 3: sp--; break;
      case 4: data[sp] = data[sp - 1]; sp++; break;
      case 5: { const t = data[sp - 1]; data[sp - 1] = data[sp - 2]; data[sp - 2] = t; break; }
      case 6: data[sp] = data[sp - 2]; sp++; break;
      case 7: {
        const a = data[sp - 3];
        data[sp - 3] = data[sp - 2]; data[sp - 2] = data[sp - 1]; data[sp - 1] = a;
        break;
      }
      case 23: data[sp - 1] = -data[sp - 1] | 0; break;
      case 27: data[sp - 1] = ~data[sp - 1]; break;
      case 16: case 17: case 18: case 19: case 20: case 21: case 22:
      case 24: case 25: case 26: case 28: case 29: case 30:
      case 32: case 33: case 34: {
        const b = data[sp - 1], a = data[sp - 2];
        let r: number;
        switch (op) {
          case 16: r = (a + b) | 0; break;
          case 17: r = (a - b) | 0; break;
          case 18: r = Math.imul(a, b); break;
          case 19:
            if (b === 0) return end(4);
            r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
            break;
          case 20:
            if (b === 0) return end(4);
            r = b === -1 ? 0 : (a % b) | 0;
            break;
          case 21:
            if (b === 0) return end(4);
            r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
            break;
          case 22:
            if (b === 0) return end(4);
            r = ((a >>> 0) % (b >>> 0)) | 0;
            break;
          case 24: r = a & b; break;
          case 25: r = a | b; break;
          case 26: r = a ^ b; break;
          case 28: r = a << (b & 31); break;
          case 29: r = a >> (b & 31); break;
          case 30: r = (a >>> (b & 31)) | 0; break;
          case 32: r = a === b ? 1 : 0; break;
          case 33: r = a < b ? 1 : 0; break;
          default: r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU
        }
        data[sp - 2] = r;
        sp--;
        break;
      }
      case 48: case 49: case 50: {
        const rel = ((prog[pc - 2] | (prog[pc - 1] << 8)) << 16) >> 16;
        // JMP always jumps and pops nothing (the || short-circuits, so it
        // never pops); JZ pops one and jumps on 0, JNZ on non-zero.
        if (op === 48 || (op === 49) === (data[--sp] === 0)) pc = next + rel;
        break;
      }
      case 51:
        if (cp === 64) return end(7);
        calls[cp++] = next;
        pc = prog[pc - 2] | (prog[pc - 1] << 8);
        break;
      case 52:
        if (cp === 0) return end(8);
        pc = calls[--cp];
        break;
      case 64: {
        const addr = data[sp - 1];
        if (addr < 0 || addr >= 256) return end(6);
        data[sp - 1] = mem[addr];
        break;
      }
      case 65: {
        const addr = data[sp - 1];
        if (addr < 0 || addr >= 256) return end(6);
        mem[addr] = data[sp - 2];
        sp -= 2;
        break;
      }
      case 80: {
        const v = data[sp - 1];
        let u = v < 0 ? (0 - v) >>> 0 : v;
        let t = 12;
        if (u === 0) DIGITS[--t] = 48;
        else while (u > 0) { DIGITS[--t] = 48 + (u % 10); u = Math.floor(u / 10); }
        if (v < 0) DIGITS[--t] = 45;
        const len = 12 - t;
        if (olen + len > 65536) return end(11);
        sp--;
        out.set(DIGITS.subarray(t), olen);
        olen += len;
        break;
      }
      case 81:
        if (olen + 1 > 65536) return end(11);
        out[olen++] = data[--sp] & 255;
        break;
      case 82: data[sp++] = ipos < input.length ? input[ipos++] : -1; break;
      case 83: return end(data[--sp] & 255);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(
    new Uint8Array(readFileSync(join(I, id, 'program.bin'))),
    new Uint8Array(readFileSync(join(I, id, 'input.bin'))),
  );
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), `${r.code}\n`);
}
