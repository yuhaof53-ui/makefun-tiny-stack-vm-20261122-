// Tiny stack VM: my own interpreter for make.fun's tiny stack ISA (ISA.md in the kit).
// One run answers every instance, writing <id>/stdout.bin and <id>/exit.txt each.
// Node 22, no deps, no network, no clock, no randomness: two runs write identical bytes.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Per opcode byte: [immediate bytes, values popped, values pushed].
// Bytes absent here are unknown opcodes and trap 5.
const T = {
  0: [0, 0, 0], 1: [1, 0, 1], 2: [4, 0, 1], 3: [0, 1, 0], 4: [0, 1, 2],
  5: [0, 2, 2], 6: [0, 2, 3], 7: [0, 3, 3],
  16: [0, 2, 1], 17: [0, 2, 1], 18: [0, 2, 1], 19: [0, 2, 1], 20: [0, 2, 1],
  21: [0, 2, 1], 22: [0, 2, 1], 23: [0, 1, 1], 24: [0, 2, 1], 25: [0, 2, 1],
  26: [0, 2, 1], 27: [0, 1, 1], 28: [0, 2, 1], 29: [0, 2, 1], 30: [0, 2, 1],
  31: [0, 2, 1], 32: [0, 2, 1], 33: [0, 2, 1], 34: [0, 2, 1],
  48: [2, 0, 0], 49: [2, 1, 0], 50: [2, 1, 0], 51: [2, 0, 0], 52: [0, 0, 0],
  64: [0, 1, 1], 65: [0, 2, 0],
  80: [0, 1, 0], 81: [0, 1, 0], 82: [0, 0, 1], 83: [0, 1, 0],
};

function run(p, inp) {
  const n = p.length;
  const D = new Int32Array(256);
  const C = new Int32Array(64);
  const M = new Int32Array(256);
  const out = new Uint8Array(65536);
  let sp = 0, cp = 0, ol = 0, ip = 0, pc = 0, st = 0;
  const end = (code) => [out.subarray(0, ol), code];
  for (;;) {
    if (st === 1000000) return end(10);
    if (pc < 0 || pc >= n) return end(9);
    const o = p[pc];
    const t = T[o];
    if (!t) return end(5);
    if (pc + t[0] >= n) return end(9);
    st++;
    const nx = pc + 1 + t[0];
    if (sp < t[1]) return end(2);
    if (sp - t[1] + t[2] > 256) return end(3);
    pc = nx;
    if (o >= 16 && o <= 34 && o !== 23 && o !== 27) { // two-operand ops, except NEG/NOT
      const b = D[sp - 1], a = D[sp - 2];
      let r;
      if (o === 16) r = (a + b) | 0;
      else if (o === 17) r = (a - b) | 0;
      else if (o === 18) r = Math.imul(a, b); // low 32 bits of the exact product
      else if (o === 19) {
        if (b === 0) return end(4);
        r = a === -2147483648 && b === -1 ? a : (a / b) | 0; // truncates toward zero
      } else if (o === 20) {
        if (b === 0) return end(4);
        r = b === -1 ? 0 : (a % b) | 0; // remainder takes the sign of a
      } else if (o === 21) {
        if (b === 0) return end(4);
        r = Math.floor((a >>> 0) / (b >>> 0)) | 0; // unsigned quotient
      } else if (o === 22) {
        if (b === 0) return end(4);
        r = ((a >>> 0) % (b >>> 0)) | 0; // unsigned remainder
      } else if (o === 24) r = a & b;
      else if (o === 25) r = a | b;
      else if (o === 26) r = a ^ b;
      else if (o === 28) r = a << (b & 31); // only the low 5 bits of the count
      else if (o === 29) r = a >> (b & 31); // arithmetic: sign bit copied in
      else if (o === 30) r = (a >>> (b & 31)) | 0; // logical: zeros in
      else if (o === 32) r = a === b ? 1 : 0;
      else if (o === 33) r = a < b ? 1 : 0;
      else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU, unsigned
      sp -= 2;
      D[sp++] = r;
      continue;
    }
    switch (o) {
      case 0: return end(0);
      case 1: D[sp++] = (p[nx - 1] << 24) >> 24; break; // PUSH8, sign-extended
      case 2: D[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24); break;
      case 3: sp--; break;
      case 4: D[sp] = D[sp - 1]; sp++; break;
      case 5: { const x = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = x; break; }
      case 6: D[sp] = D[sp - 2]; sp++; break;
      case 7: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; }
      case 23: D[sp - 1] = (-D[sp - 1]) | 0; break; // NEG wraps at -2147483648
      case 27: D[sp - 1] = ~D[sp - 1]; break;
      case 48: case 49: case 50: { // JMP/JZ/JNZ: signed 16-bit offset from next instruction
        const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
        let take = true;
        if (o !== 48) { const v = D[--sp]; take = o === 49 ? v === 0 : v !== 0; }
        if (take) pc = nx + rel;
        break;
      }
      case 51: // CALL: unsigned 16-bit target, 64 return addresses at most
        if (cp === 64) return end(7);
        C[cp++] = nx;
        pc = p[nx - 2] | (p[nx - 1] << 8);
        break;
      case 52:
        if (cp === 0) return end(8);
        pc = C[--cp];
        break;
      case 64: {
        const a = D[sp - 1];
        if (a < 0 || a >= 256) return end(6);
        D[sp - 1] = M[a];
        break;
      }
      case 65: { // STORE: ( v addr -- )
        const a = D[sp - 1], v = D[sp - 2];
        if (a < 0 || a >= 256) return end(6);
        sp -= 2;
        M[a] = v;
        break;
      }
      case 80: { // PRINT: decimal ASCII, '-' when negative, nothing past the limit
        const s = String(D[sp - 1]);
        if (ol + s.length > 65536) return end(11);
        sp--;
        for (let i = 0; i < s.length; i++) out[ol++] = s.charCodeAt(i);
        break;
      }
      case 81:
        if (ol + 1 > 65536) return end(11);
        out[ol++] = D[--sp] & 255;
        break;
      case 82: D[sp++] = ip < inp.length ? inp[ip++] : -1; break; // IN: -1 past the end
      case 83: return end(D[--sp] & 255); // EXIT: low byte
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const [out, code] = run(new Uint8Array(readFileSync(join(I, id, 'program.bin'))), new Uint8Array(readFileSync(join(I, id, 'input.bin'))));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), out);
  writeFileSync(join(O, id, 'exit.txt'), code + '\n');
}
