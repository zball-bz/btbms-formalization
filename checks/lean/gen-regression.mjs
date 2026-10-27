// Fixed raw (non-V, non-I) regression cases from the statement review (T-014), with expected
// outputs taken from the reference, plus a raw fuzz corpus with arbitrary parents.
// Usage: node checks/lean/gen-regression.mjs REFERENCE_DIR OUT_FILE FUZZ_COUNT SEED
import fs from 'node:fs';
import {loadReference} from '../js/ref-loader.mjs';

const [refDir, outFile, fuzz, seed0] = process.argv.slice(2);
const ref = loadReference(refDir);
const E = (p, h = []) => ({value: p, height: h});
const fixed = [
  [[[], [E(2, [[]])]], [0, 1]],                                   // root in the extra child forest
  [[[], [E(2, [[E(3)], []])]], [1, 2]],                           // earlier-root branch, t < r
  [[[], [E(2, [[E(3, [[E(2)]])], []])]], [1, 2]],                 // negative shift reaches a height
  [[[], [E(4, [[E(3)], []])]], [0]],                              // root beyond the extra forest
  [[[E(1, [[]])]], [0]],
];
let s = Number(seed0) >>> 0;
const rnd = k => { s = (Math.imul(s, 1664525) + 1013904223) >>> 0; return s % k; };
function gen(start, depth) {
  const cols = [];
  for (let i = 0, nc = 1 + rnd(3); i < nc; i++) {
    const col = [];
    for (let k = 0, ne = rnd(3); k < ne; k++)
      col.push(E(rnd(start + i + 3), depth < 3 && rnd(2) ? gen(start + i + 1, depth + 1) : []));
    cols.push(col);
  }
  return cols;
}
const cases = fixed.flatMap(([e, ns]) => ns.map(n => [e, n]));
for (let i = 0; i < Number(fuzz); i++) { const e = gen(0, 0); for (let n = 0; n <= 3; n++) cases.push([e, n]); }
const out = fs.openSync(outFile, 'w');
let throws = 0, negative = 0;
for (const [e, n] of cases) {
  let o = null;
  try { o = ref.FS(e, n); } catch { throws++; }
  if (o !== null && JSON.stringify(o).match(/"value":-/)) { negative++; continue; }  // not a Forest
  fs.writeSync(out, JSON.stringify({in: e, n, out: o}) + '\n');
}
fs.closeSync(out);
console.log(JSON.stringify({cases: cases.length, throws, skippedNegativeOutputs: negative}));
