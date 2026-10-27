// Cases for the Lean order, relative keys and seeds: reference `compare`, `height_compare`
// on `to_height`, and `infinity_FS(m)`. Pairs are drawn from an existing cases file.
// Usage: node checks/lean/gen-order.mjs REFERENCE_DIR CASES_IN OUT_FILE PAIRS SEED
import fs from 'node:fs';
import {loadReference} from '../js/ref-loader.mjs';

const [refDir, casesIn, outFile, pairs, seed0] = process.argv.slice(2);
const ref = loadReference(refDir);
const pool = fs.readFileSync(casesIn, 'utf8').split('\n').filter(Boolean).map(l => JSON.parse(l).in);
let s = Number(seed0) >>> 0;
const rnd = k => { s = (Math.imul(s, 1664525) + 1013904223) >>> 0; return s % k; };
const sign = x => (x > 0) - (x < 0);
const out = fs.openSync(outFile, 'w');
for (let m = 0; m <= 12; m++) fs.writeSync(out, JSON.stringify({seed: m, expr: ref.infinity_FS(m)}) + '\n');
for (let i = 0; i < Number(pairs); i++) {
  const a = pool[rnd(pool.length)];
  // half the pairs share a long prefix so that comparisons are decided late
  const b = rnd(2) ? pool[rnd(pool.length)] : JSON.parse(JSON.stringify(pool[Math.min(pool.length - 1, pool.indexOf(a) + 1 + rnd(5))]));
  const r = rnd(8);
  fs.writeSync(out, JSON.stringify({a, b, cmp: sign(ref.compare(a, b)), r,
    keycmp: sign(ref.height_compare(ref.to_height(a, r), ref.to_height(b, r)))}) + '\n');
}
fs.closeSync(out);
console.log(JSON.stringify({seeds: 13, pairs: Number(pairs)}));
