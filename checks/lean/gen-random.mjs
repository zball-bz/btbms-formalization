// Random raw expressions satisfying V (every parent a visible column below its own column),
// I not required, for checking agreement, including where FS throws, on the V domain (raw cases: gen-regression).
// Usage: node checks/lean/gen-random.mjs REFERENCE_DIR OUT_FILE COUNT SEED
import fs from 'node:fs';
import {loadReference} from '../js/ref-loader.mjs';

const [refDir, outFile, count, seed0] = process.argv.slice(2);
const ref = loadReference(refDir);
let s = Number(seed0) >>> 0;
const rnd = k => { s = (Math.imul(s, 1664525) + 1013904223) >>> 0; return s % k; };
function gen(start, vis, depth, outer) {
  const cols = [];
  const ncols = 1 + rnd(outer ? 4 : 3);
  for (let i = 0; i < ncols; i++) {
    const c = start + i;
    const here = vis.concat(Array.from({length: i}, (_, j) => start + j));
    const col = [];
    const nent = here.length ? rnd(4) : 0;
    for (let k = 0; k < nent; k++) {
      const p = here[rnd(here.length)];
      const height = depth < 3 && rnd(3) === 0 ? gen(c + 1, here.concat([c]), depth + 1, false) : [];
      col.push({value: p, height});
    }
    // keep inner columns mostly nonempty, but allow I-violations sometimes
    if (!outer && col.length === 0 && rnd(4) !== 0 && here.length) col.push({value: here[here.length - 1], height: []});
    cols.push(col);
  }
  return cols;
}
const out = fs.openSync(outFile, 'w');
let throws = 0;
for (let i = 0; i < Number(count); i++) {
  const e = gen(0, [], 0, true);
  for (let n = 0; n <= 3; n++) {
    let o = null;
    try { o = ref.FS(e, n); } catch { throws++; }
    fs.writeSync(out, JSON.stringify({in: e, n, out: o}) + '\n');
  }
}
fs.closeSync(out);
console.log(JSON.stringify({expressions: Number(count), cases: 4 * Number(count), throws}));
