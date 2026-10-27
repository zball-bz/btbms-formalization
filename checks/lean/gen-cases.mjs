// Generate differential test cases for the Lean statement (lean/BTBMS/Expansion.lean):
// breadth-first standard expressions from the seeds under the reference FS, and every
// (expression, n) pair with the reference output, or null where the reference throws.
// Usage: node checks/lean/gen-cases.mjs REFERENCE_DIR OUT_FILE MAXSEED MAXPARAM MAXSTATES
import fs from 'node:fs';
import {loadReference} from '../js/ref-loader.mjs';

const [refDir, outFile, maxSeed, maxParam, maxStates] = process.argv.slice(2);
const ref = loadReference(refDir);
const key = e => JSON.stringify(e);
const seen = new Set();
const queue = [];
for (let m = 0; m <= Number(maxSeed); m++) queue.push(ref.infinity_FS(m));
const out = fs.openSync(outFile, 'w');
let states = 0, cases = 0, throws = 0;
while (queue.length && states < Number(maxStates)) {
  const e = queue.shift();
  const k = key(e);
  if (seen.has(k)) continue;
  seen.add(k);
  states++;
  for (let n = 0; n <= Number(maxParam); n++) {
    let o = null;
    try { o = ref.FS(e, n); } catch { throws++; }
    fs.writeSync(out, JSON.stringify({in: e, n, out: o}) + '\n');
    cases++;
    if (o !== null && !seen.has(key(o))) queue.push(o);
  }
}
fs.closeSync(out);
console.log(JSON.stringify({states, cases, throws, maxSeed: Number(maxSeed), maxParam: Number(maxParam)}));
