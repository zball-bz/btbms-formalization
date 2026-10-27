#!/usr/bin/env bash
# Differential test of the Lean statement's definitions (lean/BTBMS/{Syntax,Expansion}.lean)
# against the pinned reference BTBM.ts: the operation on generated standard expressions and on
# random V-expressions, fixed raw regression cases and random raw expressions (arbitrary
# parents), including cases where the reference throws; the order, relative
# keys and seeds. Passing is evidence of definitional fidelity, not a proof of anything.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
export PATH="$root/../.tools/lean-4.33.1-linux/bin:$PATH"
ref="$root/reference/ne-rewritten"
[ -f "$ref/src/notations/BM-like/BTBM.ts" ] || "$root/scripts/fetch-reference.sh" \
  src/notations/BM-like/BTBM.ts src/utils.ts src/notation-definition.ts src/notations/notation_utils.ts
out="$root/lean/.lake/difftest"; mkdir -p "$out"
cd "$root/lean"
lake build difftest >/dev/null
gen="$root/checks/lean"
node --no-warnings "$gen/gen-cases.mjs" "$ref" "$out/standard.jsonl" 5 4 20000
node --no-warnings "$gen/gen-random.mjs" "$ref" "$out/random.jsonl" 50000 20261027
node --no-warnings "$gen/gen-order.mjs" "$ref" "$out/random.jsonl" "$out/order.jsonl" 200000 11
node --no-warnings "$gen/gen-regression.mjs" "$ref" "$out/raw.jsonl" 20000 5
for f in standard random order raw; do echo -n "$f: "; .lake/build/bin/difftest "$out/$f.jsonl"; done
