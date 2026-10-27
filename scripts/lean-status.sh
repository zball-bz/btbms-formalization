#!/usr/bin/env bash
# Build the Lean library and record per-declaration status in tracker/lean-status.json
# (read by tracker/refresh.py). Never edit that file by hand. The record carries the fingerprint
# of every input (checks/lock/lock.py), so refresh.py can tell when it is stale. A failed build
# or extraction overwrites the record with a failure, never leaving an older success in place.
set -uo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
LEAN_HOME="$(python3 "$ROOT/checks/lock/lock.py" --lean-home)"
export PATH="$LEAN_HOME/bin:$PATH"
fp="$(python3 "$ROOT/checks/lock/lock.py" --fingerprint)"
cd "$ROOT/lean"
ok=1
lake build >/dev/null 2>&1 || ok=0
decls='[]'
if [[ $ok == 1 ]]; then decls="$(lake env lean ../checks/lock/Status.lean)" || { ok=0; decls='[]'; }; fi
python3 - "$ROOT" "$fp" "$ok" "$decls" <<'PY'
import json, subprocess, sys
from datetime import datetime, timezone
root, fp, ok, decls = sys.argv[1], sys.argv[2], sys.argv[3] == '1', json.loads(sys.argv[4])
head = subprocess.run(['git', '-C', root, 'rev-parse', '--short', 'HEAD'], capture_output=True, text=True).stdout.strip()
out = {'generated': datetime.now(timezone.utc).isoformat(timespec='seconds'), 'head': head,
       'fingerprint': fp, 'build_ok': ok, 'decls': decls}
open(f'{root}/tracker/lean-status.json', 'w').write(json.dumps(out, indent=1) + '\n')
if not ok:
    sys.exit('build or extraction FAILED; status recorded as failed')
direct = sum(d['direct_sorry'] for d in decls)
trans = sum('sorryAx' in d['axioms'] for d in decls)
print(f"{len(decls)} declarations: {direct} with a direct sorry, {trans} depending on sorry")
PY
