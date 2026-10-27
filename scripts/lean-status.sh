#!/usr/bin/env bash
# Build the Lean library and record per-declaration status in tracker/lean-status.json
# (read by tracker/refresh.py). Never edit that file by hand.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
export PATH=/home/dev/ggg/.tools/lean-4.33.1-linux/bin:$PATH
cd "$ROOT/lean"
lake build >/dev/null
decls="$(lake env lean ../checks/lock/Status.lean)"
python3 - "$ROOT" "$decls" <<'PY'
import json, subprocess, sys
from datetime import datetime, timezone
root, decls = sys.argv[1], json.loads(sys.argv[2])
head = subprocess.run(['git', '-C', root, 'rev-parse', '--short', 'HEAD'], capture_output=True, text=True).stdout.strip()
out = {'generated': datetime.now(timezone.utc).isoformat(timespec='seconds'), 'head': head, 'decls': decls}
open(f'{root}/tracker/lean-status.json', 'w').write(json.dumps(out, indent=1) + '\n')
print(f"{len(decls)} declarations, {sum(d['direct_sorry'] for d in decls)} with sorry")
PY
