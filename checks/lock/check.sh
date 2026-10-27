#!/usr/bin/env bash
# Verify the statement lock: input hashes, then the elaborated statements and exported theorems.
# `check.sh --final` additionally requires the proof to be complete (no sorryAx).
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
LEAN_HOME="$(python3 "$HERE/lock.py" --lean-home)"
export PATH="$LEAN_HOME/bin:$PATH"
[[ "${1:-}" == "--final" ]] && export BTBMS_FINAL=1
python3 "$HERE/lock.py"
cd "$HERE/../../lean"
lake build >/dev/null
lake env lean ../checks/lock/LockCheck.lean
