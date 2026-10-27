#!/usr/bin/env bash
# Verify the statement lock: file hashes, then the elaborated statements (LockCheck.lean).
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
export PATH=/home/dev/ggg/.tools/lean-4.33.1-linux/bin:$PATH
python3 "$HERE/lock.py"
cd "$HERE/../../lean"
lake build >/dev/null
lake env lean ../checks/lock/LockCheck.lean
