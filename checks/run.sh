#!/usr/bin/env bash
set -euo pipefail
checks_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
exec python3 -B -I "$checks_dir/run.py" "$@"
