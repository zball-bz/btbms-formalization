#!/usr/bin/env bash
# See scripts/lean_status.py.
exec python3 "$(dirname "$0")/lean_status.py" "$@"
