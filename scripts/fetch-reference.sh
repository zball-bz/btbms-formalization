#!/usr/bin/env bash
# Fetch the reference BTBM notation code at a pinned commit into reference/ (gitignored).
# Upstream (SmileLee-lyx/ne-rewritten) declares no license, so it is not vendored.
set -eu
repo=SmileLee-lyx/ne-rewritten
rev=88df7989e270fe6eb447d7fd174d1c06ffc53cf0
dest="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)/reference/ne-rewritten"
mkdir -p "$dest"
for f in "$@"; do
  mkdir -p "$dest/$(dirname "$f")"
  curl -fsSL "https://raw.githubusercontent.com/$repo/$rev/$f" -o "$dest/$f"
done
echo "$repo@$rev" > "$dest/REVISION"
