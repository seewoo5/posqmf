#!/usr/bin/env bash
# Builds the blueprint site into `_out/site/html-multi` (run from `posqmf/lean`).

set -euo pipefail

cd "$(dirname "$0")/.."

lake exe vbp build

test -f _out/site/html-multi/index.html
test -f _out/site/html-multi/-verso-data/blueprint-manifest.json
