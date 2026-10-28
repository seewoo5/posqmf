#!/usr/bin/env bash
# Assembles the GitHub Pages site in `_site`: the root README, rendered as the landing page, and the
# Verso blueprint under `blueprint/`. Build the blueprint first, with
# `posqmf/lean/scripts/ci-pages.sh`.

set -euo pipefail

cd "$(dirname "$0")/../.."

blueprint=posqmf/lean/_out/site/html-multi
test -f "$blueprint/index.html"

rm -rf _site
mkdir _site
cp -R "$blueprint" _site/blueprint
pandoc README.md --from gfm --to html5 --standalone --mathjax \
  --template .github/pages/readme.html \
  --lua-filter .github/pages/github-links.lua \
  --metadata pagetitle=posqmf \
  --output _site/index.html
