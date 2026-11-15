#!/usr/bin/env bash
# Cheap validation run after each Codex research checkpoint; no network.
set -Eeuo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.."
export PYTHONDONTWRITEBYTECODE=1
bash -n research/phase13/overnight/drive_codex.sh
bash -n research/phase13/overnight/smoke.sh
python3 -m compileall -q research/phase13/overnight
python3 research/phase13/test_height.py
if [[ -f research/phase13/overnight/test_extended.py ]]; then
  timeout 150s python3 research/phase13/overnight/test_extended.py --quick
fi
if [[ -f research/phase13/overnight/test_basis.py ]]; then
  timeout 150s python3 research/phase13/overnight/test_basis.py --quick
fi
if [[ -f research/phase13/overnight/verify_results.py ]]; then
  python3 research/phase13/overnight/verify_results.py --check
fi
if [[ -f research/phase13/overnight/height-inventory.json ]]; then
  python3 research/phase13/overnight/summarize.py --check
fi
git diff --check
echo "PASS: overnight smoke checks"
