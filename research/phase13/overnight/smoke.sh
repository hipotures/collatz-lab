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
if [[ -f research/phase13/overnight/test_raw_shadows.py ]]; then
  timeout 60s python3 research/phase13/overnight/test_raw_shadows.py
fi
if [[ -f research/phase13/overnight/raw-shadows.jsonl ]]; then
  timeout 420s python3 research/phase13/overnight/verify_raw_shadows.py --check
fi
if [[ -f research/phase13/overnight/test_transitions.py ]]; then
  timeout 60s python3 research/phase13/overnight/test_transitions.py
fi
if [[ -f research/phase13/overnight/transitions.jsonl ]]; then
  timeout 180s python3 research/phase13/overnight/verify_transitions.py --check
fi
if [[ -f research/phase13/overnight/basis-pattern-probe.json ]]; then
  timeout 35s python3 research/phase13/overnight/probe_basis_pattern.py --check
fi
git diff --check
echo "PASS: overnight smoke checks"
