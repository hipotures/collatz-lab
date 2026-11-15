#!/usr/bin/env bash
# Additional independent checks on the combined tree, without proof changes.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.."
phase13_run=research/phase13/overnight/integration
lake env lean research/lean-audit/FamilyAudit.lean |
  tee "$phase13_run/axioms.log" |
  python3 research/lean-audit/check_axioms.py --expected-count 653
lake env lean research/phase13/referee/Signatures.lean
lake env lean research/phase13/referee/Declarations.lean > "$phase13_run/types.log"
python3 -B research/phase13/referee/audit_statements.py --source . \
  --axioms "$phase13_run/axioms.log" --output "$phase13_run/lean-statements.json" \
  --checks "$phase13_run/Declarations.lean"
cmp "$phase13_run/lean-statements.json" research/phase13/referee/lean-statements.json
cmp "$phase13_run/Declarations.lean" research/phase13/referee/Declarations.lean
echo 'PASS: current combined interfaces and independent axiom audit reproduce the pinned statements'
