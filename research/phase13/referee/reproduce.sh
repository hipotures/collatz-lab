#!/usr/bin/env bash
# Reproduce issue #31 checks in a NEW directory; no implementation writes/pushes.
set -euo pipefail
review_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../../.." && pwd)
if [[ $# != 1 || -e "$1" ]]; then
  echo 'Usage: bash research/phase13/referee/reproduce.sh NEW_DIRECTORY' >&2
  exit 2
fi
mkdir -p -- "$1"
run_root=$(cd -- "$1" && pwd)
git clone --no-checkout https://github.com/hipotures/collatz-lab.git "$run_root/source"
git -C "$run_root/source" fetch origin 65b087dc62e4950e1c504fe34865acaacb9188c9 76bf6136c334c1db9e52e399fcc33fd4c20b9c24
git -C "$run_root/source" switch --detach 65b087dc62e4950e1c504fe34865acaacb9188c9
mkdir "$run_root/night"
git -C "$run_root/source" archive 76bf6136c334c1db9e52e399fcc33fd4c20b9c24 \
  research/phase13/overnight research/phase13/overnight-summary.md research/phase13/overnight-progress.md |
  tar -x -C "$run_root/night"
cd -- "$run_root/source"
lake build > "$run_root/clean-lake-build.log" 2>&1
bash research/phase13/validate.sh > "$run_root/full-validation.log" 2>&1
lake env lean research/lean-audit/FamilyAudit.lean |
  tee "$run_root/axioms.log" |
  python3 research/lean-audit/check_axioms.py --expected-count 653
lake env lean "$review_root/research/phase13/referee/Signatures.lean" > "$run_root/signatures.log" 2>&1
lake env lean "$review_root/research/phase13/referee/Declarations.lean" > "$run_root/types.log" 2>&1
python3 -B "$review_root/research/phase13/referee/audit_statements.py" \
  --source "$run_root/source" --axioms "$run_root/axioms.log" \
  --output "$run_root/lean-statements.json" --checks "$run_root/Declarations.lean"
cmp "$run_root/lean-statements.json" "$review_root/research/phase13/referee/lean-statements.json"
python3 -B "$review_root/research/phase13/referee_checks.py" --source "$run_root/source" --baseline \
  --overnight "$run_root/night/research/phase13/overnight" --raw-level 8 \
  --output "$run_root/independent-results.json" | tee "$run_root/independent.log"
cmp "$run_root/independent-results.json" "$review_root/research/phase13/referee/independent-results.json"
echo "PASS: pinned full validation and referee evidence reproduced in $run_root"
