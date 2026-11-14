#!/usr/bin/env bash
# Reproduce the issue #19 checks using the exact current CI audit count.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.."
phase11_audit_count=$(python3 - <<'PY'
from pathlib import Path
import re
text = Path('.github/workflows/ci.yml').read_text()
counts = re.findall(r'--expected-count (\d+)', text)
assert len(counts) == 1
print(counts[0])
PY
)
phase11_audit_file=$(mktemp)
phase11_names_file=$(mktemp --suffix=.lean)
trap 'rm -f -- "$phase11_audit_file" "$phase11_names_file"' EXIT
lake build
lake env lean research/lean-audit/FamilyAudit.lean > "$phase11_audit_file"
python3 research/lean-audit/check_axioms.py --self-test
python3 research/lean-audit/check_axioms.py --expected-count "$phase11_audit_count" < "$phase11_audit_file"
if rg -n '\b(sorry|admit|axiom|opaque|unsafe|native_decide|implemented_by|extern)\b' CollatzLab CollatzLab.lean; then
  exit 1
fi
cargo fmt --check
cargo clippy --locked --all-targets --all-features -- -D warnings
cargo test --locked --all-targets
python3 research/phase8/verify_polynomial.py
python3 research/mahler-uncovered/verify_uncovered.py --check
python3 research/phase9/verify_independent.py
python3 paper/check_tex.py
python3 research/phase10/verify_unequal.py --check
python3 research/phase10/search_unequal.py --check
python3 research/phase10/verify_spectral.py --check
python3 research/phase10/verify_sparse_family.py --check
python3 research/phase10/generate_catalogue.py --check
python3 research/phase11/verify_noncontracting.py
python3 research/phase11/verify_spectral_boundary.py
python3 research/phase11/verify_partial_return.py
python3 paper/check_tex.py --lean-names > "$phase11_names_file"
lake env lean "$phase11_names_file"
git diff --check
