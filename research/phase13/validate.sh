#!/usr/bin/env bash
# Full inherited checks and bounded Phase 13 evidence; fail on any failed step.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.."
bash research/phase12/validate.sh
lake env lean research/phase13/Signatures.lean
python3 research/phase13/test_height.py
python3 research/phase13/experiments.py --check
python3 research/phase13/verify_certificates.py research/phase13/heights.json.gz
python3 research/phase13/verify_analytics.py --check
python3 research/phase13/verify_modular.py --check
python3 - <<'PY'
from pathlib import Path
import re
import subprocess

manifest = Path('research/lean-audit/FamilyAudit.lean').read_text()
names = re.findall(r'^#print axioms (\S+)', manifest, re.M)
expected = re.findall(r'--expected-count (\d+)', Path('.github/workflows/ci.yml').read_text())
assert expected == [str(len(names))]
assert len(set(names)) == len(names)
for module in ['RationalHeight', 'FrontierHeight']:
    source = Path(f'CollatzLab/{module}.lean').read_text()
    local = re.findall(r'^(?:noncomputable )?(?:def|theorem)\s+(\w+)', source, re.M)
    assert all(f'CollatzLab.{module}.{name}' in names for name in local)
base = subprocess.check_output(['git', 'show', '93647176a526eb8660b4dbf2ac428b0053117659:research/lean-audit/FamilyAudit.lean'], text=True)
old = re.findall(r'^#print axioms (\S+)', base, re.M)
assert names[:len(old)] == old
print(f'Phase 13 inventory: {len(names)-len(old)} new declarations, {len(old)} baseline entries preserved, {len(names)} total')
PY
git diff --check
