#!/usr/bin/env bash
# Full inherited matrix and the Phase 12 finite evidence/exact interfaces.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/../.."
bash research/phase11/validate.sh
lake env lean research/phase11/Signatures.lean
lake env lean research/phase12/Signatures.lean
python3 research/phase12/verify_returns.py --check
python3 - <<'PY'
from pathlib import Path
import re

audit = Path('research/lean-audit/FamilyAudit.lean').read_text()
names = re.findall(r'^#print axioms (\S+)', audit, re.M)
count = re.findall(r'--expected-count (\d+)', Path('.github/workflows/ci.yml').read_text())
assert count == [str(len(names))], 'CI and audit count differ'
assert len(names) == len(set(names)), 'duplicate audit entry'
for module, namespace in [('TwoReturn', 'CollatzLab'),
                          ('FrontierSix', 'CollatzLab.Morphism'),
                          ('FrontierSixChecks', 'CollatzLab.FrontierSixChecks')]:
    source = Path(f'CollatzLab/{module}.lean').read_text()
    declarations = re.findall(r'^(?:def|theorem)\s+(\w+)', source, re.M)
    assert all(f'{namespace}.{name}' in names for name in declarations), module
print(f'Phase 12 declaration inventory agrees with the {len(names)}-entry audit')
PY
git diff --check
