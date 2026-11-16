#!/usr/bin/env python3
"""Strictly check `ShadowCancellationAudit.lean` declarations and standard foundations."""

import argparse
from pathlib import Path
import re
import sys

import check_axioms as base


ROOT = Path(__file__).resolve().parents[2]
AUDIT_FILE = Path(__file__).with_name("ShadowCancellationAudit.lean")
MODULE_FILE = ROOT / "CollatzLab" / "ShadowCancellation.lean"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--expected-shadow-count", "--expected-count", dest="expected_count", type=int, required=True)
    args = parser.parse_args()
    source = AUDIT_FILE.read_text()
    expected = re.findall(r"^#print axioms (\S+)$", source, re.MULTILINE)
    module_source = MODULE_FILE.read_text()
    local_decls = [
        f"CollatzLab.ShadowCancellation.{name}"
        for name in re.findall(r"^(?:noncomputable )?(?:def|theorem)\s+(\w+)", module_source, re.MULTILINE)
    ]
    if expected != local_decls:
        raise ValueError("ShadowCancellationAudit.lean does not match CollatzLab/ShadowCancellation.lean declarations in order")
    if len(expected) != args.expected_count or len(set(expected)) != len(expected):
        raise ValueError("audit source count differs from expected count or contains duplicate declarations")
    base.validate(sys.stdin.read(), expected)
    print(f"{len(expected)} exact ShadowCancellation declarations; only approved standard foundations")


if __name__ == "__main__":
    main()
