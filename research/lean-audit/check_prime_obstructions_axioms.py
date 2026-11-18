#!/usr/bin/env python3
"""Strictly check `PrimeObstructionsAudit.lean` declarations and standard foundations."""

import argparse
from pathlib import Path
import re
import sys

import check_axioms as base


ROOT = Path(__file__).resolve().parents[2]
AUDIT_FILE = Path(__file__).with_name("PrimeObstructionsAudit.lean")
MODULE_FILE = ROOT / "CollatzLab" / "PrimeObstructions.lean"


def extract_module_decls(module_source: str) -> list[str]:
    in_aff = False
    decls = []
    for line in module_source.splitlines():
        if line.strip() == "namespace AffMap":
            in_aff = True
        elif line.strip() == "end AffMap":
            in_aff = False
        m = re.match(r"^(?:noncomputable )?(?:def|theorem|structure)\s+(\w+)", line)
        if m:
            prefix = (
                "CollatzLab.PrimeObstructions.AffMap."
                if in_aff
                else "CollatzLab.PrimeObstructions."
            )
            decls.append(prefix + m.group(1))
    return decls


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--expected-count", dest="expected_count", type=int, required=True
    )
    args = parser.parse_args()
    source = AUDIT_FILE.read_text()
    expected = re.findall(r"^#print axioms (\S+)$", source, re.MULTILINE)
    local_decls = extract_module_decls(MODULE_FILE.read_text())
    if expected != local_decls:
        raise ValueError(
            "PrimeObstructionsAudit.lean does not match CollatzLab/PrimeObstructions.lean declarations in order"
        )
    if len(expected) != args.expected_count or len(set(expected)) != len(expected):
        raise ValueError(
            "audit source count differs from expected count or contains duplicate declarations"
        )
    base.validate(sys.stdin.read(), expected)
    print(
        f"{len(expected)} exact PrimeObstructions declarations; only approved standard foundations"
    )


if __name__ == "__main__":
    main()
