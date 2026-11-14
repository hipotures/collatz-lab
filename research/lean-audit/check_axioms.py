#!/usr/bin/env python3
"""Strictly check the audit's exact declarations and standard foundations.

Lean wraps long declaration reports. Join only continuations spelling approved
foundation names; diagnostics and all other lines remain errors.
"""

import argparse
from pathlib import Path
import re
import sys


FOUNDATION = r"(?:propext|Classical\.choice|Quot\.sound)"
RECORD = re.compile(
    r"^'(?P<name>CollatzLab\.[A-Za-z0-9_.']+)' "
    r"(?:does not depend on any axioms|depends on axioms: \["
    + FOUNDATION + r"(?:, " + FOUNDATION + r")*\])$"
)


def validate(output, expected):
    normalized = re.sub(r",\n[ \t]+(?=" + FOUNDATION + r"(?:,|\]))", ", ", output)
    lines = normalized.splitlines()
    if len(lines) != len(expected):
        raise ValueError(f"expected {len(expected)} declarations, found {len(lines)} records/lines")
    for line, name in zip(lines, expected):
        match = RECORD.fullmatch(line)
        if match is None or match["name"] != name:
            raise ValueError(f"unapproved dependency, diagnostic or unexpected declaration: {line!r}")


def self_test():
    names = ["CollatzLab.test"]
    valid = "'CollatzLab.test' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n"
    validate(valid, names)
    validate("'CollatzLab.test' does not depend on any axioms\n", names)
    invalid = [
        "", valid + "error: bad proof\n", valid + valid,
        valid.replace("Quot.sound", "sorryAx"), valid.replace("CollatzLab.test", "CollatzLab.other"),
        valid.replace("Classical.choice", "Custom.escape"), valid.replace("]", ""),
        valid.replace(" Quot.sound", " error: Quot.sound"),
    ]
    for value in invalid:
        try:
            validate(value, names)
        except ValueError:
            continue
        raise AssertionError(f"invalid audit accepted: {value!r}")
    print("audit parser: 2 valid and 8 adversarial cases passed")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--expected-count", type=int)
    args = parser.parse_args()
    if args.self_test:
        self_test()
        return
    source = Path(__file__).with_name("FamilyAudit.lean").read_text()
    expected = re.findall(r"^#print axioms (\S+)$", source, re.MULTILINE)
    if args.expected_count is None or len(expected) != args.expected_count or len(set(expected)) != len(expected):
        raise ValueError("audit source count differs from CI or contains duplicate declarations")
    validate(sys.stdin.read(), expected)
    print(f"{len(expected)} exact declarations; only approved standard foundations")


if __name__ == "__main__":
    main()
