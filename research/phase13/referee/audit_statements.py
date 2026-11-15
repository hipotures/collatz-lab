#!/usr/bin/env python3
"""Independent declaration/axiom inventory for the exact pinned PR source.

Generate all 60 source signatures and a compiler #check fixture. Audit a full
FamilyAudit stdout without importing the repository's audit parser.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess


ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def need(condition, message):
    if not condition:
        raise ValueError(message)


def records_from_stdout(raw):
    logical = []
    for line in raw.splitlines():
        if line.startswith("'CollatzLab."):
            logical.append(line)
        else:
            need(logical and line.startswith(" "), "unexpected audit diagnostic")
            need(re.fullmatch(r"\s*(?:propext|Classical\.choice|Quot\.sound)(?:, ?|\])", line),
                 "unapproved audit continuation")
            logical[-1] += " " + line.strip()
    result = []
    for line in logical:
        match = re.fullmatch(r"'([^']+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])", line)
        need(match is not None, "malformed axiom report")
        axioms = [] if match[2] is None else match[2].split(", ")
        need(set(axioms) <= ALLOWED and len(axioms) == len(set(axioms)), "unapproved axiom")
        result.append((match[1], axioms))
    return result


def self_test():
    line = "'CollatzLab.control' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n"
    need(records_from_stdout(line)[0][1] == ["propext", "Classical.choice", "Quot.sound"], "wrapped foundations")
    damaged = [line.replace("Quot.sound", "sorryAx"), line+"error: failed\n",
               line+" Custom.axiom]\n", line.replace("[propext,", "["), ""]
    for value in damaged[:-1]:
        try:
            records_from_stdout(value)
        except ValueError:
            continue
        raise ValueError("corrupt axiom output accepted")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--axioms", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--checks", type=Path, required=True)
    args = parser.parse_args()
    self_test()
    manifest = (args.source / "research/lean-audit/FamilyAudit.lean").read_text()
    expected = re.findall(r"^#print axioms (\S+)$", manifest, re.M)
    need(len(expected) == len(set(expected)) == 653, "pinned manifest count")
    ci_counts = re.findall(r"--expected-count (\d+)", (args.source / ".github/workflows/ci.yml").read_text())
    need(ci_counts == [str(len(expected))], "CI and declaration manifest disagree")
    baseline = subprocess.check_output(["git", "-C", str(args.source), "show",
                                       "93647176a526eb8660b4dbf2ac428b0053117659:research/lean-audit/FamilyAudit.lean"],
                                      text=True)
    old_names = re.findall(r"^#print axioms (\S+)$", baseline, re.M)
    need(len(old_names) == 593 and expected[:len(old_names)] == old_names, "baseline name/order changed")
    audit = records_from_stdout(args.axioms.read_text())
    need([name for name, _ in audit] == expected, "not the exact full declaration list/order")
    declarations = []
    for module in ("RationalHeight", "FrontierHeight"):
        path = args.source / f"CollatzLab/{module}.lean"
        raw = path.read_bytes()
        text = raw.decode()
        matches = list(re.finditer(r"^(?:noncomputable )?(def|theorem)\s+(\w+)\b", text, re.M))
        for index, match in enumerate(matches):
            end = matches[index+1].start() if index+1 < len(matches) else len(text)
            declaration = text[match.start():end]
            # Recursive equation-style declarations have no ':=' in the header.
            delimiter = re.search(r" :=|\n  \|", declaration)
            need(delimiter is not None, "signature boundary not found")
            name = f"CollatzLab.{module}.{match[2]}"
            need(name in expected, "public declaration not audited")
            declarations.append({"name": name, "kind": match[1], "file": f"CollatzLab/{module}.lean",
                                 "line": text[:match.start()].count("\n")+1,
                                 "exact_source_header": declaration[:delimiter.start()].strip(),
                                 "axioms": dict(audit)[name], "source_sha256": hashlib.sha256(raw).hexdigest(),
                                 "semantic_verdict": "PASS; see the per-declaration table in the report"})
    need(len(declarations) == 60, "pinned new-declaration count")
    forbidden = re.compile(r"\b(?:sorry|admit|axiom|opaque|unsafe|native_decide|implemented_by|extern|trustLevel)\b|skipKernel")
    source_paths = [args.source / "CollatzLab.lean", *sorted((args.source / "CollatzLab").rglob("*.lean"))]
    for path in source_paths:
        need(forbidden.search(path.read_text()) is None, "forbidden escape: "+str(path))
    args.output.write_text(json.dumps({"format": "phase13-referee-statements-v1", "total_records": len(audit),
                                     "allowed_foundations": sorted(ALLOWED), "forbidden_scan_files": len(source_paths),
                                     "declarations": declarations}, indent=2)+"\n")
    args.checks.write_text("import CollatzLab\n\n-- Every pinned Phase 13 public interface, with implicit arguments explicit.\n"+
                           "".join("#check @"+d["name"]+"\n" for d in declarations))
    print(f"PASS: {len(audit)} exact foundation records; {len(declarations)} public signatures; "
          f"{len(source_paths)} trusted source files scanned")


if __name__ == "__main__":
    main()
