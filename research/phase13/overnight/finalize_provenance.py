#!/usr/bin/env python3
"""Finalize issue #33 metadata after successful, separately recorded validation.

--check only hashes/reads bounded files; it never runs a height optimizer or
replays the eight-hour experiment. --write requires the pinned Git objects and
a successful current validation ledger. Neither mode changes certificate data.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[3]
NIGHT = "research/phase13/overnight/"
SOURCE = "76bf6136c334c1db9e52e399fcc33fd4c20b9c24"
MAIN = "0190d57f43164ce2ec6016b3d3314c94ff98e06b"
IMPLEMENTATION = "65b087dc62e4950e1c504fe34865acaacb9188c9"
REVIEW = "3daf62c2c4b06e158375df16d6ca757969fba47e"
AUDIT = NIGHT + "checkpoint-audit.json"
SUMMARY = "research/phase13/overnight-summary.md"
JOURNAL = "research/phase13/overnight-progress.md"
RUNS = NIGHT + "integration/validation.json"
FORMAT = "phase13-overnight-final-audit-v4"
VALIDATION_HEAD = "d6466ed71f2036f39cb0506a4a659bfecc7a0791"
VALIDATION_SHA256 = "6dfeea6d534f46dea1b11cb50f42039d30b4f994bf482a6296307d8d475850b4"
METADATA_TOOLS = {NIGHT + name for name in (
    "finalize_provenance.py", "test_provenance.py", "validate_integration.py", "drive_codex.sh")}
BINDING_SCOPE = "frozen recorded Lean/Phase 13 certification inputs; complete validation ledger is historical"
MUTABLE = {AUDIT, SUMMARY, JOURNAL, NIGHT + "README.md", NIGHT + "drive_codex.sh"}
EVIDENCE = {
    "heights.jsonl": (24, 8027076, "08bcbb623aee8fd0bf8d6e6bcf919feed9e0cf171e2dafcb5ce89afbfc6c74a3", 8388608),
    "transitions.jsonl": (11, 481400, "24ef2b65c32e804663b20833a7bb330e85a305674fd8f5ae725e7c4fb91a38a7", 524288),
    "transitions-0002.jsonl": (5, 219248, "786cf600dc93222ab38fa1ef70cac3cb810840b188f6396f70b981ee0892e23e", 524288),
    "raw-shadows.jsonl": (9, 6288, "72088c34e8e8ac6666da741466fd8c244168350de12c124be38b086d849acad7", 65536),
}

# Kept in one place so the runner and finalizer agree about the required checks.
COMMANDS = [
    ("combined-matrix", ["bash", "research/phase13/validate.sh"], 1200, 25165824),
    ("combined-interfaces", ["bash", NIGHT + "check_integration_interfaces.sh"], 180, 1048576),
    ("overnight-smoke", ["bash", NIGHT + "smoke.sh"], 750, 1048576),
    ("pinned-referee", ["bash", "research/phase13/referee/reproduce.sh"], 1200, 25165824),
]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def file_info(raw):
    return {"bytes": len(raw), "sha256": sha(raw)}


def tracked(root):
    paths = subprocess.check_output(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard"], cwd=root, text=True).splitlines()
    # Earlier CI steps can import Python modules without our runner's
    # PYTHONDONTWRITEBYTECODE setting. Bytecode caches are generated outputs,
    # not certification inputs, including in directories without .gitignore.
    return sorted({p for p in paths if "__pycache__" not in Path(p).parts and
                   not p.endswith((".pyc", ".pyo"))})


def inputs(root):
    # The runner records the complete actual combined tree. Preserve this
    # historical manifest even when unrelated repository files later change.
    return {p: file_info((root / p).read_bytes()) for p in tracked(root)
            if not p.endswith(".md") and p != AUDIT and not p.startswith(NIGHT + "integration/")}


def certification_path(path):
    # Select only existing paths from the hash-pinned historical manifest.
    # New standalone files, unrelated Rust/CI/docs and current metadata tools
    # cannot make frozen arithmetic evidence stale. Modifying a dependency
    # already used by the certification still requires a new reviewed record.
    return (path not in METADATA_TOOLS and path != AUDIT and not path.endswith(".md") and
            not path.startswith(NIGHT + "integration/") and
            (path in {"CollatzLab.lean", "lakefile.lean", "lake-manifest.json", "lean-toolchain"} or
             path.startswith(("CollatzLab/", "research/lean-audit/", "research/phase13/"))))


def frozen_inputs(recorded):
    return {path: value for path, value in recorded.items() if certification_path(path)}


def check_frozen_inputs(root, recorded):
    expected = frozen_inputs(recorded)
    actual = {path: file_info((root / path).read_bytes()) for path in expected}
    require(actual == expected, "frozen certification code/evidence differs from the recorded validation")
    return expected


def metadata_tools(root):
    return {path: file_info((root / path).read_bytes()) for path in sorted(METADATA_TOOLS)}


def resource_stats(text):
    elapsed = re.findall(r"Elapsed \(wall clock\) time .*: (\S+)\n", text)
    peak = re.findall(r"Maximum resident set size \(kbytes\): (\d+)", text)
    require(len(elapsed) == len(peak) == 1, "missing/duplicate resource timing or RSS")
    total = 0
    for field in elapsed[0].split(":"):
        total = total * 60 + float(field)
    require(re.findall(r"Exit status: (\d+)", text) == ["0"], "timed command did not pass")
    return {"wall_seconds": round(total, 2), "peak_resident_KiB": int(peak[0]), "exit_code": 0}


def check_resource_stats(run, text):
    require({key: run[key] for key in ("wall_seconds", "peak_resident_KiB", "exit_code")} == resource_stats(text),
            "recorded wall time/RSS/exit differs from captured resources")


def inventory(root):
    require({path.name for path in (root / NIGHT).glob("transitions-*.jsonl")} == {"transitions-0002.jsonl"},
            "the frozen transition segment set changed")
    result = {}
    for name, (count, size, digest, cap) in EVIDENCE.items():
        raw = (root / NIGHT / name).read_bytes()
        require(raw.endswith(b"\n") and len(raw.splitlines()) == count,
                "wrong final record count: " + name)
        require(len(raw) == size <= cap and sha(raw) == digest,
                "original evidence changed: " + name)
        result[name] = dict(file_info(raw), records=count, cap_bytes=cap, remaining_bytes=cap-size)
    return result


def smoke_counts(text):
    heights = re.findall(r"^PASS: (\d+) independent primitive witnesses,", text, re.M)
    transitions = re.findall(r"^PASS: (\d+) independently verified witness failures", text, re.M)
    shadows = re.findall(r"^PASS: (\d+) independently replayed levels;", text, re.M)
    require(heights == ["24"] and transitions == ["16"] and shadows == ["9"],
            "smoke counts do not attest the final 24/16/9 evidence")
    require(text.count("PASS: overnight smoke checks\n") == 1, "smoke did not finish successfully")
    return {"heights": 24, "transitions": 16, "raw_shadow_levels": 9}


def check_identity(audit):
    require(audit["format"] == FORMAT, "historical audit is not a current final audit")
    require(audit["source_commit"] == SOURCE and audit["integration_base"] == MAIN and
            audit["implementation_commit"] == IMPLEMENTATION and audit["review_commit"] == REVIEW,
            "source/base/review SHA differs from the reviewed pins")
    require(audit["counts"] == {"heights": 24, "transitions": 16, "raw_shadow_levels": 9},
            "final audit counts are stale")


def check_runs(root, ledger):
    raw = (root / RUNS).read_bytes()
    require(sha(raw) == VALIDATION_SHA256 and json.loads(raw) == ledger,
            "the original combined-tree validation ledger changed")
    require(ledger["format"] == "phase13-integration-validation-v1", "unknown validation ledger")
    require(ledger["entry_head"] == VALIDATION_HEAD, "wrong recorded combined-checkout entry HEAD")
    check_frozen_inputs(root, ledger["inputs"])
    runs = ledger["commands"]
    require(len(runs) == len(COMMANDS), "incomplete validation ledger")
    for run, (name, command, seconds, memory) in zip(runs, COMMANDS):
        actual = run["command"]
        require(run["name"] == name and actual[:len(command)] == command and
                len(actual) == len(command) + (name == "pinned-referee"), "unexpected checked command")
        require(run["exit_code"] == 0 and run["timeout_seconds"] == seconds and
                run["address_space_cap_KiB"] == memory, "failed/misbounded validation: " + name)
        require(run["inputs_unchanged"] is True, "inputs changed during validation")
        for key in ("log", "resources"):
            path = run[key]["path"]
            require(path == NIGHT + "integration/" + name + (".log" if key == "log" else ".resources"),
                    "unexpected run-log path")
            require(file_info((root / path).read_bytes()) == {k: v for k, v in run[key].items() if k != "path"},
                    "run log/hash changed: " + path)
        resources = (root / run["resources"]["path"]).read_text()
        check_resource_stats(run, resources)
        require(run["started_utc"] <= run["finished_utc"], "invalid run chronology")
    smoke = (root / runs[2]["log"]["path"]).read_text()
    return smoke_counts(smoke)


def git_bytes(root, ref, path):
    return subprocess.check_output(["git", "show", ref + ":" + path], cwd=root)


def preservation(root):
    for ref in (SOURCE, MAIN):
        subprocess.run(["git", "merge-base", "--is-ancestor", ref, "HEAD"], cwd=root, check=True)
    original = subprocess.check_output(["git", "ls-tree", "-r", "--name-only", SOURCE,
        NIGHT, JOURNAL, SUMMARY], cwd=root, text=True).splitlines()
    main = subprocess.check_output(["git", "ls-tree", "-r", "--name-only", MAIN], cwd=root, text=True).splitlines()
    require(len(original) == 107, "unexpected overnight source tree")
    protected = {}
    for ref, paths, excluded in ((SOURCE, original, MUTABLE), (MAIN, main, {".github/workflows/ci.yml"})):
        for path in paths:
            if path in excluded or not certification_path(path):
                continue
            raw = git_bytes(root, ref, path)
            require((root / path).read_bytes() == raw, "protected source changed: " + path)
            protected[path] = dict(file_info(raw), source_commit=ref)
    historical = {}
    for path, copy in ((SUMMARY, "summary-at-76bf613.md"), (AUDIT, "checkpoint-audit-at-76bf613.json")):
        target = NIGHT + "history/" + copy
        raw = git_bytes(root, SOURCE, path)
        require((root / target).read_bytes() == raw, "historical snapshot changed")
        historical[target] = dict(file_info(raw), extracted_from=SOURCE + ":" + path)
    journal_raw = git_bytes(root, SOURCE, JOURNAL)
    require((root / JOURNAL).read_bytes().endswith(journal_raw), "original journal suffix changed")
    return protected, historical, file_info(journal_raw)


def summary(audit):
    rows = ["| Artifact | Records | Bytes | SHA-256 |", "|---|---:|---:|---|"]
    for name, row in sorted(audit["evidence"].items()):
        rows.append(f"| [{name}](overnight/{name}) | {row['records']} | {row['bytes']:,} | `{row['sha256']}` |")
    commands = audit["validation"]["commands"]
    checked = ["| Recorded integration command | Exit | Wall seconds | Peak RSS KiB |", "|---|---:|---:|---:|"]
    for run in commands:
        checked.append(f"| [{run['name']}](overnight/{run['log']['path'].split('/')[-2]}/{run['log']['path'].split('/')[-1]}) | {run['exit_code']} | {run['wall_seconds']} | {run['peak_resident_KiB']} |")
    return f"""# Phase 13 overnight computation — final owner handoff

The frozen evidence contains **24 exact rational-height minima, 16 certified
witness transitions, and nine raw-shadow levels k=0..8**. The sixteenth
transition is from **N=87122**, whose witness first fails at zero-based index
**87123**, to the certified minimum at **N=87124**:
`H_87121 < H_87122 = H_87123 < H_87124 < H_90000`.
The 87122..87123 plateau has width two. Both endpoint heights have 51,875
bits; the positive increase has 35,247 bits and `1 < H_87124/H_87122 < 2`.
These are finite results preserved from the original run, not new research.

## Sources and corrected provenance

The source is the immutable [overnight head {SOURCE[:7]}](https://github.com/hipotures/collatz-lab/commit/{SOURCE}).
The integration base is [main {MAIN[:7]}](https://github.com/hipotures/collatz-lab/commit/{MAIN}),
which includes implementation PR #29 and independent referee PR #32.
[Issue #33](https://github.com/hipotures/collatz-lab/issues/33) repairs the
23-minima/15-transitions handoff identified in the
[independent report](../phase13-independent-referee-report.md), sections 8, 12, 13.
The old [summary](overnight/history/summary-at-76bf613.md) and
[audit](overnight/history/checkpoint-audit-at-76bf613.json) are preserved
byte-for-byte as historical snapshots; their entry HEAD, hashes and timing
attest the older checkpoint, not the final source head. See the
[history label](overnight/history/README.md).

The new [final audit](overnight/checkpoint-audit.json) binds the unchanged
certification sources/evidence and the original integration command outputs.
The hash-pinned validation ledger retains its complete historical combined-tree
input manifest and entry HEAD; unrelated future source, CI or documentation
changes do not invalidate this frozen experiment. Current checks compare the
explicit frozen certification subset and separately hash the metadata tools.
The arithmetic runs did not execute the metadata regression tests; those are
checked separately by the finalization procedure and CI. The PR head identifies
the committed handoff without a self-hash cycle. These are recorded observations,
not independent authentication of self-reported execution timestamps.

## Unchanged evidence and capacity

{chr(10).join(rows)}

Heights retain the 8 MiB cap, with 361,532 bytes free. The sealed first
transition segment retains all 11 records. Segment 2 retains five records;
its 512 KiB cap has 305,040 bytes free. No record was appended, recomputed or
rewritten, and no third segment was created. The final transition's positive
63,384-bit failing numerator has magnitude SHA-256
`4d36741dd00f16fa4a60d6f5c237bb03626c26401313dd2094ccea8ae8018324`.
The [completed checkpoint](overnight/transition-checkpoint.json),
[16-link replay](overnight/transition-verification.json),
[inventory](overnight/height-inventory.json) and
[final original replay log](overnight/transition-87122-replay.log) remain unchanged.

## Historical and current validation

The unchanged original [smoke.log](overnight/smoke.log) passed **24/16/9**,
exit 0, **464.54 seconds**, peak **102,832 KiB**, under the recorded
750-second outer timeout and 1 GiB child address-space cap. These are
historical observations, not the timing of the fresh integration checks.

{chr(10).join(checked)}

The recorded integration smoke used a 750-second outer timeout and 1 GiB address-space cap.
The recorded combined-tree matrix checked Lean, the exact **653**-declaration axiom
allowlist, research interfaces, Rust formatting/lints/**94 tests**, all current
Python checkers and static manuscript/Lean-name consistency. Independent
interface/axiom parsing checked that combined tree. The unchanged
referee reproduction fetches its exact two pinned refs, checks all **1,691**
baseline minima, all **24** overnight minima, **16** transitions and raw gcds
through k=8, and byte-compares both committed reviewer result files.
All recorded logs, timestamps, exit codes, caps and input fingerprints are in the
[validation ledger](overnight/integration/validation.json). CI status is
reported separately in the integration journal/PR, never inferred from a local run.

## Evidence boundary and owner decision

Primitive positive odd-denominator witnesses, actual signed numerator parities,
complete lattice exclusions and independent failure checks certify the finite
minima/transitions. Plateau maximality uses inherited written parity and
monotonicity arguments. The producer and original independent certification
scripts are unchanged. The merged mathematical referee report is unchanged;
the existing Lean statements and proofs are unchanged. No new Lean theorem,
mathematical priority, asymptotic law or publication readiness is claimed.
The general methods retain the source attribution in that report.

Widths remain `2,2,3,1,2,1,1,5,3,1,3,2,2,1,1,2`; earlier finite
counterexamples to nondecreasing widths and width-determined basis updates
remain intact. Raw gcds remain `[3,1,1,1,1,1,1,347,1]`. Exact B, asymptotic
gcd cancellation, remaining intermediate minima and the next failure of the
N=87124 witness are unresolved. Level 9 was not attempted.

The repair is ready for owner review after successful PR CI on the actual
integration head. No further computation is required for issue #33. Do not
resume the historical next-experiment instructions. No PR was merged, no issue
was closed, and the original branches were not moved. See the
[current journal](overnight-progress.md) and [finalization instructions](overnight/README.md#final-state-provenance).
"""


def check_summary(text, audit):
    require(text == summary(audit), "owner summary is stale; finalize separately after validation")


def check_audit(root, audit):
    check_identity(audit)
    require(audit["binding_scope"] == BINDING_SCOPE and audit["validation_sha256"] == VALIDATION_SHA256,
            "wrong frozen validation scope/identity")
    require(json.loads((root / RUNS).read_text()) == audit["validation"], "external validation ledger differs from final audit")
    require(audit["frozen_inputs"] == frozen_inputs(audit["validation"]["inputs"]),
            "explicit frozen certification manifest differs")
    require(audit["metadata_tools"] == metadata_tools(root), "metadata tools changed; rerun bounded controls and finalize")
    require(audit["evidence"] == inventory(root), "audit evidence inventory differs")
    require(audit["counts"] == check_runs(root, audit["validation"]), "final smoke differs")
    for path, entry in (audit["protected_files"] | audit["historical_snapshots"]).items():
        require(file_info((root / path).read_bytes()) == {k: entry[k] for k in ("bytes", "sha256")},
                "protected file/snapshot changed: " + path)
    raw = (root / JOURNAL).read_bytes()[-audit["original_journal"]["bytes"]:]
    require(file_info(raw) == audit["original_journal"], "original journal history changed")
    require(smoke_counts((root / NIGHT / "smoke.log").read_text()) == audit["counts"], "historical final smoke differs")
    historical = (root / NIGHT / "smoke.log").read_bytes()
    require(audit["historical_smoke"] == dict(file_info(historical), **resource_stats(historical.decode())),
            "historical smoke metadata differs from its captured output")
    check_summary((root / SUMMARY).read_text(), audit)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.write:
        ledger = json.loads((ROOT / RUNS).read_text())
        counts = check_runs(ROOT, ledger)
        for ref in (SOURCE, MAIN):
            subprocess.run(["git", "merge-base", "--is-ancestor", ref, ledger["entry_head"]], cwd=ROOT, check=True)
        protected, historical, original_journal = preservation(ROOT)
        audit = {"format": FORMAT, "source_commit": SOURCE,
                 "integration_base": MAIN, "implementation_commit": IMPLEMENTATION, "review_commit": REVIEW,
                 "classification": "final frozen finite evidence; no new mathematical claim",
                 "counts": counts, "evidence": inventory(ROOT), "validation": ledger,
                 "binding_scope": BINDING_SCOPE, "validation_sha256": VALIDATION_SHA256,
                 "frozen_inputs": frozen_inputs(ledger["inputs"]), "metadata_tools": metadata_tools(ROOT),
                 "protected_files": protected, "historical_snapshots": historical,
                 "original_journal": original_journal,
                 "historical_smoke": dict(file_info((ROOT / NIGHT / "smoke.log").read_bytes()),
                                          **resource_stats((ROOT / NIGHT / "smoke.log").read_text())),
                 "unavailable_checks": [], "remaining_research": ["exact B", "asymptotic gcd cancellation", "unsampled minima"]}
        (ROOT / AUDIT).write_bytes(encoded(audit))
        (ROOT / SUMMARY).write_text(summary(audit))
    check_audit(ROOT, json.loads((ROOT / AUDIT).read_text()))
    print("PASS: frozen final provenance, source pins, unchanged bytes, actual run hashes, smoke 24/16/9 and owner summary")


if __name__ == "__main__":
    main()
