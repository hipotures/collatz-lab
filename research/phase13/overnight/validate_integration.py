#!/usr/bin/env python3
"""Record bounded issue #33 validation; preserve all original experiment logs.

Run from the isolated integration checkout. A new --reproduction directory is
mandatory. No optimizer, new transition, Git write, push or merge is invoked.
Finalize the summary/audit separately only after this script succeeds.
"""

import argparse
from datetime import datetime, timezone
import os
from pathlib import Path
import re
import resource
import subprocess

from finalize_provenance import COMMANDS, NIGHT, ROOT, RUNS, encoded, file_info, inputs, require


def utc():
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def wall_seconds(resources):
    value = re.findall(r"Elapsed \(wall clock\) time .*: (\S+)\n", resources)
    require(len(value) == 1, "missing resource timing")
    fields = value[0].split(":")
    total = 0
    for field in fields:
        total = total * 60 + float(field)
    return round(total, 2)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reproduction", type=Path, required=True)
    args = parser.parse_args()
    require(not args.reproduction.exists(), "referee reproduction requires a NEW directory")
    run_dir = ROOT / NIGHT / "integration"
    run_dir.mkdir(exist_ok=True)
    require(not (ROOT / RUNS).exists(), "preserve the previous ledger/logs before starting another run")
    snapshot = inputs(ROOT)
    ledger = {"format": "phase13-integration-validation-v1", "entry_head": subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(), "started_utc": utc(),
        "worktree_status_at_entry": subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT, text=True).splitlines(),
        "inputs": snapshot, "commands": [], "tools": {}}
    for name, command in (("lean", ["lake", "env", "lean", "--version"]),
                          ("rustc", ["rustc", "--version"]), ("python", ["python3", "--version"])):
        ledger["tools"][name] = subprocess.check_output(command, cwd=ROOT, text=True).strip()
    for name, base, seconds, memory in COMMANDS:
        command = base + ([str(args.reproduction.resolve())] if name == "pinned-referee" else [])
        log_path = run_dir / (name + ".log")
        resource_path = run_dir / (name + ".resources")
        for path in (log_path, resource_path):
            require(not path.exists(), "refusing to overwrite a prior validation log: " + str(path))
        started = utc()
        print("START", name, started, flush=True)

        def limit():
            resource.setrlimit(resource.RLIMIT_AS, (memory * 1024, memory * 1024))

        environment = dict(os.environ, PYTHONDONTWRITEBYTECODE="1", CARGO_BUILD_JOBS="2")
        with log_path.open("wb") as output:
            result = subprocess.run(["timeout", "--signal=TERM", "--kill-after=10s", str(seconds) + "s",
                "/usr/bin/time", "-v", "-o", str(resource_path), *command], cwd=ROOT, env=environment,
                stdout=output, stderr=subprocess.STDOUT, preexec_fn=limit)
        resources = resource_path.read_text() if resource_path.exists() else ""
        peak = re.findall(r"Maximum resident set size \(kbytes\): (\d+)", resources)
        run = {"name": name, "command": command, "exit_code": result.returncode,
               "started_utc": started, "finished_utc": utc(), "timeout_seconds": seconds,
               "address_space_cap_KiB": memory, "inputs_unchanged": snapshot == inputs(ROOT),
               "wall_seconds": wall_seconds(resources) if resources else None,
               "peak_resident_KiB": int(peak[0]) if peak else None,
               "log": dict(file_info(log_path.read_bytes()), path=str(log_path.relative_to(ROOT))),
               "resources": dict(file_info(resource_path.read_bytes()), path=str(resource_path.relative_to(ROOT)))}
        ledger["commands"].append(run)
        ledger["finished_utc"] = utc()
        (ROOT / RUNS).write_bytes(encoded(ledger))
        print("END", name, "exit", result.returncode, "wall", run["wall_seconds"], "RSS", run["peak_resident_KiB"], flush=True)
        require(result.returncode == 0 and run["inputs_unchanged"], "validation failed; logs/ledger retained, do not finalize")
    print("PASS: complete current validation recorded; run finalize_provenance.py --write then --check", flush=True)


if __name__ == "__main__":
    main()
