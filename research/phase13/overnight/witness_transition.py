#!/usr/bin/env python3
"""Locate one witness's first failure and certify only that new prefix.

The scan uses literal substitution and actual numerator iteration. A located
checkpoint survives a later timeout; existing height/transition lines are
never replaced. Independent verification is required before publication.
"""

import argparse
import hashlib
import json
from pathlib import Path
import signal
import tempfile
import time

from extended_height import (MAX_FILE_BYTES, append_atomic, basis_certificate,
                             candidates, certify, frontier_prefix, residue)
from verify_results import verify_record


ROOT = Path(__file__).resolve().parent
TARGET = ROOT / "transitions.jsonl"
CHECKPOINT = ROOT / "transition-checkpoint.json"
MAX_TRANSITION_BYTES = 512 * 1024
MAX_SCAN_SPAN = 8192
SECOND_SEGMENT = "transitions-0002.jsonl"
LOCATED_FIELDS = ("source_N", "search_end_N", "source_record_sha256",
                  "first_failure_index", "failure_numerator_sign",
                  "failure_numerator_bits", "failure_numerator_abs_sha256",
                  "search_parity_sha256")


def digest(value):
    value = abs(value)
    return hashlib.sha256(value.to_bytes((value.bit_length() + 7) // 8, "big")).hexdigest()


def literal_word(length):
    word = "1"
    while len(word) < length:
        word = "".join("100111" if b == "1" else "111110" for b in word)
    return bytearray(int(b) for b in word[:length])


def first_failure(p, q, bits):
    if q <= 0 or q % 2 != 1:
        raise ValueError("positive odd denominator required")
    value = p
    for index, bit in enumerate(bits):
        if value % 2 != bit:
            return index, value
        value = (3 * value + q) // 2 if value % 2 else value // 2
    return None


def atomic(path, data, cap=MAX_TRANSITION_BYTES):
    assert len(data) <= cap, "transition evidence cap exceeded"
    with tempfile.NamedTemporaryFile(dir=ROOT, prefix="transition-", suffix=".tmp",
                                     delete=False) as stream:
        temporary = Path(stream.name)
        stream.write(data)
    temporary.replace(path)


def load_heights():
    path = ROOT / "heights.jsonl"
    assert path.stat().st_size <= MAX_FILE_BYTES
    raw = path.read_bytes()
    assert raw and raw.endswith(b"\n")
    rows, hashes = {}, {}
    for line in raw.splitlines(keepends=True):
        row = json.loads(line)
        assert row["N"] not in rows
        rows[row["N"]] = row
        hashes[row["N"]] = hashlib.sha256(line).hexdigest()
    return rows, hashes


def encoded(row):
    return (json.dumps(row, sort_keys=True, separators=(",", ":")) + "\n").encode()


def load_transitions():
    """Two bounded segments; an existing base segment stays sealed.

    Every new link binds its predecessor's exact line, including across the
    segment boundary. The independent replay implements its own reader.
    """
    assert set(ROOT.glob("transitions-*.jsonl")) <= {ROOT / SECOND_SEGMENT}
    segments, links, seen = [], [], set()
    for number, path in enumerate((TARGET, ROOT / SECOND_SEGMENT)):
        if not path.exists():
            continue
        assert number == len(segments), "missing preceding transition segment"
        assert 0 < path.stat().st_size <= MAX_TRANSITION_BYTES
        raw = path.read_bytes()
        assert raw.endswith(b"\n"), "incomplete transition segment"
        for line in raw.splitlines(keepends=True):
            row = json.loads(line)
            assert row["source_N"] not in seen, "duplicate transition source"
            if links:
                previous = links[-1][0]
                assert row["source_N"] == previous["target_N"], "disconnected transition chain"
                assert row["search_end_N"] == previous["search_end_N"]
                assert row["source_record_sha256"] == previous["target_record_sha256"]
            if number or "previous_transition_record_sha256" in row:
                assert links and row["previous_transition_record_sha256"] == links[-1][1]
            seen.add(row["source_N"])
            links.append((row, hashlib.sha256(line).hexdigest(), path.name))
        segments.append((path, raw))
    return segments, links


def publication_target(segments, line):
    # Existing first-segment bytes are historical evidence, never extended by
    # this version. No third segment is created implicitly.
    path = ROOT / SECOND_SEGMENT if segments else TARGET
    previous = segments[-1][1] if segments and segments[-1][0] == path else b""
    assert len(previous) + len(line) <= MAX_TRANSITION_BYTES, "transition segment capacity exhausted"
    return path, previous


def finish_checkpoint(row, line_hash, segment):
    completed = {"format": "phase13-transition-checkpoint-v1", "stage": "complete",
                 **{k: row[k] for k in LOCATED_FIELDS}, "target_N": row["target_N"],
                 "transition_record_sha256": line_hash, "transition_segment": segment}
    atomic(CHECKPOINT, (json.dumps(completed, indent=2) + "\n").encode())


def transition_record(source, target, source_hash, target_hash, located):
    old_h, new_h = int(source["H"], 16), int(target["H"], 16)
    assert new_h >= old_h
    exponent = (new_h // old_h).bit_length() - 1
    difference = new_h - old_h
    return {"format": "phase13-witness-transition-v1",
            "classification": "exact finite witness failure and independently certified minima",
            **{k: located[k] for k in ("source_N", "search_end_N", "first_failure_index",
                                       "failure_numerator_sign", "failure_numerator_bits",
                                       "failure_numerator_abs_sha256", "search_parity_sha256")},
            "source_record_sha256": source_hash, "target_record_sha256": target_hash,
            "target_N": target["N"],
            "source_minimality": basis_certificate(
                [[int(x, 16) for x in row] for row in source["basis"]],
                source["N"], old_h - 1),
            "target_minimality": basis_certificate(
                [[int(x, 16) for x in row] for row in target["basis"]],
                target["N"], new_h - 1),
            "same_height": new_h == old_h,
            "same_primitive_witness": (source["p"], source["q"]) == (target["p"], target["q"]),
            "source_height_bits": old_h.bit_length(), "target_height_bits": new_h.bit_length(),
            "height_difference_bits": difference.bit_length(),
            "height_difference_abs_sha256": digest(difference),
            "height_ratio_floor_log2": exponent}


def expired(_signum, _frame):
    raise TimeoutError("bounded transition budget exceeded; published records/checkpoint survive")


def run_request(start, through):
    """Publish at most one link; small fixtures exercise the same transaction."""
    started = time.perf_counter()
    rows, hashes = load_heights()
    source = rows[start]
    segments, links = load_transitions()
    located = None
    if CHECKPOINT.exists():
        assert CHECKPOINT.stat().st_size <= MAX_TRANSITION_BYTES
        checkpoint = json.loads(CHECKPOINT.read_bytes())
        assert checkpoint["format"] == "phase13-transition-checkpoint-v1"
        if checkpoint["stage"] == "located":
            assert checkpoint["source_N"] == start and checkpoint["search_end_N"] == through
            assert checkpoint["source_record_sha256"] == hashes[start]
            located = checkpoint
        else:
            assert checkpoint["stage"] == "complete"
            matches = [(row, segment) for row, sha, segment in links
                       if sha == checkpoint["transition_record_sha256"]]
            assert len(matches) == 1, "completed transition is missing"
            saved, segment = matches[0]
            assert all(checkpoint[k] == saved[k] for k in (*LOCATED_FIELDS, "target_N"))
            assert checkpoint.get("transition_segment", segment) == segment
    # The independent checker imports no producer or optimization code.
    from verify_transitions import verify_transition
    for saved, sha, segment in links:
        if (saved["source_N"], saved["search_end_N"]) == (start, through):
            verify_transition(saved, rows, hashes)
            if located is not None:
                assert all(located[k] == saved[k] for k in LOCATED_FIELDS)
                finish_checkpoint(saved, sha, segment)
                print("RECOVER: transition published before checkpoint completion", flush=True)
            print("SKIP: transition already published and independently rechecked", flush=True)
            return
    if links:
        assert links[-1][0]["target_N"] == start, "request must extend the stored chain"
        assert links[-1][0]["search_end_N"] == through
    if located is not None:
        print("RESUME: located first failure; no new witness scan", flush=True)
    else:
        bits = literal_word(through)
        result = first_failure(int(source["p"], 16), int(source["q"], 16), bits)
        assert result is not None, "no failure in bounded window; no minimum requested"
        index, value = result
        assert index >= start, "source witness fails its certified prefix"
        located = {"format": "phase13-transition-checkpoint-v1", "stage": "located",
                   "source_N": start, "search_end_N": through,
                   "source_record_sha256": hashes[start],
                   "first_failure_index": index,
                   "failure_numerator_sign": (value > 0) - (value < 0),
                   "failure_numerator_bits": abs(value).bit_length(),
                   "failure_numerator_abs_sha256": digest(value),
                   "search_parity_sha256": hashlib.sha256(bytes(bits)).hexdigest()}
        atomic(CHECKPOINT, (json.dumps(located, indent=2) + "\n").encode())
        print(f"LOCATED first_failure_index={index} target_N={index + 1} "
              f"elapsed_seconds={time.perf_counter() - started:.3f}", flush=True)
    target_n = located["first_failure_index"] + 1
    assert start < target_n <= through
    new_height = None
    if target_n not in rows:
        bits = frontier_prefix(target_n)
        candidate = next(candidates(residue(bits), target_n, [target_n]))
        new_height = certify(candidate, bits, method="basis")
        verify_record(new_height)
        height_line = encoded(new_height)
        assert (ROOT / "heights.jsonl").stat().st_size + len(height_line) <= MAX_FILE_BYTES, "height capacity exhausted"
        rows[target_n], hashes[target_n] = new_height, hashlib.sha256(height_line).hexdigest()
    record = transition_record(source, rows[target_n], hashes[start], hashes[target_n], located)
    if links:
        record["previous_transition_record_sha256"] = links[-1][1]
    verify_transition(record, rows, hashes)
    line = encoded(record)
    destination, previous = publication_target(segments, line)
    # BOTH exact sizes are checked before either evidence file is changed.
    # A stop after either atomic publication resumes from the located checkpoint.
    if new_height is not None:
        append_atomic(new_height)
        print(f"CERTIFIED new_N={target_n} height_bits={int(new_height['H'], 16).bit_length()} "
              f"elapsed_seconds={time.perf_counter() - started:.3f}", flush=True)
    atomic(destination, previous + line)
    finish_checkpoint(record, hashlib.sha256(line).hexdigest(), destination.name)
    print(f"PASS: first witness failure and exact minimum independently verified; "
          f"same_height={record['same_height']} ratio_floor_log2={record['height_ratio_floor_log2']} "
          f"elapsed_seconds={time.perf_counter() - started:.3f}", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--start", type=int, default=87092)
    parser.add_argument("--through", type=int, default=90000)
    parser.add_argument("--seconds", type=int, default=180)
    parser.add_argument("--write", action="store_true", required=True)
    args = parser.parse_args()
    if not (16384 < args.start < args.through <= 600000
            and args.through - args.start <= MAX_SCAN_SPAN and 1 <= args.seconds <= 180):
        parser.error("require 16384 < start < through <= 600000, span <= 8192, seconds in 1..180")
    signal.signal(signal.SIGALRM, expired)
    signal.alarm(args.seconds)
    try:
        run_request(args.start, args.through)
    finally:
        signal.alarm(0)


if __name__ == "__main__":
    main()
