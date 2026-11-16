#!/usr/bin/env python3
"""Independent first-failure replay by reverse branches and 2-adic valuation.

Imports only the independent height-certificate checker, never the producer.
Each referenced minimum receives a compact box proof. This checker locates
the source's failure through an exact cylinder discrepancy, independently
of the producer's actual forward numerator scan.
"""

import argparse
import hashlib
import json
from pathlib import Path
import signal
import tempfile

from verify_results import verify_integer_record


ROOT = Path(__file__).resolve().parent
MAX_BYTES = 512 * 1024


def read_segments(root):
    """Independent bounded storage replay, with exact cross-segment links.

    This reads at most two fixed names. Partition hashes in the manifest bind
    the segment boundary as well as the concatenated evidence stream.
    """
    names = ("transitions.jsonl", "transitions-0002.jsonl")
    assert {p.name for p in root.glob("transitions-*.jsonl")} <= {names[1]}
    chunks, sources, records, seen = [], [], [], set()
    last = None
    for number, name in enumerate(names):
        path = root / name
        if not path.exists():
            assert number == 1, "missing base transition segment"
            continue
        assert number == len(chunks), "missing preceding transition segment"
        assert 0 < path.stat().st_size <= MAX_BYTES
        raw = path.read_bytes()
        assert raw.endswith(b"\n"), "incomplete transition segment"
        lines = raw.splitlines(keepends=True)
        for line in lines:
            row = json.loads(line)
            start = row["source_N"]
            assert type(start) is int and start not in seen, "duplicate transition source"
            if records:
                preceding = records[-1]
                assert start == preceding["target_N"], "disconnected transition chain"
                assert row["search_end_N"] == preceding["search_end_N"]
                assert row["source_record_sha256"] == preceding["target_record_sha256"]
            if number == 1 or "previous_transition_record_sha256" in row:
                assert last is not None and row["previous_transition_record_sha256"] == last
            seen.add(start)
            records.append(row)
            last = hashlib.sha256(line).hexdigest()
        chunks.append(raw)
        sources.append({"path": name, "bytes": len(raw), "records": len(lines),
                        "sha256": hashlib.sha256(raw).hexdigest()})
    return b"".join(chunks), sources, records


def magnitude_hash(value):
    size = (abs(value).bit_length() + 7) // 8
    return hashlib.sha256(abs(value).to_bytes(size, "big")).hexdigest()


def indexed_prefix(length):
    images = ("111110", "100111")
    bits = bytearray()
    for index in range(length):
        digits = []
        while index:
            index, digit = divmod(index, 6)
            digits.append(digit)
        letter = 1
        while digits:
            letter = int(images[letter][digits.pop()])
        bits.append(letter)
    return bits


def reverse_pair(bits):
    numerator, denominator = 0, 1
    for bit in reversed(bits):
        numerator = 2 * numerator - (denominator if bit else 0)
        denominator *= 3 if bit else 1
    return numerator, denominator


def verify_transition(row, heights, hashes):
    assert row["format"] == "phase13-witness-transition-v1"
    assert row["classification"] == "exact finite witness failure and independently certified minima"
    start, end, failure, target_n = (row[k] for k in
                                   ("source_N", "search_end_N", "first_failure_index", "target_N"))
    assert all(type(x) is int for x in (start, end, failure, target_n))
    assert 0 <= start <= failure < end <= 600000 and 0 < end - start <= 8192
    assert target_n == failure + 1
    source, target = heights[start], heights[target_n]
    assert source["N"] == start and target["N"] == target_n
    assert row["source_record_sha256"] == hashes[start]
    assert row["target_record_sha256"] == hashes[target_n]
    bits = indexed_prefix(end)
    assert hashlib.sha256(bytes(bits)).hexdigest() == row["search_parity_sha256"]
    for record, cert, n in ((source, row["source_minimality"], start),
                            (target, row["target_minimality"], target_n)):
        assert record["format"] == "phase13-overnight-height-v1"
        assert hashlib.sha256(bytes(bits[:n])).hexdigest() == record["parity_sha256"]
        verify_integer_record({**record, "minimality": cert}, bits[:n])
    p, q = int(source["p"], 16), int(source["q"], 16)
    numerator, denominator = reverse_pair(bits)
    discrepancy = p * denominator - numerator * q
    assert discrepancy != 0, "no failure within the bounded search"
    valuation = (abs(discrepancy) & -abs(discrepancy)).bit_length() - 1
    assert valuation == failure, "claimed first failure differs from exact cylinder valuation"
    numerator, denominator = reverse_pair(bits[:failure])
    value, remainder = divmod(p * denominator - numerator * q, 1 << failure)
    assert remainder == 0 and value % 2 != bits[failure]
    assert row["failure_numerator_sign"] == (value > 0) - (value < 0)
    assert row["failure_numerator_bits"] == abs(value).bit_length()
    assert row["failure_numerator_abs_sha256"] == magnitude_hash(value)
    old_h, new_h = int(source["H"], 16), int(target["H"], 16)
    assert new_h >= old_h
    assert type(row["same_height"]) is bool and row["same_height"] == (old_h == new_h)
    same_witness = (source["p"], source["q"]) == (target["p"], target["q"])
    assert type(row["same_primitive_witness"]) is bool
    assert row["same_primitive_witness"] == same_witness and not same_witness
    assert (row["source_height_bits"], row["target_height_bits"]) == (old_h.bit_length(), new_h.bit_length())
    difference = new_h - old_h
    assert row["height_difference_bits"] == difference.bit_length()
    assert row["height_difference_abs_sha256"] == magnitude_hash(difference)
    exponent = row["height_ratio_floor_log2"]
    assert type(exponent) is int and 0 <= exponent <= 600000
    assert old_h << exponent <= new_h < old_h << (exponent + 1)
    return {"source_N": start, "first_failure_index": failure, "target_N": target_n,
            "constant_minimum_through_N": failure,
            "strict_height_increase_at_target": new_h > old_h,
            "source_height_bits": old_h.bit_length(), "target_height_bits": new_h.bit_length()}


def expired(_signum, _frame):
    raise TimeoutError("independent transition check exceeded 180 seconds")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--write", action="store_true")
    args = parser.parse_args()
    path = ROOT / "heights.jsonl"
    assert path.stat().st_size <= 8 * 1024 * 1024
    height_raw = path.read_bytes()
    assert height_raw.endswith(b"\n")
    heights, hashes = {}, {}
    for line in height_raw.splitlines(keepends=True):
        record = json.loads(line)
        assert record["N"] not in heights
        heights[record["N"]] = record
        hashes[record["N"]] = hashlib.sha256(line).hexdigest()
    raw, sources, records = read_segments(ROOT)
    signal.signal(signal.SIGALRM, expired)
    results, seen = [], set()
    for row in records:
        signal.alarm(180)
        assert row["source_N"] > 16384
        key = row["source_N"], row["search_end_N"]
        assert key not in seen
        seen.add(key)
        results.append(verify_transition(row, heights, hashes))
        signal.alarm(0)
        print(json.dumps(results[-1], sort_keys=True), flush=True)
    manifest = {"format": "phase13-transition-replay-v2",
                "classification": "independent finite certificate; no asymptotic inference",
                "source_sha256": hashlib.sha256(raw).hexdigest(), "source_bytes": len(raw),
                "sources": sources,
                "height_source_sha256": hashlib.sha256(height_raw).hexdigest(),
                "results": results,
                "failure_method": "reverse inverse branches and exact 2-adic cylinder valuation"}
    destination = ROOT / "transition-verification.json"
    if args.write:
        with tempfile.NamedTemporaryFile(dir=ROOT, prefix="transition-replay-", suffix=".tmp",
                                         delete=False) as stream:
            temporary = Path(stream.name)
            stream.write((json.dumps(manifest, indent=2) + "\n").encode())
        temporary.replace(destination)
    else:
        assert json.loads(destination.read_bytes()) == manifest
    print(f"PASS: {len(results)} independently verified witness failures and exact height comparisons")


if __name__ == "__main__":
    main()
