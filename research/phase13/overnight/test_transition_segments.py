#!/usr/bin/env python3
"""Small exact controls for segmented evidence and interrupted publication.

All experiments here use the 68-bit control word in temporary directories.
Three separately implemented readers reject malformed segment boundaries.
Interruptions are injected at publication boundaries, never by killing a
child process. No stored large-prefix experiment is repeated.
"""

from contextlib import ExitStack, redirect_stdout
from copy import deepcopy
import hashlib
import io
import json
from pathlib import Path
import tempfile
from unittest.mock import patch

import extended_height as heights_engine
import probe_basis_pattern as probe
import verify_transitions as checker
from verify_results import verify_integer_record
import witness_transition as producer


ROOT = Path(__file__).resolve().parent


class Interrupted(RuntimeError):
    pass


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def fixture():
    bits = producer.literal_word(68)
    records = {r["N"]: heights_engine.certify(r, bits[:r["N"]], method="basis")
               for r in heights_engine.candidates(heights_engine.residue(bits), 68, range(69))}
    hashes = {n: sha(producer.encoded(row)) for n, row in records.items()}

    def link(start, preceding=None):
        row = records[start]
        index, value = producer.first_failure(int(row["p"], 16), int(row["q"], 16), bits)
        located = {"source_N": start, "search_end_N": 68, "first_failure_index": index,
                   "failure_numerator_sign": (value > 0) - (value < 0),
                   "failure_numerator_bits": abs(value).bit_length(),
                   "failure_numerator_abs_sha256": producer.digest(value),
                   "search_parity_sha256": sha(bytes(bits))}
        result = producer.transition_record(row, records[index + 1], hashes[start], hashes[index + 1], located)
        if preceding is not None:
            result["previous_transition_record_sha256"] = sha(producer.encoded(preceding))
        checker.verify_transition(result, records, hashes)
        return result

    first = link(11)
    second = link(first["target_N"], first)
    third = link(second["target_N"], second)
    return bits, records, hashes, (first, second, third)


def readers(root):
    return (producer.load_transitions, lambda: checker.read_segments(root),
            lambda: probe.load_transition_segments(root))


def storage_controls(records, hashes, links):
    first, second, _ = links
    base, extra = producer.encoded(first), producer.encoded(second)
    rejected = 0
    with tempfile.TemporaryDirectory(dir=ROOT, prefix="segment-read-test-") as directory:
        root = Path(directory)
        with patch.object(producer, "ROOT", root), patch.object(producer, "TARGET", root / "transitions.jsonl"):
            for segmented in (False, True):
                (root / "transitions.jsonl").write_bytes(base)
                if segmented:
                    (root / "transitions-0002.jsonl").write_bytes(extra)
                for read in readers(root):
                    read()
                raw, sources, rows = checker.read_segments(root)
                assert raw == base + (extra if segmented else b"")
                assert len(sources) == len(rows) == 1 + segmented
                for source, expected in zip(sources, (base, extra)):
                    assert source["bytes"] == len(expected) and source["sha256"] == sha(expected)
                for row in rows:
                    checker.verify_transition(row, records, hashes)

            mutations = []
            for key, value in (("source_N", first["source_N"]), ("source_N", second["source_N"] + 1),
                               ("search_end_N", 67), ("source_record_sha256", "0" * 64),
                               ("previous_transition_record_sha256", "0" * 64)):
                bad = deepcopy(second)
                bad[key] = value
                mutations.append({"transitions.jsonl": base, "transitions-0002.jsonl": producer.encoded(bad)})
            bad = deepcopy(second)
            del bad["previous_transition_record_sha256"]
            mutations.extend((
                {"transitions.jsonl": base, "transitions-0002.jsonl": producer.encoded(bad)},
                {"transitions-0002.jsonl": extra},
                {"transitions.jsonl": base, "transitions-0002.jsonl": extra[:-1]},
                {"transitions.jsonl": base, "transitions-0002.jsonl": b""},
                {"transitions.jsonl": base, "transitions-0002.jsonl": b" " * (512 * 1024 + 1)},
                {"transitions.jsonl": base, "transitions-0002.jsonl": extra + extra},
                {"transitions.jsonl": base, "transitions-0002.jsonl": extra,
                 "transitions-0003.jsonl": extra}))
            for files in mutations:
                for path in root.glob("*.jsonl"):
                    path.unlink()
                for name, raw in files.items():
                    (root / name).write_bytes(raw)
                for read in readers(root):
                    try:
                        read()
                    except (AssertionError, KeyError, ValueError):
                        rejected += 1
                    else:
                        raise AssertionError("malformed cross-segment evidence accepted")
    return rejected


def install_fixture(root, records, links, with_second=False):
    first, second, _ = links
    used = [first["source_N"], first["target_N"]]
    (root / "transitions.jsonl").write_bytes(producer.encoded(first))
    if with_second:
        # Extra inert metadata makes the existing segment almost fill a small
        # test cap; mathematical and predecessor certificates remain valid.
        second = {**second, "test_padding": "x" * 3000}
        (root / "transitions-0002.jsonl").write_bytes(producer.encoded(second))
        used.append(second["target_N"])
    (root / "heights.jsonl").write_bytes(b"".join(producer.encoded(records[n]) for n in used))
    return second if with_second else first


def publication_controls(bits, records, links):
    checked = 0
    for stop in ("none", "located", "height", "transition", "height-cap", "transition-cap"):
        with tempfile.TemporaryDirectory(dir=ROOT, prefix="segment-write-test-") as directory:
            root = Path(directory)
            first = install_fixture(root, records, links, with_second=stop == "transition-cap")
            start = first["target_N"]
            before_height = (root / "heights.jsonl").read_bytes()
            before_base = (root / "transitions.jsonl").read_bytes()
            before_extra = ((root / "transitions-0002.jsonl").read_bytes()
                            if (root / "transitions-0002.jsonl").exists() else None)
            checkpoint = root / "transition-checkpoint.json"
            with ExitStack() as stack, redirect_stdout(io.StringIO()):
                for module, name, value in (
                    (producer, "ROOT", root), (producer, "TARGET", root / "transitions.jsonl"),
                    (producer, "CHECKPOINT", checkpoint), (heights_engine, "ROOT", root),
                    (heights_engine, "TARGET", root / "heights.jsonl")):
                    stack.enter_context(patch.object(module, name, value))
                stack.enter_context(patch.object(producer, "verify_record",
                                               side_effect=lambda row: verify_integer_record(row, bits[:row["N"]])))
                if stop == "height-cap":
                    stack.enter_context(patch.object(producer, "MAX_FILE_BYTES", len(before_height)))
                if stop == "transition-cap":
                    stack.enter_context(patch.object(producer, "MAX_TRANSITION_BYTES", len(before_extra) + 1))
                original_atomic = producer.atomic
                original_candidates = producer.candidates

                def stopping_atomic(path, data, cap=producer.MAX_TRANSITION_BYTES):
                    if stop == "height" and path.name == "transitions-0002.jsonl":
                        raise Interrupted("height published before transition")
                    if stop == "transition" and path == checkpoint and json.loads(data)["stage"] == "complete":
                        raise Interrupted("transition published before completed checkpoint")
                    original_atomic(path, data, cap)

                with patch.object(producer, "atomic", side_effect=stopping_atomic), \
                     patch.object(producer, "candidates", side_effect=(Interrupted("located checkpoint saved")
                                  if stop == "located" else original_candidates)):
                    try:
                        producer.run_request(start, 68)
                    except Interrupted:
                        assert stop in ("located", "height", "transition")
                    except AssertionError as error:
                        assert stop in ("height-cap", "transition-cap"), str(error)
                        assert "capacity exhausted" in str(error)
                    else:
                        assert stop == "none"
                assert (root / "transitions.jsonl").read_bytes() == before_base
                if stop in ("height-cap", "transition-cap"):
                    assert (root / "heights.jsonl").read_bytes() == before_height
                    assert json.loads(checkpoint.read_bytes())["stage"] == "located"
                    after = ((root / "transitions-0002.jsonl").read_bytes()
                             if (root / "transitions-0002.jsonl").exists() else None)
                    assert after == before_extra
                    checked += 1
                    continue
                if stop != "none":
                    assert json.loads(checkpoint.read_bytes())["stage"] == "located"
                    published_transition = ((root / "transitions-0002.jsonl").read_bytes()
                                            if stop == "transition" else None)
                    with ExitStack() as resume:
                        for name in ("first_failure", "literal_word"):
                            resume.enter_context(patch.object(producer, name, side_effect=AssertionError("scan repeated")))
                        if stop != "located":
                            for name in ("candidates", "certify", "frontier_prefix", "residue", "append_atomic"):
                                resume.enter_context(patch.object(producer, name,
                                                                 side_effect=AssertionError("minimum repeated")))
                        producer.run_request(start, 68)
                    if published_transition is not None:
                        assert (root / "transitions-0002.jsonl").read_bytes() == published_transition
                    checked += 1
                assert json.loads(checkpoint.read_bytes())["stage"] == "complete"
                snapshot = {p.name: p.read_bytes() for p in root.iterdir()}
                with patch.object(producer, "first_failure", side_effect=AssertionError("scan repeated")), \
                     patch.object(producer, "candidates", side_effect=AssertionError("minimum repeated")):
                    producer.run_request(start, 68)
                assert snapshot == {p.name: p.read_bytes() for p in root.iterdir()}
                raw, sources, rows = checker.read_segments(root)
                stored, hashes = producer.load_heights()
                for row in rows:
                    checker.verify_transition(row, stored, hashes)
                assert len(sources) == 2 and raw.startswith(before_base)
                checked += 1
    return checked


def main():
    bits, records, hashes, links = fixture()
    rejected = storage_controls(records, hashes, links)
    checked = publication_controls(bits, records, links)
    print(f"PASS: legacy and two-segment fixtures independently replayed; {rejected} malformed-reader rejections; "
          f"{checked} publication/resumption/cap controls; base segment preserved; "
          "no repeated scan/minimum on durable resume; exact sizes checked before height publication")


if __name__ == "__main__":
    main()
