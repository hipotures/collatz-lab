#!/usr/bin/env python3
"""Exact small controls for first-failure semantics and transition certificates."""

from contextlib import ExitStack, redirect_stdout
from copy import deepcopy
from fractions import Fraction
import hashlib
import io
import json
from math import gcd
from pathlib import Path
import signal
import sys
import tempfile
from unittest.mock import patch

from extended_height import candidates, certify, residue
from verify_transitions import indexed_prefix, reverse_pair, verify_transition
import probe_basis_pattern as pattern
import witness_transition as producer
from witness_transition import digest, first_failure, literal_word, transition_record


def fraction_failure(p, q, bits):
    value = Fraction(p, q)
    for index, bit in enumerate(bits):
        parity = value.numerator % 2
        if parity != bit:
            return index, value
        value = (3 * value + 1) / 2 if parity else value / 2
    return None


def accepted(row, records, hashes):
    try:
        verify_transition(row, records, hashes)
    except (AssertionError, KeyError, ValueError):
        return False
    return True


def chain_controls(records, hashes, links, replayed):
    """Witness failures at tied heights must not certify plateau boundaries."""
    chain, start = {}, 0
    while start in links:
        chain[start] = links[start]
        start = links[start]["target_N"]
    replay = {"results": [replayed[n] for n in chain]}
    with patch.object(pattern, "END", 68):
        result = pattern.certified_chain(records, hashes, chain, replay)
        tied = [row for row in result["intervals"]
                if not row["strict_height_increase_at_next_prefix"]]
        assert tied, "missing equal-height witness change control"
        assert all(row["source_N"] not in result["counterexample_source_N"] for row in tied)

        # Independently enumerate every constant-height run in the tiny profile.
        # Compare the reported decreases with these full-height runs, including
        # the strict boundaries; witness changes alone must not count as edges.
        direct, lo, last = {}, 0, max(records)
        while lo <= last:
            hi = lo
            while hi < last and records[hi + 1]["H"] == records[lo]["H"]:
                hi += 1
            if lo > 0 and hi < last:
                direct[lo] = hi - lo + 1
            lo = hi + 1
        width_test = result["nondecreasing_width_test"]
        assert width_test["hypothesis_falsified"] and width_test["decreases"]
        for decrease in width_test["decreases"]:
            left, right = decrease["from_source_N"], decrease["to_source_N"]
            assert decrease["from_length"] == direct[left] > direct[right] == decrease["to_length"]
            assert right == left + direct[left]
            assert all(row["source_N"] not in (left, right) for row in tied)

        # Use complete height runs for eligibility and raw vector multiplication
        # for inequality of updates, independently of comparing coordinate rows.
        eligible = [row for row in result["intervals"]
                    if direct.get(row["source_N"]) == row["interval_length"]]
        pairs, expected = 0, []
        for index, left in enumerate(eligible):
            for right in eligible[index + 1:]:
                if direct[left["source_N"]] != direct[right["source_N"]]:
                    continue
                pairs += 1
                f, g = pattern.basis(records[right["source_N"]])
                predicted = [[alpha * f[i] + beta * g[i] for i in range(2)]
                             for alpha, beta in left["basis_update_rows"]]
                if predicted != pattern.basis(records[right["next_prefix_N"]]):
                    expected.append((left["source_N"], right["source_N"]))
        update_test = result["width_determines_basis_update_test"]
        assert pairs > 0 and expected
        assert update_test["equal_width_pairs_checked"] == pairs
        assert update_test["hypothesis_falsified"]
        assert [(row["from_source_N"], row["to_source_N"])
                for row in update_test["counterexamples"]] == expected
        for row in update_test["counterexamples"]:
            assert row["interval_length"] == direct[row["from_source_N"]] == direct[row["to_source_N"]]
            for key, start_key in (("from_basis_update_rows", "from_source_N"),
                                   ("to_basis_update_rows", "to_source_N")):
                start = row[start_key]
                f, g = pattern.basis(records[start])
                assert [[alpha * f[i] + beta * g[i] for i in range(2)]
                        for alpha, beta in row[key]] == pattern.basis(records[chain[start]["target_N"]])

        # A strict right boundary alone cannot establish a maximal plateau.
        row = next(row for row in result["intervals"]
                   if row["strict_height_increase_at_next_prefix"])
        source, target = row["source_N"], row["next_prefix_N"]
        isolated = pattern.certified_chain({n: records[n] for n in (source, target)}, hashes,
                                           {source: chain[source]}, {"results": [replayed[source]]})
        assert not isolated["intervals"][0]["strict_height_increase_at_source"]
        assert not isolated["hypothesis_falsified"]
        assert not isolated["nondecreasing_width_test"]["hypothesis_falsified"]
        assert isolated["nondecreasing_width_test"]["adjacent_maximal_plateau_pairs_checked"] == 0
        assert not isolated["width_determines_basis_update_test"]["hypothesis_falsified"]
        assert isolated["width_determines_basis_update_test"]["equal_width_pairs_checked"] == 0

        bad_replay = deepcopy(replay)
        bad_replay["results"][0]["constant_minimum_through_N"] += 1
        bad_links = deepcopy(chain)
        bad_links[0]["target_record_sha256"] = "0" * 64
        bad_basis = deepcopy(records)
        bad_basis[target]["basis"][0][0] = hex(int(bad_basis[target]["basis"][0][0], 16) + 1)
        disconnected = dict(chain)
        del disconnected[list(disconnected)[1]]
        mutations = ((records, hashes, chain, bad_replay),
                     (records, hashes, bad_links, replay),
                     (bad_basis, hashes, chain, replay),
                     (records, hashes, disconnected,
                      {"results": [replayed[n] for n in disconnected]}))
        for args in mutations:
            try:
                pattern.certified_chain(*args)
            except (AssertionError, KeyError, ValueError):
                pass
            else:
                raise AssertionError("malformed finite chain accepted")
    return len(chain), len(tied), len(mutations)


def resume_controls():
    """Replay publication in a temporary fixture, forbidding a new experiment."""
    root = Path(__file__).resolve().parent
    if not (root / "transitions.jsonl").exists():
        return 0
    rows = [json.loads(line) for line in (root / "transitions.jsonl").read_bytes().splitlines()]
    row = next(r for r in rows if r["source_N"] == 87092 and r["search_end_N"] == 90000)
    located = {k: row[k] for k in ("source_N", "search_end_N", "source_record_sha256",
                                   "first_failure_index", "failure_numerator_sign",
                                   "failure_numerator_bits", "failure_numerator_abs_sha256",
                                   "search_parity_sha256")}
    located.update(format="phase13-transition-checkpoint-v1", stage="located")
    fixture = b"".join(line for line in (root / "heights.jsonl").read_bytes().splitlines(keepends=True)
                       if json.loads(line)["N"] in (87092, row["target_N"]))

    class NewExperimentRequested(RuntimeError):
        pass

    handler = signal.getsignal(signal.SIGALRM)
    try:
        with tempfile.TemporaryDirectory(dir=root, prefix="transition-test-") as directory:
            temporary = Path(directory)
            heights = temporary / "heights.jsonl"
            heights.write_bytes(fixture)
            checkpoint = temporary / "transition-checkpoint.json"
            checkpoint.write_text(json.dumps(located) + "\n")
            target = temporary / "transitions.jsonl"
            with ExitStack() as stack:
                for name, value in (("ROOT", temporary), ("CHECKPOINT", checkpoint), ("TARGET", target)):
                    stack.enter_context(patch.object(producer, name, value))
                for name in ("first_failure", "candidates", "frontier_prefix", "residue", "append_atomic"):
                    stack.enter_context(patch.object(producer, name,
                                                    side_effect=AssertionError("experiment repeated on resume")))
                stack.enter_context(patch.object(producer, "literal_word", side_effect=NewExperimentRequested))
                command = ["witness_transition.py", "--start", "87092", "--through", "90000", "--write"]
                output = io.StringIO()
                with patch.object(sys, "argv", command), redirect_stdout(output):
                    producer.main()
                assert "RESUME:" in output.getvalue()
                assert json.loads(target.read_bytes()) == row
                assert heights.read_bytes() == fixture
                assert json.loads(checkpoint.read_bytes())["stage"] == "complete"
                published = target.read_bytes(), checkpoint.read_bytes()
                output = io.StringIO()
                with patch.object(sys, "argv", command), redirect_stdout(output):
                    producer.main()
                assert "SKIP:" in output.getvalue()
                assert published == (target.read_bytes(), checkpoint.read_bytes())
                # Prove the completed checkpoint permits the next request, but
                # stop before scanning that as-yet-uncertified witness.
                command[2] = str(row["target_N"])
                with patch.object(sys, "argv", command):
                    try:
                        producer.main()
                    except NewExperimentRequested:
                        pass
                    else:
                        raise AssertionError("next request did not reach its bounded scan")
                assert published == (target.read_bytes(), checkpoint.read_bytes())
                assert heights.read_bytes() == fixture
    finally:
        signal.alarm(0)
        signal.signal(signal.SIGALRM, handler)
    return 3


def main():
    fixed = literal_word(128)
    assert fixed == indexed_prefix(128)
    patterns = [fixed, bytearray(128), bytearray([1] * 128), bytearray([1, 0] * 64)]
    controls = no_failure = 0
    for p in range(-15, 16):
        for q in range(1, 16, 2):
            if gcd(p, q) != 1:
                continue
            for pattern in patterns:
                for length in (0, 1, 2, 11, 12, 68, 128):
                    bits = pattern[:length]
                    scanned = first_failure(p, q, bits)
                    reference = fraction_failure(p, q, bits)
                    numerator, denominator = reverse_pair(bits)
                    delta = p * denominator - q * numerator
                    valuation = (abs(delta) & -abs(delta)).bit_length() - 1 if delta else length
                    if reference is None:
                        assert scanned is None and valuation >= length
                        no_failure += 1
                    else:
                        assert scanned is not None and scanned[0] == reference[0] == valuation
                        assert Fraction(scanned[1], q) == reference[1]
                    controls += 1
    for q in (-3, 0, 2):
        try:
            first_failure(1, q, fixed)
        except ValueError:
            pass
        else:
            raise AssertionError("invalid denominator accepted")

    # Tiny complete profiles are controls, not new large-prefix experiments.
    bits = literal_word(68)
    all_candidates = {r["N"]: r for r in candidates(residue(bits), 68, range(69))}
    records = {n: certify(candidate, bits[:n], method="basis")
               for n, candidate in all_candidates.items()}
    hashes = {n: hashlib.sha256((json.dumps(row, sort_keys=True) + "\n").encode()).hexdigest()
              for n, row in records.items()}
    checked = tied = strict = 0
    links, replayed = {}, {}
    good = None
    for n in range(68):
        source = records[n]
        result = first_failure(int(source["p"], 16), int(source["q"], 16), bits)
        if result is None:
            continue
        index, value = result
        located = {"source_N": n, "search_end_N": len(bits), "first_failure_index": index,
                   "failure_numerator_sign": (value > 0) - (value < 0),
                   "failure_numerator_bits": abs(value).bit_length(),
                   "failure_numerator_abs_sha256": digest(value),
                   "search_parity_sha256": hashlib.sha256(bytes(bits)).hexdigest()}
        row = transition_record(source, records[index + 1], hashes[n], hashes[index + 1], located)
        result = verify_transition(row, records, hashes)
        links[n], replayed[n] = row, result
        assert result["constant_minimum_through_N"] == index
        checked += 1
        tied += row["same_height"]
        strict += not row["same_height"]
        if n == 11:
            assert index == 11 and int(source["H"], 16) == 3
            assert int(records[12]["H"], 16) == 513
            good = row
    assert good is not None and tied and strict
    mutations = []
    for key in ("first_failure_index", "target_N", "search_end_N", "source_height_bits",
                "target_height_bits", "failure_numerator_bits", "height_difference_bits",
                "height_ratio_floor_log2"):
        bad = deepcopy(good)
        bad[key] += 1
        mutations.append(bad)
    for key in ("source_record_sha256", "target_record_sha256", "search_parity_sha256",
                "failure_numerator_abs_sha256", "height_difference_abs_sha256"):
        bad = deepcopy(good)
        bad[key] = "0" * 64
        mutations.append(bad)
    for key in ("same_height", "same_primitive_witness"):
        bad = deepcopy(good)
        bad[key] = not bad[key]
        mutations.append(bad)
    bad = deepcopy(good)
    bad["failure_numerator_sign"] *= -1
    mutations.append(bad)
    for key in ("source_minimality", "target_minimality"):
        bad = deepcopy(good)
        bad[key]["bound"] = hex(int(bad[key]["bound"], 16) + 1)
        mutations.append(bad)
    for bad in mutations:
        assert not accepted(bad, records, hashes), "corrupt transition accepted"
    chain_count, chain_ties, chain_bad = chain_controls(records, hashes, links, replayed)
    resume = resume_controls()
    print(f"PASS: {controls} signed Fraction/valuation controls ({no_failure} no-failure cases); "
          f"{checked} small transition certificates ({tied} ties, {strict} strict increases); "
          f"{len(mutations)} rejected corruptions; {resume} publication/resumption controls; H_11=3, H_12=513")
    print(f"PASS: {chain_count} independently certified small chain links ({chain_ties} ties); "
          f"width decreases agree with direct complete height runs; "
          f"equal-width update comparisons agree with raw vector multiplication; "
          f"unknown left boundary stays unclassified; {chain_bad} malformed chains rejected")


if __name__ == "__main__":
    main()
