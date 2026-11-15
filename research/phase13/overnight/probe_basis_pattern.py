#!/usr/bin/env python3
"""Bounded falsification of a specific two-bit basis-update extrapolation.

The two certified links starting at 87092 and 87094 have the same update.
Test its literal repetition at the already stored N=90000 cylinder. Also
derive basis changes and plateau widths from the separately replayed chain.
No optimization or new minimum is computed. Forward actual parity and reverse
integer branches independently check the predicted witness's first failure.
"""

import argparse
import hashlib
import json
from math import gcd
from pathlib import Path
import signal
import tempfile


ROOT = Path(__file__).resolve().parent
DESTINATION = ROOT / "basis-pattern-probe.json"
SOURCES = (87092, 87094)
END = 90000


def magnitude(value):
    value = abs(value)
    return hashlib.sha256(value.to_bytes((value.bit_length() + 7) // 8, "big")).hexdigest()


def load(path, cap, key):
    assert 0 < path.stat().st_size <= cap
    raw = path.read_bytes()
    assert raw.endswith(b"\n")
    records, hashes = {}, {}
    for line in raw.splitlines(keepends=True):
        row = json.loads(line)
        identifier = row[key]
        assert identifier not in records
        records[identifier] = row
        hashes[identifier] = hashlib.sha256(line).hexdigest()
    return raw, records, hashes


def load_transition_segments(root):
    """Read both fixed segments without importing either research engine."""
    names = ("transitions.jsonl", "transitions-0002.jsonl")
    assert {p.name for p in root.glob("transitions-*.jsonl")} <= {names[1]}
    chunks, sources, records = [], [], {}
    predecessor = predecessor_hash = None
    for number, name in enumerate(names):
        path = root / name
        if not path.exists():
            assert number == 1, "missing base transition segment"
            continue
        assert number == len(chunks)
        raw, part, hashes = load(path, 512 * 1024, "source_N")
        for start, row in part.items():
            assert start not in records, "duplicate transition source"
            if predecessor is not None:
                assert start == predecessor["target_N"], "disconnected transition chain"
                assert row["search_end_N"] == predecessor["search_end_N"]
                assert row["source_record_sha256"] == predecessor["target_record_sha256"]
            if number or "previous_transition_record_sha256" in row:
                assert predecessor_hash is not None
                assert row["previous_transition_record_sha256"] == predecessor_hash
            records[start] = row
            predecessor, predecessor_hash = row, hashes[start]
        chunks.append(raw)
        sources.append({"path": name, "bytes": len(raw), "records": len(part),
                        "sha256": hashlib.sha256(raw).hexdigest()})
    return b"".join(chunks), sources, records


def basis(row):
    return [[int(x, 16) for x in v] for v in row["basis"]]


def coordinates(old, vector):
    f, g = old
    determinant = f[0] * g[1] - f[1] * g[0]
    alpha, ra = divmod(vector[0] * g[1] - vector[1] * g[0], determinant)
    beta, rb = divmod(f[0] * vector[1] - f[1] * vector[0], determinant)
    assert ra == rb == 0
    assert vector == [alpha * f[i] + beta * g[i] for i in range(2)]
    return [alpha, beta]


def certified_chain(heights, hashes, transitions, replay):
    """Derived finite metadata; smoke independently replays its certificates.

    A first failure only gives an interval of constant minimum. Call it a
    maximal plateau only when certificates also give strict changes on both
    sides. Selected-basis coordinates are checked by direct multiplication.
    """
    verified = {row["source_N"]: row for row in replay["results"]}
    assert len(verified) == len(transitions) == len(replay["results"])
    chain = []
    for start, row in sorted(transitions.items()):
        end, failure = row["target_N"], row["first_failure_index"]
        assert row["source_N"] == start and row["search_end_N"] == END
        assert start <= failure and end == failure + 1
        assert row["source_record_sha256"] == hashes[start]
        assert row["target_record_sha256"] == hashes[end]
        if chain:
            assert chain[-1]["next_prefix_N"] == start, "not a contiguous chain"
        old_h, new_h = (int(heights[n]["H"], 16) for n in (start, end))
        assert new_h >= old_h
        assert verified[start] == {
            "source_N": start, "first_failure_index": failure, "target_N": end,
            "constant_minimum_through_N": failure,
            "strict_height_increase_at_target": new_h > old_h,
            "source_height_bits": old_h.bit_length(), "target_height_bits": new_h.bit_length()}
        old, new = basis(heights[start]), basis(heights[end])
        update = [coordinates(old, vector) for vector in new]
        assert abs(update[0][0] * update[1][1] - update[0][1] * update[1][0]) == 1 << (end - start)
        for n, (f, g) in ((start, old), (end, new)):
            assert abs(f[0] * g[1] - f[1] * g[0]) == 1 << n
            assert f[1] % 2 == 0 and g[1] % 2 == 1
            a = int(heights[n]["A"], 16)
            assert all((p - a * q) % (1 << n) == 0 for p, q in (f, g))
        left_strict = (int(heights[start - 1]["H"], 16) < old_h
                       if start - 1 in heights else
                       bool(chain and chain[-1]["strict_height_increase_at_next_prefix"]))
        chain.append({"source_N": start, "constant_minimum_through_N": failure,
                      "next_prefix_N": end, "interval_length": end - start,
                      "strict_height_increase_at_source": left_strict,
                      "strict_height_increase_at_next_prefix": new_h > old_h,
                      "basis_update_rows": update})
    counterexamples = [row for row in chain if row["interval_length"] != 2
                      and row["strict_height_increase_at_source"]
                      and row["strict_height_increase_at_next_prefix"]]
    # Compare adjacent intervals only when BOTH are certified maximal plateaux.
    # A tied witness change or unknown left boundary cannot support this test.
    comparisons, decreases = 0, []
    for left, right in zip(chain, chain[1:]):
        if not all(row["strict_height_increase_at_source"]
                   and row["strict_height_increase_at_next_prefix"] for row in (left, right)):
            continue
        comparisons += 1
        if right["interval_length"] < left["interval_length"]:
            decreases.append({"from_source_N": left["source_N"],
                              "to_source_N": right["source_N"],
                              "from_length": left["interval_length"],
                              "to_length": right["interval_length"]})
    # Equal index growth fixes a determinant, but need not fix the selected
    # basis update. Compare all equal-width pairs with strict boundaries.
    maximal = [row for row in chain if row["strict_height_increase_at_source"]
               and row["strict_height_increase_at_next_prefix"]]
    equal_width_pairs, different_updates = 0, []
    for index, left in enumerate(maximal):
        for right in maximal[index + 1:]:
            if left["interval_length"] != right["interval_length"]:
                continue
            equal_width_pairs += 1
            if left["basis_update_rows"] != right["basis_update_rows"]:
                different_updates.append({
                    "from_source_N": left["source_N"], "to_source_N": right["source_N"],
                    "interval_length": left["interval_length"],
                    "from_basis_update_rows": left["basis_update_rows"],
                    "to_basis_update_rows": right["basis_update_rows"]})
    return {"classification": "derived exact finite metadata from separately replayed certificates",
            "intervals": chain,
            "hypothesis_tested": "each maximal minimum plateau in this certified chain has length two",
            "hypothesis_falsified": bool(counterexamples),
            "counterexample_source_N": [row["source_N"] for row in counterexamples],
            "nondecreasing_width_test": {
                "hypothesis_tested": "widths of consecutive certified maximal plateaux never decrease",
                "adjacent_maximal_plateau_pairs_checked": comparisons,
                "hypothesis_falsified": bool(decreases), "decreases": decreases},
            "width_determines_basis_update_test": {
                "hypothesis_tested": "equal-width certified maximal plateaux have equal selected-basis update matrices",
                "equal_width_pairs_checked": equal_width_pairs,
                "hypothesis_falsified": bool(different_updates),
                "counterexamples": different_updates}}


def probe():
    height_raw, heights, hashes = load(ROOT / "heights.jsonl", 8 * 1024 * 1024, "N")
    transition_raw, sources, transitions = load_transition_segments(ROOT)
    replay = json.loads((ROOT / "transition-verification.json").read_bytes())
    assert replay["format"] == "phase13-transition-replay-v2" and replay["sources"] == sources
    assert replay["source_sha256"] == hashlib.sha256(transition_raw).hexdigest()
    assert replay["source_bytes"] == len(transition_raw)
    assert replay["height_source_sha256"] == hashlib.sha256(height_raw).hexdigest()
    chain = certified_chain(heights, hashes, transitions, replay)
    links, increments = [], []
    for start in SOURCES:
        row = transitions[start]
        assert row["target_N"] == start + 2 and row["search_end_N"] == END
        assert row["source_record_sha256"] == hashes[start]
        assert row["target_record_sha256"] == hashes[start + 2]
        old, new = basis(heights[start]), basis(heights[start + 2])
        update = [coordinates(old, v) for v in new]
        assert update == [[4, 0], [2, 1]]
        links.append({"from_N": start, "to_N": start + 2, "basis_update_rows": update})
        increments.append(int(heights[start + 2]["H"], 16) - int(heights[start]["H"], 16))
    assert all(difference > 0 for difference in increments)

    # Derive a closed formula; separately replay all 1454 proposed updates.
    start = SOURCES[0]
    steps, remainder = divmod(END - start, 2)
    assert remainder == 0 and 0 < steps <= 4096
    f, g = basis(heights[start])
    scale = 1 << (2 * steps)
    coefficient, remainder = divmod(2 * (scale - 1), 3)
    assert remainder == 0
    predicted = [[scale * x for x in f], [g[i] + coefficient * f[i] for i in range(2)]]
    iterated_f, iterated_g = f, g
    for _ in range(steps):
        iterated_f, iterated_g = ([4 * x for x in iterated_f],
                                  [iterated_g[i] + 2 * iterated_f[i] for i in range(2)])
    assert predicted == [iterated_f, iterated_g]
    p, q = predicted[1]
    if q < 0:
        p, q = -p, -q
    assert q > 0 and q % 2 == 1
    known_end = SOURCES[-1] + 2
    assert (p - int(heights[known_end]["A"], 16) * q) % (1 << known_end) == 0

    word = "1"
    while len(word) < END:
        word = "".join("100111" if b == "1" else "111110" for b in word)
    bits = bytearray(int(b) for b in word[:END])
    assert hashlib.sha256(bytes(bits)).hexdigest() == heights[END]["parity_sha256"]
    value, forward = p, None
    for index, bit in enumerate(bits):
        if value % 2 != bit:
            forward = index
            break
        value = (3 * value + q) // 2 if bit else value // 2
    numerator, denominator = 0, 1
    for bit in reversed(bits):
        numerator = 2 * numerator - (denominator if bit else 0)
        denominator *= 3 if bit else 1
    assert numerator * pow(denominator, -1, 1 << END) % (1 << END) == int(heights[END]["A"], 16)
    discrepancy = p * denominator - q * numerator
    valuation = (abs(discrepancy) & -abs(discrepancy)).bit_length() - 1 if discrepancy else END
    reverse = valuation if valuation < END else None
    assert forward == reverse
    failure_state = None
    if forward is not None:
        assert forward >= known_end
        numerator, denominator = 0, 1
        for bit in reversed(bits[:forward]):
            numerator = 2 * numerator - (denominator if bit else 0)
            denominator *= 3 if bit else 1
        reconstructed, remainder = divmod(p * denominator - q * numerator, 1 << forward)
        assert remainder == 0 and reconstructed == value and reconstructed % 2 != bits[forward]
        failure_state = {"numerator_sign": (value > 0) - (value < 0),
                         "numerator_bits": abs(value).bit_length(),
                         "numerator_abs_sha256": magnitude(value)}
    stored = heights[END]
    return {"format": "phase13-basis-pattern-probe-v1",
            "classification": "exact finite extrapolation test; no new minimum or asymptotic inference",
            "height_source_sha256": hashlib.sha256(height_raw).hexdigest(),
            "transition_source_sha256": hashlib.sha256(transition_raw).hexdigest(),
            "transition_sources": sources,
            "observed_links": links,
            "certified_transition_chain": chain,
            "second_height_increment_is_four_times_first": increments[1] == 4 * increments[0],
            "hypothesis_tested": "repeat f'=4*f, g'=2*f+g every two bits from N=87092 through N=90000",
            "prediction_start_N": start, "prediction_end_N": END, "prediction_steps": steps,
            "predicted_numerator_sign": (p > 0) - (p < 0),
            "predicted_numerator_bits": abs(p).bit_length(), "predicted_denominator_bits": q.bit_length(),
            "predicted_numerator_abs_sha256": magnitude(p), "predicted_denominator_sha256": magnitude(q),
            "predicted_coordinate_gcd": hex(gcd(p, q)),
            "closed_formula_matches_iterated_updates": True,
            "first_failure_index": forward,
            "prediction_falsified_by_actual_parity": forward is not None,
            "first_failing_prefix_N": forward + 1 if forward is not None else None,
            "forward_and_reverse_failure_agree": True,
            "failure_state_checked_by_two_routes": failure_state,
            "predicted_height_less_than_stored_minimum": max(abs(p), q) < int(stored["H"], 16),
            "predicted_witness_equals_stored_endpoint": (p, q) == (int(stored["p"], 16), int(stored["q"], 16))}


def expired(_signum, _frame):
    raise TimeoutError("basis-pattern probe exceeded its 30-second budget")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()
    signal.signal(signal.SIGALRM, expired)
    signal.alarm(30)
    result = probe()
    if args.write:
        data = (json.dumps(result, indent=2) + "\n").encode()
        assert len(data) <= 32 * 1024
        with tempfile.NamedTemporaryFile(dir=ROOT, prefix="basis-probe-", suffix=".tmp",
                                         delete=False) as stream:
            temporary = Path(stream.name)
            stream.write(data)
        temporary.replace(DESTINATION)
    else:
        assert json.loads(DESTINATION.read_bytes()) == result
    signal.alarm(0)
    print(f"PASS: two exact basis links; 1454 proposed updates checked by two routes; "
          f"prediction_falsified={result['prediction_falsified_by_actual_parity']} "
          f"first_failure_index={result['first_failure_index']}")
    chain = result["certified_transition_chain"]
    print(f"PASS: {len(chain['intervals'])} certified chain intervals; "
          f"two-prefix plateau claim falsified={chain['hypothesis_falsified']}")
    width_test = chain["nondecreasing_width_test"]
    print(f"PASS: {width_test['adjacent_maximal_plateau_pairs_checked']} adjacent maximal plateau pairs; "
          f"nondecreasing widths falsified={width_test['hypothesis_falsified']}")
    update_test = chain["width_determines_basis_update_test"]
    print(f"PASS: {update_test['equal_width_pairs_checked']} equal-width maximal plateau pairs; "
          f"width determines selected-basis update falsified={update_test['hypothesis_falsified']}")


if __name__ == "__main__":
    main()
