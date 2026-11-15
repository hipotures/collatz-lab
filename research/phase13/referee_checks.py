#!/usr/bin/env python3
"""Issue #31: independent exact checks; no project code is imported.

The minimum proof uses a full signed Cramer-coefficient cover, with positive
odd denominators. It does not replay either author's optimization algorithm
or consume the stored minimality transcripts. See the referee report for the
proof, the checked scope, and the Python (not Lean) trust boundary.
"""

import argparse
from copy import deepcopy
from fractions import Fraction
import gzip
import hashlib
import json
from math import gcd
from pathlib import Path
import re
import subprocess
import sys
import time


PR_HEAD = "65b087dc62e4950e1c504fe34865acaacb9188c9"
NIGHT_HEAD = "76bf6136c334c1db9e52e399fcc33fd4c20b9c24"
MU = (bytes((1, 1, 1, 1, 1, 0)), bytes((1, 0, 0, 1, 1, 1)))
MAX_COEFFICIENTS = 20001


def need(condition, message):
    if not condition:
        raise ValueError(message)


def number(value):
    if type(value) is int:
        return value
    need(isinstance(value, str), "integer or canonical hexadecimal required")
    result = int(value, 16)
    need(hex(result) == value, "noncanonical hexadecimal integer")
    return result


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def integer_sha(value):
    value = abs(value)
    return sha(value.to_bytes(max(1, (value.bit_length() + 7) // 8), "big"))


def word_prefix(length, spec=None):
    if spec is None:
        images = MU
    elif spec["kind"] == "periodic":
        period = bytes(map(int, spec["period"]))
        return (period * ((length + len(period) - 1) // len(period)))[:length]
    elif spec["kind"] == "explicit":
        result = bytes(map(int, spec["bits"][:length]))
        need(len(result) == length, "short explicit word")
        return result
    else:
        need(spec["kind"] == "morphism", "unrecognized family")
        images = tuple(bytes(map(int, spec[key])) for key in ("zero", "one"))
    result = bytes((1,))
    while len(result) < length:
        result = b"".join(images[letter] for letter in result)
    return result[:length]


def indexed_bit(index):
    digits = []
    while index:
        index, digit = divmod(index, 6)
        digits.append(digit)
    state = 1
    for digit in reversed(digits):
        state = MU[state][digit]
    return state


def inverse_residue(bits):
    """Compose literal inverse branches backwards, without reducing fractions."""
    numerator, denominator = 0, 1
    for bit in reversed(bits):
        numerator <<= 1
        if bit:
            numerator -= denominator
            denominator *= 3
    modulus = 1 << len(bits)
    return numerator * pow(denominator, -1, modulus) % modulus


def numerator_scan(p, q, bits, start=0):
    """Return first mismatch and its actual numerator, or the ending state."""
    need(q % 2 == 1, "numerator semantics require an odd denominator")
    for index in range(start, len(bits)):
        bit = p % 2
        if bit != bits[index]:
            return index, p
        p = (3 * p + q) // 2 if bit else p // 2
    return len(bits), p


def rational_parities(p, q, length):
    """Different semantic route: reduce Fraction at every step of T itself."""
    value = Fraction(p, q)
    result = []
    for _ in range(length):
        need(value.denominator % 2 == 1, "rational is outside Z_2")
        bit = value.numerator % 2
        result.append(bit)
        value = (3 * value + 1) / 2 if bit else value / 2
    return bytes(result)


def linear_interval(coefficient, constant, lower, upper):
    """ALL integer x with lower <= coefficient*x+constant <= upper."""
    if coefficient == 0:
        return (None, None) if lower <= constant <= upper else None
    if coefficient < 0:
        coefficient, constant, lower, upper = -coefficient, -constant, -upper, -lower
    lo = -((constant - lower) // coefficient)
    hi = (upper - constant) // coefficient
    return lo, hi


def checked_basis(n, residue, basis):
    need(len(basis) == 2 and all(len(row) == 2 for row in basis), "basis shape")
    first, second = tuple(tuple(map(number, row)) for row in basis)
    modulus = 1 << n
    determinant = first[0] * second[1] - second[0] * first[1]
    need(abs(determinant) == modulus, "basis has wrong index")
    need(all((p - residue * q) % modulus == 0 for p, q in (first, second)),
         "basis is outside parity cylinder")
    return first, second


def box_vector(n, basis, bound):
    """Find ANY lattice vector with |p|<=B, 1<=q<=B odd, or prove none.

    Cramer's rule bounds both coefficients. Enumerate the shorter SIGNED
    range, then solve the two exact coordinate intervals, including q>0.
    No optimizer invariant, transcript, primitivity assumption or symmetric
    positive-beta shortcut is used. The caller has checked the full index.
    """
    need(bound >= 0, "negative box")
    first, second = basis
    modulus = 1 << n
    caps = [bound * sum(map(abs, second)) // modulus,
            bound * sum(map(abs, first)) // modulus]
    fixed = caps.index(min(caps))
    cap = caps[fixed]
    need(2 * cap + 1 <= MAX_COEFFICIENTS, "coefficient cover exceeds explicit budget")
    fixed_vector, variable_vector = (first, second) if fixed == 0 else (second, first)
    for coefficient in range(-cap, cap + 1):
        intervals = [linear_interval(variable_vector[0], coefficient * fixed_vector[0], -bound, bound),
                     linear_interval(variable_vector[1], coefficient * fixed_vector[1], 1, bound)]
        if any(interval is None for interval in intervals):
            continue
        lows = [interval[0] for interval in intervals if interval[0] is not None]
        highs = [interval[1] for interval in intervals if interval[1] is not None]
        need(lows and highs, "singular variable vector")
        lower, upper = max(lows), min(highs)
        if variable_vector[1] % 2:
            lower += (1 - coefficient * fixed_vector[1] - lower) % 2
        elif coefficient * fixed_vector[1] % 2 != 1:
            continue
        if lower <= upper:
            p = coefficient * fixed_vector[0] + lower * variable_vector[0]
            q = coefficient * fixed_vector[1] + lower * variable_vector[1]
            need(abs(p) <= bound and 1 <= q <= bound and q % 2 == 1, "interval bug")
            return (p, q), cap
    return None, cap


def verify_minimum(record, bits, residue):
    n = record["N"]
    need(type(n) is int and 0 <= n <= len(bits), "bad precision")
    a, h, p, q = (number(record[key]) for key in ("A", "H", "p", "q"))
    modulus = 1 << n
    need(a == residue % modulus, "wrong cylinder residue")
    need(q > 0 and q % 2 == 1 and gcd(p, q) == 1, "nonprimitive/invalid denominator")
    need(h == max(abs(p), q), "height differs from witness")
    need((p - a * q) % modulus == 0, "witness outside lattice")
    end, _ = numerator_scan(p, q, bits[:n])
    need(end == n, "actual signed numerator itinerary differs")
    basis = checked_basis(n, a, record["basis"])
    vector, cap = box_vector(n, basis, h - 1)
    need(vector is None, "strictly smaller odd-denominator vector exists")
    # Redundant producer transcripts are deliberately NOT needed for this proof.
    return {"N": n, "height_bits": h.bit_length(), "coefficient_cap": cap}


def brute_residue(n, residue):
    """Complete independent reconstruction, using the centered q=1 bound."""
    modulus = 1 << n
    upper = max(1, modulus // 2)
    candidates = []
    for q in range(1, upper + 1, 2):
        p = (residue * q + modulus // 2) % modulus - modulus // 2
        candidates.append((max(abs(p), q), p, q))
    h, p, q = min(candidates)
    divisor = gcd(p, q)
    need(divisor == 1, "brute minimum should be primitive")
    return h, p, q


def rejection(function, label):
    try:
        function()
    except ValueError:
        return label
    raise ValueError("hostile control was accepted: " + label)


def self_tests():
    counts = {"linear_intervals": 0, "small_residues": 0, "signed_semantics": 0}
    for a in range(-5, 6):
        for c in range(-6, 7):
            for bound in range(5):
                interval = linear_interval(a, c, -bound, bound)
                for x in range(-12, 13):
                    predicted = interval is not None and (interval[0] is None or interval[0] <= x <= interval[1])
                    need(predicted == (-bound <= a * x + c <= bound), "signed interval regression")
                counts["linear_intervals"] += 1
    for n in range(9):
        for residue in range(1 << n):
            h, _, _ = brute_residue(n, residue)
            basis = ((1 << n, 0), (residue, 1))
            for b, exists in ((h - 1, False), (h, True)):
                found, _ = box_vector(n, basis, b)
                need((found is not None) == exists, "complete coefficient cover versus brute force")
            counts["small_residues"] += 1
    seeds = [(p, q) for p in range(-12, 13) for q in (-5, -3, -1, 1, 3, 5)]
    itineraries = {}
    for p, q in seeds:
        bits = rational_parities(p, q, 9)
        need(numerator_scan(p, q, bits)[0] == 9, "Fraction/numStep semantic disagreement")
        need(bits == rational_parities(-p, -q, 9) == rational_parities(3*p, 3*q, 9),
             "sign or odd scaling changed the itinerary")
        need(numerator_scan(-p, -q, bits)[0] == 9 and numerator_scan(3*p, 3*q, bits)[0] == 9,
             "raw numerator iteration changed under sign normalization or odd gcd scaling")
        itineraries[(p, q)] = bits
        for n in range(10):
            modulus = 1 << n
            need((p - inverse_residue(bits[:n]) * q) % modulus == 0, "finite residue bridge")
            counts["signed_semantics"] += 1
    for (p, q), first in itineraries.items():
        for (r, s), second in itineraries.items():
            length = next((j for j, pair in enumerate(zip(first, second)) if pair[0] != pair[1]), 9)
            need((p*s-r*q) % (1 << length) == 0, "isometry loses precision")
            if length < 9:
                need((p*s-r*q) % (1 << (length+1)) != 0, "first mismatch valuation differs")
    primary = word_prefix(150)
    need(all(bit == indexed_bit(j) for j, bit in enumerate(primary)), "word indexing convention")
    small = {}
    for n in (11, 12, 13, 67):
        if n > 13:
            continue
        h, p, q = brute_residue(n, inverse_residue(primary[:n]))
        need(numerator_scan(p, q, primary[:n])[0] == n, "brute witness semantics")
        small[str(n)] = {"H": h, "p": p, "q": q}
    need(small["11"]["H"] == 3 and small["12"]["H"] == 513, "H_11/H_12")
    # A precise false whole-lattice/square-root generalization.
    n, residue = 8, 128
    h, _, _ = brute_residue(n, residue)
    need(h == 128 and h > 2**(n//2), "hostile square-root example")
    need((0-residue*2) % (1 << n) == 0 and (0-residue) % (1 << n) != 0,
         "even-denominator cancellation should fail")
    need(3**3 < 2**5 and 125 < 147, "strict c<1/2 rational comparison")
    t = 14 * 36 * 3**102
    need(2*t*t < 1 << 403 and 6*3**6 < 14**5, "all-k uniqueness induction bases")
    corrupt_record = {"N": 12, "A": 2045, "H": 513, "p": 509, "q": 513,
                      "basis": [[-6, 2], [509, 513]]}
    controls = []
    for label, mutate in (
        ("wrong numerator", lambda r: r.update(p=511)),
        ("wrong residue", lambda r: r.update(A=2047)),
        ("even denominator", lambda r: r.update(q=512)),
        ("wrong height", lambda r: r.update(H=512)),
        ("wrong lattice index", lambda r: r.update(basis=[[-12, 4], [509, 513]])),
        ("wrong argument order", lambda r: r.update(p=513, q=509)),
    ):
        damaged = deepcopy(corrupt_record)
        mutate(damaged)
        controls.append(rejection(lambda: verify_minimum(damaged, primary, inverse_residue(primary[:12])), label))
    # Literal signed-denominator wording of Cassidy's printed Lemma G.
    # a/b=-1 and P/Q=1/3: |difference|_2=1/4, printed RHS=1/2.
    need(Fraction(1, 4) < Fraction(1, abs(1)*abs(3)+abs(1)*(-1)),
         "external signed-denominator counterexample")
    # A nonperiodic ordinary-digit Liouville word defeats an unqualified
    # Roth bound. These finite partial sums support the independent infinite
    # construction in the report, not an inference from finitely many cases.
    factorial, partial = 1, 0
    liouville_controls = []
    for k in range(1, 8):
        factorial *= k
        partial += 1 << factorial
        next_precision = factorial * (k+1)
        need(partial.bit_length() <= factorial+1, "Liouville partial height")
        if k >= 3:
            need(3*(partial.bit_length()) < next_precision, "Liouville precision/height control")
            liouville_controls.append([k, partial.bit_length(), next_precision])
    return {"counts": counts, "exact_small_minima": small,
            "rejected_corruptions": controls,
            "external_signed_gap_counterexample": {"a": 1, "b": -1, "P": 1, "Q": 3,
                                                   "actual_2_adic_distance": "1/4", "printed_lower_bound": "1/2"},
            "liouville_partial_height_bits_and_next_precision": liouville_controls,
            "false_square_root_claim": {"N": 8, "A": 128, "H": h, "even_vector": [0, 2]}}


def baseline_checks(source):
    head = subprocess.check_output(["git", "-C", str(source), "rev-parse", "HEAD"], text=True).strip()
    need(head == PR_HEAD, "--source must be checked out at the exact pinned implementation head")
    path = source / "research/phase13/heights.json.gz"
    raw = path.read_bytes()
    data = json.loads(gzip.decompress(raw))
    output = []
    for family in data["families"]:
        records = family["records"]
        length = max(record["N"] for record in records)
        bits = word_prefix(length, family["spec"])
        residue = inverse_residue(bits)
        checks = [verify_minimum(record, bits, residue) for record in records]
        output.append({"name": family["name"], "records": len(checks), "max_N": length,
                       "max_shorter_coefficient_cap": max(row["coefficient_cap"] for row in checks)})
        print("BASELINE", family["name"], len(checks), "exact minima", flush=True)
    return {"sha256": sha(raw), "families": output, "total": sum(row["records"] for row in output)}


def overnight_checks(directory):
    raw = (directory / "heights.jsonl").read_bytes()
    lines = raw.splitlines(keepends=True)
    records = [json.loads(line) for line in lines]
    need(len({record["N"] for record in records}) == len(records), "duplicate height")
    bits = word_prefix(max(record["N"] for record in records))
    residue = inverse_residue(bits)
    by_n = {}
    results = []
    for line, record in zip(lines, records):
        n = record["N"]
        need(sha(bits[:n]) == record["parity_sha256"], "parity hash")
        result = verify_minimum(record, bits, residue)
        by_n[n] = (record, sha(line))
        results.append(result)
        print("OVERNIGHT", result, flush=True)
    transitions = []
    previous_hash = None
    source_manifest = []
    for name in ("transitions.jsonl", "transitions-0002.jsonl"):
        contents = (directory / name).read_bytes()
        source_manifest.append({"path": name, "sha256": sha(contents), "records": len(contents.splitlines())})
        for line in contents.splitlines(keepends=True):
            transition = json.loads(line)
            if "previous_transition_record_sha256" in transition:
                need(transition["previous_transition_record_sha256"] == previous_hash, "transition predecessor")
            previous_hash = sha(line)
            start, end = transition["source_N"], transition["target_N"]
            failure = transition["first_failure_index"]
            need(end == failure + 1, "transition off-by-one")
            (first, first_hash), (second, second_hash) = by_n[start], by_n[end]
            need(first_hash == transition["source_record_sha256"] and
                 second_hash == transition["target_record_sha256"], "transition endpoint references")
            p, q = number(first["p"]), number(first["q"])
            actual_failure, numerator = numerator_scan(p, q, bits[:end])
            need(actual_failure == failure, "wrong first failure from actual iteration")
            need((1 if numerator > 0 else -1 if numerator < 0 else 0) == transition["failure_numerator_sign"],
                 "failing numerator sign")
            need(abs(numerator).bit_length() == transition["failure_numerator_bits"] and
                 integer_sha(numerator) == transition["failure_numerator_abs_sha256"], "failing numerator hash")
            difference = number(second["H"]) - number(first["H"])
            need(difference > 0 and difference.bit_length() == transition["height_difference_bits"] and
                 integer_sha(difference) == transition["height_difference_abs_sha256"], "height jump")
            transitions.append({"source_N": start, "failure": failure, "target_N": end, "width": end-start})
    need(all(a["target_N"] == b["source_N"] for a, b in zip(transitions, transitions[1:])),
         "transition chain disconnected")
    decreases = [(a["source_N"], b["source_N"]) for a, b in zip(transitions, transitions[1:])
                 if a["width"] > b["width"]]
    need((87096, 87099) in decreases, "known false monotone-width claim not falsified")
    # Equal widths do not determine the algorithm-selected basis change.
    def change(start, end):
        f, g = checked_basis(start, number(by_n[start][0]["A"]), by_n[start][0]["basis"])
        u, v = checked_basis(end, number(by_n[end][0]["A"]), by_n[end][0]["basis"])
        determinant = f[0]*g[1]-f[1]*g[0]
        result = []
        for row in (u, v):
            a, b = row[0]*g[1]-row[1]*g[0], f[0]*row[1]-f[1]*row[0]
            need(a % determinant == b % determinant == 0, "basis update is not integral")
            a, b = a//determinant, b//determinant
            need(tuple(a*f[j]+b*g[j] for j in (0, 1)) == row, "basis update multiplication")
            result.append([a, b])
        return result
    singleton_changes = [change(87099, 87100), change(87102, 87103)]
    need(singleton_changes[0] != singleton_changes[1], "false equal-width law accepted")
    # A corrupted large certificate must fail independently, not just hash checking.
    damaged = deepcopy(by_n[87094][0])
    damaged["basis"][0][0] = hex(number(damaged["basis"][0][0]) + 2)
    rejected = rejection(lambda: verify_minimum(damaged, bits, residue), "corrupted large basis")
    inventory = json.loads((directory / "height-inventory.json").read_bytes())
    replay = json.loads((directory / "transition-verification.json").read_bytes())
    need(inventory["source_sha256"] == sha(raw) and inventory["source_bytes"] == len(raw), "stale inventory source")
    need(len(inventory["samples"]) == len(records), "inventory sample count")
    for sample in inventory["samples"]:
        record = by_n[sample["N"]][0]
        p, q, h = (number(record[key]) for key in ("p", "q", "H"))
        need(sample["height_bits"] == h.bit_length(), "inventory height bits")
        need(sample["numerator_abs_sha256"] == integer_sha(p) and sample["denominator_sha256"] == integer_sha(q),
             "inventory coordinate hash")
    need(len(replay["results"]) == len(transitions), "stale transition replay metadata")
    need(replay["height_source_sha256"] == sha(raw), "stale height replay metadata")
    for declared, checked in zip(replay["results"], transitions):
        need(declared["source_N"] == checked["source_N"] and declared["target_N"] == checked["target_N"] and
             declared["first_failure_index"] == checked["failure"], "transition replay disagrees with independent scan")
    checkpoint = json.loads((directory / "checkpoint-audit.json").read_bytes())
    historical_counts = checkpoint["smoke_certificate_counts"]
    need(historical_counts == {"heights": 23, "transitions": 15, "raw_shadow_levels": 9},
         "pinned historical checkpoint metadata unexpectedly changed")
    current_smoke = (directory / "smoke.log").read_bytes()
    need(b"PASS: 24 independent primitive witnesses" in current_smoke and
         b"PASS: 16 independently verified witness failures" in current_smoke and b"Exit status: 0" in current_smoke,
         "pinned final stored smoke log not complete/successful")
    need(checkpoint["evidence_sha256"]["research/phase13/overnight/heights.jsonl"] != sha(raw),
         "expected stale checkpoint height hash")
    need(checkpoint["validation_resources"]["smoke.log"]["sha256"] != sha(current_smoke),
         "expected stale checkpoint smoke hash")
    return {"height_sha256": sha(raw), "height_bytes": len(raw), "heights": results,
            "transition_files": source_manifest, "transitions": transitions,
            "width_decreases": decreases, "unequal_singleton_updates": singleton_changes,
            "hostile_large_rejected": rejected,
            "provenance_finding": {"verdict_as_final_snapshot": "FAIL",
                                   "stale_files": ["overnight-summary.md", "overnight/checkpoint-audit.json"],
                                   "checkpoint_claimed_counts": historical_counts,
                                   "actual_counts": {"heights": len(records), "transitions": len(transitions)},
                                   "actual_stored_smoke_sha256": sha(current_smoke),
                                   "mathematical_certificates_affected": False}}


def forward_concat(left, right):
    """Actual forward affine numerator identity; order is noncommutative.

    2^n T^n(x) = a*x+c. For XY, C = a_Y*c_X+2^|X|*c_Y.
    """
    m, a, c = left
    n, b, d = right
    return m*n, a*b, b*c+m*d


def raw_shadows(max_level, stored=None):
    # Explicit positive forward sums, not an inverse-matrix implementation.
    summaries = [(2, 1, 0), (2, 3, 1)]
    results = []
    stored_records = {} if stored is None else {r["k"]: r for r in map(json.loads, stored.read_bytes().splitlines())}
    for k in range(max_level + 1):
        m, b, d = summaries[1]
        _, a, c = forward_concat(forward_concat(summaries[1], summaries[0]), summaries[0])
        gap = b-m
        need(gap > 0 and gap % 2 == 1, "raw shadow denominator gap")
        p, q = -(m**3*d+c*gap), a*gap
        # Coprime factors of Q give an independent split-gcd calculation.
        need(gcd(a, gap) == 1, "split factors are not coprime")
        g = gcd(m**3*d+c*gap, a) * gcd(d, gap)
        need(p % g == q % g == 0, "split gcd is not a common factor")
        if k <= 4:
            need(gcd(p, q) == g, "split gcd disagrees with direct gcd")
            u = word_prefix(3*6**k)
            v = word_prefix(6**k)
            tail = Fraction(-d, gap)
            for bit in reversed(u):
                tail = 2*tail if not bit else (2*tail-1)/3
            need(tail == Fraction(p, q), "literal rational inverse shadow differs")
            length = (56*6**k-1)//5
            itinerary = u + v*((length+2)//len(v)+2)
            need(numerator_scan(p//g, q//g, itinerary)[0] == len(itinerary), "whole-period sample semantics")
            prefix = word_prefix(length+1)
            need(numerator_scan(p//g, q//g, prefix)[0] == length, "exact shadow failure")
        s, length = 6**k, (56*6**k-1)//5
        r = (20*s-6*(-1)**k)//7
        t = 14*s*3**r
        need(max(abs(p), q) <= t, "shadow T bound")
        reduced_height = max(abs(p), q)//g
        need(2*reduced_height**2 < 1 << length, "strict reconstruction uniqueness")
        row = {"k": k, "L": length, "gcd": g, "raw_height_bits": max(abs(p), q).bit_length(),
               "reduced_height_bits": reduced_height.bit_length(), "p_abs_sha256": integer_sha(p),
               "q_sha256": integer_sha(q), "strict_uniqueness": True}
        if k in stored_records:
            record = stored_records[k]
            need(number(record["raw_gcd"]) == g and record["L"] == length, "raw gcd/length artifact")
            need(record["S"] == s and record["denominator_odd"] and record["denominator_sign"] == 1 and
                 record["numerator_sign"] == -1, "raw shadow signs/scale")
            need(record["raw_numerator_bits"] == abs(p).bit_length() and record["raw_denominator_bits"] == q.bit_length() and
                 record["reduced_height_bits"] == reduced_height.bit_length(), "raw shadow bit lengths")
            need(record["raw_numerator_abs_sha256"] == integer_sha(p) and
                 record["raw_denominator_sha256"] == integer_sha(q), "raw shadow coordinate artifact")
            need(record["reduced_numerator_abs_sha256"] == integer_sha(p//g) and
                 record["reduced_denominator_sha256"] == integer_sha(q//g), "reduced shadow artifact")
        results.append(row)
        print("SHADOW", row, flush=True)
        if k < max_level:
            updated = []
            for image in MU:
                result = (1, 1, 0)
                for bit in image:
                    result = forward_concat(result, summaries[bit])
                updated.append(result)
            summaries = updated
    return results


def modular_cycles():
    output = []
    for modulus, first, period, identity in ((347, 1, 86, 7), (347**2, 62, 14878, 5425)):
        inv = pow(3, -1, modulus)
        # Maps represented by their VALUES AT 0 AND 1, not by matrix entries.
        state = ((0, 2), ((-inv) % modulus, inv))
        evidence = {}
        for k in range(first+period+1):
            if k in (first, identity, first+period):
                evidence[k] = state
            if k == first+period:
                break
            updated = []
            for image in MU:
                values = []
                for initial in (0, 1):
                    x = initial
                    for bit in reversed(image):
                        at_zero, at_one = state[bit]
                        x = (at_zero+(at_one-at_zero)*x) % modulus
                    values.append(x)
                updated.append(tuple(values))
            state = tuple(updated)
        need(evidence[first] == evidence[first+period], "claimed modular state repetition is false")
        need(evidence[identity][1] == (0, 1), "claimed identity map is false")
        output.append({"modulus": modulus, "cycle_start": first, "period": period,
                       "identity_level": identity,
                       "states_by_values_at_0_and_1": {str(k): value for k, value in evidence.items()}})
    return output


def lean_inventory(source):
    audit_path = source / "research/lean-audit/FamilyAudit.lean"
    names = re.findall(r"^#print axioms (\S+)$", audit_path.read_text(), re.M)
    count = re.findall(r"--expected-count (\d+)", (source / ".github/workflows/ci.yml").read_text())
    need(count == [str(len(names))] and len(names) == len(set(names)), "Lean CI exact count")
    declarations = []
    for module in ("RationalHeight", "FrontierHeight"):
        text = (source / f"CollatzLab/{module}.lean").read_text()
        for match in re.finditer(r"^(?:noncomputable )?(?:def|theorem)\s+(\w+)\b", text, re.M):
            name = f"CollatzLab.{module}.{match[1]}"
            need(name in names, "new declaration absent from explicit audit: "+name)
            declarations.append(name)
    need(len(declarations) == 60 and len(names) == 653, "pinned inventory changed")
    return {"total": len(names), "new_public": len(declarations), "new_names": declarations,
            "audit_source_sha256": sha(audit_path.read_bytes())}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=Path.cwd(), help="pinned PR #29 source checkout")
    parser.add_argument("--overnight", type=Path, help="pinned extracted overnight/ directory")
    parser.add_argument("--baseline", action="store_true", help="check all 1,691 baseline minima")
    parser.add_argument("--raw-level", type=int, default=-1, help="independent forward/split gcd, maximum 8")
    parser.add_argument("--output", type=Path, help="write compact deterministic results")
    args = parser.parse_args()
    need(-1 <= args.raw_level <= 8, "raw level is outside explicit resource scope")
    sys.set_int_max_str_digits(20000)
    started = time.monotonic()
    result = {"format": "phase13-independent-referee-v1", "implementation_head": PR_HEAD,
              "overnight_head": NIGHT_HEAD, "trust": "Python exact arithmetic; not a Lean proof",
              "self_tests": self_tests(), "modular_cycles": modular_cycles()}
    print("SELF TESTS and independent modular cycles PASS", flush=True)
    if args.baseline:
        result["lean_inventory"] = lean_inventory(args.source)
        result["baseline"] = baseline_checks(args.source)
    if args.overnight:
        result["overnight"] = overnight_checks(args.overnight)
    if args.raw_level >= 0:
        stored = None if args.overnight is None else args.overnight / "raw-shadows.jsonl"
        result["raw_shadows"] = raw_shadows(args.raw_level, stored)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2, sort_keys=True)+"\n")
    print(f"PASS: independent exact checks completed in {time.monotonic()-started:.3f}s", flush=True)


if __name__ == "__main__":
    main()
