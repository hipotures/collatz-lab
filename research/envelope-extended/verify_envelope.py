#!/usr/bin/env python3
"""Independent checker for research/envelope-extended/evidence.json.

Shares no code with the Rust implementation.

1. Witness check (every row): every recorded extremal witness m is iterated
   directly with T(n) = n/2 or (3n+1)/2 on Python integers. The parity word
   must match; the coefficient 3^(r_j)/2^j must first drop below 1 exactly at
   j = k with r odd steps; and 2^k T^k(m) = 3^r m + c must hold. m must be the
   least member >= 2 of its class mod 2^k. R_r, U_r and E_r are recomputed
   from these witnesses as reduced fractions.
2. Exhaustive cross-check (rows r <= --exhaustive-max-r): every first
   crossing with r odd steps is enumerated by a separate breadth-first
   construction of (word, residue, c). max c, min m and the maximal ratio
   c/(d m) are recomputed, including the complete tie sets.

Exit status 0 iff all checks pass. Finite exact checks only.
"""

import argparse
import json
import sys
from fractions import Fraction


def crossing_length(r: int) -> int:
    k = 1
    while 2**k <= 3**r:
        k += 1
    return k


def iterate(m: int, k: int):
    """Direct iteration: parity word, odd count, endpoint, and first j with 2^j > 3^(r_j)."""
    x, word, r, first = m, [], 0, None
    for j in range(1, k + 1):
        if x % 2:
            word.append("1")
            x = (3 * x + 1) // 2
            r += 1
        else:
            word.append("0")
            x //= 2
        if first is None and 2**j > 3**r:
            first = j
    return "".join(word), r, x, first


def check_witness(w: dict, r: int, k: int) -> None:
    m, c, res = int(w["m"]), int(w["c"]), int(w["residue"])
    word, rr, end, first = iterate(m, k)
    assert word == w["parity"], f"parity mismatch at m={m}"
    assert rr == r and first == k, f"m={m} is not a first crossing of length {k} with r={r}"
    assert 2**k * end == 3**r * m + c, f"affine identity fails at m={m}"
    assert res == m % 2**k and m >= 2 and (m < 2**k or m - 2**k < 2), f"m={m} not least >= 2"


def frac(d: dict) -> Fraction:
    return Fraction(int(d["numerator"]), int(d["denominator"]))


def enumerate_family(r: int, k: int):
    """All first crossings with r odd steps: (word, m, c), built level by level.

    State (word, res, a, c): residue res mod 2^j of the class, and the affine
    form T^j(n) = (3^a n + c) / 2^j. The next parity bit of the class is the
    parity of (3^a res + c) / 2^j, which fixes bit j of the residue by
    choosing between res and res + 2^j.
    """
    out = []
    level = [("", 0, 0, 0)]
    for j in range(k):
        nxt = []
        for word, res, a, c in level:
            for odd in (1, 0):
                if odd and a == r:
                    continue
                # pick the lift res' in {res, res + 2^j} whose step-j parity equals `odd`
                for cand in (res, res + 2**j):
                    if ((3**a * cand + c) // 2**j) % 2 == odd:
                        break
                a2 = a + odd
                c2 = 3 * c + 2**j if odd else c
                w2 = word + str(odd)
                if 2 ** (j + 1) > 3**a2:
                    if a2 == r:
                        assert j + 1 == k
                        m = cand if cand >= 2 else cand + 2**k
                        out.append((w2, m, c2))
                    continue
                if j + 1 < k:
                    nxt.append((w2, cand, a2, c2))
        level = nxt
    return out


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--evidence", default="research/envelope-extended/evidence.json")
    ap.add_argument("--exhaustive-max-r", type=int, default=16)
    args = ap.parse_args()
    data = json.load(open(args.evidence))
    total = 0
    for row in data["rows"]:
        r, k = row["r"], row["k"]
        assert k == crossing_length(r), f"r={r}: wrong k"
        d = 2**k - 3**r
        assert int(row["d"]) == d
        total += int(row["family_count"])
        for key in ("max_c_witnesses", "min_m_witnesses", "max_ratio_witnesses"):
            for w in row[key]:
                check_witness(w, r, k)
        best = row["max_ratio_witnesses"][0]
        R = Fraction(int(best["c"]), d * int(best["m"]))
        U = Fraction(int(row["max_c"]), d * int(row["min_m"]))
        assert R == frac(row["r_ratio"]) and U == frac(row["u_ratio"]), f"r={r}: ratios"
        assert row["e_ratio"] is None or U / R == frac(row["e_ratio"]), f"r={r}: E_r"
        if r <= args.exhaustive_max_r:
            fam = enumerate_family(r, k)
            assert len(fam) == int(row["family_count"]), f"r={r}: count"
            max_c = max(c for _, _, c in fam)
            min_m = min(m for _, m, _ in fam)
            best_ratio = max(Fraction(c, m) for _, m, c in fam)
            assert max_c == int(row["max_c"]) and min_m == int(row["min_m"]), f"r={r}: extrema"
            assert best_ratio / d == R, f"r={r}: best ratio"
            ties = sorted(w for w, m, c in fam if Fraction(c, m) == best_ratio)
            assert ties == [w["parity"] for w in row["max_ratio_witnesses"]], f"r={r}: ties"
            assert sorted(w for w, m, _ in fam if m == min_m) == [
                w["parity"] for w in row["min_m_witnesses"]
            ], f"r={r}: min_m ties"
            assert sorted(w for w, _, c in fam if c == max_c) == [
                w["parity"] for w in row["max_c_witnesses"]
            ], f"r={r}: max_c ties"
        print(f"r={r:>2} k={k:>2} R_r={float(R):.6g} E_r={float(U / R):.4f} ok", flush=True)
    assert total == int(data["total_classes_checked"]), "total class count"
    print(f"PASS ({len(data['rows'])} rows, witnesses all rows, exhaustive r <= {args.exhaustive_max_r})")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except AssertionError as e:
        print(f"FAIL: {e}", file=sys.stderr)
        sys.exit(1)
