#!/usr/bin/env python3
"""Independent exact checker for 3-adic non-cancellation, tail-GCD reduction,
shadow plateau constancy, and the unconditional two-shadow lower bound dichotomy.
"""

import gzip
import json
from math import gcd
from pathlib import Path
import sys

sys.set_int_max_str_digits(200000)
ROOT = Path(__file__).resolve().parent


def forward_compose(left, right):
    # Forward summary (2^|X|, 3^r_X, offset(X))
    m, a, c = left
    n, b, d = right
    return m * n, a * b, b * c + m * d


def forward_product(items):
    state = (1, 1, 0)
    for item in items:
        state = forward_compose(state, item)
    return state


def check_shadow_levels():
    # Base letters: 0 -> (2, 1, 0), 1 -> (2, 3, 1)
    zero, one = (2, 1, 0), (2, 3, 1)
    shadows = []
    for k in range(8):
        s = 6 ** k
        ell = (56 * s - 1) // 5
        e = (-1) ** k
        r_u = (15 * s - 8 * e) // 7
        r_v = (5 * s + 2 * e) // 7
        m_v, b, d = one
        m_u, a, c = forward_product([one, zero, zero])
        assert m_v == 1 << s and m_u == 1 << (3 * s)
        assert a == 3 ** r_u and b == 3 ** r_v
        tail_den = b - m_v
        assert tail_den > 0 and tail_den % 2 == 1
        p = -(m_u * d + c * tail_den)
        q = a * tail_den
        g_raw = gcd(abs(p), q)
        g_tail = gcd(d, tail_den)
        raw_h = max(abs(p), q)
        red_p, red_q = p // g_raw, q // g_raw
        red_h = max(abs(red_p), red_q)
        cap = 14 * s * (3 ** (r_u + r_v))
        assert raw_h <= cap
        assert g_raw * red_h == raw_h
        if k == 0:
            assert g_raw == 3 and g_tail == 1 and red_h == 3
        else:
            # Exact mod-3 congruences proved in ShadowCancellation.lean
            assert d % 3 == 2, f"d_{k} mod 3 != 2"
            assert c % 3 == 1, f"c_{k} mod 3 != 1"
            assert p % 3 == 2, f"P_{k} mod 3 != 2"
            assert gcd(abs(p), 3) == 1
            assert gcd(abs(p), a) == 1
            assert g_raw == g_tail, f"k={k}: raw gcd {g_raw} != tail gcd {g_tail}"
            assert tail_den % g_raw == 0
            assert g_raw <= tail_den
            assert red_q % a == 0
            assert red_h >= red_q >= a
            assert 2 * raw_h * raw_h < (1 << ell)
        if k >= 2:
            assert 2 * cap * cap < (1 << ell)
        shadows.append({
            "k": k, "S": s, "L": ell, "a": a, "b": b, "c": c, "d": d,
            "P": p, "Q": q, "gcd": g_raw, "red_p": red_p, "red_q": red_q,
            "raw_h": raw_h, "red_h": red_h, "cap": cap,
        })
        # Substitution: 0 -> 111110, 1 -> 100111
        zero, one = (
            forward_product([one] * 5 + [zero]),
            forward_product([one, zero, zero, one, one, one]),
        )
    assert [row["gcd"] for row in shadows] == [3, 1, 1, 1, 1, 1, 1, 347]
    return shadows


def check_profiles_against_dichotomy(shadows):
    data = json.loads(gzip.open(ROOT / "heights.json.gz").read())
    f6 = [fam for fam in data["families"] if fam["name"] == "frontierSix"][0]["records"]
    by_n = {rec["N"]: rec for rec in f6}
    assert int(by_n[67]["H"]) == 297087259
    assert int(by_n[68]["H"]) >= 248368026765

    dichotomy_checked = 0
    plateau_checked = 0
    for rec in f6:
        n = rec["N"]
        h = int(rec["H"])
        p = int(rec["p"])
        q = int(rec["q"])
        if n <= 11:
            continue
        # Find k such that L_k < n <= L_{k+1}
        k = 0
        while shadows[k + 1]["L"] < n:
            k += 1
        sh_lo = shadows[k]
        sh_hi = shadows[k + 1]
        assert sh_lo["L"] < n <= sh_hi["L"]

        # Check unconditional plateau theorem when 2 * raw_h^2 < 2^n
        if 2 * sh_hi["raw_h"] * sh_hi["raw_h"] < (1 << n):
            assert h == sh_hi["red_h"]
            assert (p, q) == (sh_hi["red_p"], sh_hi["red_q"])
            plateau_checked += 1

        # Check unconditional two-shadow dichotomy (H_two_shadow_dichotomy)
        branch1 = (h >= sh_hi["a"]) and (p * sh_hi["Q"] == sh_hi["P"] * q)
        branch2 = (
            (1 << sh_lo["L"]) <= 2 * sh_lo["cap"] * h
            and (1 << n) <= 2 * sh_hi["cap"] * h
            and (p * sh_hi["Q"] != sh_hi["P"] * q)
        )
        assert branch1 or branch2, f"Dichotomy failed at N={n}"
        dichotomy_checked += 1

    # Also check overnight heights (L_5 = 87091, L_6 = 522547, and intermediate transitions)
    overnight_path = ROOT / "overnight" / "heights.jsonl"
    overnight_checked = 0
    if overnight_path.exists():
        for line in overnight_path.read_text().splitlines():
            row = json.loads(line)
            n = row["N"]
            h = int(row["H"], 16)
            p = int(row["p"], 16)
            q = int(row["q"], 16)
            k = 0
            while shadows[k + 1]["L"] < n:
                k += 1
            sh_lo = shadows[k]
            sh_hi = shadows[k + 1]
            branch1 = (h >= sh_hi["a"]) and (p * sh_hi["Q"] == sh_hi["P"] * q)
            branch2 = (
                (1 << sh_lo["L"]) <= 2 * sh_lo["cap"] * h
                and (1 << n) <= 2 * sh_hi["cap"] * h
                and (p * sh_hi["Q"] != sh_hi["P"] * q)
            )
            assert branch1 or branch2, f"Overnight dichotomy failed at N={n}"
            overnight_checked += 1

    return dichotomy_checked, plateau_checked, overnight_checked


def main():
    shadows = check_shadow_levels()
    dichotomy_checked, plateau_checked, overnight_checked = check_profiles_against_dichotomy(shadows)
    print(
        f"PASS: shadow mod-3 non-cancellation and tail-gcd reduction verified for k=0..7; "
        f"{plateau_checked} plateau records and {dichotomy_checked}+{overnight_checked} "
        f"two-shadow dichotomy records verified"
    )


if __name__ == "__main__":
    main()
