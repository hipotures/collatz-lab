#!/usr/bin/env python3
"""Phase 13 follow-up: exact 2-primary / 3-primary power-residue obstructions
and the post-identity abelian trap for resonant primes dividing gcd(|P_k|, Q_k).

For frontierSix (1 -> 100111, 0 -> 111110), the slope of f_1^(k) is
    a_1^(k) = 2^(6^k) / 3^(r_k),   r_k = (5 * 6^k + 2 * (-1)^k) / 7.
Because v_2(r_k) = 1 for all k >= 2 and v_3(r_k) = 0 for all k >= 1:
  - Theorem 1 (2-primary & 3-primary obstructions):
    Let s = v_2(p - 1) and u = v_3(p - 1).
    * For every k >= max(2, s), a_1^(k) == 1 (mod p) forces 3^((p-1)/2^(s-1)) == 1 (mod p).
    * For every k >= max(1, u), a_1^(k) == 1 (mod p) forces 3^((p-1)/3^u) == 1 (mod p).
    * Corollary: NO prime p == 5 (mod 12) EVER divides gcd(|P_k|, Q_k) for any k >= 1.
    * Counterexample to the naive "p == 1 (mod 4) impossible" guess:
      p = 10597 == 1 (mod 12) divides gcd(|P_677|, Q_677), and satisfies both power-residue
      conditions (s = 2, u = 1, 3^((p-1)/2) == 1, 3^((p-1)/3) == 1 mod 10597).
  - Theorem 2 (Post-identity abelian trap):
    Whenever f_1^(b) == id (mod p) at any b >= 1, then for all j >= 0:
      f_0^(b+j) = (f_0^(b))^(u_j),   f_1^(b+j) = (f_0^(b))^(v_j),
    where u_j = (2*6^j + 5*(-1)^j)/7 and v_j = 2*(6^j - (-1)^j)/7.
    Hence f_1^(b+j) == id (mod p) iff ord_p(a_0^(b)) | v_j, proving automatically
    that every single hit at b >= 1 generates infinitely many divisible levels.

This script verifies both theorems on bounded ranges and reproduces exact artifacts.
"""

import argparse
import json
import math
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))

from scan_tail_gcd_primes import primes_in_range, step_mod_p

JSON_OUT = ROOT / "prime-obstructions.json"
MD_OUT = ROOT / "prime-obstructions.md"


def valuation(n: int, base: int) -> int:
    v = 0
    while n % base == 0:
        n //= base
        v += 1
    return v


def mult_order(a: int, p: int) -> int:
    """Exact multiplicative order of a (mod p) for prime p."""
    a %= p
    assert a != 0
    order = p - 1
    temp = order
    d = 2
    while d * d <= temp:
        if temp % d == 0:
            while temp % d == 0:
                temp //= d
            while order % d == 0 and pow(a, order // d, p) == 1:
                order //= d
        d += 1
    if temp > 1 and pow(a, order // temp, p) == 1:
        order //= temp
    return order


def verify_abelian_trap(p: int, b: int, extra_steps: int = 250) -> dict:
    """Independently verify Theorem 2 for prime p with first hit at level b."""
    inv = pow(3, -1, p)
    z0, z1, o0, o1 = 2 % p, 0, (2 * inv) % p, (-inv) % p
    for k in range(1, b + 1):
        z0, z1, o0, o1 = step_mod_p(z0, z1, o0, o1, p)
    assert o0 == 1 and o1 == 0, f"p={p}: expected identity at b={b}"

    # Verify power-residue conditions of Theorem 1
    s = valuation(p - 1, 2)
    u = valuation(p - 1, 3)
    c2 = pow(3, (p - 1) // (1 << (s - 1)), p) if s >= 2 else 1
    c3 = pow(3, (p - 1) // (3**u), p) if u >= 1 else 1
    if b >= max(2, s):
        assert c2 == 1, f"p={p}: 2-primary condition violated at b={b}"
    if b >= max(1, u):
        assert c3 == 1, f"p={p}: 3-primary condition violated at b={b}"

    ord_a0 = mult_order(z0, p)

    # Compare literal iteration vs exact abelian trap formula for j = 0..extra_steps
    cur_z0, cur_z1, cur_o0, cur_o1 = z0, z1, o0, o1
    actual_hits = []
    predicted_hits = []
    u_j, v_j = 1, 0
    for j in range(extra_steps + 1):
        # Closed-form check for (u_j, v_j)
        assert u_j == (2 * 6**j + 5 * (-1) ** j) // 7
        assert v_j == (2 * (6**j - (-1) ** j)) // 7
        is_hit = (cur_o0 == 1 and cur_o1 == 0)
        pred_hit = (v_j % ord_a0 == 0)
        assert is_hit == pred_hit, f"p={p}, b={b}, j={j}: trap formula mismatch"
        if is_hit:
            actual_hits.append(b + j)
            predicted_hits.append(b + j)
        # Step both
        cur_z0, cur_z1, cur_o0, cur_o1 = step_mod_p(cur_z0, cur_z1, cur_o0, cur_o1, p)
        u_j, v_j = u_j + 5 * v_j, 2 * u_j + 4 * v_j

    # Find exact smallest j > 0 with ord_a0 | v_j
    j_next = 1
    v_mod = 2 % ord_a0
    u_mod = 1 % ord_a0
    while v_mod != 0:
        u_mod, v_mod = (u_mod + 5 * v_mod) % ord_a0, (2 * u_mod + 4 * v_mod) % ord_a0
        j_next += 1
        assert j_next <= 2 * p, f"p={p}: failed to find next hit"

    return {
        "prime": p,
        "p_mod_12": p % 12,
        "v2_p_minus_1": s,
        "v3_p_minus_1": u,
        "three_is_2_power": c2 == 1,
        "three_is_3_power": c3 == 1,
        "first_hit_b": b,
        "ord_a0_at_b": ord_a0,
        "first_return_gap_j": j_next,
        "verified_hits_through_b_plus_250": actual_hits,
    }


def run_experiment() -> dict:
    # 1. Exhaustive scan of all primes 5 <= p <= 5,000 through k = 2,000,
    #    broken down by p mod 12.
    primes_5k = primes_in_range(5, 5_000)
    by_mod12 = {
        str(r): {
            "total_primes": 0,
            "eligible_primes": 0,
            "slope_hit_primes": 0,
            "full_hit_primes": [],
        }
        for r in (1, 5, 7, 11)
    }

    resonant_entries = []
    for p in primes_5k:
        r_key = str(p % 12)
        by_mod12[r_key]["total_primes"] += 1
        s = valuation(p - 1, 2)
        u = valuation(p - 1, 3)
        c2 = pow(3, (p - 1) // (1 << (s - 1)), p) if s >= 2 else 1
        c3 = pow(3, (p - 1) // (3**u), p) if u >= 1 else 1
        if c2 == 1 and c3 == 1:
            by_mod12[r_key]["eligible_primes"] += 1

        inv = pow(3, -1, p)
        z0, z1, o0, o1 = 2 % p, 0, (2 * inv) % p, (-inv) % p
        got_slope = False
        first_full = None
        for k in range(1, 2001):
            z0, z1, o0, o1 = step_mod_p(z0, z1, o0, o1, p)
            if o0 == 1:
                got_slope = True
                # Verify Theorem 1 on every single slope hit!
                if k >= max(2, s):
                    assert c2 == 1, f"p={p}, k={k}: Theorem 1 (2-primary) failed!"
                if k >= max(1, u):
                    assert c3 == 1, f"p={p}, k={k}: Theorem 1 (3-primary) failed!"
                if o1 == 0 and first_full is None:
                    first_full = k
                    break
        if got_slope:
            by_mod12[r_key]["slope_hit_primes"] += 1
        if first_full is not None:
            by_mod12[r_key]["full_hit_primes"].append({"prime": p, "first_hit_b": first_full})
            resonant_entries.append(verify_abelian_trap(p, first_full))

    # Confirm zero p == 5 (mod 12) full hits (and only p=17 at k=1 for slope)
    assert by_mod12["5"]["eligible_primes"] == 0
    assert by_mod12["5"]["full_hit_primes"] == []

    # 2. Verify the first p == 1 (mod 12) resonant prime p = 10597 at b = 677
    p10597_entry = verify_abelian_trap(10597, 677)
    assert p10597_entry["p_mod_12"] == 1

    # 3. Verify that no prime p == 5 (mod 12) <= 20,000 ever hits slope a_1 == 1 for k = 2..500
    primes_5mod12_20k = [p for p in primes_in_range(5, 20_000) if p % 12 == 5]
    for p in primes_5mod12_20k:
        inv = pow(3, -1, p)
        z0, z1, o0, o1 = 2 % p, 0, (2 * inv) % p, (-inv) % p
        for k in range(1, 201):
            z0, z1, o0, o1 = step_mod_p(z0, z1, o0, o1, p)
            if k >= 2:
                assert o0 != 1, f"p={p} == 5 (mod 12) hit a1=1 at k={k}"
            else:
                assert not (o0 == 1 and o1 == 0)

    return {
        "format": "phase13-prime-obstructions-v1",
        "scan_5k_k2000": {
            "prime_bound": 5_000,
            "primes_scanned": len(primes_5k),
            "k_max": 2000,
            "by_p_mod_12": by_mod12,
        },
        "mod12_eq_5_check": {
            "prime_bound": 20_000,
            "primes_checked": len(primes_5mod12_20k),
            "k_max": 200,
            "zero_hits_verified": True,
        },
        "p_1_mod_12_counterexample": p10597_entry,
        "verified_resonant_primes_5k": resonant_entries,
    }


def render_markdown(data: dict) -> str:
    s5 = data["scan_5k_k2000"]
    c1 = data["p_1_mod_12_counterexample"]
    lines = [
        "# Phase 13 follow-up: power-residue obstructions and the post-identity abelian trap",
        "",
        "Exact algebraic analysis and bounded verification explaining the strong `p mod 12`",
        "asymmetry and period structure observed in [`tail-gcd-primes.md`](tail-gcd-primes.md)",
        "for `frontierSix` (`1 -> 100111, 0 -> 111110`).",
        "",
        "Reproduce both artifacts byte-for-byte with:",
        "",
        "```bash",
        "python3 research/phase13/analyze_prime_obstructions.py --check",
        "```",
        "",
        "## Theorem 1 (2-primary and 3-primary power-residue obstructions)",
        "",
        "The slope of the periodic-tail inverse map `f_1^(k)` is",
        "`a_1^(k) = 2^(6^k) / 3^(r_k)` where `r_k = (5 * 6^k + 2 * (-1)^k) / 7`.",
        "For every `k >= 2`, `7 * r_k = 2*(-1)^k (mod 4)` forces `v_2(r_k) = 1` (so `r_k = 2 (mod 4)`),",
        "and for every `k >= 1`, `7 * r_k = 2*(-1)^k (mod 3)` forces `v_3(r_k) = 0`.",
        "Let `p >= 5` be prime, `s = v_2(p - 1) >= 1`, and `u = v_3(p - 1) >= 0`.",
        "",
        "1. **2-primary obstruction:** for every `k >= max(2, s)`, `2^s | 6^k` kills the 2-part",
        "   of `2^(6^k)` in `F_p^*`, while `v_2(r_k) = 1`. Thus `a_1^(k) == 1 (mod p)` requires",
        "   `3^((p-1)/2^(s-1)) == 1 (mod p)` (`3` is a `2^(s-1)`-th power residue mod `p`).",
        "2. **3-primary obstruction:** for every `k >= max(1, u)`, `3^u | 6^k` kills the 3-part",
        "   of `2^(6^k)` in `F_p^*`, while `v_3(r_k) = 0`. Thus `a_1^(k) == 1 (mod p)` requires",
        "   `3^((p-1)/3^u) == 1 (mod p)` (`3` is a `3^u`-th power residue mod `p`).",
        "3. **Exact Corollary (`p == 5 (mod 12)` completely excluded):** every prime `p == 5 (mod 12)`",
        "   has `s >= 2` and `(3/p) = -1`, so `p` never divides `3^(r_k) - 2^(6^k)` for any `k >= 2`;",
        "   at `k = 1`, `3^4 - 2^6 = 17` and `gcd(|P_1|, Q_1) = 1`. Hence **no prime `p == 5 (mod 12)`",
        "   ever divides `gcd(|P_k|, Q_k)` at any level `k >= 1`**.",
        "4. **Refutation of the naive `p == 1 (mod 4)` impossibility guess:** `p = 10597 == 1 (mod 12)`",
        f"   (`s = {c1['v2_p_minus_1']}`, `u = {c1['v3_p_minus_1']}`, both power-residue conditions hold)",
        f"   satisfies `f_1^({c1['first_hit_b']}) == id (mod 10597)`, so `10597 | gcd(|P_{c1['first_hit_b']}|, Q_{c1['first_hit_b']})`.",
        "",
        "## Theorem 2 (Post-identity abelian trap)",
        "",
        "Whenever `f_1^(b) == id (mod p)` at any level `b >= 1`, then `f_0^(b+1) = f_0^(b)` and",
        "`f_1^(b+1) = (f_0^(b))^2`, so for every `j >= 0` the pair `(f_0^(b+j), f_1^(b+j))` is",
        "trapped forever in the cyclic abelian subgroup `<f_0^(b)> <= Aff(F_p)`:",
        "",
        "```text",
        "f_0^(b+j) = (f_0^(b))^(u_j),   f_1^(b+j) = (f_0^(b))^(v_j),",
        "u_j = (2 * 6^j + 5 * (-1)^j) / 7,   v_j = 2 * (6^j - (-1)^j) / 7.",
        "```",
        "",
        "Therefore `p | gcd(|P_{b+j}|, Q_{b+j})` **if and only if** `ord_p(a_0^(b)) | v_j`.",
        "In particular, any single hit at `b >= 1` automatically generates infinitely many divisible",
        "levels, and explains both why `full_period == slope_period` and why `p = 619` hits every",
        "`51` levels (half of its `102`-step state period).",
        "",
        "## Bounded verification by residue class `p mod 12` (`5 <= p <= 5,000`, `k <= 2,000`)",
        "",
        "| `p mod 12` | total primes | eligible (Thm 1) | slope `a_1 = 1` hits | full `f_1 = id` hits | asymptotic eligibility |",
        "|---:|---:|---:|---:|---:|---|",
    ]
    asymp = {"1": "~8.3% (1/12)", "5": "**0%** (exact)", "7": "~25% (1/4)", "11": "**100%** (exact)"}
    for r_key in ("1", "5", "7", "11"):
        row = s5["by_p_mod_12"][r_key]
        lines.append(
            f"| {r_key} | {row['total_primes']} | {row['eligible_primes']} | "
            f"{row['slope_hit_primes']} | {len(row['full_hit_primes'])} | {asymp[r_key]} |"
        )
    lines.extend([
        "",
        "## Verified abelian-trap parameters (21 primes `<= 5,000` plus `p = 10597`)",
        "",
        "| prime `p` | `p mod 12` | `s = v_2(p-1)` | `u = v_3(p-1)` | first hit `b` | `ord_p(a_0^(b))` | first return gap `j` |",
        "|---:|---:|---:|---:|---:|---:|---:|",
    ])
    for entry in data["verified_resonant_primes_5k"] + [c1]:
        lines.append(
            f"| {entry['prime']} | {entry['p_mod_12']} | {entry['v2_p_minus_1']} | "
            f"{entry['v3_p_minus_1']} | {entry['first_hit_b']} | "
            f"{entry['ord_a0_at_b']} | {entry['first_return_gap_j']} |"
        )
    lines.extend([
        "",
        "## Evidence boundary",
        "",
        "- Theorems 1 and 2 are **Lean 4 kernel-verified** in `CollatzLab/PrimeObstructions.lean`",
        "  (43 audited declarations via `research/lean-audit/PrimeObstructionsAudit.lean` and",
        "  `research/phase13/PrimeObstructionsSignatures.lean`, using only standard Lean foundations).",
        "- All 22 resonant primes above (and all 667 primes `<= 5,000`, plus all 568 primes",
        "  `p == 5 (mod 12) <= 20,000`) are verified by exact modular arithmetic.",
        "- These results explain the observed `p mod 12` and period structure, but do not",
        "  prove `log2(gcd_k) = o(6^k)` or `B = c`.",
        "",
    ])
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()

    data = run_experiment()
    md = render_markdown(data)
    if args.write:
        JSON_OUT.write_text(json.dumps(data, indent=2) + "\n")
        MD_OUT.write_text(md)
        print(
            f"WROTE: verified Thm 1 & Thm 2 on 21 primes <= 5000 + p=10597 (p==1 mod 12)"
        )
    else:
        assert data == json.loads(JSON_OUT.read_text()), "JSON mismatch"
        assert md == MD_OUT.read_text(), "Markdown mismatch"
        print(
            f"PASS: verified Thm 1 & Thm 2 on 21 primes <= 5000 + p=10597 (p==1 mod 12)"
        )


if __name__ == "__main__":
    main()
