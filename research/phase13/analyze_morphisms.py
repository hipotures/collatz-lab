#!/usr/bin/env python3
"""Phase 13 follow-up: cross-morphism rational shadows and 3-adic non-cancellation
for Phase 11 unequal-weight morphisms (`110/111`, `1011/1111`) vs `frontierSix`
and equal-weight controls (`110/011`, Thue-Morse `10/01`).

For each unequal-weight morphism, this script constructs the exact minimal-preperiod
eventually-periodic rational shadow y_k = P_k / Q_k, verifies:
  1. exact first mismatch L_k against the literal substituted word w,
  2. strict reconstruction uniqueness 2 * H_k^2 < 2^(L_k),
  3. exact agreement of the reduced shadow (p_k, q_k) with the lattice minimizer
     at N = L_k (and records the jump at N = L_k + 1),
  4. exact raw gcd(|P_k|, Q_k) and 3-adic residues (|P_k| mod 3, Q_k mod 3).

Bounded exact arithmetic only; no general all-morphism theorem is claimed.
"""

import argparse
import json
from math import gcd, log2
from pathlib import Path
import sys

sys.set_int_max_str_digits(50000)
ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))

from experiments import residue, word
from height_lattice import profile

JSON_OUT = ROOT / "morphism-shadows.json"
MD_OUT = ROOT / "morphism-shadows.md"


def affine_params(bits: list[int]) -> tuple[int, int, int]:
    """Return (2^len, offset c, 3^weight) for a parity block."""
    c, pow2, pow3 = 0, 1, 1
    for b in bits:
        if b:
            c = 3 * c + pow2
            pow3 *= 3
        pow2 *= 2
    return pow2, c, pow3


def eventual_periodic_shadow(pre: list[int], per: list[int]) -> tuple[int, int]:
    """Exact raw (P, Q) with Q > 0 odd realizing pre + per^inf.

    The periodic tail y_per = -d / (b - m) satisfies T^|per|(y_per) = y_per
    where T^|per|(x) = (b*x + d)/m. Applying the inverse of pre (T^|pre|(x) = (a*x + c)/u)
    gives x = (u * y_per - c) / a = -(u*d + c*(b - m)) / (a*(b - m)).
    """
    u, c, a = affine_params(pre)
    m, d, b = affine_params(per)
    p = -(u * d + c * (b - m))
    q = a * (b - m)
    assert q > 0 and q % 2 == 1
    return p, q


def minimal_preperiod_and_period(pre: list[int], per: list[int]) -> tuple[list[int], list[int]]:
    """Trim any suffix of `pre` that already matches the cyclic tail of `per`."""
    pre = list(pre)
    per = list(per)
    s = len(per)
    while pre and pre[-1] == per[-1]:
        pre.pop()
        per = [per[-1]] + per[:-1]
    assert len(per) == s
    return pre, per


def first_mismatch(w: list[int], pre: list[int], per: list[int]) -> int:
    n_pre = len(pre)
    n_per = len(per)
    for i, bit in enumerate(w):
        s_bit = pre[i] if i < n_pre else per[(i - n_pre) % n_per]
        if bit != s_bit:
            return i
    raise AssertionError("word matched shadow through entire buffer")


def analyze_unequal_family(
    name: str,
    spec: dict,
    c_exact_label: str,
    c_val: float,
    l_formula,
    shadow_builder,
    max_k_lattice: int,
    max_k_raw: int,
) -> dict:
    max_l_needed = l_formula(max_k_lattice) + 2
    w_full = word(spec, max_l_needed)
    a_full = residue(w_full)

    target_ns = set()
    for k in range(max_k_lattice + 1):
        lk = l_formula(k)
        target_ns.add(lk)
        target_ns.add(lk + 1)

    lattice_at = {}
    for n, h, p, q, _, _, _ in profile(a_full, max_l_needed):
        if n in target_ns:
            lattice_at[n] = (h, p, q)

    levels = []
    for k in range(max_k_raw + 1):
        lk = l_formula(k)
        pre_raw, per_raw = shadow_builder(k)
        pre, per = minimal_preperiod_and_period(pre_raw, per_raw)
        p_raw, q_raw = eventual_periodic_shadow(pre, per)
        g = gcd(abs(p_raw), q_raw)
        p_red, q_red = p_raw // g, q_raw // g
        h_red = max(abs(p_red), q_red)
        strict_unique = (2 * h_red * h_red) < (1 << lk)

        row = {
            "k": k,
            "L_k": lk,
            "min_preperiod_len": len(pre),
            "period_len": len(per),
            "raw_gcd": g,
            "raw_p_mod_3": abs(p_raw) % 3,
            "raw_q_mod_3": q_raw % 3,
            "reduced_height_bits": h_red.bit_length(),
            "ratio_at_L_k": round(log2(h_red) / lk, 8),
            "strict_uniqueness": strict_unique,
        }
        if k <= max_k_lattice:
            assert first_mismatch(w_full, pre, per) == lk, f"{name} k={k}: mismatch != L_k"
            h_lat, p_lat, q_lat = lattice_at[lk]
            assert (h_lat, p_lat, q_lat) == (h_red, p_red, q_red), (
                f"{name} k={k}: lattice minimizer disagrees with reduced shadow"
            )
            h_next, _, _ = lattice_at[lk + 1]
            row["matches_lattice_minimizer"] = True
            row["ratio_at_L_k_plus_1"] = round(log2(h_next) / (lk + 1), 8)
        else:
            row["matches_lattice_minimizer"] = None
            row["ratio_at_L_k_plus_1"] = None
        levels.append(row)

    return {
        "name": name,
        "spec": spec,
        "c_exact": c_exact_label,
        "c_numeric": round(c_val, 10),
        "one_minus_c_numeric": round(1.0 - c_val, 10),
        "nonconvergent": c_val < 0.5,
        "levels": levels,
    }


def analyze_equal_weight_control(name: str, spec: dict, max_n: int = 4096) -> dict:
    w = word(spec, max_n)
    a = residue(w)
    min_r = (1.0, 0)
    max_r = (0.0, 0)
    for n, h, _, _, _, _, _ in profile(a, max_n):
        if n >= 128:
            r = log2(h) / n
            if r < min_r[0]:
                min_r = (r, n)
            if r > max_r[0]:
                max_r = (r, n)
    return {
        "name": name,
        "spec": spec,
        "max_n": max_n,
        "min_ratio_from_128": [round(min_r[0], 8), min_r[1]],
        "max_ratio_from_128": [round(max_r[0], 8), max_r[1]],
        "spread": round(max_r[0] - min_r[0], 8),
    }


def run_experiment() -> dict:
    # 1. phase11-110: 1 -> 110, 0 -> 111
    #    Shadow: purely periodic (mu^k(1))^inf, L_k = 3^(k+1) - 1, c = (1/4)*log2(3)
    spec_110 = {"kind": "morphism", "one": "110", "zero": "111"}
    w_110_cache = word(spec_110, 3**8)
    fam_110 = analyze_unequal_family(
        name="phase11-110",
        spec=spec_110,
        c_exact_label="(1/4)*log2(3)",
        c_val=0.25 * log2(3.0),
        l_formula=lambda k: 3 ** (k + 1) - 1,
        shadow_builder=lambda k: ([], w_110_cache[: 3**k]),
        max_k_lattice=7,  # L_7 = 6560
        max_k_raw=8,      # L_8 = 19682
    )

    # 2. phase11-1011: 1 -> 1011, 0 -> 1111
    #    Shadow: mu^k(10) (mu^k(1))^inf (trimmed preperiod length (4*4^k + 2)/3, period 4^k)
    #    L_k = (28*4^k - 1)/3, c = (1/5)*log2(3)
    spec_1011 = {"kind": "morphism", "one": "1011", "zero": "1111"}
    w_1011_cache = word(spec_1011, 2 * 4**5)
    fam_1011 = analyze_unequal_family(
        name="phase11-1011",
        spec=spec_1011,
        c_exact_label="(1/5)*log2(3)",
        c_val=0.2 * log2(3.0),
        l_formula=lambda k: (28 * 4**k - 1) // 3,
        shadow_builder=lambda k: (w_1011_cache[: 2 * 4**k], w_1011_cache[: 4**k]),
        max_k_lattice=4,  # L_4 = 2389
        max_k_raw=5,      # L_5 = 9557
    )

    # 3. Equal-weight controls (through N = 4096)
    ctrl_p8 = analyze_equal_weight_control(
        "phase8-110", {"kind": "morphism", "one": "110", "zero": "011"}, 4096
    )
    ctrl_tm = analyze_equal_weight_control(
        "thue-morse-10", {"kind": "morphism", "one": "10", "zero": "01"}, 4096
    )

    return {
        "format": "phase13-morphism-shadows-v1",
        "unequal_weight_families": [fam_110, fam_1011],
        "equal_weight_controls": [ctrl_p8, ctrl_tm],
    }


def render_markdown(data: dict) -> str:
    lines = [
        "# Phase 13 follow-up: rational shadows and 3-adic non-cancellation across morphisms",
        "",
        "Generated exact-arithmetic comparison extending the Phase 13 rational-shadow",
        "mechanism from `frontierSix` (`1 -> 100111, 0 -> 111110`, `c = (25/98) log2(3) ~= 0.404327`)",
        "to the two Phase 11 unequal-weight morphisms (`110/111`, `1011/1111`) and contrasting",
        "them with equal-weight controls (`110/011`, Thue-Morse `10/01`).",
        "",
        "Reproduce both artifacts byte-for-byte with:",
        "",
        "```bash",
        "python3 research/phase13/analyze_morphisms.py --check",
        "```",
        "",
        "## Overview: three nonconvergent unequal-weight morphisms",
        "",
        "| family | substitution | shadow match `L_k` | exact exponent `c` | `c` (numeric) | `1 - c` | nonconvergent? |",
        "|---|---|---|---|---:|---:|---|",
        "| `frontierSix` (baseline) | `1->100111, 0->111110` | `(56*6^k - 1)/5` | `(25/98)*log2(3)` | 0.404327 | 0.595673 | **yes** |",
    ]
    for fam in data["unequal_weight_families"]:
        spec = fam["spec"]
        l_str = "`3^(k+1) - 1`" if fam["name"] == "phase11-110" else "`(28*4^k - 1)/3`"
        lines.append(
            f"| `{fam['name']}` | `1->{spec['one']}, 0->{spec['zero']}` | {l_str} | "
            f"`{fam['c_exact']}` | {fam['c_numeric']:.6f} | {fam['one_minus_c_numeric']:.6f} | "
            f"**{'yes' if fam['nonconvergent'] else 'no'}** |"
        )
    lines.append("")

    for fam in data["unequal_weight_families"]:
        lines.extend([
            f"## `{fam['name']}` (`1 -> {fam['spec']['one']}, 0 -> {fam['spec']['zero']}`)",
            "",
            "| `k` | `L_k` | min preperiod | period | raw gcd | `|P_k| mod 3` | `Q_k mod 3` | `log2(H)/L_k` | `log2(H)/(L_k+1)` | unique? | lattice match? |",
            "|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|",
        ])
        for lv in fam["levels"]:
            r_next = f"{lv['ratio_at_L_k_plus_1']:.6f}" if lv["ratio_at_L_k_plus_1"] is not None else "—"
            lm = "yes" if lv["matches_lattice_minimizer"] else ("—" if lv["matches_lattice_minimizer"] is None else "NO")
            lines.append(
                f"| {lv['k']} | {lv['L_k']} | {lv['min_preperiod_len']} | {lv['period_len']} | "
                f"{lv['raw_gcd']} | {lv['raw_p_mod_3']} | {lv['raw_q_mod_3']} | "
                f"{lv['ratio_at_L_k']:.6f} | {r_next} | {'yes' if lv['strict_uniqueness'] else 'no'} | {lm} |"
            )
        lines.append("")

    lines.extend([
        "## Equal-weight controls (`128 <= N <= 4096`)",
        "",
        "| family | substitution | min `log2(H_N)/N` (N) | max `log2(H_N)/N` (N) | spread |",
        "|---|---|---:|---:|---:|",
    ])
    for ctrl in data["equal_weight_controls"]:
        spec = ctrl["spec"]
        lines.append(
            f"| `{ctrl['name']}` | `1->{spec['one']}, 0->{spec['zero']}` | "
            f"{ctrl['min_ratio_from_128'][0]:.6f} ({ctrl['min_ratio_from_128'][1]}) | "
            f"{ctrl['max_ratio_from_128'][0]:.6f} ({ctrl['max_ratio_from_128'][1]}) | "
            f"{ctrl['spread']:.6f} |"
        )
    lines.extend([
        "",
        "## Observations and evidence boundary",
        "",
        "- For **`phase11-110`**, the purely periodic shadows `(mu^k(1))^inf` have `Q_k = 3^(w_1(k)) - 2^(3^k)`",
        "  automatically coprime to 3 (no preperiod factor), exact match length `L_k = 3^(k+1) - 1`,",
        "  and exponent `c = (1/4)*log2(3) ~= 0.396241 < 1/2`. Every level `k = 0..7` matches the",
        "  exact lattice minimizer; raw GCDs are `1` at `k = 0..8`.",
        "- For **`phase11-1011`**, the trimmed eventually-periodic shadows `mu^k(10)(mu^k(1))^inf`",
        "  have exact match length `L_k = (28*4^k - 1)/3` and exponent `c = (1/5)*log2(3) ~= 0.316993 < 1/2`.",
        "  At all tested levels `k = 0..5`, `|P_k| mod 3 != 0` (exact 3-adic preperiod non-cancellation,",
        "  matching `frontierSix`!) and every level `k = 0..4` matches the exact lattice minimizer.",
        "- By the same determinant inequality as in `phase13-theory.md`, both `phase11-110` and",
        "  `phase11-1011` have nonconvergent normalized height profiles (`liminf <= c < 1/2 < 1 - c <= limsup`).",
        "- These are bounded exact verifications and written exponent derivations, not Lean-formalized",
        "  theorems for `phase11-110` or `phase11-1011`.",
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
        print("WROTE: cross-morphism shadow & 3-adic non-cancellation analysis")
    else:
        assert data == json.loads(JSON_OUT.read_text()), "JSON mismatch"
        assert md == MD_OUT.read_text(), "Markdown mismatch"
        print("PASS: cross-morphism shadow & 3-adic non-cancellation analysis")


if __name__ == "__main__":
    main()
