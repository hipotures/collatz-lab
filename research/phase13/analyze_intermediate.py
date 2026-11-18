#!/usr/bin/env python3
"""Phase 13 follow-up: dense exact analysis of intermediate best approximants
between consecutive shadow failure levels L_k and L_{k+1} for frontierSix.

For k = 0, 1, 2, 3 (covering N = 12..14,515 exhaustively at every single N):
  - Splits (L_k, L_{k+1}] into the intermediate zone (L_k, N_entry(k+1)) and
    the shadow plateau [N_entry(k+1), L_{k+1}].
  - Counts all distinct intermediate plateaux and records their width distribution.
  - Finds the exact deepest intermediate minimum of log2(H_N)/N in each window
    and compares it against c = (25/98)*log2(3) ~= 0.404327 and the unconditional
    two-shadow lower bound (1-c)/(1+5c) ~= 0.197136.
  - Independently certifies the deepest intermediate dip and the plateau entry
    for every window using the Phase 13 minimality certificate verifier.

Bounded finite evidence only (k <= 3, N <= 14,515); does not prove B = c.
"""

import argparse
import json
from math import log2
from pathlib import Path
import sys

sys.set_int_max_str_digits(20000)
ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))

from experiments import residue, word
from height_lattice import profile
from height_reference import minimality_certificate
from verify_certificates import verify

JSON_OUT = ROOT / "intermediate-approximants.json"
MD_OUT = ROOT / "intermediate-approximants.md"

C_SHADOW = (25.0 / 98.0) * log2(3.0)
B_TWO_SHADOW = (1.0 - C_SHADOW) / (1.0 + 5.0 * C_SHADOW)
SPEC = {"kind": "morphism", "one": "100111", "zero": "111110"}
LEVELS = [(56 * 6**k - 1) // 5 for k in range(5)]  # [11, 67, 403, 2419, 14515]


def run_analysis() -> dict:
    max_n = LEVELS[-1]
    bits = word(SPEC, max_n)
    a = residue(bits)

    # Collect exact (H, p, q, f, g, transition) for every N = 1..max_n
    rows = {}
    for n, h, p, q, f, g, trans in profile(a, max_n):
        rows[n] = (h, p, q, f, g, trans)

    windows = []
    for k in range(4):
        lo = LEVELS[k]
        hi = LEVELS[k + 1]
        sh_h, sh_p, sh_q, _, _, _ = rows[hi]

        # Find exact plateau entry: earliest N in (lo, hi] where (p, q) == (sh_p, sh_q)
        entry_n = hi
        while entry_n > lo + 1 and rows[entry_n - 1][1:3] == (sh_p, sh_q):
            entry_n -= 1
        assert rows[entry_n][1:3] == (sh_p, sh_q)
        assert rows[entry_n - 1][1:3] != (sh_p, sh_q)

        # Partition intermediate zone (lo, entry_n) into maximal constant-(p, q) plateaux
        plateaux = []
        cur_start = lo + 1
        while cur_start < entry_n:
            cur_pq = rows[cur_start][1:3]
            cur_end = cur_start
            while cur_end + 1 < entry_n and rows[cur_end + 1][1:3] == cur_pq:
                cur_end += 1
            h_val = rows[cur_start][0]
            # Minimum of log2(H)/N on a plateau occurs at its right endpoint cur_end
            ratio_end = log2(h_val) / cur_end
            plateaux.append({
                "start_n": cur_start,
                "end_n": cur_end,
                "width": cur_end - cur_start + 1,
                "height_bits": h_val.bit_length(),
                "ratio_at_end": ratio_end,
            })
            cur_start = cur_end + 1

        # Deepest intermediate dip (minimizing log2(H_N)/N over lo < N < entry_n)
        deepest = min(plateaux, key=lambda pl: (pl["ratio_at_end"], pl["end_n"]))
        deep_n = deepest["end_n"]
        deep_h, deep_p, deep_q, deep_f, deep_g, _ = rows[deep_n]

        # Independently verify minimality certificates at deep_n and entry_n
        for check_n in (deep_n, entry_n):
            ch, cp, cq, cf, cg, ctrans = rows[check_n]
            rec = {
                "N": check_n,
                "A": a % (1 << check_n),
                "H": ch,
                "p": cp,
                "q": cq,
                "gcd": 1,
                "q_parity": 1,
                "basis": [list(cf), list(cg)],
                "transition": ctrans,
                "minimality": minimality_certificate(a % (1 << check_n), check_n, ch),
            }
            verify(rec, bits)

        widths = [pl["width"] for pl in plateaux]
        width_hist = {}
        for w in widths:
            width_hist[str(w)] = width_hist.get(str(w), 0) + 1

        below_c = [pl for pl in plateaux if pl["ratio_at_end"] < C_SHADOW]
        below_045 = [pl for pl in plateaux if pl["ratio_at_end"] < 0.45]

        windows.append({
            "k": k,
            "L_k": lo,
            "L_next": hi,
            "shadow_height_bits": sh_h.bit_length(),
            "shadow_ratio_at_L_next": round(log2(sh_h) / hi, 10),
            "plateau_entry_n": entry_n,
            "plateau_entry_fraction_of_L_next": round(entry_n / hi, 10),
            "plateau_length": hi - entry_n + 1,
            "intermediate_zone_length": entry_n - lo - 1,
            "intermediate_plateau_count": len(plateaux),
            "max_intermediate_width": max(widths),
            "width_histogram": dict(sorted(width_hist.items(), key=lambda kv: int(kv[0]))),
            "deepest_intermediate": {
                "N": deep_n,
                "fraction_of_L_next": round(deep_n / hi, 10),
                "plateau_start": deepest["start_n"],
                "plateau_width": deepest["width"],
                "height_bits": deep_h.bit_length(),
                "ratio": round(deepest["ratio_at_end"], 10),
                "excess_above_c": round(deepest["ratio_at_end"] - C_SHADOW, 10),
                "certified": True,
            },
            "intermediate_count_below_c": len(below_c),
            "intermediate_count_below_045": len(below_045),
        })

    return {
        "format": "phase13-intermediate-approximants-v1",
        "c_shadow": round(C_SHADOW, 12),
        "b_two_shadow": round(B_TWO_SHADOW, 12),
        "windows": windows,
    }


def render_markdown(data: dict) -> str:
    lines = [
        "# Phase 13 follow-up: dense intermediate best approximants in `(L_k, L_{k+1}]`",
        "",
        "Generated exact-arithmetic report for `frontierSix` (`1 -> 100111, 0 -> 111110`)",
        "covering every integer `N` in `12 <= N <= 14,515` (`k = 0, 1, 2, 3`).",
        f"Reference constants: `c = (25/98) log2(3) ~= {data['c_shadow']:.10f}`,",
        f"unconditional two-shadow lower bound `(1-c)/(1+5c) ~= {data['b_two_shadow']:.10f}`.",
        "",
        "Reproduce both artifacts byte-for-byte with:",
        "",
        "```bash",
        "python3 research/phase13/analyze_intermediate.py --check",
        "```",
        "",
        "## Window summary",
        "",
        "| `k` | `(L_k, L_{k+1}]` | plateau entry `N_entry` (`N_entry/L_{k+1}`) | inter. plateaux | max width | deepest inter. `N` (`N/L_{k+1}`) | deepest `log2(H_N)/N` | excess above `c` | `< c` count |",
        "|---:|---|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for w in data["windows"]:
        d = w["deepest_intermediate"]
        lines.append(
            f"| {w['k']} | `({w['L_k']}, {w['L_next']}]` | "
            f"{w['plateau_entry_n']} ({w['plateau_entry_fraction_of_L_next']:.4f}) | "
            f"{w['intermediate_plateau_count']} | {w['max_intermediate_width']} | "
            f"{d['N']} ({d['fraction_of_L_next']:.4f}) | "
            f"{d['ratio']:.6f} | {d['excess_above_c']:+.6f} | {w['intermediate_count_below_c']} |"
        )
    lines.extend([
        "",
        "## Observations and evidence boundary",
        "",
        "- In all four completed windows `k = 0, 1, 2, 3` (`12 <= N <= 14,515`), **zero**",
        "  intermediate best approximants dip below `c = (25/98) log2(3)`.",
        "- The shadow plateau entry `N_entry / L_{k+1}` approaches `2*c ~= 0.808654` as `k`",
        "  grows, matching the strict reconstruction uniqueness threshold `2*H^2 < 2^N`.",
        "- Both the deepest intermediate minimum and the exact plateau entry in every window",
        "  are independently verified via Phase 13 minimality certificates (`verify_certificates.py`).",
        "- This is bounded finite evidence (`k <= 3`) only; it does **not** rule out deeper",
        "  intermediate dips at `k >= 4` and does **not** prove `B = c`.",
        "",
    ])
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()

    data = run_analysis()
    md = render_markdown(data)
    if args.write:
        JSON_OUT.write_text(json.dumps(data, indent=2) + "\n")
        MD_OUT.write_text(md)
        print("WROTE: intermediate approximants analysis for k=0..3 (N <= 14,515)")
    else:
        assert data == json.loads(JSON_OUT.read_text()), "JSON mismatch"
        assert md == MD_OUT.read_text(), "Markdown mismatch"
        print("PASS: intermediate approximants analysis for k=0..3 (N <= 14,515)")


if __name__ == "__main__":
    main()
