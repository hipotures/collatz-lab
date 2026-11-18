# Phase 13 follow-up: dense intermediate best approximants in `(L_k, L_{k+1}]`

Generated exact-arithmetic report for `frontierSix` (`1 -> 100111, 0 -> 111110`)
covering every integer `N` in `12 <= N <= 14,515` (`k = 0, 1, 2, 3`).
Reference constants: `c = (25/98) log2(3) ~= 0.4043271686`,
unconditional two-shadow lower bound `(1-c)/(1+5c) ~= 0.1971358769`.

Reproduce both artifacts byte-for-byte with:

```bash
python3 research/phase13/analyze_intermediate.py --check
```

## Window summary

| `k` | `(L_k, L_{k+1}]` | plateau entry `N_entry` (`N_entry/L_{k+1}`) | inter. plateaux | max width | deepest inter. `N` (`N/L_{k+1}`) | deepest `log2(H_N)/N` | excess above `c` | `< c` count |
|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 0 | `(11, 67]` | 57 (0.8507) | 26 | 6 | 31 (0.4627) | 0.410653 | +0.006326 | 0 |
| 1 | `(67, 403]` | 327 (0.8114) | 120 | 7 | 95 (0.2357) | 0.473408 | +0.069081 | 0 |
| 2 | `(403, 2419]` | 1963 (0.8115) | 778 | 11 | 667 (0.2757) | 0.494817 | +0.090490 | 0 |
| 3 | `(2419, 14515]` | 11739 (0.8087) | 4705 | 13 | 3134 (0.2159) | 0.498798 | +0.094471 | 0 |

## Observations and evidence boundary

- In all four completed windows `k = 0, 1, 2, 3` (`12 <= N <= 14,515`), **zero**
  intermediate best approximants dip below `c = (25/98) log2(3)`.
- The shadow plateau entry `N_entry / L_{k+1}` approaches `2*c ~= 0.808654` as `k`
  grows, matching the strict reconstruction uniqueness threshold `2*H^2 < 2^N`.
- Both the deepest intermediate minimum and the exact plateau entry in every window
  are independently verified via Phase 13 minimality certificates (`verify_certificates.py`).
- This is bounded finite evidence (`k <= 3`) only; it does **not** rule out deeper
  intermediate dips at `k >= 4` and does **not** prove `B = c`.
