# Phase 13 follow-up: rational shadows and 3-adic non-cancellation across morphisms

Generated exact-arithmetic comparison extending the Phase 13 rational-shadow
mechanism from `frontierSix` (`1 -> 100111, 0 -> 111110`, `c = (25/98) log2(3) ~= 0.404327`)
to the two Phase 11 unequal-weight morphisms (`110/111`, `1011/1111`) and contrasting
them with equal-weight controls (`110/011`, Thue-Morse `10/01`).

Reproduce both artifacts byte-for-byte with:

```bash
python3 research/phase13/analyze_morphisms.py --check
```

## Overview: three nonconvergent unequal-weight morphisms

| family | substitution | shadow match `L_k` | exact exponent `c` | `c` (numeric) | `1 - c` | nonconvergent? |
|---|---|---|---|---:|---:|---|
| `frontierSix` (baseline) | `1->100111, 0->111110` | `(56*6^k - 1)/5` | `(25/98)*log2(3)` | 0.404327 | 0.595673 | **yes** |
| `phase11-110` | `1->110, 0->111` | `3^(k+1) - 1` | `(1/4)*log2(3)` | 0.396241 | 0.603759 | **yes** |
| `phase11-1011` | `1->1011, 0->1111` | `(28*4^k - 1)/3` | `(1/5)*log2(3)` | 0.316993 | 0.683007 | **yes** |

## `phase11-110` (`1 -> 110, 0 -> 111`)

| `k` | `L_k` | min preperiod | period | raw gcd | `|P_k| mod 3` | `Q_k mod 3` | `log2(H)/L_k` | `log2(H)/(L_k+1)` | unique? | lattice match? |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|
| 0 | 2 | 0 | 1 | 1 | 1 | 1 | 0.000000 | 0.528321 | yes | yes |
| 1 | 8 | 0 | 3 | 1 | 2 | 1 | 0.290241 | 0.602918 | yes | yes |
| 2 | 26 | 0 | 9 | 1 | 1 | 1 | 0.452987 | 0.510682 | yes | yes |
| 3 | 80 | 0 | 27 | 1 | 2 | 1 | 0.409298 | 0.576594 | yes | yes |
| 4 | 242 | 0 | 81 | 1 | 1 | 1 | 0.404066 | 0.591210 | yes | yes |
| 5 | 728 | 0 | 243 | 1 | 2 | 1 | 0.397753 | 0.600663 | yes | yes |
| 6 | 2186 | 0 | 729 | 1 | 1 | 1 | 0.397107 | 0.602365 | yes | yes |
| 7 | 6560 | 0 | 2187 | 1 | 2 | 1 | 0.396408 | 0.603415 | yes | yes |
| 8 | 19682 | 0 | 6561 | 1 | 1 | 1 | 0.396337 | — | yes | — |

## `phase11-1011` (`1 -> 1011, 0 -> 1111`)

| `k` | `L_k` | min preperiod | period | raw gcd | `|P_k| mod 3` | `Q_k mod 3` | `log2(H)/L_k` | `log2(H)/(L_k+1)` | unique? | lattice match? |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|
| 0 | 9 | 2 | 1 | 1 | 2 | 0 | 0.257992 | 0.606609 | yes | yes |
| 1 | 37 | 6 | 4 | 1 | 2 | 0 | 0.331842 | 0.634230 | yes | yes |
| 2 | 149 | 22 | 16 | 13 | 1 | 0 | 0.299856 | 0.691327 | yes | yes |
| 3 | 597 | 86 | 64 | 1 | 2 | 0 | 0.320077 | 0.677745 | yes | yes |
| 4 | 2389 | 342 | 256 | 13 | 1 | 0 | 0.315949 | 0.683504 | yes | yes |
| 5 | 9557 | 1366 | 1024 | 1 | 2 | 0 | 0.317185 | — | yes | — |

## Equal-weight controls (`128 <= N <= 4096`)

| family | substitution | min `log2(H_N)/N` (N) | max `log2(H_N)/N` (N) | spread |
|---|---|---:|---:|---:|
| `phase8-110` | `1->110, 0->011` | 0.471126 (156) | 0.520199 (141) | 0.049073 |
| `thue-morse-10` | `1->10, 0->01` | 0.469235 (192) | 0.527969 (193) | 0.058734 |

## Observations and evidence boundary

- For **`phase11-110`**, the purely periodic shadows `(mu^k(1))^inf` have `Q_k = 3^(w_1(k)) - 2^(3^k)`
  automatically coprime to 3 (no preperiod factor), exact match length `L_k = 3^(k+1) - 1`,
  and exponent `c = (1/4)*log2(3) ~= 0.396241 < 1/2`. Every level `k = 0..7` matches the
  exact lattice minimizer; raw GCDs are `1` at `k = 0..8`.
- For **`phase11-1011`**, the trimmed eventually-periodic shadows `mu^k(10)(mu^k(1))^inf`
  have exact match length `L_k = (28*4^k - 1)/3` and exponent `c = (1/5)*log2(3) ~= 0.316993 < 1/2`.
  At all tested levels `k = 0..5`, `|P_k| mod 3 != 0` (exact 3-adic preperiod non-cancellation,
  matching `frontierSix`!) and every level `k = 0..4` matches the exact lattice minimizer.
- By the same determinant inequality as in `phase13-theory.md`, both `phase11-110` and
  `phase11-1011` have nonconvergent normalized height profiles (`liminf <= c < 1/2 < 1 - c <= limsup`).
- These are bounded exact verifications and written exponent derivations, not Lean-formalized
  theorems for `phase11-110` or `phase11-1011`.
