# Phase 3: aperiodic survivor itinerary and exact 2-adic Mahler reduction

Generated deterministic evidence for the fixed point `w = lim_{j -> infinity} mu^j(1)` of the uniform morphism `mu(1) = 1110`, `mu(0) = 1101` under the accelerated Collatz map `T(n) = n/2` (even), `(3n+1)/2` (odd). All arithmetic uses exact arbitrary-precision integers (`BigUint` and `BigInt`); no floating point is used anywhere.

Nothing below claims originality over Bernstein-Lagarias (1996), Lagarias (1990), Terras (1976), or `msharpe248/collatz`, and nothing claims a proof of CST or the Collatz conjecture. See [the mathematical memo](../infinite-itineraries.md) for complete proofs, derivations, and literature citations.

Reproduce this summary and `evidence.json` from the repository root with:

```text
cargo run --locked --release -- mahler --out-dir research/mahler
```

## Epistemic status summary

| claim | status |
|---|---|
| All-prefix coefficient survival `3^(r_k) > 2^k` for all `k >= 1` | `proven-by-algebra` |
| Aperiodicity of `w` (`w` is not eventually periodic) | `proven-by-algebra` |
| Mahler functional equation, `x(w) = -23/11 + (4/27)*F_2(16/27)`, repaired tower + degree-4 Padé irrationality of `x(w)`, and inverse-branch exclusion of all shifts `sigma^t(w)` (`t >= 0`) | `proven-by-algebra` |
| Five-way modular checkpoint agreement up to `2^1024` and periodic control `-19/11` | `verified-for-finite-domain` |
| Uncancelled polynomial Mahler denominator keeps `D_k` odd for `B(z) = z^2 - z^3` | `refuted` |
| Bounded exact Padé table (`1 <= m <= 16`) and `a_k^2`-cancelled height ledger | `verified-for-finite-domain` |
| General Periodicity Conjecture, non-automatic survivor itineraries, CST, and general divergent positive orbits | `conjectured` |

## Five-way 2-adic checkpoint verification (`w = lim mu^j(1)`)

At each `K`, the unique compatible residue `x_K in [0, 2^K)` is computed five ways: (1) prefix affine map + modular inverse, (2) cylinder Hensel lifting, (3) parity-position inverse sum `-sum_{i=0}^{r_K-1} 2^(d_i) / 3^(i+1) (mod 2^K)`, (4) the Mahler reduction `-23/11 + (4/27)*F_2(16/27) (mod 2^K)`, and (5) direct iteration of `T` for `K` steps on `x_K`. In addition, the repaired seed normalization `D_0 = 11, u_0 = 27*(11*x_K + 23)/4` is checked on each actual checkpoint seed `x_K` across `1 <= L <= K/4 - 1` blocks at level 0 and `1 <= L <= (K/4 - 1)/4` blocks at level 1 (while recording that the unnormalized `(11*x_K + 23)/4` gives `1 != 11 (mod 16)` at `L = 1`). Full decimal values are recorded in `evidence.json`.

| K | r_K | prefixes survive | F_2(16/27) mod 2^K | residue x_K mod 2^K | unnorm / repaired u_0 mod 16 | repaired L_0 / L_1 blocks | 5-way + Mahler eq + cocycle |
|---|---|---|---|---|---|---|---|
| 16 | 12 | yes | `2609` | `25319` | `1 != 11` / `11 == 11` | `1..=3` / `1..=0` | exact match |
| 32 | 24 | yes | `2103183921` | `2437374695` | `1 != 11` / `11 == 11` | `1..=7` / `1..=1` | exact match |
| 64 | 48 | yes | `2121339037416163889` | `9941361107984147175` | `1 != 11` / `11 == 11` | `1..=15` / `1..=3` | exact match |
| 128 | 96 | yes | `847981005358...037442144817 (38 digits)` | `186713926584...903286944487 (39 digits)` | `1 != 11` / `11 == 11` | `1..=31` / `1..=7` | exact match |
| 256 | 192 | yes | `824830789101...452407638577 (77 digits)` | `176779283547...490537882343 (77 digits)` | `1 != 11` / `11 == 11` | `1..=63` / `1..=15` | exact match |
| 512 | 384 | yes | `337108179551...335331895857 (154 digits)` | `614243633079...578721764071 (154 digits)` | `1 != 11` / `11 == 11` | `1..=127` / `1..=31` | exact match |
| 1024 | 768 | yes | `124595597578...656957970993 (309 digits)` | `158884468088...015912964839 (309 digits)` | `1 != 11` / `11 == 11` | `1..=255` / `1..=63` | exact match |

## Periodic control `(1110)^infinity` (`x = -19/11`)

Every finite prefix of `(1110)^infinity` is realized by positive integers `n_K >= 2` with `T^K(n_K) > n_K`, even though the unique 2-adic limit is the negative rational `-19/11`. Every `n_K` therefore diverges from `(1110)^infinity` at a finite step `k >= K`.

| K | r_K | least positive seed n_K >= 2 | 11*n_K + 19 == 0 (mod 2^K) | T^K(n_K) > n_K | first divergence step |
|---|---|---|---|---|---|
| 16 | 12 | `41703` | yes | yes | 16 |
| 32 | 24 | `780903143` | yes | yes | 33 |
| 64 | 48 | `10061860403841573607` | yes | yes | 65 |
| 128 | 96 | `309347606291...028880192231 (39 digits)` | yes | yes | 129 |
| 256 | 192 | `736858749692...217446134503 (77 digits)` | yes | yes | 256 |
| 512 | 384 | `243778325998...572546560743 (154 digits)` | yes | yes | 513 |
| 1024 | 768 | `980559891743...158667711207 (308 digits)` | yes | yes | 1025 |

## Mahler tower structure, repaired `(u_0, D_0)` seed normalization, and `B(z) = z^2 - z^3`

- Power-series identity `(1 - z^4)(F(z) - (z^2 - z^3)F(z^4)) = 1 + z + z^3` verified to degree: `1024`
- Homogenised prefix recurrence `preS(a, b, 4L)` verified for block counts: `1..=64`
- Vanishing order of `B(z) = z^2(1 - z)` at `z = 0`: `2`
- Base-case regression on unnormalized `u_0^old = (11*x_K + 23)/4` (`D_0 = 11`): `u_0^old mod 16 = 1 != 11 = D_0*preS(16, 27, 1) mod 16` and `Delta_0^old mod 256 = 134 != 0` (fails at `L = 1`)
- Repaired seed normalization `D_0 = 11`, `u_0 = 27*(11*x_K + 23)/4` on actual checkpoint seed `x_1024`: `u_0 mod 16 = 11 == 11`, verified across `1..=255` blocks at level 0, `1..=63` blocks at level 1 (`D_1 = 56374505`, odd: `yes`), and `1..=15` blocks at level 2 (`D_2 = 209459418257...043875033625 (37 digits)`, odd: `yes`)
- 2-adic valuation `v_2(D_1)` of the **uncancelled** polynomial tower denominator: `8` (`D_1` is even, refuting `Odd D_k` without `a_k^2` cancellation)
- Exact integer divisibility `a_0^2 | Delta_0` and `a_1^2 | Delta_1` in the **`a_k^2`-cancelled** seed tower: `yes` / `yes`
- Corrected degree-4 linear form `E_k = D_k*P_0(a_k, b_k) + u_k*P_1(a_k, b_k)` on `x_1024` seed tower: `v_2(E_0) = 56`, `v_2(E_1) = 224`, `v_2(E_2) = 896` (`= 56 * 4^k`)
- Explicit uniform archimedean height step `H_{k+1} <= b_k^7 * H_k` and `|E_k| < 3*(|u_0| + D_0)*3^(19*4^k)` verified on `k = 0, 1, 2`: `yes` (`2^56 = 72057594037927936` vs `3^19 = 1162261467`)
- Naive series truncation Liouville exponent `< 1` (`16^L < 27^L`): `yes`
- Degree-1 Padé (`m = 1`, `N = 3`) in `a_k^2`-cancelled ledger: `2^44 = 17592186044416` vs `3^30 = 205891132094649` (closes: `no`)
- Degree-4 Padé (`m = 4`, `N = 14`) coarse step gain vs cost: `2^56 = 72057594037927936` vs `16 * 27^7 = 167365651248` (closes: `yes`)

## Bounded exact Padé auxiliary-form table (`1 <= m <= 16`)

For each degree bound `m`, the nullspace of the `(2m + 1) x (2m + 2)` integer Hankel/Toeplitz system for `p_0(z) + p_1(z)*F(z) = O(z^(2m+1))` is solved by exact fraction-free `BigInt` row reduction, normalized to primitive integer coefficients, and stripped of any common `z^s` shift (`reduced deg`).

| m | null dim | shift s | red deg | singular block | reduced p_0(z) | reduced p_1(z) | L_1 | L_inf | red order N | lead coeff c | v_2(c) | closes cancelled ledger | closes coarse ledger |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | 1 | 0 | 1 | no | `1` | `-1 + z` | 3 | 1 | 3 | `1` | 0 | `2^44 vs 3^30` (no) | no |
| 2 | 1 | 0 | 2 | no | `1 + 2*z + z^2` | `-1 - z + z^2` | 7 | 2 | 5 | `-2` | 1 | `2^68 vs 3^39` (yes) | no |
| 3 | 1 | 0 | 3 | no | `2 + z - 3*z^3` | `-2 + z + z^2 + z^3` | 11 | 3 | 7 | `3` | 0 | `2^92 vs 3^48` (yes) | no |
| 4 | 1 | 0 | 4 | no | `1 + z + z^2` | `-1 + z^4` | 5 | 1 | 14 | `1` | 0 | `2^176 vs 3^57` (yes) | yes |
| 5 | 2 | 0 | 4 | yes | `1 + z + z^2` | `-1 + z^4` | 5 | 1 | 14 | `1` | 0 | `2^176 vs 3^57` (yes) | yes |
| 6 | 3 | 0 | 4 | yes | `1 + z + z^2` | `-1 + z^4` | 5 | 1 | 14 | `1` | 0 | `2^176 vs 3^57` (yes) | yes |
| 7 | 3 | 1 | 4 | yes | `1 + z + z^2` | `-1 + z^4` | 5 | 1 | 14 | `1` | 0 | `2^176 vs 3^57` (yes) | yes |
| 8 | 2 | 3 | 4 | yes | `1 + z + z^2` | `-1 + z^4` | 5 | 1 | 14 | `1` | 0 | `2^176 vs 3^57` (yes) | yes |
| 9 | 1 | 5 | 4 | yes | `1 + z + z^2` | `-1 + z^4` | 5 | 1 | 14 | `1` | 0 | `2^176 vs 3^57` (yes) | yes |
| 10 | 1 | 0 | 10 | no | `3 + 6*z + 9*...z^8 + 3*z^10 (76 digits)` | `-3 - 3*z - 3...z^9 + 8*z^10 (81 digits)` | 176 | 27 | 21 | `-11` | 0 | `2^260 vs 3^111` (yes) | yes |
| 11 | 1 | 0 | 11 | no | `11 + 5*z - z...10 - 17*z^11 (94 digits)` | `-11 + 6*z + ...^10 - 5*z^11 (94 digits)` | 283 | 54 | 23 | `34` | 1 | `2^284 vs 3^120` (yes) | no |
| 12 | 1 | 0 | 12 | no | `1 + z + z^2 ...*z^10 - z^11 (67 digits)` | `-1 - z^4 - z^8 + z^11 + 2*z^12` | 25 | 3 | 25 | `-1` | 0 | `2^308 vs 3^129` (yes) | yes |
| 13 | 1 | 0 | 13 | no | `34 - 34*z - ...12 - 17*z^13 (125 digits)` | `-34 + 68*z -...2 - 141*z^13 (118 digits)` | 1731 | 243 | 27 | `227` | 0 | `2^332 vs 3^138` (yes) | yes |
| 14 | 1 | 0 | 14 | no | `227 + 447*z ...3 - 337*z^14 (145 digits)` | `-227 - 220*z...3 + 236*z^14 (140 digits)` | 10498 | 899 | 29 | `299` | 0 | `2^356 vs 3^147` (yes) | yes |
| 15 | 1 | 0 | 15 | no | `299 - 38*z -...4 + 960*z^15 (159 digits)` | `-299 + 337*z...4 - 407*z^15 (155 digits)` | 15921 | 1278 | 31 | `-960` | 6 | `2^380 vs 3^156` (yes) | no |
| 16 | 1 | 0 | 16 | no | `1 + z + z^2 ... z^13 + z^15 (69 digits)` | `-1 + z^16` | 14 | 1 | 58 | `1` | 0 | `2^704 vs 3^165` (yes) | yes |

## Unresolved proof obligations

- Kernel-checked formalization (e.g., in Lean 4) of the repaired a_k^2-cancelled backward Mahler tower (Theorem 6.2), the degree-4 Padé contradiction (Theorem 7.1), and the inverse-branch exclusion of all shifted tails sigma^t(w) (Corollary 7.3).
- The open Periodicity Conjecture (Lagarias 1985; Rozier 2019, Conjecture 1) asserting that every rational 2-adic integer has an eventually periodic parity sequence (Lagarias 1990, Corollary 2.1b proves only the periodic-to-rational direction; the 2021 arXiv preprint of López and Stoll conflates the real limit Phi_R(v) with the 2-adic limit Phi_{Z_2}(v)).
- Exclusion of general non-automatic, Sturmian, or arbitrary aperiodic survivor itineraries in S_infinity \ {sigma^t(w) : t >= 0}, which satisfy no Mahler functional equation.
- Resolution of the Coefficient Stopping Time conjecture (whether any minimal nonconvergent positive integer orbit can cross a coefficient threshold) and the Collatz conjecture itself.
