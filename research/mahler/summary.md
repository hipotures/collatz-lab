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
| Mahler functional equation and 2-adic identity `x(w) = -23/11 + (4/27)*F_2(16/27)` | `proven-by-algebra` |
| Five-way modular checkpoint agreement up to `2^1024` and periodic control `-19/11` | `verified-for-finite-domain` |
| Uncancelled polynomial Mahler denominator keeps `D_k` odd for `B(z) = z^2 - z^3` | `refuted` |
| Bounded exact Padé table (`1 <= m <= 16`) and `a_k^2`-cancelled height ledger | `verified-for-finite-domain` |
| All shifts `sigma^t(w)` (`t >= 0`) and general divergent positive orbits | `conjectured` |

## Five-way 2-adic checkpoint verification (`w = lim mu^j(1)`)

At each `K`, the unique compatible residue `x_K in [0, 2^K)` is computed five ways: (1) prefix affine map + modular inverse, (2) cylinder Hensel lifting, (3) parity-position inverse sum `-sum_{i=0}^{r_K-1} 2^(d_i) / 3^(i+1) (mod 2^K)`, (4) the Mahler reduction `-23/11 + (4/27)*F_2(16/27) (mod 2^K)`, and (5) direct iteration of `T` for `K` steps on `x_K`. Full decimal values are recorded in `evidence.json`.

| K | r_K | prefixes survive | F_2(16/27) mod 2^K | residue x_K mod 2^K | 5-way + Mahler eq + cocycle |
|---|---|---|---|---|---|
| 16 | 12 | yes | `2609` | `25319` | exact match |
| 32 | 24 | yes | `2103183921` | `2437374695` | exact match |
| 64 | 48 | yes | `2121339037416163889` | `9941361107984147175` | exact match |
| 128 | 96 | yes | `847981005358...037442144817 (38 digits)` | `186713926584...903286944487 (39 digits)` | exact match |
| 256 | 192 | yes | `824830789101...452407638577 (77 digits)` | `176779283547...490537882343 (77 digits)` | exact match |
| 512 | 384 | yes | `337108179551...335331895857 (154 digits)` | `614243633079...578721764071 (154 digits)` | exact match |
| 1024 | 768 | yes | `124595597578...656957970993 (309 digits)` | `158884468088...015912964839 (309 digits)` | exact match |

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

## Mahler tower structure and the `B(z) = z^2 - z^3` denominator obstruction

- Power-series identity `(1 - z^4)(F(z) - (z^2 - z^3)F(z^4)) = 1 + z + z^3` verified to degree: `1024`
- Homogenised prefix recurrence `preS(a, b, 4L)` verified for block counts: `0..=64`
- Vanishing order of `B(z) = z^2(1 - z)` at `z = 0`: `2`
- 2-adic valuation `v_2(D_1)` of the **uncancelled** polynomial tower denominator: `8` (`D_1` is even, refuting `Odd D_k` without `a_k^2` cancellation)
- Exact integer divisibility `a_0^2 | Delta_0` in the **`a_k^2`-cancelled** tower: `yes` (verified across `0..=15` blocks)
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

- Kernel-checked formalization (e.g., in Lean 4) of the a_k^2-cancelled backward Mahler tower transport for B(z) = z^2(1 - z) and the degree-4 Padé contradiction.
- Exclusion of arbitrary shifted itineraries w^(s)(t) = w[s + t] (s >= 1), which require a coupled 4-state inhomogeneous Mahler system rather than the unshifted scalar equation.
- Exclusion of general non-automatic, Sturmian, or arbitrary aperiodic survivor itineraries with tau(n) = +infinity.
- Resolution of the Coefficient Stopping Time conjecture (whether any minimal nonconvergent positive integer orbit can cross a coefficient threshold) and the Collatz conjecture itself.
