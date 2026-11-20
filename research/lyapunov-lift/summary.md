# Monotone lift chain for F3 excluded sets (`1 <= M <= 21`)

Generated exact-arithmetic report for the accelerated Collatz transition graph `G_M` modulo `2^M` at contraction target `63/100` (verified `3^63 < 2^100`). No asymptotic density limit, optimality for `M > 8`, or proof of Collatz/CST is claimed.

Reproduce this report and `evidence.json` from the repository root with:

```text
cargo run --locked --release -- lyapunov-lift --max-m 21 --exact-seed-max-m 8 --out-dir research/lyapunov-lift
```

## Lifting lemma (written proof; checked concretely at every depth here)

Reduction modulo `2^M` maps every edge `u -> v` of `G_{M+1}` to an edge `u mod 2^M -> v mod 2^M` of `G_M` (both are `T(n)` reduced, for the same `n`), and it preserves the odd-step label `odd(u)`. Therefore, if `phi` is an F3 potential on `V_M \ S`, then `u -> phi(u mod 2^M)` is an F3 potential on `V_{M+1} \ lift(S)`, where `lift(S) = {u : u mod 2^M in S}` has exactly `2|S|` elements. In particular the exact optimum density `|S_M*| / 2^M` is **non-increasing in `M`**, and any `UB_M` yields `UB_{M+1} <= 2 UB_M`. This is a short paper argument, not a Lean theorem; the column `lifted edges` records the finite edge-by-edge verification of the lifted potential performed at each depth.

## Method

1. Lift the chain element of depth `M - 1` (for `M = 1`, the set `{0}` mod `1`) and verify the lifted potential on every active edge.
2. Prune two starting bases, the lifted set (`lift`) and its union with the F2 survivors (`lift+F2`), by exact incremental warm-start SPFA, trying to restore *every* excluded vertex (odd or even, inside or outside the F2 survivors). Orders: `ascending`, `descending`, `low-odd-weight`, `even-first`, plus 16 pseudo-random orders from fixed xorshift seeds. Feasibility is monotone under restoration, so one pass per order suffices.
3. Compare with the survivors-only F3 heuristic of `lyapunov` (min of ascending and low-odd-weight orders over `Survivors_M`) and, for `M <= 8`, with the exact optimum `|S_M*|` from `lyapunov-exact`. The smallest set becomes the chain element.
4. Re-solve a fresh potential for the chain element from scratch and verify every active edge in exact `i64` arithmetic.

## Results

| M | `2^M` | parent | lifted (`2x`) | lifted edges | lift-pruned (%) | survivor heur (%) | exact `|S_M*|` | **chain `UB_M`** (%) | source | even | non-F2 | span | `L_0` |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---:|---:|---:|---:|
| 1 | 2 | 1 | 2 | 0 | 1 (50.000%) | 1 (50.000%) | 1 | **1 (50.000%)** | lift | 0 | 0 | 0 | 1 |
| 2 | 4 | 1 | 2 | 2 | 1 (25.000%) | 1 (25.000%) | 1 | **1 (25.000%)** | lift | 0 | 0 | 37 | 398 |
| 3 | 8 | 1 | 2 | 10 | 2 (25.000%) | 2 (25.000%) | 2 | **2 (25.000%)** | lift | 0 | 0 | 37 | 398 |
| 4 | 16 | 2 | 4 | 20 | 2 (12.500%) | 2 (12.500%) | 2 | **2 (12.500%)** | lift | 0 | 0 | 111 | 1194 |
| 5 | 32 | 2 | 4 | 50 | 4 (12.500%) | 4 (12.500%) | 4 | **4 (12.500%)** | lift | 0 | 1 | 111 | 1194 |
| 6 | 64 | 4 | 8 | 100 | 5 (7.812%) | 5 (7.812%) | 5 | **5 (7.812%)** | lift | 0 | 0 | 111 | 1194 |
| 7 | 128 | 5 | 10 | 218 | 8 (6.250%) | 9 (7.031%) | 8 | **8 (6.250%)** | lift | 0 | 2 | 122 | 1313 |
| 8 | 256 | 8 | 16 | 450 | 14 (5.469%) | 14 (5.469%) | 12 | **12 (4.688%)** | exact | 8 | 10 | 344 | 3700 |
| 9 | 512 | 12 | 24 | 930 | 20 (3.906%) | 20 (3.906%) | - | **20 (3.906%)** | lift | 0 | 1 | 196 | 2109 |
| 10 | 1024 | 20 | 40 | 1890 | 37 (3.613%) | 38 (3.711%) | - | **37 (3.613%)** | lift | 0 | 9 | 318 | 3421 |
| 11 | 2048 | 37 | 74 | 3814 | 61 (2.979%) | 59 (2.881%) | - | **59 (2.881%)** | survivor-heuristic | 0 | 0 | 281 | 3023 |
| 12 | 4096 | 59 | 118 | 7728 | 110 (2.686%) | 114 (2.783%) | - | **110 (2.686%)** | lift | 0 | 28 | 477 | 5131 |
| 13 | 8192 | 110 | 220 | 15510 | 200 (2.441%) | 200 (2.441%) | - | **200 (2.441%)** | lift | 0 | 0 | 540 | 5808 |
| 14 | 16384 | 200 | 400 | 31326 | 314 (1.917%) | 314 (1.917%) | - | **314 (1.917%)** | lift | 0 | 0 | 636 | 6841 |
| 15 | 32768 | 314 | 628 | 63044 | 599 (1.828%) | 662 (2.020%) | - | **599 (1.828%)** | lift | 0 | 143 | 943 | 10143 |
| 16 | 65536 | 599 | 1198 | 126284 | 1143 (1.744%) | 1254 (1.913%) | - | **1143 (1.744%)** | lift | 0 | 546 | 1172 | 12606 |
| 17 | 131072 | 1143 | 2286 | 253002 | 2046 (1.561%) | 1908 (1.456%) | - | **1908 (1.456%)** | survivor-heuristic | 0 | 0 | 2835 | 30492 |
| 18 | 262144 | 1908 | 3816 | 509062 | 3490 (1.331%) | 3926 (1.498%) | - | **3490 (1.331%)** | lift | 0 | 961 | 2979 | 32041 |
| 19 | 524288 | 3490 | 6980 | 1020660 | 6426 (1.226%) | 6469 (1.234%) | - | **6426 (1.226%)** | lift | 0 | 1922 | 3630 | 39043 |
| 20 | 1048576 | 6426 | 12852 | 2045746 | 12627 (1.204%) | 12929 (1.233%) | - | **12627 (1.204%)** | lift | 0 | 5535 | 4675 | 50283 |
| 21 | 2097152 | 12627 | 25254 | 4093290 | 22691 (1.082%) | 22691 (1.082%) | - | **22691 (1.082%)** | lift | 0 | 0 | 4185 | 45012 |

### Pruning results by starting base and restoration order

Minimum excluded count per base over the deterministic orders and over the seeded pseudo-random orders.

| M | `lift` named | `lift` random | `lift+F2` named | `lift+F2` random |
|---:|---:|---:|---:|---:|
| 1 | 1 | 1 | 1 | 1 |
| 2 | 1 | 1 | 1 | 1 |
| 3 | 2 | 2 | 2 | 2 |
| 4 | 2 | 2 | 2 | 2 |
| 5 | 4 | 4 | 4 | 4 |
| 6 | 6 | 6 | 5 | 5 |
| 7 | 9 | 9 | 9 | 8 |
| 8 | 15 | 15 | 14 | 14 |
| 9 | 23 | 23 | 20 | 21 |
| 10 | 38 | 38 | 38 | 37 |
| 11 | 65 | 65 | 61 | 62 |
| 12 | 110 | 110 | 114 | 112 |
| 13 | 206 | 206 | 200 | 212 |
| 14 | 317 | 317 | 314 | 317 |
| 15 | 599 | 599 | 645 | 638 |
| 16 | 1143 | 1143 | 1247 | 1240 |
| 17 | 2176 | 2176 | 2046 | 2174 |
| 18 | 3490 | 3490 | 3659 | 3704 |
| 19 | 6426 | 6426 | 6927 | 6864 |
| 20 | 12628 | 12627 | 12882 | 13547 |
| 21 | 24590 | 24585 | 22691 | 25967 |

## Observations (derived from the table above)

- The chain is strictly smaller than the survivors-only F3 heuristic at: `M=7` (8 vs 9), `M=8` (12 vs 14), `M=10` (37 vs 38), `M=12` (110 vs 114), `M=15` (599 vs 662), `M=16` (1143 vs 1254), `M=18` (3490 vs 3926), `M=19` (6426 vs 6469), `M=20` (12627 vs 12929).
- The survivors-only heuristic supplied the chain element at: `M=11`, `M=17`.
- The chain density strictly decreased from `M - 1` to `M` at 19 of 21 depths; by construction it never increased.

## Evidence boundary and limitations

- For `M` above the exact-seed range, every chain value is an **upper bound** `UB_M >= |S_M*|` only; the pruning is greedy and order-dependent.
- The monotonicity of `|S_M*| / 2^M` is a written lifting argument with a finite per-depth check, not a Lean-verified theorem and not a statement about the limit of the density as `M -> infinity`.
- **What F3 does not claim:** staying inside `V_M \ S` is a conditional hypothesis on an orbit segment; F3 does not prevent an integer orbit from entering the excluded residue set `S`, and does not prove global convergence.
