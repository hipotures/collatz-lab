# Exact minimum excluded sets `|S_M*|` in F3, certified brackets, and `p/q` sensitivity

Generated exact-arithmetic report for the accelerated Collatz transition graph `G_M` modulo `2^M` at baseline contraction target `63/100` (verified `3^63 < 2^100`). No all-`M` asymptotic claim or proof of Collatz/CST is asserted.

Reproduce this report and `evidence.json` from the repository root with:

```text
cargo run --locked --release -- lyapunov-exact --out-dir research/lyapunov-exact
```

## Part A: Exact global minimum `|S_M*|` over all subsets `S <= V_M` (`1 <= M <= 8`)

Computed by exact Branch-and-Cut with certified integer dual-LP lower bounds. Every optimal excluded set `S_M*` is independently verified by a fresh SPFA potential check edge-by-edge in `i64` arithmetic.

| M | `2^M` | F2 excl | F3 heur (%) | **exact `|S_M*|`** (%) | heur gap | even in `S*` | non-F2 in `S*` | `S*` horizon `L_0` | B&C nodes |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 1 | 2 | 1 | 1 (50.00%) | **1 (50.00%)** | +0 | 0 | 0 | 1 | 1 |
| 2 | 4 | 1 | 1 (25.00%) | **1 (25.00%)** | +0 | 0 | 0 | 398 | 1 |
| 3 | 8 | 2 | 2 (25.00%) | **2 (25.00%)** | +0 | 0 | 0 | 398 | 1 |
| 4 | 16 | 3 | 2 (12.50%) | **2 (12.50%)** | +0 | 0 | 0 | 1194 | 1 |
| 5 | 32 | 4 | 4 (12.50%) | **4 (12.50%)** | +0 | 0 | 0 | 1194 | 19 |
| 6 | 64 | 8 | 5 (7.81%) | **5 (7.81%)** | +0 | 0 | 0 | 1313 | 1 |
| 7 | 128 | 13 | 9 (7.03%) | **8 (6.25%)** | +1 | 3 | 5 | 2507 | 376 |
| 8 | 256 | 19 | 14 (5.47%) | **12 (4.69%)** | +2 | 8 | 10 | 3700 | 12170 |

## Part B: Certified integer brackets `[LB_M, UB_M]` (`9 <= M <= 12`)

Each lower bound `LB_M = 1 + ceil(sum_y / max_load)` is certified in exact `i64` arithmetic by an explicit collection of independently verified violating cycles in `G_M \ {2^M - 1}` (`q * r(C) > p * |C|`). Each upper bound `UB_M` is certified by an edge-verified F3 integer potential.

| M | `2^M` | certified `LB_M` (%) | verified `UB_M` (%) | dual cycles | `sum_y / max_load` |
|---:|---:|---:|---:|---:|---:|
| 9 | 512 | 16 (3.12%) | 20 (3.91%) | 51 | 15.34 |
| 10 | 1024 | 18 (1.76%) | 38 (3.71%) | 138 | 17.88 |
| 11 | 2048 | 45 (2.20%) | 59 (2.88%) | 258 | 44.01 |
| 12 | 4096 | 56 (1.37%) | 114 (2.78%) | 620 | 55.05 |

## Part C: Sensitivity to contraction target `p/q < 1/log2(3) ~= 0.630930`

### C1. Exact global minimum `|S_M*|` (`4 <= M <= 7`)

| M | `5/8` (0.6250) | `17/27` (0.6296) | `63/100` (0.6300) | `41/65` (0.6308) | `94/149` (0.6309) |
|---:|---:|---:|---:|---:|---:|
| 4 | 2 (`L_0=190`) | 2 (`L_0=855`) | 2 (`L_0=1194`) | 2 (`L_0=6901`) | 2 (`L_0=19337`) |
| 5 | 4 (`L_0=190`) | 4 (`L_0=855`) | 4 (`L_0=1194`) | 4 (`L_0=6901`) | 4 (`L_0=19337`) |
| 6 | 5 (`L_0=211`) | 5 (`L_0=941`) | 5 (`L_0=1313`) | 5 (`L_0=7572`) | 5 (`L_0=21212`) |
| 7 | 8 (`L_0=401`) | 8 (`L_0=1795`) | 8 (`L_0=2507`) | 8 (`L_0=14472`) | 8 (`L_0=40548`) |

### C2. F3 ascending-pruned `|S_M|` and horizon `L_0` (`8 <= M <= 15`)

| M | F2 | `5/8` | `17/27` | `63/100` | `41/65` | `94/149` |
|---:|---:|---:|---:|---:|---:|---:|
| 8 | 19 | 14 (`L_0=317`) | 14 (`L_0=1425`) | 14 (`L_0=1990`) | 14 (`L_0=11501`) | 14 (`L_0=32227`) |
| 9 | 38 | 20 (`L_0=464`) | 20 (`L_0=2080`) | 20 (`L_0=2904`) | 20 (`L_0=16773`) | 20 (`L_0=46993`) |
| 10 | 64 | 38 (`L_0=401`) | 38 (`L_0=1795`) | 38 (`L_0=2507`) | 38 (`L_0=14472`) | 38 (`L_0=40548`) |
| 11 | 128 | 60 (`L_0=654`) | 60 (`L_0=2935`) | 60 (`L_0=4098`) | 60 (`L_0=23673`) | 60 (`L_0=66329`) |
| 12 | 226 | 122 (`L_0=675`) | 122 (`L_0=3020`) | 122 (`L_0=4217`) | 122 (`L_0=24344`) | 122 (`L_0=68204`) |
| 13 | 367 | 205 (`L_0=949`) | 205 (`L_0=4245`) | 205 (`L_0=5927`) | 205 (`L_0=34216`) | 205 (`L_0=95860`) |
| 14 | 734 | 327 (`L_0=1645`) | 327 (`L_0=7350`) | 327 (`L_0=10261`) | 327 (`L_0=59230`) | 327 (`L_0=165939`) |
| 15 | 1295 | 662 (`L_0=2109`) | 662 (`L_0=9401`) | 662 (`L_0=13122`) | 662 (`L_0=75715`) | 662 (`L_0=212111`) |

## Key findings and evidence boundary

- **Heuristic gap:** F3 pruning over `Survivors_M` is exact through `M = 6`, but misses the global optimum by `+1` at `M = 7` (`9` vs `8`) and `+2` at `M = 8` (`14` vs `12`), in part because the global minimum over `V_M` can exclude non-survivor (and even) bottleneck vertices.
- **Real downward trend vs `M = 14 -> 15` bump:** The certified lower bound at `M = 11` (`45/2048 = 2.20%`) is strictly above the verified upper bound at `M = 14` (`314/16384 = 1.92%`), proving rigorously that `|S_14*|/2^14 < |S_11*|/2^11`. The small `1.92% -> 2.02%` bump at `M = 15` lies well inside the measured heuristic suboptimality gap (already `12%–17%` at `M = 7, 8`).
- **`p/q` sensitivity:** Across the entire range from `5/8` (`0.6250`) through `17/27`, `63/100`, `41/65`, and `94/149` (`0.6309`), `|S_M|` is **100% identical** at every tested `M <= 15` (and exact `|S_M*|` for `M <= 7`), while the contraction horizon `L_0` spans a ~100x range (e.g. at `M = 15`: `2,109` at `5/8` vs `13,122` at `63/100` vs `212,111` at `94/149`).
