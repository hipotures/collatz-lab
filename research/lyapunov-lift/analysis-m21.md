# F3 lift chain to `M = 21`: run record and trend analysis

Hand-written analysis of the extended lift-chain run. The tables in
[`summary.md`](summary.md) and [`evidence.json`](evidence.json) are generated;
this note adds the run record, the independent re-check, and a comparison
with the F2 survivor counts. **Every value for `M > 8` is a greedy upper
bound `UB_M >= |S_M*|`.** Nothing here proves an asymptotic density, an
optimality statement, or anything about the Collatz conjecture.

## Run record

- Command (commit `0da0455`, 8 worker threads):
  `collatz-lab lyapunov-lift --max-m 22 --out-dir research/runs/lift22`.
- Depths `1..=21` completed and were checkpointed in `progress.jsonl`. The
  run was **stopped by the owner's decision during `M = 22`** after about
  5.3 h on that depth: the observed growth predicted another 30–40 h.
- The committed `evidence.json` / `summary.md` were assembled with
  `--max-m 21 --resume <progress.jsonl>`. Resuming re-checks every recorded
  row from scratch (lifted potential, freshly solved chain potential, edge
  count, span, horizon, even and non-survivor counts). A resume from the first
  14 rows reproduces the previously committed `M <= 18` files byte for byte,
  and rows `1..=18` of the new evidence are identical to the old ones.
- From scratch, `cargo run --locked --release -- lyapunov-lift --max-m 21
  --exact-seed-max-m 8 --out-dir research/lyapunov-lift` regenerates the same
  files (output is independent of `--threads`), but takes about 10.5 h of wall
  time on 8 cores.

Wall time per depth (8 threads; 40 pruning jobs plus the survivors-only
heuristic per depth):

| M | wall time | ratio to `M - 1` |
|---:|---:|---:|
| 16 | 3.3 s | – |
| 17 | 16.1 s | 4.9 |
| 18 | 63.4 s | 3.9 |
| 19 | 13.5 min | 12.8 |
| 20 | 1.70 h | 7.5 |
| 21 | 8.26 h | 4.9 |

A projection made from `M <= 18` (factor about 4 per depth) underestimated
`M = 19..21` by 3–5x. The cost of one incremental-SPFA pruning pass grows
much faster than `2^M`, and short runs did not predict it.

## Independent re-check

[`verify_chain.py`](verify_chain.py) shares no code with the Rust
implementation. It builds `G_M` by applying `T` to the representatives `u` and
`u + 2^M`, computes the least non-negative F3 potential by label-correcting
longest paths (bounded by `(q - p) * |V_M \ S|` in the absence of a positive
cycle), and re-checks every active edge.

```text
python3 research/lyapunov-lift/verify_chain.py   # PASS for M = 1..21, ~9.5 min, ~0.6 GB
```

For every depth the independent maximum potential equals the recorded
`chain_potential_span` (e.g. `4675` at `M = 20`, `4185` at `M = 21`), and the
active edge counts match. Controls: the empty exclusion and `{2^M - 1}` at
`M = 6` are correctly reported infeasible.

## New values

| M | `2^M` | `UB_M` | density | `UB_M / (2 UB_{M-1})` |
|---:|---:|---:|---:|---:|
| 18 | 262,144 | 3,490 | 1.331% | 0.915 |
| 19 | 524,288 | 6,426 | 1.226% | 0.921 |
| 20 | 1,048,576 | 12,627 | 1.204% | 0.983 |
| 21 | 2,097,152 | 22,691 | 1.082% | 0.899 |

At `M = 21` the best set came from the `lift+F2` base and contains **no**
vertex outside the F2 survivors (it ties the survivors-only heuristic,
22,691). Pruning the pure `lift` base gave only 24,585, so at this depth the
lifted set by itself was not the best starting point.

## Trend: the chain tracks the F2 survivors

`surv_M` below is the exact number of length-`M` F2 survivors (residues whose
prefixes satisfy `2^j < 3^(r_j)` for all `j <= M`), computed by a dynamic
program over `(j, r_j)`:

| M | `UB_M` | `surv_M` | `UB_M / surv_M` | non-F2 in chain |
|---:|---:|---:|---:|---:|
| 9 | 20 | 38 | 0.526 | 1 |
| 11 | 59 | 128 | 0.461 | 0 |
| 13 | 200 | 367 | 0.545 | 0 |
| 15 | 599 | 1,295 | 0.463 | 143 |
| 17 | 1,908 | 4,228 | 0.451 | 0 |
| 18 | 3,490 | 7,495 | 0.466 | 961 |
| 19 | 6,426 | 14,990 | 0.429 | 1,922 |
| 20 | 12,627 | 27,328 | 0.462 | 5,535 |
| 21 | 22,691 | 46,611 | 0.487 | 0 |

Least-squares fits of `log2` counts against `M` (finite-range descriptive
statistics, not estimates of a limit):

| range | `log2 UB_M` slope | `log2 surv_M` slope |
|---|---:|---:|
| `9 <= M <= 21` | 0.843 | 0.860 |
| `13 <= M <= 21` | 0.863 | 0.875 |

**Observation (finite data only).** For `9 <= M <= 21` the greedy F3 chain
removes a roughly constant fraction, about 45–55%, of the F2 survivors. The
ratio `UB_M / surv_M` shows no downward trend. The decrease of the density
`UB_M / 2^M` therefore matches the decay of the F2 survivor density, which
is classical (Terras; Everett). In this range the greedy F3 certificates give
a constant-factor gain over F2, not a visibly faster exponential rate. Two
points remain open. First, the greedy procedure may simply miss smaller sets:
the exact optimum is known only for `M <= 8`, and the dual-LP brackets only for
`M <= 12`. Second, a factor `0.97–0.98` per depth could stay hidden at these
sizes.

## Suggested next steps (not started)

- Certified lower bounds for `M >= 13` would show whether `|S_M*| / surv_M`
  really stays bounded below. The ratio is the meaningful quantity, not the
  raw density.
- `M = 22` can be resumed from the `M = 21` row with
  `--resume <progress.jsonl> --max-m 22`. A full 40-job depth is expected to
  take 30–40 h on 8 cores. The `lift+F2` named orders alone produced the
  `M = 21` result, so a reduced order set (not implemented) could make it
  feasible, at the cost of departing from the recorded method.
