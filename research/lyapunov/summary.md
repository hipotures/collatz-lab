# Finite-state modular Lyapunov contraction certificates (F3, 1 <= M <= 15)

Generated exact-arithmetic report for the accelerated map `T(n)=n/2` (even), `(3n+1)/2` (odd) on the finite-state transition graph `G_M` modulo `2^M`. No proof of the Collatz conjecture or CST is claimed.

Reproduce this table and `evidence.json` from the repository root with:

```text
cargo run --locked --release -- lyapunov --max-m 15 --out-dir research/lyapunov
```

## Exact definitions and finite-state no-go results

- **Transition graph `G_M`:** vertices `V_M = {0, ..., 2^M - 1}`, two outgoing edges per vertex corresponding to the next bit `t mod 2` of `n = u + 2^M t`.
- **Exact contraction target:** `p/q = 63/100` (verified `3^63 < 2^100`, so `p/q < 1/log2(3)`).
- **F3 certificate on `V_M \ S`:** an integer potential `phi: V_M \ S -> Z` satisfying `q * odd(u) + phi(v) - phi(u) <= p` on every active edge `(u -> v)`. Telescoping along any length-`L` orbit segment staying inside `V_M \ S` yields `q * r_L + phi(u_L) - phi(u_0) <= p * L`, guaranteeing a strict coefficient crossing `3^(r_L) < 2^L` once `L >= L_0` (where `2^(q*L_0) > 3^(p*L_0 + span)`).
- **Finite-state no-go on `G_M` and `G_M \ {2^M - 1}`:**
1. On full `G_M`, the self-loop `(2^M - 1) -> (2^M - 1)` has odd-step density `1/1`.
2. On `G_M \ {2^M - 1}`, the exact maximum odd-step cycle density is `(M - 1)/M` (upper bound certified by an integer potential at `(M - 1, M)`; lower bound witnessed by an explicit length-`M` cycle from `2^(M-1) - 1` through `2^M - 2`). Thus for every `M >= 3`, deleting only the Mersenne class `2^M - 1` still leaves an expanding cycle (`3^(M-1) > 2^M`), so no modular Lyapunov contraction exists on `G_M \ {2^M - 1}`.

## F2 survivors vs. F3 pruned Lyapunov certificates

Every F2 cover complement `V_M \ Survivors_M` admits an exact integer F3 potential at `63/100`. Pruning redundant F2 survivors while preserving exact edge-by-edge contraction strictly reduces the excluded residue set for `M = 4` and all `M >= 6`.

| M | `2^M` | max cycle `G_M\{-1}` | F2 excluded (%) | F3 asc | F3 low-wt | F3 best (%) | saved vs F2 | F3 span | F3 horizon `L_0` |
|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| 1 | 2 | `0/1` | 1 (50.00%) | 1 | 1 | 1 (50.00%) | 0 | 0 | 1 |
| 2 | 4 | `1/2` | 1 (25.00%) | 1 | 1 | 1 (25.00%) | 0 | 37 | 398 |
| 3 | 8 | `2/3` | 2 (25.00%) | 2 | 2 | 2 (25.00%) | 0 | 37 | 398 |
| 4 | 16 | `3/4` | 3 (18.75%) | 2 | 2 | 2 (12.50%) | 1 | 111 | 1194 |
| 5 | 32 | `4/5` | 4 (12.50%) | 4 | 4 | 4 (12.50%) | 0 | 111 | 1194 |
| 6 | 64 | `5/6` | 8 (12.50%) | 5 | 5 | 5 (7.81%) | 3 | 122 | 1313 |
| 7 | 128 | `6/7` | 13 (10.16%) | 9 | 9 | 9 (7.03%) | 4 | 159 | 1711 |
| 8 | 256 | `7/8` | 19 (7.42%) | 14 | 14 | 14 (5.47%) | 5 | 185 | 1990 |
| 9 | 512 | `8/9` | 38 (7.42%) | 20 | 20 | 20 (3.91%) | 18 | 270 | 2904 |
| 10 | 1024 | `9/10` | 64 (6.25%) | 38 | 38 | 38 (3.71%) | 26 | 233 | 2507 |
| 11 | 2048 | `10/11` | 128 (6.25%) | 60 | 59 | 59 (2.88%) | 69 | 281 | 3023 |
| 12 | 4096 | `11/12` | 226 (5.52%) | 122 | 114 | 114 (2.78%) | 112 | 307 | 3302 |
| 13 | 8192 | `12/13` | 367 (4.48%) | 205 | 200 | 200 (2.44%) | 167 | 540 | 5808 |
| 14 | 16384 | `13/14` | 734 (4.48%) | 327 | 314 | 314 (1.92%) | 420 | 636 | 6841 |
| 15 | 32768 | `14/15` | 1295 (3.95%) | 662 | 696 | 662 (2.02%) | 633 | 1220 | 13122 |

## Lifting bound

Reduction modulo `2^M` is an odd-label-preserving graph homomorphism `G_{M+1} -> G_M`, so an F3 certificate on `V_M \ S` lifts to one on `V_{M+1} \ lift(S)` with `|lift(S)| = 2|S|` (written argument, checked per depth in `research/lyapunov-lift`). The F3 column above is a survivors-only greedy upper bound that does not use this; it exceeds the lifted bound `2 * F3(M - 1)` at: `M = 15` (`662 > 2 * 314 = 628`). Such density increases are artifacts of the heuristic, not of `|S_M*| / 2^M`, which is non-increasing in `M`.

## Evidence boundary and limitations

- Every F2 survivor count is cross-checked against `count_by_length` in `src/counting.rs`.
- Every F3 certificate is verified edge-by-edge in exact `i64` arithmetic with no floating-point decisions.
- **What F3 does not claim:** staying inside `V_M \ S` is a conditional hypothesis on an orbit segment; F3 does not prevent an integer orbit from entering the excluded residue set `S`, and does not prove global convergence.
