# Extended envelope to `r = 33`: run record and observations

Hand-written companion to the generated [`summary.md`](summary.md) and
[`evidence.json`](evidence.json). All statements are finite exact computations
over the stated range. No all-`r` bound, CST proof or Collatz proof is claimed.

## Run record

- Command (commit `1bb769e`, 8 threads):
  `collatz-lab envelope-extended --max-r 34 --out-dir research/runs/env34`.
- `r = 1..=33` completed and were checkpointed in `progress.jsonl`. At the
  **owner's request the run was stopped during `r = 34`**. That depth has
  5,636,545,892,795 classes and was projected at about 5.5 h.
- The committed files were assembled with `--max-r 33 --resume
  <progress.jsonl>`. Resuming re-checks every recorded row:
  - the class count against both counting recurrences;
  - `d`, the Terras extremal word and `max_c` (Terras's recurrence certifies
    `max_c` independently of the scan);
  - every witness, rebuilt from its parity word by the full `checked_witness`
    pipeline (modular inverse, lifted cylinder, `certify`, verifier, direct
    iteration);
  - tie consistency and all ratios.

  The **exhaustive extremality of `min_m` and of the best ratio for `r >= 22`
  rests on the logged scan**, which is the same deterministic code that
  regenerates them from scratch. A resume from the first 15 rows reproduces the
  previously committed `r <= 23` files byte for byte.
- From scratch, `--max-r 33` regenerates the same files in about 2.7 h on
  8 cores. The output is independent of `--threads`.

Wall time per `r` (8 threads):

| r | k | classes | wall time |
|---:|---:|---:|---:|
| 26 | 42 | 1,899,474,678 | 6.9 s |
| 27 | 43 | 5,723,030,586 | 17.9 s |
| 28 | 45 | 12,809,477,536 | 45.8 s |
| 29 | 46 | 38,036,848,410 | 1.95 min |
| 30 | 48 | 84,141,805,077 | 5.0 min |
| 31 | 50 | 248,369,601,964 | 14.4 min |
| 32 | 51 | 794,919,136,728 | 40.7 min |
| 33 | 53 | 1,857,112,329,035 | 1.81 h |

Throughput was about 3.5 ns per class. The
projection made from exact class counts matched `r = 33` within 1%.

## Independent check

[`verify_envelope.py`](verify_envelope.py) shares no code with Rust. It
iterates every recorded witness directly and checks:
- the parity word;
- that the first coefficient crossing occurs exactly at `k` with `r` odd steps;
- `2^k T^k(m) = 3^r m + c`;
- that `m` is the least member `>= 2` of its class.

It also recomputes `R_r`, `U_r` and `E_r` as reduced fractions. For
`r <= --exhaustive-max-r` it enumerates every first crossing by a separate
level-by-level residue construction and recomputes `max c`, `min m`, the best
ratio and all three tie sets.

```text
python3 research/envelope-extended/verify_envelope.py --exhaustive-max-r 21   # PASS, ~112 s, ~7.9 GB
```

CI runs it with `--exhaustive-max-r 14`.

## Observations on `1 <= r <= 33` (finite, exact)

1. **`r = 34` is the least `r > 5` at which P1b fails.** `R_r <= R_5 = 251/507`
   holds for every `r <= 33`, with `R_5` uniquely maximal. The verified
   witnesses `m = 47, 63` at `r = 34` give `rho > 251/507`. The largest
   `R_r` with `r > 5` is still `R_17 ~ 0.2628` (`m = 251`), followed by
   `R_32 ~ 0.2047` (`m = 71`).
2. **P1a fails only at `r = 6, 8, 14`.** For `15 <= r <= 33` the maximal ratio
   is attained at the least class member `min_m`, and for `20 <= r <= 33`
   both the best-ratio witness and the `min_m` witness are unique.
3. **`E_r` stays below 4.** `E_r > 3` occurs at `r = 22` (`3.294`) and
   `r = 31` (`3.082`). `E_r > 2` occurs at 15 of the 28 rows `r = 6..33`.
4. `R_r` fluctuates by more than two orders of magnitude (`8.7e-4` at
   `r = 33` to `0.2047` at `r = 32`). The fluctuation tracks small `min_m`
   values (`71`, `91`, `103`, `155` at `r = 32, 28, 26, 25`), consistent
   with `R_r = c / (d m)` being dominated by the smallest class member.

## Not done

- `r = 34` (the exact `R_34`, which is `>= rho(47)`) was not completed. It can
  be resumed with `--resume <progress.jsonl> --max-r 34` (about 5.5 h).
