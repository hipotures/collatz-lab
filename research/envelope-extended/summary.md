# Extended mini-max envelope (1 <= r <= 23) and P1b refutation

Generated finite exact-arithmetic report for the accelerated map `T(n)=n/2` (even), `(3n+1)/2` (odd). No originality claim, no all-`r` theorem, and no proof of CST or Collatz is asserted. **P1a**, **P1b**, **`E_r <= 2`**, and **`E_r <= 3`** are all **refuted** by explicit independently verified witnesses.

Reproduce this table and `evidence.json` from the repository root with:

```text
cargo run --locked --release -- envelope-extended --max-r 23 --out-dir research/envelope-extended
```

## Refutation of P1b (`R_r <= R_5 = 251/507` for all `r > 5`)

Recall that for any first coefficient crossing `p` of length `k` with `r` odd steps, `d = 2^k - 3^r`, integer offset `c`, and least class member `m >= 2`, we have `T^k(m) = (3^r * m + c) / 2^k` and `rho(p) = c / (d * m)`. Equivalently:

```text
rho(p) = 1 - 2^k * (m - T^k(m)) / (d * m).
```

Whenever `m < 2^k` and `m >= 2`, `m` is the exact least member `>= 2` of its residue class modulo `2^k`, so `R_r = max rho >= rho(p)`. At `r = 34`, `k = 54`, the following independently verified witnesses exceed `R_5 = 251/507`:

| seed `m` | `r` | `k` | `T^k(m)` | drop `m - T^k(m)` | exact `rho(m)` | `rho(m) > 251/507` |
|---:|---:|---:|---:|---:|---|---|
| 47 | 34 | 54 | 46 | 1 | `44834791551842521/62849190061324505` | yes (margin `6956092611391707392`) |
| 63 | 34 | 54 | 61 | 2 | `48215861999407177/84244659018371145` | yes (margin `3300032620088281344`) |

Every witness above is verified by direct `BigUint` iteration of `T`, exact affine identity, `Cylinder::from_prefix`, modular-inverse residue, `certify`, and `verifier::verify_certificate`. Independent regression test: `tests/p1b_refutation.rs`.

## Exhaustive mini-max envelope (`1 <= r <= 23`, `k <= 37`, 150456309 classes)

Across all 150456309 first-crossing classes on `1 <= r <= 23`, `R_r <= R_5` holds everywhere (with `R_5 = 251/507` uniquely maximal on this range, and the `r > 5` peak occurring at `r = 17`, `k = 27`, `m = 251`). This illustrates sharply why exhaustive verification through `r = 23` does not establish P1b, which fails at `r = 34`.

- **P1a counterexamples (`m_r != best_m`) on `1 <= r <= 23`:** `[6, 8, 14]`
- **`E_r <= 2` status:** refuted (first counterexample: `Some(11)`)
- **`E_r <= 3` status:** refuted (first counterexample: `Some(22)`)

| r | k | count | m_r | best_m | R_r | U_r | E_r | P1a? | E_r <= 2 |
|---:|---:|---:|---:|---:|---|---|---|---|---|
| 1 | 2 | 1 | 5 | 5 | `1/5` | `1/5` | `1/1` | holds | yes |
| 2 | 4 | 1 | 3 | 3 | `5/21` | `5/21` | `1/1` | holds | yes |
| 3 | 5 | 2 | 11 | 11 | `23/55` | `23/55` | `1/1` | holds | yes |
| 4 | 7 | 3 | 7 | 7 | `73/329` | `85/329` | `85/73` | holds | yes |
| 5 | 8 | 7 | 39 | 39 | `251/507` | `319/507` | `319/251` | holds | yes |
| 6 | 10 | 12 | 287 | 347 | `989/102365` | `31/2419` | `53785/40549` | **fails** | yes |
| 7 | 12 | 30 | 231 | 231 | `2707/440979` | `3767/440979` | `3767/2707` | holds | yes |
| 8 | 13 | 85 | 191 | 207 | `9937/337617` | `1907/44503` | `2763243/1897967` | **fails** | yes |
| 9 | 15 | 173 | 127 | 127 | `4679/332359` | `44143/1661795` | `44143/23395` | holds | yes |
| 10 | 16 | 476 | 359 | 359 | `100609/2328833` | `148813/2328833` | `148813/100609` | holds | yes |
| 11 | 18 | 961 | 511 | 511 | `16337/3948497` | `479207/43433467` | `479207/179707` | holds | no |
| 12 | 20 | 2652 | 239 | 239 | `911873/123595265` | `1568693/123595265` | `1568693/911873` | holds | yes |
| 13 | 21 | 8045 | 159 | 159 | `2355187/79949811` | `5230367/79949811` | `5230367/2355187` | holds | no |
| 14 | 23 | 17637 | 639 | 1115 | `10532861/4020287485` | `16739677/2304003321` | `18664739855/6730498179` | **fails** | no |
| 15 | 24 | 51033 | 283 | 283 | `2530771/52862419` | `54413335/687211447` | `54413335/32900023` | holds | yes |
| 16 | 26 | 108950 | 991 | 991 | `89045857/23845583713` | `171628613/23845583713` | `171628613/89045857` | holds | yes |
| 17 | 27 | 312455 | 251 | 251 | `334944719/1274468815` | `2185021/5077565` | `548440271/334944719` | holds | yes |
| 18 | 29 | 663535 | 167 | 167 | `799029601/24958220641` | `1712429677/24958220641` | `1712429677/799029601` | holds | no |
| 19 | 31 | 1900470 | 111 | 111 | `1985479691/109359662091` | `5405724487/109359662091` | `5405724487/1985479691` | holds | no |
| 20 | 32 | 5936673 | 1695 | 1695 | `8365374193/1369870007025` | `3458183057/273974001405` | `17290915285/8365374193` | holds | no |
| 21 | 34 | 13472296 | 1307 | 1307 | `20674103327/8782407387167` | `54020229503/8782407387167` | `54020229503/20674103327` | holds | no |
| 22 | 35 | 39993895 | 871 | 871 | `51808559857/2594429199089` | `24378660443/370632742727` | `170650623101/51808559857` | holds | no |
| 23 | 37 | 87986917 | 927 | 927 | `55577317807/8027036619183` | `529131738487/40135183095915` | `48102885317/25262417185` | holds | yes |

## Checks and evidence boundary

- Every family count matches both independent recurrences (`count_by_length` and `count_by_odd_positions` in `src/counting.rs`).
- Every `max_c` matches Terras's independent extremal-word recurrence.
- Every reported extremizing witness (`C_r`, `m_r`, `R_r`, including ties) is re-verified in `BigUint` via modular inverse, `Cylinder::from_prefix`, `certify`, `verifier::verify_certificate`, and direct iteration of `T^k`.
- For `1 <= r <= 12`, `run_envelope_extended(12)` agrees row-for-row with the frozen Phase 2 `run_envelope()`.
- All statements are finite exact computations; no all-`r` bound, CST proof, or Collatz proof is claimed.
