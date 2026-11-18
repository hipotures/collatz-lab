# Phase 13 follow-up: bounded resonant-prime scan for tail-GCD `gcd(|P_k|, Q_k)`

Generated exact-arithmetic report for `frontierSix` (`1 -> 100111, 0 -> 111110`).
By `CollatzLab/ShadowCancellation.lean` (`shadow_gcd_eq_tail_gcd`) and
[`phase13-theory.md`](../phase13-theory.md), for every `k >= 1` and prime `p >= 5`:

```text
p | gcd(|P_k|, Q_k)   iff   f_1^(k) == (1, 0) (mod p).
```

Reproduce both artifacts byte-for-byte with:

```bash
python3 research/phase13/scan_tail_gcd_primes.py --check
```

## Summary of bounded scans

- **Scan 1 (`5 <= p <= 100,000`, `9,590` primes, `1 <= k <= 200`):**
  - Resonant primes found: **4** (hitting **13** distinct levels).
  - Cross-check with exact `k = 1..8` raw GCDs `[1, 1, 1, 1, 1, 1, 347, 1]`: **PASS** (`p = 347` is the unique prime `<= 100,000` at `k = 7`, and zero primes `<= 100,000` divide `k in {1..6, 8}`).
  - Largest single-level prime product: `k = 49`, primes `[47, 619]`, product `29093` (15 bits).
- **Scan 2 (`5 <= p <= 10,000`, `1,227` primes, `1 <= k <= 1000`):**
  - Resonant primes found: **13** (hitting **93** distinct levels).
  - Certified infinite modular cycles (within 50,000 steps): **13**.
  - Largest single-level prime product: `k = 944`, primes `[227, 2963]`, product `672601` (20 bits).

## Certified infinite modular cycles (`p | gcd(|P_k|, Q_k)` at `k = b + t*j`)

| prime `p` | cycle start `a` | period `t` | first identity `b` |
|---:|---:|---:|---:|
| 47 | 15 | 22 | 27 |
| 227 | 60 | 112 | 160 |
| 347 | 1 | 86 | 7 |
| 619 | 41 | 102 | 49 |
| 1163 | 450 | 574 | 507 |
| 1187 | 146 | 592 | 294 |
| 1367 | 423 | 682 | 659 |
| 1439 | 372 | 718 | 710 |
| 1667 | 590 | 784 | 758 |
| 1823 | 752 | 910 | 768 |
| 2963 | 585 | 1480 | 944 |
| 3203 | 86 | 1600 | 727 |
| 3739 | 20 | 616 | 542 |

## Resonant primes in Scan 1 (`5 <= p <= 100,000`, `1 <= k <= 200`)

| prime `p` | divisible levels `k <= 200` |
|---:|---|
| 47 | `[27, 49, 71, 93, 115, 137, 159, 181]` |
| 227 | `[160]` |
| 347 | `[7, 93, 179]` |
| 619 | `[49, 100, 151]` |

## Multi-prime collisions (`k <= 200`, `p <= 100,000`)

| level `k` | dividing primes `<= 100,000` | product |
|---:|---|---:|
| 49 | `[47, 619]` | 29093 |
| 93 | `[47, 347]` | 16309 |

## Evidence boundary

- Every reported resonant prime and cycle is verified independently by exact modular
  affine-map composition modulo `p`, with zero floating-point decisions.
- These bounded prime scans show that small-prime resonance (`p <= 100,000`) is
  extremely sparse relative to the `6^k`-bit scale of `Q_k`, but they do **not**
  rule out large prime factors `p > 100,000` and do **not** prove `log2(gcd_k) = o(6^k)` or `B = c`.
