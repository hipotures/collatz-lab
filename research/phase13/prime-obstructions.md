# Phase 13 follow-up: power-residue obstructions and the post-identity abelian trap

Exact algebraic analysis and bounded verification explaining the strong `p mod 12`
asymmetry and period structure observed in [`tail-gcd-primes.md`](tail-gcd-primes.md)
for `frontierSix` (`1 -> 100111, 0 -> 111110`).

Reproduce both artifacts byte-for-byte with:

```bash
python3 research/phase13/analyze_prime_obstructions.py --check
```

## Theorem 1 (2-primary and 3-primary power-residue obstructions)

The slope of the periodic-tail inverse map `f_1^(k)` is
`a_1^(k) = 2^(6^k) / 3^(r_k)` where `r_k = (5 * 6^k + 2 * (-1)^k) / 7`.
For every `k >= 2`, `7 * r_k = 2*(-1)^k (mod 4)` forces `v_2(r_k) = 1` (so `r_k = 2 (mod 4)`),
and for every `k >= 1`, `7 * r_k = 2*(-1)^k (mod 3)` forces `v_3(r_k) = 0`.
Let `p >= 5` be prime, `s = v_2(p - 1) >= 1`, and `u = v_3(p - 1) >= 0`.

1. **2-primary obstruction:** for every `k >= max(2, s)`, `2^s | 6^k` kills the 2-part
   of `2^(6^k)` in `F_p^*`, while `v_2(r_k) = 1`. Thus `a_1^(k) == 1 (mod p)` requires
   `3^((p-1)/2^(s-1)) == 1 (mod p)` (`3` is a `2^(s-1)`-th power residue mod `p`).
2. **3-primary obstruction:** for every `k >= max(1, u)`, `3^u | 6^k` kills the 3-part
   of `2^(6^k)` in `F_p^*`, while `v_3(r_k) = 0`. Thus `a_1^(k) == 1 (mod p)` requires
   `3^((p-1)/3^u) == 1 (mod p)` (`3` is a `3^u`-th power residue mod `p`).
3. **Exact Corollary (`p == 5 (mod 12)` completely excluded):** every prime `p == 5 (mod 12)`
   has `s >= 2` and `(3/p) = -1`, so `p` never divides `3^(r_k) - 2^(6^k)` for any `k >= 2`;
   at `k = 1`, `3^4 - 2^6 = 17` and `gcd(|P_1|, Q_1) = 1`. Hence **no prime `p == 5 (mod 12)`
   ever divides `gcd(|P_k|, Q_k)` at any level `k >= 1`**.
4. **Refutation of the naive `p == 1 (mod 4)` impossibility guess:** `p = 10597 == 1 (mod 12)`
   (`s = 2`, `u = 1`, both power-residue conditions hold)
   satisfies `f_1^(677) == id (mod 10597)`, so `10597 | gcd(|P_677|, Q_677)`.

## Theorem 2 (Post-identity abelian trap)

Whenever `f_1^(b) == id (mod p)` at any level `b >= 1`, then `f_0^(b+1) = f_0^(b)` and
`f_1^(b+1) = (f_0^(b))^2`, so for every `j >= 0` the pair `(f_0^(b+j), f_1^(b+j))` is
trapped forever in the cyclic abelian subgroup `<f_0^(b)> <= Aff(F_p)`:

```text
f_0^(b+j) = (f_0^(b))^(u_j),   f_1^(b+j) = (f_0^(b))^(v_j),
u_j = (2 * 6^j + 5 * (-1)^j) / 7,   v_j = 2 * (6^j - (-1)^j) / 7.
```

Therefore `p | gcd(|P_{b+j}|, Q_{b+j})` **if and only if** `ord_p(a_0^(b)) | v_j`.
In particular, any single hit at `b >= 1` automatically generates infinitely many divisible
levels, and explains both why `full_period == slope_period` and why `p = 619` hits every
`51` levels (half of its `102`-step state period).

## Bounded verification by residue class `p mod 12` (`5 <= p <= 5,000`, `k <= 2,000`)

| `p mod 12` | total primes | eligible (Thm 1) | slope `a_1 = 1` hits | full `f_1 = id` hits | asymptotic eligibility |
|---:|---:|---:|---:|---:|---|
| 1 | 159 | 24 | 9 | 0 | ~8.3% (1/12) |
| 5 | 170 | 0 | 1 | 0 | **0%** (exact) |
| 7 | 171 | 43 | 19 | 2 | ~25% (1/4) |
| 11 | 167 | 167 | 66 | 19 | **100%** (exact) |

## Verified abelian-trap parameters (21 primes `<= 5,000` plus `p = 10597`)

| prime `p` | `p mod 12` | `s = v_2(p-1)` | `u = v_3(p-1)` | first hit `b` | `ord_p(a_0^(b))` | first return gap `j` |
|---:|---:|---:|---:|---:|---:|---:|
| 47 | 11 | 1 | 0 | 27 | 23 | 22 |
| 227 | 11 | 1 | 0 | 160 | 113 | 112 |
| 347 | 11 | 1 | 0 | 7 | 173 | 86 |
| 619 | 7 | 1 | 1 | 49 | 206 | 51 |
| 1163 | 11 | 1 | 0 | 507 | 581 | 287 |
| 1187 | 11 | 1 | 0 | 294 | 593 | 592 |
| 1283 | 11 | 1 | 0 | 1064 | 641 | 640 |
| 1367 | 11 | 1 | 0 | 659 | 683 | 341 |
| 1439 | 11 | 1 | 0 | 710 | 719 | 718 |
| 1667 | 11 | 1 | 0 | 758 | 833 | 784 |
| 1823 | 11 | 1 | 0 | 768 | 911 | 910 |
| 1907 | 11 | 1 | 0 | 1223 | 953 | 952 |
| 2063 | 11 | 1 | 0 | 1509 | 1031 | 1030 |
| 2819 | 11 | 1 | 0 | 1692 | 1409 | 1408 |
| 2963 | 11 | 1 | 0 | 944 | 1481 | 1480 |
| 3203 | 11 | 1 | 0 | 727 | 1601 | 1600 |
| 3467 | 11 | 1 | 0 | 1190 | 1733 | 866 |
| 3623 | 11 | 1 | 0 | 1382 | 1811 | 905 |
| 3739 | 7 | 1 | 1 | 542 | 1246 | 616 |
| 3779 | 11 | 1 | 0 | 1912 | 1889 | 1888 |
| 4547 | 11 | 1 | 0 | 1828 | 2273 | 2272 |
| 10597 | 1 | 2 | 1 | 677 | 1766 | 882 |

## Evidence boundary

- Theorems 1 and 2 are **Lean 4 kernel-verified** in `CollatzLab/PrimeObstructions.lean`
  (43 audited declarations via `research/lean-audit/PrimeObstructionsAudit.lean` and
  `research/phase13/PrimeObstructionsSignatures.lean`, using only standard Lean foundations).
- All 22 resonant primes above (and all 667 primes `<= 5,000`, plus all 568 primes
  `p == 5 (mod 12) <= 20,000`) are verified by exact modular arithmetic.
- These results explain the observed `p mod 12` and period structure, but do not
  prove `log2(gcd_k) = o(6^k)` or `B = c`.
