# Bounded experiment summary

This file is generated. It reports a **bounded** experiment on the accelerated Collatz map `T`. Nothing below is a proof, a novelty claim, a completeness claim or a counterexample to the Collatz conjecture.

Reproduce with:

```text
cargo run --release -- experiment --out-dir research/example
```

## Parameters

| parameter | value |
|---|---|
| seed | 1 |
| cover depth | 16 |
| exhaustive limit | 100000 |
| candidate window | 16 |
| bit-length factor | 2 |
| sample size | 200 integers of 192 bits |
| sample step budget | 100000 |
| tool version | 0.1.0 |

## Status legend

- `proven-by-algebra`: follows from an explicit algebraic argument; finite checks are only a cross-check.
- `verified-for-finite-domain`: exhaustively checked on the stated finite domain and nowhere else.
- `experimentally-observed`: seen on a sample; not exhaustive.
- `conjectured`: open; recorded as a proof obligation, with no claim of truth.
- `refuted`: false as stated; counterexamples were re-checked by the independent verifier.

## Hypotheses

| id | status | domain | failure cases |
|---|---|---|---|
| `universal-window` | refuted | all positive integers | 3 |
| `bounded-window` | refuted | 2 <= n <= 100000 | 1 |
| `bit-length-bound` | refuted | 2 <= n <= 100000 | 1 |
| `prefix-residue-bijection` | proven-by-algebra | all k >= 0 | 0 |
| `descent-needs-even-majority` | refuted | first-descent prefixes of length <= 16 (all 791 of them) | 1 |
| `threshold-exceptions-trivial` | verified-for-finite-domain | first-descent prefixes of length k <= 16 | 0 |
| `threshold-exceptions-trivial-all-depths` | conjectured | first-descent prefixes of every length | 0 |
| `sampled-stopping-times` | experimentally-observed | 200 integers of exactly 192 bits drawn by SplitMix64 with seed 1 | 0 |

### `universal-window` (refuted)

**Statement.** Every sufficiently large n satisfies T^j(n) < n for some 1 <= j <= 16.

**Domain.** all positive integers

**Evidence.**

- [proven-by-algebra] every n = -1 (mod 2^16) has parity prefix 1^16, so T^j(n) = 3^j (n + 1) / 2^j - 1 > n for 1 <= j <= 16; the class is unbounded
- [verified-for-finite-domain] T^j(2^L - 1) = 3^j 2^(L - j) - 1 checked by direct iteration for all 0 <= j <= L <= 128
- [verified-for-finite-domain] the listed witnesses (least members of the class above 2^0, 2^64, 2^130) were re-checked by direct iteration

**Counterexamples (verified by direct iteration).**

- n = 65535: T^j(n) >= n for all 1 <= j <= 16
- n = 18446744073709617151: T^j(n) >= n for all 1 <= j <= 16
- n = 1361129467683753853853498429727072911359: T^j(n) >= n for all 1 <= j <= 16

### `bounded-window` (refuted)

**Statement.** Every n in the domain satisfies T^j(n) < n for some 1 <= j <= 16.

**Domain.** 2 <= n <= 100000

**Evidence.**

- exhaustive search in increasing order; 27 is the least counterexample

**Counterexamples (verified by direct iteration).**

- n = 27: T^j(n) >= n for all 1 <= j <= 16

### `bit-length-bound` (refuted)

**Statement.** Every n in the domain has stopping time at most 2 * bit_length(n).

**Domain.** 2 <= n <= 100000

**Evidence.**

- exhaustive search in increasing order; 7 is the least counterexample (no descent within 6 steps)

**Counterexamples (verified by direct iteration).**

- n = 7: T^j(n) >= n for all 1 <= j <= 6

### `prefix-residue-bijection` (proven-by-algebra)

**Statement.** For every k >= 0, parity prefixes of length k correspond bijectively to residue classes modulo 2^k, and T^k(n) = (3^r n + c) / 2^k on each class.

**Domain.** all k >= 0

**Evidence.**

- [proven-by-algebra] induction on k: for n = rho + 2^k t in a length-k cylinder, T^k(n) = T^k(rho) + 3^r t, so the next parity splits the class in two
- [verified-for-finite-domain] for every prefix of length k <= 12: residues are pairwise distinct, two independent residue constructions agree, the recursive and closed-form offsets agree, and the affine form matches direct iteration on two members

### `descent-needs-even-majority` (refuted)

**Statement.** If a parity prefix of length k with r odd steps satisfies 2^k > 3^r, then 2r <= k.

**Domain.** first-descent prefixes of length <= 16 (all 791 of them)

**Evidence.**

- shortest counterexample in the cover: k = 5, r = 3, 2^k - 3^r = 5

**Counterexamples (verified by direct iteration).**

- prefix 11010 descends although odd steps are a majority; witness n = 11

### `threshold-exceptions-trivial` (verified-for-finite-domain)

**Statement.** For a first-descent prefix (2^k > 3^r, and 2^j < 3^(r_j) for all 1 <= j < k), every class member n >= 2 satisfies T^k(n) < n; that is, the only positive member below the certificate threshold is n = 1 (prefix 10).

**Domain.** first-descent prefixes of length k <= 16

**Evidence.**

- all 791 first-descent certificates were enumerated and their exact thresholds compared with the least positive class member

### `threshold-exceptions-trivial-all-depths` (conjectured)

**Statement.** For a first-descent prefix (2^k > 3^r, and 2^j < 3^(r_j) for all 1 <= j < k), every class member n >= 2 satisfies T^k(n) < n; that is, the only positive member below the certificate threshold is n = 1 (prefix 10).

**Domain.** first-descent prefixes of every length

**Evidence.**

- only the finite check up to length 16 (entry threshold-exceptions-trivial); this is not evidence of truth for longer prefixes
- not a new conjecture: this statement is equivalent to the Coefficient Stopping Time (CST) conjecture of Terras (1976), sigma(n) = tau(n) for all n >= 2; the two-way reduction is written out in research/literature-cst.md

**Open proof obligations.**

- CST alone does not give convergence: finiteness of the coefficient stopping time for every n >= 2 is a separate open statement
- bound c / (2^k - 3^r) below the least positive class member for every first-descent prefix; this needs control of how close 2^k can be to 3^r

### `sampled-stopping-times` (experimentally-observed)

**Statement.** Sampled 192-bit integers descend below themselves within 100000 steps.

**Domain.** 200 integers of exactly 192 bits drawn by SplitMix64 with seed 1

**Evidence.**

- 200 of 200 samples descended; largest observed stopping time 69 at n = 5749849943665558361297495371776865326957657425074175724007
- for each descending sample the stopping-time prefix has 2^k > 3^r, the sample lies at or above the certificate threshold, and the affine form equals direct iteration

**Open proof obligations.**

- a sample says nothing about unsampled integers; no density or convergence claim follows

## First-descent cover to depth 16

- certified first-descent prefixes: 791 (longest has length 16)
- residue classes modulo 2^16 covered: 63422 of 65536
- **uncovered classes modulo 2^16: 2114** (each has `2^j < 3^(r_j)` for every `1 <= j <= 16`)
- certificates with positive members below threshold:
  - prefix 10: n in {1}

Every certificate was re-derived by the independent verifier (integer arithmetic and direct iteration only). Each certificate is conditional: it asserts one descent step count for one residue class above an explicit threshold.

## What this does not show

- The uncovered set is non-empty at every depth: the class `-1 (mod 2^depth)` is never certified (proven by algebra, see `universal-window`). A covered fraction close to 1 is therefore not progress toward a proof by itself.
- A descent certificate gives `T^k(n) < n` once; turning a full family of such statements into convergence needs every class covered and every exception handled, which no finite depth provides.
- Finite searches and samples cover only their stated domains.
