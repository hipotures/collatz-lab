# Phase 0 report: exact parity certificates and a no-go baseline

Scope: the accelerated map `T(n) = n/2` (n even), `(3n+1)/2` (n odd) on
positive integers. This report describes a **bounded** experiment and the
algebra behind the tool. It contains no proof of the Collatz conjecture, no
counterexample, and no claim of novelty: the parity-vector facts below are
classical, and they are restated only so the tool's outputs can be audited.

## Reproduction

Toolchain used: `rustc 1.100.0 (0ef1bc386 2026-11-09)`, `cargo 1.100.0 (3acc79c0c 2026-11-05)`. Dependency versions are pinned by `Cargo.lock`.

```text
cargo fmt --check
cargo clippy --all-targets --all-features -- -D warnings
cargo test --all-targets
cargo run --release -- experiment --out-dir research/example
cargo run --release -- verify
cargo run --release -- verify --ledger research/example/ledger.jsonl
```

The experiment uses seed 1, cover depth 16, exhaustive limit 100000, candidate
window 16, and 200 sampled 192-bit integers. Its outputs are
[`example/summary.md`](example/summary.md) and
[`example/ledger.jsonl`](example/ledger.jsonl).

## Audit: what has which status

### Proven by algebra

Each item is an elementary induction; the code cross-checks it but the status
rests on the argument, which is short enough to read in full.

1. **Affine form.** If `n` has parity prefix `p` of length `k` with `r` odd
   entries, then `T^k(n) = (3^r n + c) / 2^k`, with `c = 0` for the empty
   prefix, unchanged by an even step, and replaced by `3c + 2^k` by an odd
   step. Equivalently `c` is the sum, over odd positions `i`, of
   `3^(number of later odd positions) * 2^i`.
2. **Cylinder.** The integers with a given prefix of length `k` form exactly
   one residue class modulo `2^k`: for `n = rho + 2^k t` in the class,
   `T^k(n) = T^k(rho) + 3^r t`, so the next parity is decided by the parity
   of `t`.
3. **Descent threshold.** On such a class, `T^k(n) < n` iff
   `(2^k - 3^r) n > c`. If `2^k > 3^r` this is `n >= floor(c / (2^k - 3^r)) + 1`;
   if `2^k <= 3^r` it never holds.
4. **Mersenne identity.** `T^j(2^L - 1) = 3^j 2^(L-j) - 1` for `0 <= j <= L`,
   and more generally `T^j(n) = 3^j (n+1) / 2^j - 1 > n` for
   `n = -1 (mod 2^W)` and `1 <= j <= W`.
5. **Uncovered classes persist.** If `2^k < 3^r` then `2^(k+1) < 3^(r+1)`, so
   the odd child of an uncovered class is uncovered; the number of uncovered
   classes of the first-descent cover is positive and non-decreasing in depth.

### Verified for a finite domain only

- Every `2 <= n <= 100000` descends below itself (largest stopping time 135,
  at `n = 35655`), hence every `n <= 100000` reaches 1. This is far inside
  the range already verified elsewhere and is only an oracle for the code.
- The Mersenne identity by direct iteration for all `0 <= j <= L <= 128`.
- Prefix/residue bijection, agreement of two independent residue
  constructions and of recursive and closed-form offsets, for all prefixes of
  length at most 12 (tests: affine form against direct iteration on every
  prefix up to length 8, thresholds on every prefix up to length 10).
- All 791 first-descent certificates of length at most 16 pass the
  independent verifier, and the only positive class member below any of their
  thresholds is `n = 1` (prefix `10`, the cycle `1 -> 2 -> 1`). The same
  holds for the 81119 certificates up to length 24
  (`collatz-lab certificates --depth 24`).

### Experimentally observed

- 200 seeded 192-bit integers all descended within the step budget; the
  largest stopping time seen was 69. For each, the stopping-time prefix has a
  certificate, the sample lies above its threshold, and the affine form agrees
  with direct iteration. A sample of 200 supports no general statement.

### Conjectured (open)

- For first-descent prefixes of **every** length, no class member `n >= 2`
  lies below the certificate threshold. This is not a new conjecture: it is
  equivalent to the **Coefficient Stopping Time (CST) conjecture** of Terras
  (1976), also conjectured by Garner (1981) and named by Lagarias (1985):
  `sigma(n) = tau(n)` for all `n >= 2`. The two-way reduction, the sources
  and their provenance are in [`literature-cst.md`](literature-cst.md). The
  finite checks above are implied already by Terras's p. 252 argument for
  `tau<=2592`, reproduced in `tests/primary_sources.rs`, and are a consistency
  test of the tool only. Rozier–Terracol arXiv v5, Corollary 5.4, gives a
  separate seed bound `n<=2.8*10^19`; neither is the full conjecture.

### Refuted candidates

| candidate | least counterexample found |
|---|---|
| every large `n` descends within 16 steps | every `n = -1 (mod 2^16)`; witnesses 65535, and the least such `n` above `2^64` and above `2^130` |
| every `2 <= n <= 100000` descends within 16 steps | `n = 27` |
| stopping time at most `2 * bit_length(n)` on that range | `n = 7` (stopping time 7, 3 bits) |
| a prefix with `2^k > 3^r` has `2r <= k` | prefix `11010` (`k = 5`, `r = 3`), witness `n = 11` |

All counterexamples are stored in the ledger and re-verified by
`verify --ledger`.

## First-descent cover: the numbers

| depth `K` | certified prefixes | uncovered classes mod `2^K` | uncovered fraction |
|---|---|---|---|
| 4 | 3 | 3 | 3 / 16 |
| 8 | 15 | 19 | 19 / 256 |
| 12 | 57 | 226 | 226 / 4096 |
| 16 | 791 | 2114 | 2114 / 65536 |
| 20 | 4404 | 27328 | 27328 / 1048576 |
| 24 | 81119 | 286581 | 286581 / 16777216 |

These are exact counts for the listed depths and nothing more. They agree
with two independent recurrences (`collatz-lab counts`) and with OEIS A076227
(uncovered classes) and A100982 (first crossings by number of odd steps); see
[`literature-cst.md`](literature-cst.md), section 8.

## Limitations of naive finite-window certification

1. **No fixed window exists.** By item 4, for every window `W` the class
   `-1 (mod 2^W)` contains arbitrarily large integers that stay above their
   starting value for `W` steps. Any proof of the form "check all classes
   modulo `2^W` and each one descends within `W` steps" is impossible, for
   every `W`.
2. **The uncovered fraction shrinks while the uncovered count grows.** In
   the table the fraction falls from 3/16 to about 1.7 percent, but the number
   of classes left grows roughly tenfold every four levels. Deepening the tree
   converts one unsolved class into more unsolved classes; it never empties
   the set (item 5). A fraction near 1 is a density statement, not a
   statement about every integer.
3. **A certificate is one descent, above a threshold.** Even a complete
   family of certificates would need every below-threshold member handled.
   Here the thresholds are trivial as far as checked, but that is exactly the
   open conjecture above, not a theorem.
4. **Scope of the no-go.** The obstruction concerns fixed descent windows. It
   does not address adaptive horizons, potential functions, or other
   certificate shapes, and should not be cited as if it did.

## Follow-up after the primary-source audit

The earlier three exploratory questions have been re-evaluated in
[`phase1-next-questions.md`](phase1-next-questions.md). Terras's mini-max
bound and Garner's power-gap estimates already address threshold envelopes;
the finite recurrences and structural results in the literature audit cover
much of the proposed counting work. The adaptive-round rate was not proved,
and a finite density trend cannot resolve the all-integers question.

P1a (the claim that the smallest representative maximizes the normalized
threshold ratio) is **refuted** at `r=6`: the cylinders of 287 and 347 give
`697/84665 < 989/102365`. All twelve words are checked independently in
`tests/p1a_refutation.rs`. This follow-up is recorded in that test and the
research plan, not in the historical Phase 0 ledger above. P1b is not settled.
The revised plan proposes just one bounded envelope-tightness comparison.

## Handoff

Later work on adaptive or unbounded-horizon certificates and on
machine-proposed hypotheses should plug into `hypothesis.rs` and must keep
the rule that every recorded claim passes the independent verifier and keeps
its status label.
