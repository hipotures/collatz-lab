# collatz-lab

A small, reproducible, exact-arithmetic workbench for studying **parity
itineraries** and **conditional descent certificates** of the accelerated
Collatz map

```text
T(n) = n / 2          if n is even
T(n) = (3n + 1) / 2   if n is odd
```

The aim is mathematical discovery toward a proof, not brute-force search.
**This project does not prove the Collatz conjecture and makes no novelty,
completeness or counterexample claim.** Every output is labelled with what
kind of statement it is.

## What is here

| module | purpose |
|---|---|
| `collatz` | the map, direct orbit evaluation, stopping times, a small-range oracle, a checked `u64` fast path |
| `prefix` | parity prefixes, the affine form `T^k(n) = (3^r n + c) / 2^k`, and the residue class modulo `2^k` of each prefix |
| `certificate` | exact conditional descent certificates and the first-descent cover of the integers to a given depth |
| `counting` | two independent exact recurrences for the number of first coefficient crossings and of surviving classes |
| `envelope` | exhaustive comparison of Terras's mini-max envelope with exact class ratios for `1 <= r <= 12` |
| `mahler` | 2-adic Mahler reduction, five-way modular checkpoints, periodic control `(1110)^infinity`, and exact Padé table (`1 <= m <= 16`) for `mu(1)=1110, mu(0)=1101` |
| `nogo` | the Mersenne family `2^L - 1`, which rules out every fixed universal descent window |
| `verifier` | an independent checker that trusts only direct iteration and elementary integer identities |
| `hypothesis` | a bounded generate-and-falsify workflow writing a JSONL research ledger |
| `report` | the human-readable summary of an experiment |

The library (`src/lib.rs`) holds all mathematics; the CLI (`src/main.rs`) is a
thin front end. Rust only, stable toolchain, `Cargo.lock` committed.

## Quick start

```text
cargo test --all-targets
cargo run --release -- experiment --out-dir research/example
```

The second command is the documented reference experiment. It finishes in
well under a second and rewrites `research/example/ledger.jsonl`
(machine-readable evidence) and `research/example/summary.md` (readable
summary) byte for byte. See [`research/phase0-report.md`](research/phase0-report.md)
for the discussion.

## Commands

```text
collatz-lab verify        [--limit N] [--depth K] [--mersenne-max L] [--ledger FILE]
collatz-lab prefixes      --length K | --parity BITS | --n N --length K
collatz-lab certificates  [--depth K] [--parity BITS] [--out FILE.jsonl]
collatz-lab experiment    [--seed S] [--depth K] [--limit N] [--window W] ... [--out-dir DIR]
collatz-lab counts        [--max-depth K] [--walker-depth K]
collatz-lab envelope      [--out-dir DIR]
collatz-lab mahler        [--out-dir DIR]
```

- `verify` runs the deterministic self-checks (range oracle, fast path against
  `BigUint`, Mersenne identity, certificates through the independent
  verifier). `verify --ledger FILE` re-checks every counterexample recorded in
  a ledger by direct iteration.
- `prefixes` prints, for each parity prefix, its residue class and affine
  form. `--n` accepts integers of any size.
- `certificates` walks the first-descent tree and reports certificates **and
  the classes that remain uncovered**. `--out` streams one JSON object per
  leaf, so an interrupted run leaves a valid partial file.
- `experiment` runs the bounded hypothesis workflow.
- `counts` tabulates first coefficient crossings and survivors by two
  recurrences that do not use the cover walker, and compares all three.
- `envelope` measures the slack from separately maximizing the offset and
  minimizing the class representative. Its bounds are fixed at `1 <= r <= 12`
  and `k <= 20`; it has no `--allow-large` override.
- `mahler` verifies the fixed point `w = lim mu^j(1)` of `mu(1)=1110, mu(0)=1101`,
  checks all-prefix survival up to `k=1024`, runs five-way 2-adic residue
  checks at `K in {16, 32, 64, 128, 256, 512, 1024}` against the Mahler
  reduction `x(w) = -23/11 + (4/27)*F_2(16/27)`, evaluates the periodic
  control `(1110)^infinity` (`x = -19/11`), and computes the bounded exact
  Padé table for `1 <= m <= 16`.

Defaults run promptly on a laptop. Bounds beyond the defaults (for example
`--depth` above 24) are refused unless `--allow-large` is passed; long
enumerations log progress to stderr. Parity strings read left to right:
`1` is an odd step, `0` an even step.

Examples:

```text
$ collatz-lab prefixes --parity 11010
11010    n = 11 (mod 2^5)  T^5(n) = (3^3 n + 23) / 2^5  [T^5(n) < n iff n >= 5]

$ collatz-lab certificates --parity 10
certificate: for all n >= 2 with n = 1 (mod 2^2): T^2(n) = (3^1 n + 1) / 2^2 < n
positive class members below the threshold: 1 {1}
```

## Mini-max envelope experiment (issue #5)

Reproduce the [exact table](research/envelope/summary.md) and
[machine-readable evidence](research/envelope/evidence.json) with:

```text
cargo run --locked --release -- envelope --out-dir research/envelope
```

This exhausts all 4,403 first-crossing words with `1 <= r <= 12`, cross-checks
each family size against both counting recurrences, and independently computes
Terras's maximal offset. All classes are checked through modular inversion,
residue lifting, closed-form affine identities and direct iteration. All extrema
and ties are retained; fractions and rankings use arbitrary-precision integers.
The residue-1 class `10` uses its least member at least 2, namely 5.

The finite prediction `E_r <= 2` is **refuted**: its first counterexample is
`r=11`, `k=18`, where `E_r=479207/179707 > 2`. The other eleven tested values
satisfy the inequality. This is a bounded comparison only: P1a remains refuted,
P1b remains open, and no CST, Collatz, originality or all-`r` claim follows.
If `R_r=0`, the envelope factor and its comparison with 2 are explicitly N/A
(`null` in JSON).

The release command took 19 ms after compilation in the implementation
environment (Rust 1.100.0); timing is machine-dependent. It retains at most
one family of 2,652 classes plus the summaries, stops after `r=12` or immediately
on an invariant failure, and finishes all mathematical checks before replacing
outputs. Timing goes to stderr, so artifacts reproduce byte for byte. The new
evidence format is separate from the reference experiment's unchanged JSONL
ledger. `tests/envelope.rs` independently scans a full residue period to recheck
all extrema, ties and exact fractions, and checks CLI artifact reproduction.

## Phase 3: aperiodic survivor itineraries and 2-adic Mahler reduction (issues #6, #7)

Reproduce the [Phase 3 summary](research/mahler/summary.md) and
[machine-readable evidence](research/mahler/evidence.json) with:

```text
cargo run --locked --release -- mahler --out-dir research/mahler
```

See [`research/infinite-itineraries.md`](research/infinite-itineraries.md) for
the full mathematical derivations and literature audit:

- **Algebraic proofs (`proven-by-algebra`)**: all prefixes of `w = lim mu^j(1)`
  (`mu(1)=1110, mu(0)=1101`) satisfy `3^(r_k) > 2^k` for all `k >= 1`; `w` is not
  eventually periodic (ruling out rational cycles by Lagarias 1990, Corollary
  2.1b, whereas ruling out general rational seeds from aperiodicity alone is the
  open Periodicity Conjecture; see also the primary-source audit of López &
  Stoll 2021); and its unique 2-adic seed satisfies
  `x(w) = -23/11 + (4/27)*F_2(16/27)` in `Z_2` where
  `F(z) = (1 + z + z^3)/(1 - z^4) + (z^2 - z^3) F(z^4)`.
- **Five-way checkpoints and periodic control (`verified-for-finite-domain`)**:
  at `K in {16, 32, 64, 128, 256, 512, 1024}`, the residue `x_K mod 2^K` is
  checked across affine inversion, Hensel cylinder lifting, parity-position
  inverse sums, the Mahler reduction, and direct iteration of `T`. The periodic
  control `(1110)^infinity` (`x = -19/11`) illustrates how every finite prefix
  has positive integer realizations `n_K >= 2` with `T^K(n_K) > n_K` even when
  no positive integer realizes the infinite word.
- **Repaired seed normalization, denominator obstruction, degree-4 Padé
  contradiction, and shifted-itinerary exclusion**: because
  `(11*x(w) + 23)/4 = (11/27)*F_2(16/27)`, the unnormalized
  `u_0^old = (11*x + 23)/4` fails at `L = 1 (mod 16)` (`1 != 11 mod 16`); the
  repaired normalization `D_0 = 11*q`, `u_0 = 27*(11*p + 23*q)/4` restores
  `b_0^(L-1)*u_0 = D_0*preS(a_0, b_0, L) (mod a_0^L)` for all `L >= 1`.
  Moreover, because `B(z) = z^2(1 - z)` vanishes to order 2 at `z = 0`, the
  uncancelled polynomial denominator recurrence makes `D_1` even (`v_2(D_1) = 8`,
  `refuted` for uncancelled `Odd D_k`), whereas cancelling `a_k^2` via the
  `L = 2` congruence restores an odd denominator
  `D_{k+1} = D_k(b_k - a_k)(b_k^4 - a_k^4)`. For the degree-4 Padé pair
  `p_0 = 1 + z + z^2`, `p_1 = -1 + z^4` (`N = 14`, `c = 1`), the integer linear
  form `E_k = D_k*P_0(a_k, b_k) + u_k*P_1(a_k, b_k)` satisfies `E_k != 0`,
  `v_2(E_k) = 56 * 4^k`, and `|E_k| < 3*(|u_0| + D_0)*3^(19 * 4^k)` (`2^56 >
  2^25 * 3^19`). By the inverse parity-branch maps `T_0^(-1)(z) = 2z` and
  `T_1^(-1)(z) = (2z - 1)/3` on `Z_2 intersect Q` (`Corollary 7.3`), this also
  rules out rational seeds for every shifted tail `sigma^t(w)` (`t >= 0`),
  without implying anything about general infinite survivor words.

## Phase 4: Lean 4 kernel formalization (issue #8)

The integer-arithmetic core of the irrationality proof in
[`research/infinite-itineraries.md`](research/infinite-itineraries.md)
(Theorems 6.2, 7.1 and Corollary 7.3) is formalized and verified by the Lean 4 kernel
(`leanprover/lean4:v4.18.0`, core `Init` library only, zero `sorry`, `admit`,
custom `axiom`, `unsafe`, or `native_decide`) in [`CollatzLab/`](CollatzLab):

```text
lake build
```

See [`research/lean-formalization.md`](research/lean-formalization.md) for the
complete paper-to-Lean theorem mapping (`CollatzLab.all_prefixes_survive`,
`CollatzLab.w_not_eventually_periodic`, `CollatzLab.uncancelled_d1_divisible_by_256`,
`CollatzLab.tower_congruence_all`, `CollatzLab.theorem_7_1_part1`,
`CollatzLab.eForm_upper_bound`, `CollatzLab.no_rational_seed_realizes_w`,
`CollatzLab.no_rational_seed_realizes_shifted_w`,
`CollatzLab.no_eventually_shifted_w_itinerary`) and the `#print axioms` audit.
The generating-function and 2-adic statements are represented by the finite
integer identities needed for the contradiction, not formalized as standalone
power-series or 2-adic analytic theorems.
The Phase 4 formalization covers the explicit 4-automatic word `w` and its shifts
`w^(t)` only; it does not prove the Collatz conjecture, CST, or the general
open Periodicity Conjecture.

## Phase 6: uniform family theorem in Lean 4 (issue #12)

The integer-arithmetic proof now covers **every `L >= 4`** for
`mu_L(1) = 1^(L-1)0`, `mu_L(0) = 1^(L-2)01`. The publicly exported theorem is

```lean
theorem CollatzLab.no_rational_seed_realizes_family
  (L : Nat) (hL : 4 <= L) (p q : Int) :
  ¬ CollatzLab.RealizesWord p q (CollatzLab.familyWord L)
```

`lake build` checks the uniform finite Mahler identities, exact cancelled
tower, nonvanishing and exact divisibility of the linear form, and height
contradiction. The shifted-tail and eventual-itinerary exclusions are
`no_rational_seed_realizes_shifted_family` and
`no_eventually_shifted_family_itinerary`. `familyWord_four` proves equality
with the original `w`; a concrete `L=5` positive prefix witness checks the
parity semantics. CI audits 44 declarations using only standard Lean
foundation axioms.

See [`research/lean-family-formalization.md`](research/lean-family-formalization.md)
for full signatures, dependencies, semantic checks, validation, and scope.
The independent [Phase 7 semantic audit](research/lean-family-semantic-audit.md)
adds literal substitution and signed rational checks, bringing the CI audit to
52 declarations. The arbitrary-morphism criterion and the family's general symbolic survival
and aperiodicity arguments remain written proofs. This result does not
prove Collatz, CST, or the general Periodicity Conjecture.

## Epistemic statuses

Every ledger entry and report line carries exactly one of:

| status | meaning |
|---|---|
| `proven-by-algebra` | follows from an explicit algebraic argument given in the source or report; finite checks only cross-check it |
| `verified-for-finite-domain` | exhaustively checked on the stated finite domain, and nowhere else |
| `experimentally-observed` | seen on a seeded sample; not exhaustive |
| `conjectured` | open; recorded together with its proof obligations, with no claim of truth |
| `refuted` | false as stated; the counterexamples are stored and re-verifiable |

Statuses are never promoted: a finite check never becomes a general claim.

## Paradoxical prefixes are not first-crossing counterexamples

Two different things can look like "the coefficient is below 1 but the orbit
did not descend":

- A **paradoxical prefix**: some parity prefix of `n` has `2^k > 3^r` and yet
  `T^k(n) >= n`. These exist and are classical. For `n = 7` the orbit is
  `7, 11, 17, 26, 13, 20, 10, 5, 8`; the prefix `11101001` has
  `3^5 / 2^8 = 243/256 < 1` while `T^8(7) = 8 >= 7`. As a single-cylinder
  certificate this is simply a below-threshold member (`7 < N0`), and it is
  listed as such.
- A **first-crossing exception**: the prefix is the *first* length at which
  the coefficient drops below 1 (`2^j < 3^(r_j)` for all `1 <= j < k`, and
  `2^k > 3^r`) and still `T^k(n) >= n` for some `n >= 2`. None is known;
  one would be a counterexample to the Coefficient Stopping Time conjecture
  (see [`research/literature-cst.md`](research/literature-cst.md)).

The `n = 7` example is only the first kind: its coefficient first crosses at
step 7, where `T^7(7) = 5 < 7`. The ledger kind `threshold-exception` means
the second kind exclusively, and `verifier::verify_failure_case` re-derives
the whole first-crossing premise from the parity string before accepting
one, so `verify --ledger` rejects the `n = 7` case. Likewise
`verify_certificate` requires the exception list to be exactly the first
`min(exception_count, 16)` below-threshold members. Nothing here proves or
refutes that conjecture.

## Exactness rules

- Validity checks use `num-bigint` integers only. There is no floating point
  in the crate.
- The single primitive fast path (`collatz::stopping_time_fast`) uses checked
  `u64` arithmetic and continues in `BigUint` at the first step that would
  overflow; it is cross-validated against the `BigUint` evaluator in tests.
- Release builds keep `overflow-checks = true`.
- The sampler (`rng::SplitMix64`) only chooses inputs; it never decides
  whether a statement holds.

## Ledger format

`ledger.jsonl` has one JSON object per line with the fields `schema_version`,
`tool_version`, `seed`, `parameters`, `hypothesis_id`, `hypothesis`, `domain`,
`status`, `evidence`, `failure_cases`, `proof_obligations`. Integers that may
exceed 64 bits are decimal strings. Failure cases are self-contained:

```json
{"kind":"no-descent-within-window","n":"27","window":16}
```

## Extending

A new candidate statement is a function in `src/hypothesis.rs` returning
`LedgerEntry` values, registered in `run_experiment`. Any counterexample it
records must be a `FailureCase` variant with a matching branch in
`verifier::verify_failure_case`; the experiment aborts if the verifier
rejects one. No autonomous agent loop is implemented.

## References and attribution

The objects built here are classical and are attributed in
[`research/literature-cst.md`](research/literature-cst.md):

- parity vectors, coefficient stopping time and its congruence classes:
  R. Terras, Acta Arith. 30 (1976) 241-252;
- the open statement the lab tests, `sigma(n) = tau(n)` for all `n >= 2`, is
  the **Coefficient Stopping Time conjecture** (Terras 1976; Garner, Proc.
  Amer. Math. Soc. 82 (1981) 19-22; named in Lagarias, Amer. Math. Monthly 92
  (1985) 3-23);
- paradoxical sequences and the `n = 7` example: O. Rozier and C. Terracol,
  Discrete Math. 349 (2026) 115167, arXiv:2502.00948;
- the counts are OEIS A076227 and A100982; the enumeration by odd positions
  follows M. Winkler, arXiv:1709.03385.

The primary-source audit now includes Terras's and Garner's cached scans,
versioned arXiv text and the indexed ResearchGate preprints, with exact
access and theorem references. Terras's historical argument covers
`tau<=2592`; our finite-depth checks are reproductions, not new evidence.
No third-party code was copied. The earlier literature investigation did not
compile the external Lean project; this repository's own Lean results are
kernel-checked as documented above.

The slack hypothesis **P1a is refuted**: among the twelve first-crossing
words with six odd steps, the least member is 287, while the largest
`c/((2^k-3^r)*m)` occurs at 347. See
[`tests/p1a_refutation.rs`](tests/p1a_refutation.rs) and the
[revised research plan](research/phase1-next-questions.md). P1b remains open
in that plan; no conclusion about it follows from this counterexample.
Primary-source convention and bound checks are in
[`tests/primary_sources.rs`](tests/primary_sources.rs).

## License

CC0 1.0 Universal, see [`LICENSE`](LICENSE).
