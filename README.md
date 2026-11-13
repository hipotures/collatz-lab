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

That document also records which sources were actually read and which were
not (Terras's and Garner's papers were not accessible). No code or theorem
text was copied from any source, including the Lean project
`msharpe248/collatz`, whose statements were read but not compiled.

## License

CC0 1.0 Universal, see [`LICENSE`](LICENSE).
