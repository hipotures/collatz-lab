# Phase 1: next experiments

Context: [`literature-cst.md`](literature-cst.md). The lab's cover, its
counts and its open conjecture are all known objects (Terras's coefficient
stopping-time classes, OEIS A076227 / A100982, the CST conjecture). The
proposals below are chosen so that a result would say something not already
implied by the verified range `n <= 2.8 * 10^19`. Each is exact, bounded and
has a stopping rule. None is implemented yet, and none can prove CST or
Collatz.

Notation: for a first coefficient crossing `p` of length `k` with `r` odd
steps, `d = 2^k - 3^r`, `c` its offset, `m` its least member `>= 2`.

## 1. Exact signed threshold slack

**Quantity.** `slack(p) = d * m - c`, an integer. CST on the cylinder of `p`
is `slack(p) > 0`. Compare it with `d * m` through the exact rational
`rho(p) = c / (d * m)`, so CST is `rho(p) < 1`.

**Why it is not a rerun of known checks.** Existence of an exception at
length up to 64 is already excluded. What is not tabulated in the sources
read is *how close* cylinders come: the distribution of `rho` per `r`, and
whether its maximum is governed by small `d` (lengths where `2^k` is just
above `3^r`: `r = 5`, `17`, `29`, `41`, ...) or by small `m`.

**Falsifiable predictions.**

- P1a: for each `r`, the maximum of `rho` over first crossings with `r` odd
  steps is attained by the cylinder with the smallest `m`.
- P1b: `max rho` at `r` is at most `max rho` at `r = 5` for every `r > 5`.

A single cylinder refutes either. Both are guesses made before looking.

**Bounds and stopping rule.** Exhaustive for `r <= 17` (about half a million
first crossings in total, length at most 27). Stop there. Extend only if P1a
holds, in which case the maximum for larger `r` can be found by following
the small-`m` branch instead of enumerating. Abandon if `max rho` shows no
dependence on `d`.

**Novelty check before running.** Read Terras's and Garner's papers for
explicit bounds on `c / d`; Garner's paper could not be accessed in this
audit.

## 2. Adaptive first-crossing horizons

**Idea.** A fixed depth `K` leaves `S(K)` classes uncovered. A survivor word
`w` of length `K` with `r` odd steps can cross no earlier than length `k(r)`
(the bit length of `3^r`), and the sub-cylinder `w 0...0` of that length does
cross. So the natural horizon for `w` is `k(r_K(w))`, which depends on the
word, not a fixed `K + 1`.

**Experiment.** Start from depth `K_0`. In each round, replace every
survivor `w` by its descendants at its own horizon `k(r(w))`, certify those
that cross, keep the rest. Record after each round the exact surviving
density (a dyadic rational) and the largest horizon in use. The densities can
be computed by the recurrence in `counting` restricted to a subtree, without
enumerating classes, so many rounds are cheap.

**Falsifiable prediction.** P2: each round removes at least a fixed fraction
`q > 0` of the surviving density, with `q` independent of the round
(geometric decay in the number of rounds). Falsified if the removed fraction
tends to 0 over the rounds computed.

**Bounds and stopping rule.** `K_0 = 16`, horizons capped at 4000, at most
200 rounds. Stop early if the removed fraction falls below 1 percent for ten
consecutive rounds (P2 fails) or stays above a constant for 100 rounds.

**Known-versus-new.** That the surviving density tends to 0 is Terras's
density theorem. The rate per adaptive round is probably derivable from the
asymptotics behind A076227 and Wagon's constant; treat a confirmed P2 as a
prompt to derive it, not as a finding. This scheme still leaves the class of
`-1` uncovered in every round and cannot close the gap in obligation 2.

## 3. Cross-depth survivor structure in residue terms

**Idea.** In word terms survival has a one-counter description (track
`r_j` against `j`). In residue terms it is less transparent: for a survivor
class `rho mod 2^K`, which of `rho` and `rho + 2^K` is the odd-step child
depends on the parity of `T^K(rho)`.

**Experiment.** For each survivor class at depth `K`, record its least
member `m_K >= 2`. Let `M(K)` be the minimum of `m_K` over survivors: the
least integer `>= 2` with `tau > K`.

**Falsifiable prediction.** P3: the sequence of values taken by `M(K)` is
exactly the sequence of stopping-time record holders for `T` (27, 703, ...),
and `M(K)` is realised by a class other than `-1 mod 2^K` for every
`K >= 3`.

**Bounds and stopping rule.** `K <= 40`, by branch and bound on the least
member (no full enumeration). Stop at `K = 40` or at the first mismatch.

**Known-versus-new.** This is mostly calibration against published record
tables (Oliveira e Silva, Roosendaal), and is listed last for that reason.
Its value is the by-product: the residue-side description of the branch that
realises `M(K)`, which is what an adaptive certificate for survivor families
would have to be parametrised by.

## Not proposed

Extending the cover depth, extending the range of `n`, unbounded searches,
and any autonomous hypothesis loop.
