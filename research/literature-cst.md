# The lab and the Coefficient Stopping Time literature

Purpose: say precisely which known objects the workbench rebuilt, which open
statement its finite checks actually test, and what is left. Nothing here
proves or refutes the Coefficient Stopping Time (CST) conjecture or the
Collatz conjecture, and nothing here is claimed to be new.

## 1. How the sources were consulted

Audit date: 2026-11-13. "Read" below means the text was retrieved and its
statements extracted by an automated reader, then cross-checked against the
lab's own computations where possible. Statements quoted from a source that
was only reached second-hand are marked. Before any of this is cited outside
the repository, the theorem numbers should be rechecked against the
published versions.

| source | kind | how consulted | used here for |
|---|---|---|---|
| R. Terras, *A stopping time problem on the positive integers*, Acta Arith. 30 (1976), 241-252 | peer-reviewed, historical | **not read**; known through Lagarias, Rozier-Terracol and OEIS comments | origin of the coefficient stopping time, of the conjecture, and of the counting recursion |
| L. E. Garner, *On the Collatz 3n+1 algorithm*, Proc. Amer. Math. Soc. 82 (1981), 19-22, DOI 10.1090/S0002-9939-1981-0603593-2 | peer-reviewed, historical | **not read** (the AMS PDF returned HTTP 403); bibliographic data from the DOI record | second attribution of the conjecture; computational verification as reported by Rozier-Terracol |
| J. C. Lagarias, *The 3x+1 problem and its generalizations*, Amer. Math. Monthly 92 (1985), 3-23 | peer-reviewed survey | read in the HTML edition hosted at cecm.sfu.ca (formulas are images, so only the prose was readable) | name "Coefficient Stopping Time Conjecture"; Theorem C (Terras) |
| O. Rozier, C. Terracol, *Paradoxical behavior in Collatz sequences*, Discrete Math. 349 (2026) 115167, DOI 10.1016/j.disc.2026.115167 | peer-reviewed | read as arXiv:2502.00948v5 (17 May 2026), not the journal PDF | CST statement, paradoxical sequences, the `n = 7` example, verified range |
| M. Winkler, *Deterministic Structures in the Stopping Time Dynamics of the 3x+1 Problem*, arXiv:1709.03385v8 (28 Jul 2026) | preprint, not peer-reviewed | abstract only | enumeration of coefficient stopping-time classes by odd positions |
| M. Winkler, revised preprint of 23 Aug 2026, DOI 10.13140/RG.2.2.20089.94563 | preprint | **not read** (ResearchGate returned HTTP 403); assumed, not verified, to be a revision of the arXiv paper | - |
| OEIS A076227, A100982, A020914 | curated database | read 2026-11-13 | names and terms of the count sequences |
| `msharpe248/collatz` at commit `ec8174b` | author-supplied Lean 4 project, MIT licence | theorem statements read in `NoGo.lean`, `Density.lean`, `Paradoxical.lean` and one analysis note; **nothing was compiled or kernel-checked here** | comparison of scope only |
| V. Angeltveit, *An improved algorithm for checking the Collatz conjecture for all n < 2^N*, arXiv:2602.10466 (11 Feb 2026) | preprint | abstract only | context: a verification algorithm, not about CST |
| D. Barina, J. Supercomput. 77 (2021) 2681-2688 and 81 (2025) 810; pcbarina.fit.vut.cz | peer-reviewed computation | project page only | context: convergence verified below `2^71` (page entry dated 2025-01-15) |

No code or theorem text was copied from any of these.

## 2. Definitions

Throughout, `T(n) = n/2` for even `n` and `(3n+1)/2` for odd `n`, on positive
integers. For `n >= 1` and `k >= 0`:

- `r_k(n)` is the number of odd terms among `n, T(n), ..., T^(k-1)(n)`;
- `c_k(n)` is the non-negative integer with
  `T^k(n) = (3^(r_k(n)) n + c_k(n)) / 2^k` (the affine formula; `c_0 = 0`,
  an even step keeps `c`, an odd step at position `k` gives `3c + 2^k`);
- the **stopping time** is `sigma(n) = inf { k >= 1 : T^k(n) < n }`;
- the **coefficient stopping time** is
  `tau(n) = inf { k >= 1 : 3^(r_k(n)) < 2^k }`;
- `inf` of the empty set is `+infinity`, for both.

A parity word `p` of length `k >= 1` with `r_j` odd letters among its first
`j` is a **first coefficient crossing** if `2^j < 3^(r_j)` for all
`1 <= j < k` and `2^k > 3^(r_k)`. (`2^j = 3^(r_j)` cannot happen for
`j >= 1`.) Its **cylinder** is the residue class modulo `2^k` of integers
whose parity prefix is `p`; `r` and `c` are constant on it. Its **threshold**
is `N0(p) = floor(c / (2^k - 3^r)) + 1`.

**CST conjecture** (Terras 1976; also conjectured by Garner 1981; named by
Lagarias 1985): `sigma(n) = tau(n)` for every `n >= 2`, as an equality in
`{1, 2, ...} + {+infinity}`. `n = 1` is excluded: `tau(1) = 2` (prefix `10`,
`3 < 4`) while `sigma(1) = +infinity`.

## 3. Three elementary lemmas

**Lemma 1 (`tau <= sigma`).** For every `n >= 1`, `tau(n) <= sigma(n)`.
*Proof.* If `sigma(n) = +infinity` there is nothing to show. Otherwise let
`k = sigma(n)`. Then `(3^r n + c)/2^k < n` with `r = r_k(n)`, `c = c_k(n) >= 0`,
so `3^r n <= 3^r n + c < 2^k n`, and `n >= 1` gives `3^r < 2^k`. Hence the set
defining `tau(n)` contains `k`. In particular `tau(n) = +infinity` forces
`sigma(n) = +infinity`. ∎

**Lemma 2 (cylinders of `tau`).** For `n >= 1` and `k >= 1`: `tau(n) = k` iff
the length-`k` parity prefix of `n` is a first coefficient crossing.
*Proof.* `tau(n) = k` means `3^(r_k) < 2^k` and `3^(r_j) >= 2^j` for
`1 <= j < k`; the latter is `3^(r_j) > 2^j` because equality is impossible.
These conditions involve only the first `k` parities of `n`. ∎

**Lemma 3 (threshold).** Let `p` be a word of length `k` with `2^k > 3^r`, and
`n >= 1` in its cylinder. Then `T^k(n) < n` iff `n >= N0(p)`.
*Proof.* `T^k(n) < n` iff `3^r n + c < 2^k n` iff `(2^k - 3^r) n > c` iff
`n > c / (2^k - 3^r)` iff `n >= floor(c / (2^k - 3^r)) + 1`, all quantities
being integers and `2^k - 3^r > 0`. ∎

Lemma 2 with Lemma 3 is, as far as the readable prose shows, the content of
what Lagarias states as Theorem C and attributes to Terras: the integers with
coefficient stopping time `k` are exactly certain congruence classes modulo
`2^k`, and all sufficiently large members of such a class have stopping time
`k`. The lab's "first-descent certificates" are these classes with the
explicit bound `N0`.

## 4. The lab's conjecture is CST

**Statement L** (the ledger entry `threshold-exceptions-trivial-all-depths`):
for every first coefficient crossing `p`, every integer `n >= 2` in the
cylinder of `p` satisfies `n >= N0(p)`.

**Theorem.** L holds if and only if CST holds.

*L implies CST.* Let `n >= 2`.

- Case `tau(n) = +infinity`. By Lemma 1, `sigma(n) >= tau(n) = +infinity`, so
  `sigma(n) = tau(n)`. L is not used: such an `n` lies in no first-crossing
  cylinder.
- Case `tau(n) = k < +infinity`. By Lemma 2 the length-`k` prefix `p` of `n`
  is a first crossing and `n` is in its cylinder. By L, `n >= N0(p)`. By
  Lemma 3, `T^k(n) < n`, so `sigma(n) <= k = tau(n)`. With Lemma 1,
  `sigma(n) = tau(n)`.

*CST implies L.* Let `p` be a first crossing of length `k` and `n >= 2` in its
cylinder. By Lemma 2, `tau(n) = k`. By CST, `sigma(n) = k`, which is finite,
so `T^k(n) < n`. By Lemma 3, `n >= N0(p)`. ∎

Remarks on the infinite cases.

- The proof never needs `tau` to be finite. Both L and CST are silent about
  whether `tau(n) < +infinity`; for seeds with `tau(n) = +infinity` CST holds
  automatically by Lemma 1.
- `n = 1` must be excluded on both sides: it lies in the cylinder of `10`
  with `N0 = 2`.
- The depth-restricted ledger entry `threshold-exceptions-trivial` (prefixes
  of length at most `K`) is, by the same argument applied to those cylinders
  only, equivalent to "`sigma(n) = tau(n)` for every `n >= 2` with
  `tau(n) <= K`".

## 5. What the lab's finite check is worth

The enumeration to depth 24 shows: `sigma(n) = tau(n)` for every `n >= 2`
with `tau(n) <= 24`. That covers infinitely many integers but is **already
implied by published work**. Rozier and Terracol report (their Corollary 5.4,
as read from arXiv v5) that `t(n) = tau(n)` for all `2 <= n <= 2.8 * 10^19`.
Given that, take any first crossing `p` of length `k <= 64`. Its least member
`m >= 2` is below `2^k + 2 <= 2.8 * 10^19`, so `sigma(m) = tau(m) = k`, hence
`m >= N0(p)` by Lemma 3, hence every member `n >= 2` is `>= N0(p)`. So for
`k <= 64` Statement L follows from the verified range, and no enumeration
below length 65 can find an exception. The lab's check is a consistency test
of the tool, not new evidence.

## 6. What separates all this from the Collatz conjecture

Collatz for `T` is equivalent to: `sigma(n) < +infinity` for every `n >= 2`
(strong induction on `n` in one direction; in the other, an orbit reaching 1
passes below any `n >= 2`). Write

- (A) CST: `sigma(n) = tau(n)` for all `n >= 2`;
- (B) `tau(n) < +infinity` for all `n >= 2`.

Then:

- (A) and (B) together give Collatz. Neither is known, and (A) is not known
  to imply (B).
- Collatz gives (B), by Lemma 1. This audit found no source deriving (A) from
  Collatz, and none is claimed here.
- (A) alone excludes nontrivial cycles (noted by Lagarias and by
  Rozier-Terracol). Proof: let `m >= 2` be the least element of a cycle of
  length `l` other than `{1, 2}`. Then `sigma(m) = +infinity`. From
  `T^l(m) = m`, `3^r m + c = 2^l m` with `c > 0` (a cycle has an odd step),
  so `3^r < 2^l` and `tau(m) <= l`, contradicting (A).
- (A) alone does **not** exclude divergent orbits. It only says that the
  least element `m` of such an orbit has `tau(m) = +infinity`, i.e. every
  prefix of its parity sequence keeps `3^(r_j) > 2^j`. Threshold properties of
  first-crossing cylinders say nothing about integers that lie in no such
  cylinder.
- (B) is known for a set of integers of natural density 1 (Terras); that is a
  density statement, not a statement about every integer.

## 7. Paradoxical segments are not first-crossing exceptions

Rozier and Terracol (Definition 1.1) call the sequence
`n, T(n), ..., T^j(n)` with `n > 2` *paradoxical* when `3^(r_j) < 2^j` and
`T^j(n) >= n`, repetitions of the trivial cycle aside. Intermediate descent is
allowed. Their own first example is the one used in this repository:

```text
n = 7:  7, 11, 17, 26, 13, 20, 10, 5, 8      parity prefix 11101001
3^5 / 2^8 = 243/256 < 1,   T^8(7) = 8 >= 7
```

This does not contradict CST: `tau(7) = sigma(7) = 7`, because the prefix
`1110100` already has `3^4 = 81 < 128 = 2^7`, and `T^7(7) = 5 < 7`. A
counterexample to CST must be a first crossing whose member fails to descend.
So `3^r < 2^k` together with `T^k(n) >= n` proves nothing about CST unless
`k = tau(n)`.

In the lab's terms a paradoxical pair `(n, j)` is exactly a member above 2
below the threshold of the single-cylinder certificate of length `j` (up to
their exclusion of trivial-cycle repetitions, which only concerns `n <= 2`
here). The
test `tests/paradoxical.rs` enumerates them without any bound on the seed for
all lengths up to 14 and finds five, all of length 8: `n = 7, 9, 18, 19, 25`,
with first descents at steps `7, 2, 1, 4, 2`. The third-party Lean project
states the same five seeds at length eight as a theorem
(`paradoxical_eight_iff`); the agreement is a cross-check of this tool.

The hardened verifier (`tests/adversarial.rs`) rejects
`ThresholdException { parity: "11101001", n: 7 }` with the reason that the
coefficient already crosses at step 7.

Results reported by Rozier and Terracol, not rechecked here: exactly 593
paradoxical sequences start at integers up to 4614, and any other must start
above `2.8 * 10^19` (Theorem 1.3); if there are only finitely many paradoxical
sequences then the Collatz conjecture holds (Corollary 3.3); their
Conjecture 6.1, that none starts above 4614, is described as stronger than
both the Collatz and the CST conjecture.

## 8. Count reconciliation

Counted objects, for the accelerated map and parity words read from the
seed:

- `F(K)`: first coefficient crossings of length at most `K` (the number of
  certificates in the cover to depth `K`), including the word `0`;
- `S(K)`: words of length `K` with `2^j < 3^(r_j)` for all `1 <= j <= K`
  (uncovered classes modulo `2^K`).

Three computations:

1. the constructive cover walker (`certificate::walk_first_descent`), which
   builds every residue and threshold;
2. `counting::count_by_length`: a recurrence on (length, odd steps) with exact
   comparisons of `2^k` and `3^r`;
3. `counting::count_by_odd_positions`: enumeration of admissible odd positions
   `0 = a_1 < ... < a_r` with `a_(i+1) <= k(i) - 1`, where `k(i)` is the bit
   length of `3^i`.

2 and 3 share no code with 1 and never construct a residue.

| `K` | `F(K)` walker | `F(K)` by length | `F(K)` by positions | `S(K)` walker | `S(K)` by length | `S(K)` by positions | OEIS A076227(`K`) |
|---|---|---|---|---|---|---|---|
| 4 | 3 | 3 | 3 | 3 | 3 | 3 | 3 |
| 8 | 15 | 15 | 15 | 19 | 19 | 19 | 19 |
| 12 | 57 | 57 | 57 | 226 | 226 | 226 | 226 |
| 16 | 791 | 791 | 791 | 2114 | 2114 | 2114 | 2114 |
| 20 | 4404 | 4404 | 4404 | 27328 | 27328 | 27328 | 27328 |
| 24 | 81119 | 81119 | 81119 | 286581 | 286581 | 286581 | 286581 |

No discrepancy was found. Identifications, confirmed term by term in
`tests/counts.rs`:

- `S(K)` is OEIS **A076227**, "Number of surviving Collatz residues mod 2^n"
  (offset 0; all 26 terms `K = 0..25` match). An OEIS comment traces the
  recursion to Terras's 1976 paper.
- The number of first crossings with exactly `r >= 1` odd steps is OEIS
  **A100982**, "Number of admissible sequences of order n; related to 3x+1
  problem and Wagon's constant" (offset 1; the 20 terms `r = 1..20` match).
  Hence `F(K) = 1 + sum of A100982(r) over r >= 1 with k(r) <= K`; the leading
  1 is the word `0`, which A100982 does not count.
- All first crossings with `r` odd steps have the same length `k(r)`, the bit
  length of `3^r`: OEIS **A020914**.

The two recurrences also agree with each other at every depth up to 150
(tested) and run to depth 1000 in well under a second
(`collatz-lab counts --max-depth 1000 --walker-depth 0`).

Assumptions behind the counts: words are counted, and each word of length `k`
is one residue class modulo `2^k` (proved in `src/prefix.rs`); residue 0 and
the class of `n = 1` are included; "crossing" uses the strict comparison
`2^k > 3^r`.

## 9. What the lab rediscovered

| lab object | known as | source |
|---|---|---|
| parity prefix, affine form, residue class modulo `2^k` | parity vectors and their congruence classes | Terras 1976 (via Lagarias) |
| first-descent certificate with threshold `N0` | classes of coefficient stopping time `k`; "all sufficiently large" members have stopping time `k` | Theorem C in Lagarias, attributed to Terras |
| `threshold-exceptions-trivial-all-depths` | the CST conjecture | Terras 1976, Garner 1981, named by Lagarias 1985 |
| uncovered classes at depth `K` | surviving residues, A076227 | Terras; OEIS |
| first crossings by odd steps | admissible sequences, A100982; coefficient stopping-time classes | Terras; Winkler |
| Mersenne identity and no uniform window | `terras_mersenne`, `no_uniform_descent_bound` | stated in the third-party Lean project; elementary |
| below-threshold members of a non-first cylinder | paradoxical sequences | Rozier-Terracol 2026 |

On the Lean project: the statements read there are (i) the Mersenne identity
and "for every window `B` and cutoff `N0` some `n >= N0` has no descent within
`B` steps"; (ii) `no_finite_certificate`, which excludes descent certificates
of the specific form `T^t(n) W(T^t(n)) <= rho n W(n)` with a potential bounded
between two positive constants, a fixed window and a fixed `rho < 1`;
(iii) `collatz_iff_descent`. (ii) is a statement about bounded multiplicative
potentials with a fixed window. It does not address unbounded potentials or
horizons that grow with `n`, and the first-crossing certificates here (horizon
`tau(n)`, unbounded over `n`) are outside its hypotheses. The density
exponents and cycle bounds advertised in that project's README were not
examined.

## 10. Open obligations, stated exactly

1. **CST.** For every first coefficient crossing `p` of length `k >= 65`:
   `c(p) < (2^k - 3^r) m(p)`, where `m(p)` is the least member `>= 2`. Open.
   (Lengths up to 64 follow from the verified range, section 5.)
2. **Finiteness of `tau`.** For every `n >= 2` some prefix has
   `3^(r_j) < 2^j`. Open; independent of 1.
3. Neither 1 nor 2 is approached by counting classes: the counts in section 8
   are exact but carry no information about a particular integer.
