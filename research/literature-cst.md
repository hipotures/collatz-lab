# The lab and the Coefficient Stopping Time literature

Purpose: say precisely which known objects the workbench rebuilt, which open
statement its finite checks actually test, and what is left. Nothing here
proves or refutes the Coefficient Stopping Time (CST) conjecture or the
Collatz conjecture, and nothing here is claimed to be new.

## 1. How the sources were consulted

Audit date: 2026-11-13 (issue #4). "Directly read" means that the primary
text was inspected, not that its proofs were formally verified. Terras and
Garner were inspected as locally cached scan images from the interrupted
session; the other cached papers have extracted text. ResearchGate text was
read through the search service's indexed HTML, **not a downloaded PDF**.
Access failures are not evidence of nonexistence. No blocked PDF endpoint
was retried during continuation, and no source PDF is redistributed here.

| source | kind and version | access and inspected locations |
|---|---|---|
| R. Terras, *A stopping time problem on the positive integers*, Acta Arith. 30 (1976), 241–252, [DOI](https://doi.org/10.4064/aa-30-3-241-252), [scan](https://matwbn.icm.edu.pl/ksiazki/aa/aa30/aa3034.pdf) | peer-reviewed historical paper | **directly read**, printed pp. 241–252 in the cached scan; PDF spreads also contain adjacent articles |
| L. E. Garner, *On the Collatz 3n+1 algorithm*, Proc. Amer. Math. Soc. 82 (1981), 19–22, [DOI](https://doi.org/10.1090/S0002-9939-1981-0603593-2) | peer-reviewed historical paper | **directly read**, cached [Wayback copy of the AMS scan](https://web.archive.org/web/2id_/https://www.ams.org/journals/proc/1981-082-01/S0002-9939-1981-0603593-2/S0002-9939-1981-0603593-2.pdf), pp. 19–22; equations in §§4–6 checked visually; direct AMS/SciSpace access had failed |
| J. C. Lagarias, *The 3x+1 problem and its generalizations*, Amer. Math. Monthly 92 (1985), 3–23 | peer-reviewed survey | previous audit: [HTML prose](https://www.cecm.sfu.ca/organics/papers/lagarias/paper/html/paper.html) read; image formulas not read; Theorem C is now checked against Terras directly |
| O. Rozier, C. Terracol, *Paradoxical behavior in Collatz sequences*, Discrete Math. 349(10) (2026), 115167, [DOI](https://doi.org/10.1016/j.disc.2026.115167) | peer-reviewed work; consulted **arXiv:2502.00948v5**, 17 May 2026 | **directly read** in cached extracted text and [versioned HTML](https://arxiv.org/html/2502.00948v5); Theorem 1.3 p. 4, Theorem 5.3 pp. 15–16, Corollary 5.4 p. 17; journal numbering **not checked** |
| M. Winkler, *Deterministic Structures in the Coefficient Stopping-Time Dynamics of the 3x+1 Problem*, [arXiv:1709.03385v8](https://arxiv.org/pdf/1709.03385v8) | preprint; title page revised 27 July 2026, arXiv stamp 28 July | **directly read**, cached extracted §§2–5: Theorem 7 pp. 4–5, Proposition 8 pp. 5–6, Theorem 16 pp. 10–11, arithmetic transitions pp. 12–16, coverage pp. 17–18 |
| M. Winkler, [ResearchGate manuscript](https://www.researchgate.net/publication/400315289_Deterministic_Structures_in_the_Coefficient_Stopping-Time_Dynamics_of_the_3x1_Problem), DOI 10.13140/RG.2.2.20089.94563 | preprint; indexed title page says revised **23 August 2026** | primary indexed text inspected: §§2–5, Proposition 9, Theorem 17, Propositions 27–28; PDF unavailable; keep separate from arXiv v8 |
| K. Hikawa, K. Nakanishi, *Parity Vector Analysis in the Study of the Collatz Conjecture*, [author PDF](https://kanazawa-j.sakura.ne.jp/Collatz/Edited_English_paper.pdf) | preprint; 25 January 2026 | **directly read** in cached extracted text, §§1–2, especially Theorem 1 p. 8 and Theorem 2 p. 11; linked tables/software not independently audited |
| K. Hikawa, [*Finite-Dimensional Combinatorial and Arithmetic Structures of Parity Vectors for the Accelerated Collatz Map*](https://www.researchgate.net/publication/408442963_Finite-Dimensional_Combinatorial_and_Arithmetic_Structures_of_Parity_Vectors_for_the_Accelerated_Collatz_Map), DOI 10.13140/RG.2.2.29894.84804/1 | preprint; page describes **v2.1, 2 August 2026** | primary indexed text inspected: Theorem 3.3 p. 14, Theorem 5.2 p. 22, Theorem 6.3 pp. 28–29, Conjecture 7.1 §7.3; PDF unavailable; pagination is that rendered by the index and may change |
| [OEIS A076227](https://oeis.org/A076227), [A100982](https://oeis.org/A100982), [A020914](https://oeis.org/A020914) | curated database | previous audit: terms and comments read; reproducible comparisons in `tests/counts.rs` |
| [`msharpe248/collatz`](https://github.com/msharpe248/collatz) at `ec8174b` | author-supplied Lean 4 project, MIT licence | previous audit: selected theorem statements only; **not compiled or kernel-checked** |
| V. Angeltveit, [arXiv:2602.10466](https://arxiv.org/abs/2602.10466), 11 February 2026 | preprint | previous audit: abstract only; verification-algorithm context |
| D. Barina, J. Supercomput. 77 (2021), 2681–2688 and 81 (2025), 810; [project page](https://pcbarina.fit.vut.cz/) | peer-reviewed computation | previous audit: project page only; convergence bound below `2^71`, entry dated 2025-01-15; not a CST bound |

The changing ResearchGate pages are not immutable versions; theorem labels
above identify the text actually inspected. No byte identity with arXiv is
assumed. The older title *The Recursive Stopping Time Structure of the 3x+1
Function* belongs to earlier arXiv revisions, not the inspected v8 title page.
The optional Zenodo toolkit comparison was not performed. No code was copied
from these sources; mathematical statements below are paraphrased.

### Primary-source claims and conventions

**Terras.** His `chi` is our actual stopping time `sigma`; his `tau` is our
`tau`. His rational remainder `varrho_k` is `c/2^k`, not our integer `c`.
Theorem 1.1 (p. 242) gives the affine decomposition; Theorem 1.2
(pp. 242–243) and Corollary 1.3 identify parity words with residue classes.
Definition 1.5 (p. 243) defines `tau`, including infinity. Proposition 1.7
(p. 244) supplies the threshold criterion on the contracting branch
`lambda_k = 3^r/2^k < 1`; Proposition 1.8 proves `tau <= chi`.
Theorem 1.9 (p. 244) gives eventual equality in each finite-`tau` class.
Theorem 1.14 (pp. 245–246) is the modified binomial recurrence;
Theorems 1.11 and 1.17 (pp. 244–247) give the density distribution and its
vanishing tail. A density-one result allows an exceptional set of density zero.

Theorem 2.6 (p. 250), **Mini-Max**, identifies a unique residue in `[1,2^k]`
maximizing `varrho_k` among classes with `tau = k`. At fixed crossing length
both `r` and `d = 2^k - 3^r` are fixed. Thus it maximizes `c` and `c/d`,
**not** `c/(d*m)` where the least member `m` changes with the class.
Its extremal word is the first `k-1` entries of the sequence in Theorem 2.4
(p. 249), followed by zero: start `nu_0=1`, and choose `nu_i=1` exactly when
`3^(nu_0+...+nu_(i-1)) < 2^(i+1)`. Use only possible crossing lengths.
Writing the resulting maximum integer offset as `C_k`, Corollary 2.8
(p. 251) says `n > C_k/d` suffices for `sigma(n)=tau(n)=k`.
Conjecture 2.9 (p. 251) asserts equality for **all** `n >= 2`; it remains a
conjecture. The numerical argument on p. 252 establishes equality when
`tau <= 2592`, using Table C and a finite seed check. Section 5 explains its
reproduction here.

**Garner.** His map `s` uses odd step `3n+1`. After `k` lab steps with `r`
odd steps, exactly `K=k+r` ordinary steps have occurred and
`s^K(n)=T^k(n)`. His coefficient `3^r/2^(K-r)` is therefore `3^r/2^k`.
An odd ordinary step increases both the integer and its coefficient, so the
first descent and first coefficient crossing occur at paired endpoints.
For finite times, `kappa_G = tau + r_tau` and
`sigma_G = sigma + r_sigma`; equality of the two times translates correctly,
although the numerical indices differ. Section 4 (p. 20) conjectures equality
and reports checking seeds through 1,150,000. The first three examples on
p. 20 convert `(n, sigma, r, sigma_G)` to `(27,59,37,96)`,
`(703,81,51,132)`, `(35655,135,85,220)` (`tests/primary_sources.rs`).

In §5 (pp. 20–21), put `p(j)=floor(j log_2 3)`. His `b(M)` and `B(M)`
are negative base-3 logarithms of the minimum relative gaps
`(3^j-2^p(j))/3^j` and `(2^(p(j)+1)-3^j)/3^j`, for `1 <= j <= M`.
Equations (2)–(3) give finite power-gap lower bounds; §6 (pp. 21–22)
uses them to give a sufficient bound on the odd-step count for CST.
Small gaps concern rational approximations to `log_2 3`, but §5 does **not**
prove a uniform all-orders gap estimate or a continued-fraction theorem.
It supplies no ordering of `c/(d*m)` by `m`, and does not settle P1a or P1b.

**Winkler.** In the indexed August manuscript, `sigma*` is our `tau`,
order `n=r-1`, and `sigma_n=k(r)`. Admissible odd positions form a tree
by deleting the final position; Proposition 9 counts these via a Pascal-type
recurrence, matching our position recurrence after this index shift.
Theorem 17 constructs the tree, §4 gives arithmetic transitions, and
Propositions 27–28 give finite periodic coverage and its relation to
finiteness of coefficient times. These are finite structures, without
asserting CST or finiteness for every integer. The July arXiv version has
Proposition 8, Theorem 16 and Propositions 26–27 instead.

**Hikawa–Nakanishi.** January §§2.1–2.2 distinguish survivors, first
crossings and already-crossed words. Their Theorem 1 uses
`W(k+1,r) = [2^(k+1)<3^r] (W(k,r)+W(k,r-1))`, the lab's length recurrence.
Theorem 2 groups by weight and obtains `X(r+1)=W(r)`, summing survivors over
all lengths of that weight. "Convergence" of a word here is coefficient
crossing, not proof that its integer orbit reaches 1.

**Hikawa, indexed v2.1.** Theorem 3.3 gives the explicit bijection
`U(d) -> J(d+1)`, `d>=1`, by appending `1` and then zeros until crossing.
Thus `X(d+1)=W(d)`; `X(d)=A100982(d)` and length-count `W(k)=A076227(k)`.
Theorem 5.2 requires equal length **and equal weight**: for distinct words
starting with `1`, `v_2(c(v)-c(w))=j_min-1`, with one-based positions.
Theorem 6.3 states `log_2 W(d)=gamma*d+O(log d)`,
`gamma=(log_2 3) H(1/log_2 3)`; Conjecture 7.1 separately proposes the
stronger `Theta(d^(-3/2) 2^(gamma*d))` form. These are finite counting and
arithmetic results; they do not determine every infinite orbit.

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

Lemma 2 with Lemma 3 recovers Terras Theorem 1.9 (p. 244), also
stated as Theorem C by Lagarias: the integers with
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

The enumeration to depth 24 shows `sigma(n)=tau(n)` for every `n>=2`
with `tau(n)<=24`. This is already implied by **Terras, p. 252**, whose
finite argument reaches `tau<=2592` without enumerating `2^2592` classes.
For each possible `k`, the mini-max bound reduces exceptions to seeds
`n <= C_k/(2^k-3^r)`. Our exact implementation finds

```text
max floor(C_k/(2^k-3^r)), possible k <= 2592: 238670
floor(C_2593/(2^2593-3^1636)):              420841
```

The test `terras_2592_cutoff_has_a_small_exact_exception_bound` in
`tests/primary_sources.rs` independently reproduces the extremal recurrence
with `BigUint` and checks `sigma=tau` by direct iteration for every
`2<=n<=250000`. It also checks descent within 135 accelerated steps on that
finite range. This reproduces the numerical ingredients of the historical
argument, relying on Terras's mini-max theorem for the all-class bound;
it is not a new CST result. A separate exhaustive test through length 14
cross-checks the extremal construction and uniqueness. We do not require
identity with rounded entries of Table C (p. 251): for example its printed
238672 at 1539 is a conservative bound, whereas exact floor-plus-one is
238671. Both are below 250000.

A different domain is covered by **Rozier–Terracol, arXiv v5**:

- Theorem 1.3 (p. 4): 593 paradoxical sequences start at seeds at most 4614;
  any others start above `2.8*10^19`; absence of others implies Collatz.
- Theorem 5.3 (pp. 15–16): the 593 have length at most 92; there are no
  others with `93<=j<=301993`, or with `4615<=n<=2.8*10^19`.
- Corollary 5.4 (p. 17): `sigma(n)=tau(n)` for `2<=n<=2.8*10^19`, using
  Theorem 5.3 and prior finite checks. Their actual stopping time is `t`. See the [versioned primary text](https://arxiv.org/html/2502.00948v5).

Theorem statements were inspected; the large computations and external
record tables in their proof were **not rerun**. Journal theorem numbering
is not asserted. Their seed bound alone implies Statement L through length
64: the least member `>=2` of any such cylinder is below `2^k+2`, hence
inside that bound, and the threshold test then covers the entire cylinder.
That implication is weaker in the length parameter than Terras's result.
Neither a seed bound nor a coefficient-time bound settles all integers.

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
- (A) alone does **not by the argument given here** exclude divergent orbits. It only says that the
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
here). The test `tests/paradoxical.rs` enumerates them without any bound on the seed for
all lengths up to 14 and finds five, all of length 8: `n = 7, 9, 18, 19, 25`,
with first descents at steps `7, 2, 1, 4, 2`. The third-party Lean project
states the same five seeds at length eight as a theorem
(`paradoxical_eight_iff`); the agreement is a cross-check of this tool.

The hardened verifier (`tests/adversarial.rs`) rejects
`ThresholdException { parity: "11101001", n: 7 }` with the reason that the
coefficient already crosses at step 7.

Results reported by Rozier and Terracol (arXiv v5 statements checked, large
computations not rerun): exactly 593
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
| parity prefix, affine form, residue class modulo `2^k` | parity vectors and their congruence classes | Terras 1976, Theorems 1.1–1.2 |
| first-descent certificate with threshold `N0` | classes of coefficient stopping time `k`; "all sufficiently large" members have stopping time `k` | Terras Theorem 1.9; Theorem C in Lagarias |
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

1. **CST.** For every first coefficient crossing `p` of length `k >= 2593`:
   `c(p) < (2^k - 3^r) m(p)`, where `m(p)` is the least member `>= 2`. Open.
   (The historical argument covers lengths up to 2592, section 5; this is
   a lower bound on the remaining search domain, not a claim of the best
   current bound.)
2. **Finiteness of `tau`.** For every `n >= 2` some prefix has
   `3^(r_j) < 2^j`. Open; not supplied by the threshold argument in 1. No logical
   independence theorem is claimed.
3. Neither 1 nor 2 is approached by counting classes: the counts in section 8
   are exact but carry no information about a particular integer.
