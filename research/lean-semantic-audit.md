# Phase 5, Gate A: adversarial semantic and proof audit of Lean PR #9

**Object audited:** [PR #9](https://github.com/hipotures/collatz-lab/pull/9) at commit
`ec67222eb3453f0ae32a08928b04e763783e4aa8` (branch `codex/issue-lean-mahler`), read-only.
**Issue:** [#10](https://github.com/hipotures/collatz-lab/issues/10), Gate A.
**Auditor's checks:** [`lean-audit/AuditChecks.lean`](lean-audit/AuditChecks.lean) (17 new
kernel-checked statements about the PR's definitions), an independent Python recomputation,
and the PR's own Rust suite.

## 1. Verdict

| Question | Classification |
|---|---|
| Does `CollatzLab.no_rational_seed_realizes_w` state the intended theorem (no rational with odd denominator has accelerated-Collatz parity itinerary `w`)? | **verified** |
| Is the Lean word `w` the fixed point of `mu(1)=1110, mu(0)=1101`? | **verified** |
| Is `RealizesWord` a faithful, non-vacuous model of the accelerated map on `Z_2 ∩ Q`? | **verified** |
| Is the dependency chain free of hidden hypotheses, division artifacts and exponent slips? | **verified** (by reading every proof on the path; see §4) |
| Shifted-word and inverse-branch statements | **verified** |
| Axioms, forbidden constructs, clean rebuild, Rust suite | **verified** locally (see §6) |
| `research/lean-formalization.md`, `CollatzLab.lean` header, README section, PR body | **repairable documentation** — nine defects, two of which state mathematically false facts (§7) |
| CI axiom gate | **repairable** — it is a deny-list, not an allow-list (§6.3) |
| Critical proof or semantics defect | **none found** |

Gate A does not block Gate B. The documentation conflict flagged in the issue is a
documentation-only defect: the false recurrence and the false inequality appear only in
prose, and the kernel-checked statements contradict them (§7, D2 and D3).

What this audit is not: it is one reader plus mechanical checks. No second kernel
(`lean4checker`) was run, because the pinned toolchain `v4.18.0` ships no `leanchecker`
binary on the audit machine. The trusted base is therefore the Lean 4.18.0 kernel, as
for the PR itself.

## 2. The word `w` (issue item 1)

**Mathematical definition.** `w = lim mu^j(1)` with `mu(1) = 1110`, `mu(0) = 1101`;
equivalently `w(4n) = 1`, `w(4n+1) = 1`, `w(4n+2) = w(n)`, `w(4n+3) = 1 - w(n)`.

**Lean definition** (`CollatzLab/Word.lean`): `w n := wAux n n`, where `wAux` recurses on
a fuel argument through `n / 4` and `n % 4` with the four cases above, and returns `1` at
`n = 0` or at fuel `0`. Fuel `n` suffices because `n / 4 < n` for `n ≥ 1`
(`wAux_eq_of_le`, `wAux_ge`).

Independent checks, all kernel-accepted in `AuditChecks.lean`:

| Check | Statement | Result |
|---|---|---|
| `w_is_mu_fixed_point` | `w (4n + r) = muBlock (w n) r` for `r < 4`, with `muBlock` spelling out `1110` / `1101` | proved |
| `w_unique` | any `v` satisfying the four recurrences equals `w` everywhere | proved |
| `w_prefix_256_eq_mu_iterate` | `(List.range 256).map w = mu(mu(mu(mu([1]))))` with `mu` implemented on lists | `decide`, no axioms |
| `w_prefix_64_explicit` | the first 64 symbols, written out | `decide` |

The explicit 64-symbol check is worth a remark. My first hand-written list had a wrong last
block (`1101 1101 1101 1110` in place of `1110 1110 1101 1110`), and the kernel rejected it
(`decide proved that the proposition is false`). The check is therefore discriminating.

**Rust generator** (`src/mahler.rs`): `mu_word_by_substitution` iterates the substitution,
`mu_bit_by_recurrence` uses the recurrence, and `verify_word_and_all_prefix_survival`
compares them index by index. Neither file hard-codes a prefix.

**Third implementation** (Python, standard library, written for this audit): the residues
of `x(w)` modulo `2^16`, `2^32` and `2^64` were computed by the parity-position series,
by bit-by-bit lifting, and by the closed formula `-23/11 + (4/27) F(16/27)`:

```text
x mod 2^16 = 25319
x mod 2^32 = 2437374695
x mod 2^64 = 9941361107984147175
```

The first two equal `residue_*` in the committed `research/mahler/evidence.json`
(checkpoints `K = 16, 32`). The third is used as a Lean witness in §3.

## 3. `RealizesWord` (issue items 1 and 2)

```lean
def numStep (q p : Int) : Int := if p % 2 = 0 then p / 2 else (3 * p + q) / 2
def numIter (q p : Int) : Nat → Int | 0 => p | j + 1 => numStep q (numIter q p j)
def seedParity (q p : Int) (j : Nat) : Int := (numIter q p j) % 2
def RealizesWord (p q : Int) (v : Nat → Int) : Prop :=
  q > 0 ∧ q % 2 = 1 ∧ ∀ j : Nat, seedParity q p j = v j
```

**Faithfulness.** For `x = p/q` with `q` odd, `x` is even in `Z_2` exactly when `p` is
even. Then `T(x) = x/2 = (p/2)/q`, and otherwise `T(x) = (3x+1)/2 = ((3p+q)/2)/q`, where
`3p + q` is even because both are odd. So `T` preserves the denominator `q`, and
`numStep q` is `T` on numerators. This is what the Lean definitions say, provided the
divisions are exact and `%` is a true parity:

- `numStep_eq` proves `2 * numStep q p = p` (even `p`) and `= 3 * p + q` (odd `p`) for odd `q`.
  Both numerator branches are exact.
- Lean core `Int` uses Euclidean `/` and `%`. `AuditChecks.int_div_mod_are_euclidean`
  checks `(-7) / 2 = -4` and `(-7) % 2 = 1`, so parity is in `{0, 1}` for negative
  numerators (`seedParity_binary`), and `numStep 11 (-19) = -23` matches `T(-19/11) = -23/11`.
- `numIter_equiv` proves that equivalent fractions `p/q = p'/q'` (both denominators odd)
  have equal itineraries. `RealizesWord` does not require `gcd(p, q) = 1`, which only makes
  the excluded set larger.
- `numIter_one` identifies the case `q = 1` with the integer map `tIterInt`.

The domain is all of `Z_2 ∩ Q`: every `p ∈ Z` and every odd `q > 0`. Negative rationals
are included.

**Not vacuous.** A theorem of the form `¬ RealizesWord p q w` would be worthless if the
predicate were unsatisfiable for an accidental reason (for example a word leaving `{0,1}`,
or a parity convention that no orbit can meet). Three witnesses rule this out:

| Check | Statement |
|---|---|
| `realizes_trivial_cycle` | `RealizesWord 1 1 (10)^∞`: the positive integer `1` realizes an infinite word |
| `realizes_periodic_control` | `RealizesWord (-19) 11 (1110)^∞`: a rational realizes a word that agrees with `w` on its first 14 symbols |
| `finite_prefix_witness` | `∀ j < 64, seedParity 1 9941361107984147175 j = w j`, by `decide` with no axioms |

The last line is the finite parity-prefix realization by a positive integer requested in the
issue; `finite_prefix_witness_grows` adds `T^64(n) > n`. Together with `w_binary` this
shows that the theorem excludes something that is finitely approachable at every depth and
that the same predicate accepts the periodic control. The difference between `w` and the
control is exactly what the Mahler/Padé argument detects.

**Scope of the formal statement.** The theorem is a statement about rationals. It does not
mention `Z_2`, the series `F_2`, or the map `Φ`. Reading it as "the 2-adic number `x(w)` is
irrational" uses the standard, unformalized fact that the parity vector determines the
2-adic integer. The Lean statement itself needs no such fact.

## 4. Dependency path of `no_rational_seed_realizes_w` (issue item 2)

```text
no_rational_seed_realizes_w
├─ exponential_bound_from_seed            2^(25·4^k) < 3·H_0 for every k
│  ├─ theorem_7_1_part1                   2^(56·4^k) ≤ |E_k|
│  │  └─ eForm_odd_multiple_of_aTower14   E_k = a_k^14 · (odd)
│  │     ├─ tower_congruence_all          a_k^L | b_k^(L-1) u_k − D_k preS(a_k, b_k, L)
│  │     │  ├─ base_tower_identity ← blockQuotient_step ← numIter_block4 ← numIter_step_eq
│  │     │  └─ tower_congruence_step ← deltaTower_dvd_of_level_k, preS_mahler_4L, IsBezout.*
│  │     ├─ pade4_identity, pade_linear_form_factor
│  │     └─ dTower_pos_and_odd, abTower_invariants
│  ├─ eForm_upper_bound                   |E_k| < 3·H_0·3^(19·4^k)
│  │  ├─ eForm_bound_aux
│  │  └─ hTower_closed_bound ← hTower_step ← height_step_aux, deltaTower_exact_div
│  └─ pow25_mul_pow19_le_pow56            2^25 · 3^19 ≤ 2^56 (by `decide`)
└─ nat_lt_pow4, nat_lt_pow2               K < 2^(25·4^K) with K = toNat (3·H_0)
```

I read every proof on this path. Findings, organised by the failure modes named in the issue:

- **Hidden hypotheses.** None. `#check` prints
  `∀ (p q : Int), ¬ RealizesWord p q w`. Every intermediate lemma takes only
  `hreal : RealizesWord p q w`, or is a parametric identity with explicit numeric hypotheses
  (`a ≥ 16`, `b ≥ 27`, `27 a ≤ 16 b`, `D > 0`) discharged by `abTower_invariants` and
  `dTower_pos_and_odd`.
- **Integer-division artifacts.** There are three truncating divisions, and each has an
  exactness lemma on the path:
  `numStep` (`/ 2`, exact by `numStep_eq`);
  `blockQuotient` and `uTower _ _ 0` (`/ 4`, exact by `four_mul_blockQuotient`, which needs
  `hreal`);
  `uTower _ _ (k+1)` (`/ a_k^2`, exact by `deltaTower_dvd_of_level_k`, which rewrites the
  quotient as `a_k^2 * u_{k+1} = b_k^3 * Δ_k` before anything is bounded).
  The base case of `tower_congruence_all` unfolds `uTower p q 0` to
  `27 * blockQuotient p q 0` definitionally, so the same floor expression is used on both sides.
- **Exponent and valuation conventions.** `aTower_eq_pow2`: `a_k = 2^(4·4^k)`;
  `aTower14_eq_pow2`: `a_k^14 = 2^(56·4^k)`; `bTower_eq_pow3`: `b_k = 3^(3·4^k)`;
  `b_k^7 = 3^(21·4^k)`, `b_k^4 = 3^(12·4^k)`; the telescoping exponent
  `21·4^k + 7(4^k − 1) = 7(4^(k+1) − 1)` is proved with the truncated subtraction guarded by
  `pow4_ge_one`. `v2Int` is defined with `v2Nat 0 = 0`; the theorem also states `E_k ≠ 0` and
  the two explicit divisibility facts, so nothing rests on that convention.
- **Modulus conversions.** `preS a b L` is `∑_{j<L} w(j) a^j b^(L−1−j)`
  (`preS_eq_partialSum`); the exponent `L − 1` is used only under `L ≥ 1`. The step from
  modulus `a_k^(4L+4)` to `a_{k+1}^L` cancels `a_k^2` by `dvd_cancel_left_of_pos` and `b_k`,
  `b_{k+1}` by the constructive Bézout lemma, which is the argument of the paper proof.
- **Overly strong or mis-specified lemmas.** None found. `pade4_identity` is proved by
  unfolding the first 15 values of the actual `w`, so it cannot silently refer to a different
  word. `uncancelled_d1_divisible_by_256` has two conjuncts that are stated for `q = 1` only
  (`dTowerUncancelled 1 1 % 256 = 0`, `% 512 ≠ 0`); this is weaker than its docstring's
  "`v_2(D_1) = 8`" for general odd `q`, but it is off the main path.
- **Final contradiction.** With `K = toNat (3·H_0)`: `2^(25·4^K) < 3·H_0 = K < 4^K ≤ 25·4^K < 2^(25·4^K)`.
  `H_0 > 0` is derived from `q > 0`, so `toNat` is exact.

**A posteriori vacuity is inherent, not a defect.** Since no seed exists, every lemma with
hypothesis `hreal` is vacuously true in hindsight. Two things guard against a chain that is
"consistent but about the wrong object": the hypothesis-free identities (`preS_mahler_4L`,
`pade4_identity`, `height_step_aux`, `IsBezout.*`) are meaningful on their own, and the
Rust suite checks the same tower identities on the truncated seeds `x_K` up to level 2
(`tests/mahler.rs`).

## 5. Inverse branches and shifts (issue item 3)

`invBranchNum b p q` and `invBranchDen b q` implement `T_0^{-1}(p/q) = 2p/q` and
`T_1^{-1}(p/q) = (2p − q)/(3q)`. `invBranch_step_props` proves, for `b ∈ {0,1}` and odd
`q > 0`: the new denominator is positive and odd, the new parity is `b`, and one forward
step returns a fraction equal to `p/q` (`numStep q' p' * q = p * q'`).
`realizes_shiftWord_pred` then uses `numIter_equiv` to pass from that equal fraction to
`(p, q)`. This is the same `numStep` as in the main theorem, so the shift result is about the
same map. `no_rational_seed_realizes_shifted_w` is the induction on `t`, and
`no_eventually_shifted_w_itinerary` adds the forward direction through `seedParity_add`.

Scope: these exclude the countable set of words that eventually coincide with a tail of `w`.
They say nothing about other survivor words.

## 6. Reproduction on the audit machine

### 6.1 Commands and results (commit `ec67222`, worktree clean before and after)

| Command | Result |
|---|---|
| `lean --version`, `lake --version` | Lean 4.18.0, Lake 5.0.0-11ccbce |
| `rm -rf .lake/build && lake build` | exit 0, no warnings, no errors (about 21 s) |
| `cargo fmt --check` | exit 0 |
| `cargo clippy --locked --all-targets --all-features -- -D warnings` | exit 0 (cargo 1.100.0; incremental, not from scratch) |
| `cargo test --locked --all-targets` | 78 passed, 0 failed |
| `grep -rnE '\b(sorry\|admit\|native_decide\|unsafe\|axiom\|opaque\|implemented_by\|extern)\b' CollatzLab CollatzLab.lean` | no matches |
| `lake env lean AuditChecks.lean` | exit 0, no errors |
| GitHub Actions on the PR head | jobs `check` and `lean` both `SUCCESS` |
| independent kernel replay (`leanchecker`) | **not run**: binary absent from toolchain `v4.18.0` |

### 6.2 Axioms

`#print axioms` was run on 31 declarations of the PR (every theorem named in its mapping
table, plus `numIter_equiv`, `numIter_block4`, `exponential_bound_from_seed`,
`no_int_seed_realizes_shifted_w`, `no_int_orbit_enters_shifted_w`). Every one reports a
subset of `[propext, Classical.choice, Quot.sound]`. The 26 lines printed in
`research/lean-formalization.md` §4 are reproduced exactly. The audit's own witnesses use
at most `[propext, Quot.sound]`; the two `decide` checks use no axioms.

### 6.3 CI behaviour

The `lean` job runs a keyword grep, `lake build`, and an axiom print. Two weaknesses, neither
exploited by the current sources:

1. The axiom step fails only if the output contains `sorryAx`. A user-declared axiom or
   `Lean.ofReduceBool` would pass that step and be caught only by the keyword grep. The gate
   should be an allow-list.
2. The keyword grep omits `opaque`, `implemented_by` and `extern`.

Suggested replacement for the last step of `.github/workflows/ci.yml`:

```bash
if echo "$output" | grep -vE "^'[A-Za-z0-9_.']+' (does not depend on any axioms|depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\])$" | grep -q .; then
  echo "Unexpected axiom or malformed audit output"; exit 1
fi
```

The elan installer is fetched from the `master` branch without a pinned hash; that is a
supply-chain remark, not a proof issue.

## 7. Theorem-to-prose mapping (issue item 4)

All defects below are in prose. None changes a kernel-checked statement. Because the affected
files exist only in PR #9, they are not edited on this branch; exact patches are given instead.

| # | Location (at `ec67222`) | Defect | Evidence | Suggested text |
|---|---|---|---|---|
| D1 | `research/lean-formalization.md` lines 3, 11, 56; `README.md` line 178; `CollatzLab.lean` line 11; PR body | Companion paper `research/mahler-collatz-parity.md` does not exist at this ref or on `main` | `git ls-files` | `research/infinite-itineraries.md` (its Lemma 3.1, Theorems 3.1, 3.2, 4.1, 4.3, Lemma 4.2, Proposition 6.1, Theorems 6.2, 7.1, Lemma 7.2, Corollary 7.3 are the statements the table refers to) |
| D2 | `lean-formalization.md` line 58 | States `w(4m)=w(m)`, `w(4m+1)=1`, `w(4m+2)=1`, `w(4m+3)=0`. **False** for the Lean `w` and for the mathematical `w` | `documented_recurrence_is_false : w 14 ≠ 1`, `documented_recurrence_is_false' : w 15 ≠ 0` | `w(4m)=1`, `w(4m+1)=1`, `w(4m+2)=w(m)`, `w(4m+3)=1−w(m)` |
| D3 | `lean-formalization.md` line 60; PR body | Describes `all_prefixes_survive_strong` as `4·S(k) ≥ 3k+1`. **False** at `k = 4` (`S(4) = 3`, `12 < 13`) and not what Lean proves | `documented_strong_form_is_false` | `8·16^⌊(k−1)/4⌋·3^S(k) ≥ 9·27^⌊(k−1)/4⌋·2^k`, i.e. `3^S(k)/2^k ≥ (9/8)(27/16)^⌊(k−1)/4⌋` |
| D4 | `lean-formalization.md` lines 22, 40, 70; `CollatzLab.lean` lines 19–20 | "`n = 2` Padé", "Padé `(2,2)`", `v_2(E_k) = 14·4^k` | Lean proves `v2Int (eForm p q k) = 56 * 4^k` (`theorem_7_1_part1`); the pair is `(1+z+z^2, −1+z^4)` | "degree-4 Padé pair `(1+z+z^2, −1+z^4)` of order `N = 14`; `v_2(E_k) = v_2(a_k^14) = 56·4^k`" |
| D5 | `lean-formalization.md` line 65 | Formula for the "Mahler 4-block step" matches no Lean statement; "Section 4.3" does not exist | `preS_mahler_4L` | `(b^4−a^4)·preS(a,b,4L) = (b^3+ab^2+a^3)(b^(4L)−a^(4L)) + a^2(b−a)(b^4−a^4)·preS(a^4,b^4,L)` (homogenised Theorem 4.1) |
| D6 | `lean-formalization.md` line 66 | `D_1^raw = (11q)·c(16,27)·(27^4−16^4)` with `c` undefined | `dTowerUncancelled` | `D_1^unc = 11q·16^2·(27−16)·(27^4−16^4)`; `256 ∣ D_1^unc`; exact valuation 8 stated for `q = 1` |
| D7 | `lean-formalization.md` lines 46, 48; `CollatzLab/Shifted.lean` line 8 | Names that do not exist: `wAux_eq`, `v2NatAux_eq`, `absInt_ge_of_dvd_of_ne_zero`, `invBranch_realizes`. Also `preS a b L = a^(L−1) b^(L−1) S_k(a/b)` is wrong | `grep` | `wAux_eq_of_le`, `v2NatAux_eq_of_le`, `exponential_bound_from_seed`, `invBranch_step_props`; `preS(a,b,L) = b^(L−1) ∑_{j<L} w(j)(a/b)^j` |
| D8 | `lean-formalization.md` line 27 | Expands CST as "Cycle Survival Termination" | `research/literature-cst.md` | "Coefficient Stopping Time conjecture (CST)" |
| D9 | `lean-formalization.md` line 11; `README.md` line 178 | "Every lemma, proposition, theorem, and corollary in Sections 3, 4, 6, and 7 … has been formalized" overstates | Theorem 4.1 (identity in `Z[[z]]`), Theorem 4.3 (identity in `Z_2`) and the `Φ^{-1}` statements of Lemma 7.2(1) are not Lean statements; finite homogenised integer analogues are | "The integer statements needed for the contradiction are formalized: … . The power-series and 2-adic formulations (Theorems 4.1, 4.3) are represented by their finite homogenised analogues `preS_mahler_4L`, `iter4L_affine_identity`, `base_tower_identity`." |

Assessment of the issue's specific question: the conflicting recurrence in the mapping table
is a documentation error and does **not** signal a theorem mismatch. `w_is_mu_fixed_point`,
`w_unique` and the 256-symbol comparison tie the Lean `w` to the morphism directly.

## 8. Confidence and unresolved gaps

- **High confidence** that the kernel-checked statement is the intended one: definitions are
  short, were read in full, and were tested from outside by positive and negative witnesses.
- **High confidence** that the proof path has no extra assumptions: there is exactly one
  hypothesis on the main theorem's lemmas, and the axiom report is the standard triple.
- **Not done:** an independent kernel replay; a from-scratch `clippy` run; any review of
  Lean's elaborator beyond trusting the kernel.
- **Outside the formal statement:** the identification with the 2-adic number `x(w)`, the
  formal-series Mahler equation, and every claim about words other than `w` and its tails.
- **Recommendation:** fix D1–D9 and the CI gate in PR #9 before merging. None of them
  requires a change to a `.lean` proof.
