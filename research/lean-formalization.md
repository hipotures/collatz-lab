# Phase 4: Lean 4 Formalization of the 4-Automatic Mahler Parity Word Proof

**Companion Paper:** [`research/mahler-collatz-parity.md`](mahler-collatz-parity.md)  
**Rust Verification Suite:** [`src/mahler.rs`](../src/mahler.rs)  
**Lean 4 Root Module:** [`CollatzLab.lean`](../CollatzLab.lean)

---

## 1. Executive Summary and Scope Quarantine

This document records the complete, kernel-verified **Lean 4** formalization of the mathematical results in [`research/mahler-collatz-parity.md`](mahler-collatz-parity.md). Every lemma, proposition, theorem, and corollary in Sections 3, 4, 6, and 7 of the paper has been formalized and checked by the Lean 4 kernel (`leanprover/lean4:v4.18.0`) using only Lean's standard `Init` library, with:

- **Zero `sorry` or `admit` placeholders**
- **Zero user-declared `axiom` or `opaque` assumptions**
- **Zero `unsafe` declarations**
- **Zero `native_decide` trust escapes**

### Scope Quarantine (What Is and Is Not Proved)

1. **What is machine-checked in Lean 4:**
   - The 4-automatic parity word $w : \mathbb{N} \to \mathbb{Z}$ satisfies the prefix survival inequality $3^{S(k)} > 2^k$ for all $k \ge 1$ (`CollatzLab.all_prefixes_survive`) and is not eventually periodic (`CollatzLab.w_not_eventually_periodic`).
   - Every rational $2$-adic seed $x = p/q \in \mathbb{Z}_{(2)}$ ($p, q \in \mathbb{Z}$, $q > 0$ odd) whose accelerated Collatz parity itinerary matches $w$ satisfies the finite Mahler prefix identities, the cancelled backward tower recurrence $(D_k, u_k)$ with $D_k > 0$ odd and $a_k^2 \mid \Delta_k$, the $n = 2$ Padé linear form identity $2\text{-adic valuation } v_2(E_k) = 14 \cdot 4^k$, and the Archimedean height bound $|E_k| < 3 H_0 \cdot 3^{19 \cdot 4^k}$.
   - **Primary Theorem (`CollatzLab.no_rational_seed_realizes_w`):** No rational $2$-adic seed $x = p/q$ ($p, q \in \mathbb{Z}$, $q > 0$ odd) realizes $w$.
   - **Shifted-Itinerary Corollary (`CollatzLab.no_rational_seed_realizes_shifted_w`, `CollatzLab.no_eventually_shifted_w_itinerary`):** For every shift $t \ge 0$, no rational $2$-adic seed realizes $w^{(t)}(n) = w(t+n)$, and no rational $2$-adic or integer Collatz trajectory can ever enter $w^{(t)}$ after $s \ge 0$ steps.
2. **What is NOT claimed:**
   - This formalization applies to the specific explicit $4$-automatic word $w$ and its shifts $w^{(t)}$, where the backward Mahler tower $(a_k, b_k) = (16^{4^k}, 27^{4^k})$ is algebraically self-similar.
   - It does **not** prove the general Collatz conjecture, the general Lagarias Periodicity Conjecture ($\Phi(\mathbb{Q} \cap \mathbb{Z}_2) = \text{Per}(T)$), or Cycle Survival Termination (CST).

---

## 2. Architecture and Design Decisions

| Component | Path | Contents |
|---|---|---|
| Toolchain configuration | [`lean-toolchain`](../lean-toolchain), [`lakefile.toml`](../lakefile.toml) | Pinned to `leanprover/lean4:v4.18.0` (`Init` only; zero external dependencies). |
| Root library export | [`CollatzLab.lean`](../CollatzLab.lean) | Exports `Word`, `Prefix`, `Tower`, `Pade`, and `Shifted`. |
| Automatic word & survival | [`CollatzLab/Word.lean`](../CollatzLab/Word.lean) | Definition of $w$, Lemma 3.1, Theorem 3.1, Theorem 3.2, and rational $2$-adic itinerary definitions (`numStep`, `numIter`, `seedParity`, `RealizesWord`, `numIter_equiv`). |
| Finite prefix functional equation | [`CollatzLab/Prefix.lean`](../CollatzLab/Prefix.lean) | Homogenised finite prefix sum `preS`, indexed sum equivalence `preS_eq_partialSum`, block recurrence `numIter_block4`, Lemma 4.2(2) (`iter4L_affine_identity`), Theorem 6.2(1) (`base_tower_identity`), and 4-block Mahler step (`preS_mahler_4L`). |
| Cancelled backward tower | [`CollatzLab/Tower.lean`](../CollatzLab/Tower.lean) | Proposition 6.1 (`uncancelled_d1_divisible_by_256`), constructive Bézout coprimality (`isBezout_aTower_bTower`), closed-form exponents, Theorem 6.2(2) (`dTower_pos_and_odd`), and Theorem 6.2(3) (`tower_congruence_all`, `deltaTower_exact_div`). |
| Padé $(2, 2)$ forms & diophantine contradiction | [`CollatzLab/Pade.lean`](../CollatzLab/Pade.lean) | Polynomial identity `pade4_identity`, Theorem 7.1(1) (`eForm_odd_multiple_of_aTower14`, `theorem_7_1_part1`), Theorem 7.1(2) (`hTower_closed_bound`, `eForm_upper_bound`), and Theorem 7.1(3) (`exponential_bound_from_seed`, `no_rational_seed_realizes_w`, `no_int_seed_realizes_w`). |
| Shifted words & preimage closure | [`CollatzLab/Shifted.lean`](../CollatzLab/Shifted.lean) | Inverse branch maps `invBranchNum`, `invBranchDen`, Lemma 7.2 (`invBranch_step_props`, `realizes_shiftWord_pred`), and Corollary 7.3 (`no_rational_seed_realizes_shifted_w`, `no_eventually_shifted_w_itinerary`). |

### Key Formalization Techniques

1. **Fuel-Based Structural Recursion for $w$ and $v_2$:**
   Defining `w n := wAux n n` and `v2Nat n := v2NatAux n n` by structural recursion on a fuel parameter avoids `WellFounded.fix`. As a result, concrete evaluations reduce definitionally in the Lean kernel (`rfl` / `decide`), and inductive steps follow cleanly from fuel invariance (`wAux_eq`, `v2NatAux_eq`).
2. **Homogenised Integer Polynomials Everywhere:**
   Rather than working over $\mathbb{Q}_2$ and $\mathbb{R}$ simultaneously, every congruence in Sections 4, 6, and 7 is formalized in cleared-denominator homogenised integer form (`preS a b L = a^{L-1} b^{L-1} S_k(a/b)`). This makes both the $2$-adic divisibility $a_k^{14} \mid E_k$ and the Archimedean inequality $|E_k| < 3 H_0 \cdot 3^{19 \cdot 4^k}$ statements in $\mathbb{Z}$ that meet directly in `absInt_ge_of_dvd_of_ne_zero`.
3. **Constructive Bézout Certificates for $(16^{4^k}, 27^{4^k})$:**
   Instead of importing a general GCD/unique-factorization library, `CollatzLab/Tower.lean` begins from the base Bézout identity $(-5) \cdot 16 + 3 \cdot 27 = 1$ (`isBezout_16_27`) and lifts coprimality through arbitrary powers via constructive binomial/telescoping witnesses (`IsBezout.pow_left`, `IsBezout.pow_right`), yielding Euclid's lemma (`IsBezout.dvd_of_dvd_mul_left`) in ~60 lines of self-contained Lean.

---

## 3. Paper-to-Lean Theorem Mapping

| Paper Reference (`research/mahler-collatz-parity.md`) | Mathematical Statement | Lean 4 Declaration | File |
|---|---|---|---|
| **Definition of $w$** (Section 3.1) | $w(0)=1$, $w(4m)=w(m)$, $w(4m+1)=1$, $w(4m+2)=1$, $w(4m+3)=0$ | `CollatzLab.w` | [`CollatzLab/Word.lean`](../CollatzLab/Word.lean) |
| **Lemma 3.1** | Exact 4-aligned recurrence relations and binary range $w(n) \in \{0,1\}$ | `CollatzLab.w_zero`, `CollatzLab.w_mul4`, `CollatzLab.w_mul4_add1`, `CollatzLab.w_mul4_add2`, `CollatzLab.w_mul4_add3`, `CollatzLab.w_binary` | [`CollatzLab/Word.lean`](../CollatzLab/Word.lean) |
| **Theorem 3.1** (Prefix survival) | For all $k \ge 1$, $4 \cdot S(k) \ge 3k + 1$ and $3^{S(k)} > 2^k$ | `CollatzLab.all_prefixes_survive_strong`, `CollatzLab.all_prefixes_survive` | [`CollatzLab/Word.lean`](../CollatzLab/Word.lean) |
| **Theorem 3.2** (Aperiodicity) | $w$ is not eventually periodic ($\neg \exists M, p \ge 1, \forall n \ge M, w(n+p) = w(n)$) | `CollatzLab.w_not_eventually_periodic` | [`CollatzLab/Word.lean`](../CollatzLab/Word.lean) |
| **Rational $2$-adic itinerary** (Section 2) | Denominator-preserving step $T(p/q) = \text{numStep}(q,p)/q$, parity $v(j) = p_j \bmod 2$, fraction equivalence invariance | `CollatzLab.numStep`, `CollatzLab.numIter`, `CollatzLab.seedParity`, `CollatzLab.RealizesWord`, `CollatzLab.numIter_equiv` | [`CollatzLab/Word.lean`](../CollatzLab/Word.lean) |
| **Lemma 4.2(1)** (4-step block recurrence) | $4 \mid (11 p_{4m} + 23 q)$ and $16 p_{4(m+1)} = 27 p_{4m} + (23 - 4 w(m)) q$ | `CollatzLab.numIter_block4`, `CollatzLab.four_dvd_eleven_p_add_23_q`, `CollatzLab.blockQuotient_step` | [`CollatzLab/Prefix.lean`](../CollatzLab/Prefix.lean) |
| **Lemma 4.2(2)** ($4L$-step affine identity) | $11(16^L p_{4L} - 27^L p) = (23(27^L - 16^L) - 44\,\text{preS}(16,27,L)) q$ | `CollatzLab.iter4L_affine_identity`, `CollatzLab.preS_eq_partialSum` | [`CollatzLab/Prefix.lean`](../CollatzLab/Prefix.lean) |
| **Mahler 4-block step** (Section 4.3) | $\text{preS}(a,b,4L) = c(a,b) b^{3L} \text{preS}(a^4,b^4,L) + a b (b-a) \frac{b^{4L}-a^{4L}}{b^4-a^4}$ | `CollatzLab.preS_mahler_4L` | [`CollatzLab/Prefix.lean`](../CollatzLab/Prefix.lean) |
| **Proposition 6.1** (Uncancelled $D_k$ refutation) | For odd $q$, the uncancelled denominator $D_1^{\text{raw}} = (11q) c(16,27)(27^4 - 16^4)$ satisfies $256 \mid D_1^{\text{raw}}$ (hence is even) | `CollatzLab.uncancelled_d1_divisible_by_256` | [`CollatzLab/Tower.lean`](../CollatzLab/Tower.lean) |
| **Theorem 6.2(1)** (Base congruence, $k=0$) | $b_0^{L-1} u_0 - D_0\,\text{preS}(a_0,b_0,L) = a_0^L q_L \equiv 0 \pmod{a_0^L}$ for all $L \ge 1$ | `CollatzLab.base_tower_identity` | [`CollatzLab/Prefix.lean`](../CollatzLab/Prefix.lean) |
| **Theorem 6.2(2)** (Oddness & positivity of $D_k$) | For $q > 0$ odd and $D_{k+1} = D_k(b_k - a_k)(b_k^4 - a_k^4)$, every $D_k > 0$ and $D_k \equiv 1 \pmod 2$ | `CollatzLab.dTower_pos_and_odd` | [`CollatzLab/Tower.lean`](../CollatzLab/Tower.lean) |
| **Theorem 6.2(3)** (Divisibility $a_k^2 \mid \Delta_k$ & tower induction) | $a_k^2 \mid \Delta_k$, $a_k^2 u_{k+1} = b_k^3 \Delta_k$, and $a_k^L \mid (b_k^{L-1} u_k - D_k\,\text{preS}(a_k,b_k,L))$ for all $k \ge 0, L \ge 1$ | `CollatzLab.deltaTower_dvd_of_level_k`, `CollatzLab.tower_congruence_step`, `CollatzLab.tower_congruence_all`, `CollatzLab.deltaTower_exact_div` | [`CollatzLab/Tower.lean`](../CollatzLab/Tower.lean) |
| **Theorem 7.1(1)** (Padé $(2,2)$ identity & valuation) | Algebraic identity for $E_k = D_k P_0(a_k,b_k) + u_k P_1(a_k,b_k)$, $E_k = a_k^{14} \cdot m_{\text{odd}}$ ($m_{\text{odd}}$ odd), $E_k \ne 0$, and $v_2(|E_k|) = 14 \cdot 4^k$ | `CollatzLab.pade4_identity`, `CollatzLab.eForm_odd_multiple_of_aTower14`, `CollatzLab.theorem_7_1_part1` | [`CollatzLab/Pade.lean`](../CollatzLab/Pade.lean) |
| **Theorem 7.1(2)** (Height recurrence & upper bound) | $H_{k+1} \le b_k^7 H_k$, $H_k < H_0 \cdot 3^{7 \cdot 4^k}$, and $|E_k| \le 3 b_k^4 H_k < 3 H_0 \cdot 3^{19 \cdot 4^k}$ | `CollatzLab.tower_cubic_ratio_bound`, `CollatzLab.hTower_step`, `CollatzLab.hTower_closed_bound`, `CollatzLab.eForm_upper_bound` | [`CollatzLab/Pade.lean`](../CollatzLab/Pade.lean) |
| **Theorem 7.1(3) & Primary Theorem** | $2^{25 \cdot 4^k} < 3 H_0$ for all $k \ge 0$, hence $\neg \text{RealizesWord}(p, q, w)$ for all $p, q \in \mathbb{Z}$ | `CollatzLab.exponential_bound_from_seed`, `CollatzLab.no_rational_seed_realizes_w`, `CollatzLab.no_int_seed_realizes_w` | [`CollatzLab/Pade.lean`](../CollatzLab/Pade.lean) |
| **Lemma 7.2** (Inverse parity branches) | $T_0^{-1}(p/q) = (2p)/q$ and $T_1^{-1}(p/q) = (2p-q)/(3q)$ map a seed realizing $w^{(t+1)}$ to a seed realizing $w^{(t)}$ | `CollatzLab.invBranch_step_props`, `CollatzLab.realizes_shiftWord_pred` | [`CollatzLab/Shifted.lean`](../CollatzLab/Shifted.lean) |
| **Corollary 7.3** (Shifted parity words) | For all $t \ge 0$ and $p, q \in \mathbb{Z}$, $\neg \text{RealizesWord}(p, q, w^{(t)})$, and no orbit enters $w^{(t)}$ after $s \ge 0$ steps | `CollatzLab.no_rational_seed_realizes_shifted_w`, `CollatzLab.no_int_seed_realizes_shifted_w`, `CollatzLab.no_eventually_shifted_w_itinerary`, `CollatzLab.no_int_orbit_enters_shifted_w` | [`CollatzLab/Shifted.lean`](../CollatzLab/Shifted.lean) |

---

## 4. Axiom Audit (`#print axioms`)

Running `lake env lean` with `#print axioms` on the exported theorems produces:

```text
'CollatzLab.w_mul4' depends on axioms: [propext, Quot.sound]
'CollatzLab.w_mul4_add1' depends on axioms: [propext, Quot.sound]
'CollatzLab.w_mul4_add2' depends on axioms: [propext, Quot.sound]
'CollatzLab.w_mul4_add3' depends on axioms: [propext, Quot.sound]
'CollatzLab.w_binary' depends on axioms: [propext, Quot.sound]
'CollatzLab.all_prefixes_survive_strong' depends on axioms: [propext, Quot.sound]
'CollatzLab.all_prefixes_survive' depends on axioms: [propext, Quot.sound]
'CollatzLab.w_not_eventually_periodic' depends on axioms: [propext, Quot.sound]
'CollatzLab.iter4L_affine_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollatzLab.base_tower_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollatzLab.preS_mahler_4L' depends on axioms: [propext, Quot.sound]
'CollatzLab.uncancelled_d1_divisible_by_256' depends on axioms: [propext, Quot.sound]
'CollatzLab.isBezout_aTower_bTower' depends on axioms: [propext, Quot.sound]
'CollatzLab.dTower_pos_and_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollatzLab.tower_congruence_all' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollatzLab.deltaTower_exact_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollatzLab.pade4_identity' depends on axioms: [propext, Quot.sound]
'CollatzLab.eForm_odd_multiple_of_aTower14' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollatzLab.theorem_7_1_part1' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollatzLab.hTower_closed_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollatzLab.eForm_upper_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollatzLab.no_rational_seed_realizes_w' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollatzLab.no_int_seed_realizes_w' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollatzLab.realizes_shiftWord_pred' depends on axioms: [propext, Quot.sound]
'CollatzLab.no_rational_seed_realizes_shifted_w' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollatzLab.no_eventually_shifted_w_itinerary' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every theorem depends solely on Lean 4's foundational axioms (`propext`, `Quot.sound`, and `Classical.choice` from `omega` case-splits on Euclidean integer division).

---

## 5. Reproduction Commands

With [`elan`](https://github.com/leanprover/elan) installed (the pinned toolchain `leanprover/lean4:v4.18.0` in [`lean-toolchain`](../lean-toolchain) is fetched automatically):

```bash
# Build and kernel-verify the entire Lean 4 library
lake build

# Verify that no forbidden keywords appear in the Lean sources
! grep -rnE '\b(sorry|admit|axiom|unsafe|native_decide)\b' CollatzLab CollatzLab.lean

# Run the axiom audit
lake env lean --stdin <<'EOF'
import CollatzLab
#print axioms CollatzLab.all_prefixes_survive
#print axioms CollatzLab.w_not_eventually_periodic
#print axioms CollatzLab.tower_congruence_all
#print axioms CollatzLab.theorem_7_1_part1
#print axioms CollatzLab.eForm_upper_bound
#print axioms CollatzLab.no_rational_seed_realizes_w
#print axioms CollatzLab.no_rational_seed_realizes_shifted_w
#print axioms CollatzLab.no_eventually_shifted_w_itinerary
EOF
```
