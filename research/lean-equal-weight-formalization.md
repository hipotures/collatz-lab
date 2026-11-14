# Generic equal-weight formalization: partial, Theorem 8.1 NOT VERIFIED

Phase 7 B, 2026-11-14 UTC. The modules below are accepted by the Lean 4.18.0
kernel. **The generic irrationality theorem is incomplete.** No finite
catalogue or conditional helper is presented as Theorem 8.1.

## Completed generic components

`CollatzLab.Morphism.Images L` stores `zero, one : Fin L → Bool`.
`image` extends each finite image by false outside its length; every theorem
about a block uses offsets strictly below `L`. `word` is the fuelled fixed
point starting at true, `parityWord` converts it to the original integer-valued
parity interface. No numerator or denominator enters this definition.

`MorphismWord.lean` proves, for every `L>=2` and `image M true 0=true`:

```lean
word_block ... (n j : Nat) (hj : j < L) :
  word M (L*n+j) = image M (word M n) j

word_unique ... (v : Nat → Bool) (hv0 : v 0 = true)
  (hv : ∀ n j, j < L → v (L*n+j) = image M (v n) j) : v = word M

literal_block ... (n : Nat) :
  List.ofFn (fun j : Fin L => word M (L*n+j.val)) =
  List.ofFn (fun j : Fin L => if word M n then M.one j else M.zero j)
```

Starting-symbol uniqueness is essential: `10/01` also has a fixed point
starting in zero. `weight_positive`, `one_has_zero`, `weight_lt_length` prove
`1<=r<L` from exactly H1–H3. `affine_prefix` derives ordinary integer block
arithmetic directly from signed `numStep`, for every positive or negative
numerator and odd denominator.

`MorphismPrefix.lean` defines homogeneous finite sums `pre`, the two image
polynomials `Q M false`, `Q M true`, and their difference `Gamma`. It proves:

```lean
prefix_mahler ... (a b : Int) : ∀ n,
  (b^L-a^L)*pre M a b (L*n) =
    Q M false a b*(b^(L*n)-a^(L*n)) +
    Gamma M a b*(b^L-a^L)*pre M (a^L) (b^L) n
```

This identity is unconditional in integer `a,b`; no real ordering or analytic
convergence is assumed. The equal-weight affine block theorem and
unnormalized all-length base identity are also proved from `RealizesWord`.
With `c_b=offset(image M b) L`, `A=2^L`, `B=3^r` and
`g_n=(B-A)*numIter q p (L*n)+c_0*q`, the latter is exactly

```text
B^(n-1)*(B*g_0) - ((B-A)*(c_0-c_1)*q)*pre M A B n = A^n*g_n.
```

`MorphismParameters.lean` defines computable canonical `t,s,e,N` and criterion
(C). `t_bounds` proves `1<=t<L`. Concrete reductions verify the admissible
`110/011` instance satisfies (C), `10/01` is admissible and fails (C), and
`101/011` fails (C). Failing a sufficient condition has no irrationality
conclusion.

`MorphismOffset.lean` proves the exact signed offset assertion generically:

```lean
offsets_odd_multiple {L : Nat} (M : Images L)
  (hw : weight (image M false) L = weight (image M true) L)
  (hd : M.zero ≠ M.one) :
  ∃ kappa : Int, kappa % 2 = 1 ∧
    c M false - c M true = (2 : Int)^s M * kappa
```

It uses an independent concatenation formula for affine offsets: equal total
weights cancel the shared-prefix contribution, leaving `2^s` times a tail
offset difference whose parity is odd. Thus signs are handled without
assuming `A<B` or `c_0>c_1`. `first_disagreement` proves, under exactly H1–H3,
agreement with the periodic image of `1` at every index below `N=L*t+s` and
disagreement at `N`.

## Exact remaining obligations

The first unproved component is the **normalized generic tower**, not a
failure of the fixed-point or seed identity. Required targets, in the notation
of §8 (not yet executable definitions):

```text
Gamma_h(a,b) = a^s * b^(L-1-e) * GammaStar_h(a,b),
GammaStar_h(a,b) odd and nonzero for even a, odd b.

For every k,n>=1:
a_k^n | b_k^(n-1)*u_k - D_k*pre M a_k b_k n,
D_k>0 and D_k odd,
a_k^s | delta_k,
a_k^s * sigma_k*u_(k+1) = b_k^e*delta_k,
sigma_k in {-1,1},
D_(k+1)=D_k*abs(GammaStar_h(a_k,b_k))*abs(b_k^L-a_k^L).
```

The normalized initial step must prove `2^s | g_0`, choose the sign so that
`D_0=abs(B-A)*abs(kappa)*q`, and transport the full congruence using an old
length **larger than `L*n`** before dividing by `a^s`. The family proof's
transport at `L*(n+1)` is the model, but its positive factors `(b-a)` and
`(b^L-a^L)` cannot simply be reused: both signs are allowed here.

After this come (1) homogenized residual with odd leading term and exact
valuation `N*L^(k+1)`, (2) the general height bound including `(2L)^k`,
(3) a kernel proof that the strict integer base gap in (C) dominates that
factor for every initial height, and (4) the rational theorem and shift
corollaries. The factor `(2L)^k` cannot be discarded without proof.
`s<e<L` also still needs a symbolic theorem (equal weight rules out a single
disagreement); the canonical positions and exact first disagreement already
compile without that unused bound.

These are open formal proof goals, not assumed propositions inside a public
irrationality theorem. There are no incomplete imported proofs or new
unproved assumptions. B remains incomplete until all of them are discharged.

## Validation

Run `lake build` and `lake env lean research/lean-audit/FamilyAudit.lean`.
The audit now includes 70 declarations (18 generic statements added to A's 52),
with only standard foundational dependencies. The full Rust suite remains 90
passing tests; formatting, Clippy and the forbidden-proof-escape scan pass.
The campaign journal records commit and CI checkpoints.
