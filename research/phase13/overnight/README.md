# Sparse overnight height certificates

These experiments are separate from the original, 16,384-bit-capped Phase 13
engines. They use the fixed word `1 -> 100111`, `0 -> 111110`. New samples
are bounded by 600,000 bits; `heights.jsonl` is bounded by 8 MiB. There is no
network access or Git mutation in the experiment or checker.

`extended_height.py` constructs the word by an indexed substitution automaton
and the seed residue by balanced forward affine composition. Its odd-coset
optimizer maintains exact discrepancies and skips consecutive hold steps.
An optimizer result is only a candidate until independently checked.

`verify_results.py` imports no producer or other project implementation. It
constructs the word by literal substitution and its seed residue by reverse
rational inverse branches. It checks a primitive witness with positive odd
denominator, every actual numerator parity, and the lattice determinant.
Large integers are stored as canonical hexadecimal strings.

For a height bound `B`, write `t=(B+1)//2`, `M=2^N`, and
`S(t,M,a,b)=sum(floor((a*i+b)/M), i=0..t-1)`. The exact number of vectors
with `|p| <= B`, `1 <= q <= B` odd, and `p = A*q (mod M)` is

```
S(t,M,2*A,A+B) - S(t,M,2*A,A-B-1).
```

For `odd-box-floor-sum-v1`, the checker reconstructs the two Euclidean quotient transcripts at `B=H-1`,
validates all quotient remainder inequalities and terminal conditions, and
requires the difference to be zero. This counts even nonprimitive vectors;
none can conceal a smaller primitive witness. Together with the witness at
height `H`, it certifies the exact finite minimum. The counting identity and
its Euclidean recursion are proved in `research/phase13-theory.md`, Section 4.
The trust boundary is exact Python integer arithmetic plus that written
argument. This is not an additional Lean-kernel proof or an asymptotic claim.

Each sample has a signal-enforced budget (at most 180 seconds), including
independent checking before publication. A temporary file followed by atomic
replacement preserves all earlier JSONL lines byte for byte. Resuming checks
and skips every existing sample. Separate invocations should additionally
use `timeout` and a process memory cap; see the journal for commands actually
run and resource observations. A timeout can leave earlier certified lines
intact; an unpublished candidate does not count as a result.

Validation commands:

```bash
python3 -B research/phase13/overnight/test_extended.py
python3 -B research/phase13/overnight/test_basis.py
python3 -B research/phase13/overnight/verify_results.py --check
bash research/phase13/overnight/smoke.sh
```

The full regression compares every one of the 1,691 historical certificates
and minimizes all 511 residues through eight bits against brute force.
It also checks independently constructed prefixes/residues and rejects
corrupted witnesses and transcripts. `test_extended.py --quick`, used by
smoke, retains the first and final historical records in each of ten families
as well as the brute-force, parity, and corruption tests. Smoke additionally
rechecks every published overnight height certificate.

Read `../overnight-progress.md` before requesting another sample. The known
shadow minimum at `N=L_k` is a control, not a new theorem discovered by these
experiments. Intermediate minima, their transitions, and odd gcd growth are
the continuing research questions.

## Compact basis certificates

`odd-box-basis-interval-v1` implements the following written elementary
argument. The producer now defaults to this compact certificate when its
coefficient bound is at most 4095, and falls back to the existing floor-sum
certificate above that cap. `--certificate basis` rejects an oversized bound;
`--certificate floor` selects the original method explicitly. Existing
published records retain their full floor-sum certificates byte for byte.

Let `f,g` be integer vectors in the cylinder lattice, with
`abs(det(f,g))=M`, `f_q` even, and `g_q` odd. These vectors form a basis:
the cylinder lattice has index `M`, and their span has the same index.
Every vector `v=alpha*f+beta*g` with odd denominator has odd integer `beta`.
For a vector inside the symmetric height-`B` box,

```
abs(beta) = abs(det(f,v))/M <= B*(abs(f_p)+abs(f_q))/M.
```

Thus it suffices to inspect odd `beta` up to the floor of that bound.
By central symmetry only positive `beta` need be inspected when proving the
odd-denominator portion of the symmetric box empty. For fixed `beta`, the two inequalities
`-B <= alpha*f_i+beta*g_i <= B` give integer intervals for `alpha`.
Their intersection must be empty. Use exact floor/ceiling arithmetic, reverse
endpoints when `f_i<0`, and handle a zero `f_i` as a constant constraint.
Excluding all these odd-denominator vectors also excludes every positive
odd-denominator witness of smaller height.

The certificate stores the exact coefficient bound `C` and exactly
`(C+1)//2` rows, in order `beta=1,3,...,C`. Each row contains the two integer
endpoint pairs for `alpha`, or `null` for a zero coefficient. The independent
checker validates both lattice congruences, determinant, denominator parities,
and `C*M <= B*(|f_p|+|f_q|) < (C+1)*M`. It checks endpoint tightness using
multiplication and inequalities, independently of the producer's division.
After normalizing the sign of a nonzero coefficient, write
`d=abs(f_i)` and `z=sign(f_i)*beta*g_i`. The endpoints must satisfy

```
(lo-1)*d+z < -B <= lo*d+z,
hi*d+z <= B < (hi+1)*d+z.
```

For `f_i=0`, it checks the constant constraint directly. Each row must have
an impossible constant or disjoint integer intervals. No coefficients are
omitted when the bound exceeds the enumeration cap: the independent checker
rejects, and the producer either rejects or uses the floor-sum fallback.
The witness's actual parity check is still required in both methods.

`test_basis.py` compares producer and independent checker separately against
27,540 directly enumerated small boxes, including 8,748 nonempty boxes, sign
changes, zero coordinates, and unimodular shears. It rejects malformed bases,
intervals, omitted rows, invalid parity/membership, and oversized enumeration,
and checks the floor-sum fallback. It constructs alternative compact proofs
for all 1,691 historical minima and the stored overnight minima, without
recomputing those samples. `basis-validation.json` records the full regression
against its particular source hashes; a smoke run checks the current records.
These are exact finite tests plus a written certificate argument, not a
Lean-kernel proof or a theorem about asymptotic behavior.
