# Sparse overnight height certificates

These experiments are separate from the original, 16,384-bit-capped Phase 13
engines. They use the fixed word `1 -> 100111`, `0 -> 111110`. New samples
are bounded by 600,000 bits; `heights.jsonl` is bounded by 8 MiB. There is no
network access or Git mutation in the experiment or checker.

See [the current two-segment continuation](#two-segment-continuation) for
storage and the next request. Earlier transition notes below describe the
sealed first segment through the eleventh transition; their next-step
sentences are historical.

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

## Raw-shadow cancellation replay

`raw_shadows.py` computes the full signed matrices `[[m,-c],[0,a]]`, starting
at `B_0=[[2,0],[0,1]]`, `B_1=[[2,-1],[0,3]]`. It evaluates
`B_0'=B_1^5 B_0` and `B_1'=B_1 B_0 B_0 B_1 B_1 B_1` simultaneously.
The matrices for `U_k=mu^k(100)` and `V_k=mu^k(1)` then give the raw shadow
coordinates in theory Section 5. Records contain the exact gcd (canonical
hexadecimal), coordinate bit lengths and SHA-256 hashes of the minimal-length
unsigned big-endian magnitudes. The numerator sign, positive odd denominator,
reduced coordinate hashes and strict finite height separation are checked.
Full raw coordinates are not written to the evidence file.

`verify_raw_shadows.py` imports no producer or project implementation. It
computes positive offsets with expanded scalar recurrences and denominators
from the exact letter counts. At a level with `m=2^S`, let
`a=3^r_0`, `b=3^r_1` and offsets `c_0,c_1`. Its separate updates are

```
c_0' = m^5*c_0 + a*c_1*(m^4+m^3*b+m^2*b^2+m*b^3+b^4),
c_1' = c_1*(a^2*b^3+m^3*b^2+m^4*b+m^5)
       + c_0*(m*a*b^3+m^2*b^3).
```

These follow by expanding the ordered product: position `j` contributes
`m^j*c_(x_j)*product(a_(x_i), i>j)`. The checker constructs
`c_U=c_1*a^2+m*c_0*a+m^2*c_0`, then the exact `P,Q`. It checks the gcd by
factoring the denominator as `Q=3^r_U*(b-m)`. Since `b-m` is coprime to 3,
the gcd is the product of the bounded 3-adic part and `gcd(P,b-m)`; it also
checks that both factors of the reduced denominator are coprime to the
reduced numerator. This elementary identity is a written arithmetic argument,
implemented in Python, not a Lean theorem.

Both calculations compare inherited levels `0..7` with `../modular.json`.
The separate replay also checks ten literal reverse-branch maps through
level 4. `test_raw_shadows.py` tests the split-gcd identity on 37,800 signed
inputs, five exact matrix/offset shadow controls, twenty rejected record
corruptions and checkpoint resumption before and after record publication.

The experiment is capped at level 8, 64 KiB of JSONL evidence and an 8 MiB
emergency checkpoint. Each level has a signal budget of at most 240 seconds
(default 180). A `matrix-ready` checkpoint permits repeating only an
unfinished level or advancing from the previous completed one; independently
verified results are identified by the separate replay manifest. At the final
level the checkpoint becomes compact completed status. Existing record bytes
are preserved on resume. Use an additional outer timeout and child memory cap:

```bash
ulimit -v 1048576
timeout 420s python3 -B research/phase13/overnight/raw_shadows.py --through-level 8 --seconds-per-level 180 --write
timeout 420s python3 -B research/phase13/overnight/verify_raw_shadows.py --write
```

`--write` on the checker writes only its small verification manifest;
`--check` independently replays the computation and compares that manifest.
Smoke runs the small controls and the independent replay, without rerunning
the matrix producer. The JSONL is exact computation and the replay is an
independent finite certificate. The inherited all-level shadow-minimum
argument remains written mathematics. These records do not constitute new
large-prefix parity/minimality certificates or any asymptotic gcd conclusion.

## A bounded witness transition

`witness_transition.py` scans one stored primitive witness against a literal
fixed-word prefix, using its actual numerator recurrence with fixed positive
odd denominator. The scan window beyond the source prefix is capped at 8192
symbols, the total prefix at 600,000 symbols, and the complete calculation
at 180 seconds. It saves a `located` checkpoint before requesting a minimum
at the first failing prefix. It computes and independently checks that one
minimum only if absent from `heights.jsonl`; existing samples are preserved.
An interrupted run can reuse the located failure and any published minimum.
A repeated completed request skips calculation. After completion a different
request may replace the small checkpoint while preserving all evidence lines.

If the first mismatch is at zero-based index `t`, the old witness realizes
prefixes through length `t`, and fails at prefix length `t+1`. A minimum at
source length `n` therefore remains a minimum throughout `n..t`, by
monotonicity and the same witness's upper bound. A witness failure alone does
not prove the next height increases: another witness might have equal height.
The independently certified minimum at `t+1` resolves that question exactly.

`transitions.jsonl` stores the first failure, orbit-numerator hash, exact height
comparisons and compact box certificates for both referenced minima. Hashes
bind the references to their exact height-record lines, including newlines.
The height file retains its 8 MiB cap; transition evidence and its checkpoint
each have a separate 512 KiB cap. Temporary-file replacement publishes new
lines atomically. The full witness integers remain in the height file.

`verify_transitions.py` imports only the independent height checker. It
constructs the word by indexed substitution rather than the producer's literal
expansion. Reverse rational branches give `u/v=F_prefix(0)` with odd `v`.
For a source witness `p/q`, the exact valuation

```
v_2(p*v-u*q) = t < length(prefix)
```

certifies its first failure index `t`, by the inherited finite parity/cylinder
equivalence. This replaces the producer's forward scan with a different exact
calculation. Reverse branches through `t` also reconstruct its failing orbit
numerator by division by `2^t`; the verifier checks divisibility, actual
failure parity, sign, bit length and hash. Both minima receive independently
checked primitive positive odd-denominator witnesses, all actual parities and
compact no-smaller-height proofs. The replay manifest binds this verification
to the evidence files. It is an independent finite certificate using Python
exact arithmetic and the written cylinder/basis arguments, not a new Lean
proof or an asymptotic result.

`test_transitions.py` compares scans and reverse-branch valuations with exact
`Fraction` iteration on 5404 signed controls, including 1364 no-failure cases.
Its 68 small transition certificates include two equal-height witness changes
and 66 strict increases; eighteen corrupted records are rejected. Smoke runs
these controls and the separate transition replay. Once the first large
transition is published, three temporary-fixture controls check resumption
from a located failure with an existing target, byte-preserving completed
reuse, and entry to a subsequent request. New scans and optimizer calls are
forbidden in the fixture; the next request stops before its scan.

Commands for the latest completed request (do not repeat its producer):

```bash
ulimit -v 1048576
timeout 185s python3 -B research/phase13/overnight/witness_transition.py --start 87118 --through 90000 --seconds 180 --write
timeout 180s python3 -B research/phase13/overnight/verify_transitions.py --write
python3 -B research/phase13/overnight/summarize.py --write
timeout 35s python3 -B research/phase13/overnight/probe_basis_pattern.py --write
```

Transitions from `87092`, `87094`, `87096`, `87099`, `87100`, `87102`,
`87103`, `87104`, `87109`, `87112`, `87113`, `87116` and `87118` are certified,
with failures at indices `87093`, `87095`, `87098`, `87099`, `87101`, `87102`,
`87103`, `87108`, `87111`, `87112`, `87115`, `87117` and `87119`,
and strict height increases at prefixes
`87094`, `87096`, `87099`, `87100`, `87102`, `87103`, `87104`, `87109`, `87112`,
`87113`, `87116`, `87118` and `87120`.
All endpoint heights have 51,875 bits. The exact consecutive maximal plateaux
have lengths 2, 2, 3, 1, 2, 1, 1, 5, 3, 1, 3, 2, 2. The actual `87104` witness realizes
all five prefixes `87104..87108`, the longest plateau in this stored chain;
the next witnesses realize `87109..87111`, the singleton `87112`, and
`87113..87115`, `87116..87117` and `87118..87119`.
The new `87120` witness has not been scanned beyond its certified prefix;
it differs from the stored `90000` witness and has smaller height.
Check evidence headroom before further requests; remaining height and
second-segment headroom is 739,226 and 436,584 bytes. The sealed base
segment must stay unchanged. Keep both fixed caps in force. No dense height
profile or general plateau rule follows.

## A specific basis-pattern falsification

`probe_basis_pattern.py` imports no project implementation. It reads the
already certified minima and transition references; it computes no minimum.
Both stored links from 87092 to 87094 and from 87094 to 87096 have the
selected-basis update `f'=4*f, g'=2*f+g`. The script derives the coordinates
by determinants and checks them by direct vector multiplication. It tests the
specific prediction that this update repeats every two bits through 90000.
For `r=1454` proposed updates, the closed formula
`f_r=4^r*f_0, g_r=g_0+2*(4^r-1)/3*f_0` agrees with explicit iteration.

The predicted primitive positive odd-denominator candidate has lower height
than the stored minimum at 90000, but fails actual parity first at index
87097. Literal forward iteration and reverse-branch discrepancy valuation
agree; a second reverse calculation reconstructs the exact failing numerator.
The endpoint parity hash and reverse residue also match the stored certificate.
This is an exact finite counterexample to this particular selected-basis
extrapolation. It is not the actual 87096 witness, whose separately certified
first failure is at index 87098 (prefix length 87099). No separate minimum at
87098 was calculated: monotonicity and the persistent actual witness give
`H_87096=H_87097=H_87098`. The extrapolation probe itself certifies no minimum
or general plateau law.
The two observed height increments also fail the exact scalar ratio four;
a repeated basis update alone does not imply that height relation.

`basis-pattern-probe.json` stores hashes, bit lengths and the explicit finite
claim, under a 32 KiB cap. The probe has a 30-second signal budget and caps
its proposed iteration count at 4096. `--write` publishes its derived report
atomically; `--check`, called by smoke under `timeout 35s`, independently
replays both arithmetic routes and compares the report. Refresh it after
appending height or transition evidence, because its source hashes cover the
whole files. Its trust boundary is Python exact arithmetic and the written
finite parity equivalence, with no optimizer or new Lean theorem.

The probe also derives `certified_transition_chain` from the separately
replayed transition certificates. It checks source hashes, replay fields,
contiguous intervals, lattice membership, denominator parity and basis
determinants. Cramer's coordinates are checked by direct vector multiplication.
The third selected-basis update is `f'=8*f, g'=4*f+g`, the fourth is
`f'=2*f, g'=g-f`, the fifth returns to `f'=4*f, g'=2*f+g`, the sixth is
`f'=2*f, g'=f+g`, the seventh returns to `f'=2*f, g'=g-f`, and the eighth
is `f'=32*f, g'=16*f+g`; the ninth returns to `f'=8*f, g'=4*f+g`, and
the tenth returns to `f'=2*f, g'=f+g`; the eleventh returns to
`f'=8*f, g'=4*f+g`.
A constant interval is classified as a maximal plateau only when certificates
give strict height changes on both sides. This gives the finite lengths
2, 2, 3, 1, 2, 1, 1, 5, 3, 1, 3 and rejects the precise claim that each
maximal plateau in this chain has length two. These fields are derived metadata, not an additional
minimum certificate.

The derived `nondecreasing_width_test` compares adjacent intervals only when
both have certified strict height changes on both sides. The ten adjacent
pairs include decreases from width 3 at 87096 to width 1 at 87099 and from
width 2 at 87100 to width 1 at 87102, and from width 5 at 87104 to width 3
at 87109, followed by width 3 at 87109 to width 1 at 87112. This
falsifies the explicit finite claim that consecutive maximal plateau widths
never decrease on this chain. A tied witness change or an unknown left
boundary cannot establish a maximal plateau and is excluded from this test.
The new width-3 plateau adds a comparison, with no additional decrease.
No replacement rule or asymptotic behavior is inferred from eleven widths.

The `width_determines_basis_update_test` compares all equal-width pairs of
certified maximal plateaux. Twelve pairs are available on the current chain.
The singleton plateaux starting at 87099 and 87102 have different selected
basis updates: respectively `[[2,0],[-1,1]]` and `[[2,0],[1,1]]`. This rejects
the explicit finite claim that equal plateau widths determine equal selected
basis update matrices on this chain. The determinant remains 2 in each case;
equal index growth does not fix the shear sign. The new singleton at 87103
uses `[[2,0],[-1,1]]`, adding a second unequal-update pair with 87102.
The singleton at 87112 uses `[[2,0],[1,1]]`, adding unequal-update pairs
with 87099 and 87103, for four in total. The new width-3 plateau at 87113
has the same selected-basis update as the earlier width-3 plateaux at 87096
and 87109, adding two comparisons and no new unequal-update pair.
These are coordinates of
the stored algorithm-selected bases, not an invariant of all possible bases.

`test_transitions.py`, already called by smoke, checks a 31-link small chain
from independently verified minima and first failures. Two equal-height
witness changes do not falsely establish right plateau boundaries; omitting
a left boundary leaves maximality unclassified. Four malformed-chain controls
reject changed replay intervals, source references, basis coordinates and a
missing connecting link. The real certificates are independently replayed
before the probe in smoke. A separate complete-height-run enumeration in the
small profile checks the reported width decreases and their strict boundaries.
The equal-width controls use those complete height runs for eligibility and
raw vector multiplication to check unequal updates, independently of comparing
coordinate rows. Tied witness changes and unknown left boundaries remain
excluded. Smoke already invokes these controls and the probe.
The new 87116 witness remains the next bounded research obligation after
segmented evidence support; no extrapolation from these eleven widths is justified.

## Two-segment continuation

The thirteenth transition is now independently certified. The actual `N=87118`
witness first fails at index 87119, giving the maximal plateau `87118..87119`
and `H_87117 < H_87118 = H_87119 < H_87120 < H_90000`. The new height has
51,875 bits and its positive increase has 35,243 bits, with exact comparison
`1 < H_87120/H_87118 < 2`. No minimum at 87119 was recomputed. The selected
basis update is `[[4,0],[2,1]]`. The consecutive maximal widths are now
`2,2,3,1,2,1,1,5,3,1,3,2,2`; twelve adjacent pairs retain five decreases.
Nineteen equal-width comparisons retain the four earlier unequal updates.
These finite observations do not determine an asymptotic law.

`transitions.jsonl` is sealed at 481,400 bytes and eleven records, unchanged
from entry commit `dbefca3041ead2a7fb98624cf579170ba5a4fe1e`.
`transitions-0002.jsonl` has two records totaling 87,704 bytes, preserving
the first 43,853-byte line. The latest line adds 43,851 bytes. Each segment keeps
the fixed 512 KiB cap, and only these two fixed filenames are supported.
Every new link includes `previous_transition_record_sha256`, the SHA-256 of
the exact preceding JSONL line including its newline. At the segment boundary
it binds the new record to the last historical line. The producer,
independent checker and derived probe have separately implemented readers;
all reject duplicate sources, disconnected intervals, mismatched height
references, missing or incorrect predecessor hashes, incomplete files and
unexpected additional segments. Mathematical checking remains independent
of the producer.

The independent replay now writes `phase13-transition-replay-v2`: `sources`
binds each filename, byte count, record count and hash; `source_sha256` hashes
the concatenation in fixed segment order. The probe binds the same partition
and concatenation, as well as the height file. All twelve earlier replay
results, chain intervals and extrapolation fields are preserved. Height
record and mathematical transition formats remain v1.

Before publishing a new height the producer verifies both endpoint minima,
the failure and the **exact sizes of both proposed output files**. It then
atomically appends the height, atomically appends the transition, and marks
the checkpoint complete. These are separate atomic replacements, with a
durable located checkpoint covering the intervening boundaries. Resuming
after height publication uses that certified target without another scan or
optimization. Resuming after transition publication independently rechecks
it and completes the checkpoint without appending a duplicate. A completed
request is independently rechecked and leaves all files unchanged. Capacity
failure leaves evidence unchanged and a resumable located checkpoint.

`test_transition_segments.py`, now called by smoke, uses only 68-bit exact
temporary fixtures. Its three readers reject 36 malformed-reader cases.
Nine controls cover normal second-segment publication, interruption after
the located checkpoint, height publication and transition publication,
completed reuse, and both file-capacity failures before height publication.
Resume controls explicitly forbid another scan and, once the target is
published, another optimizer call. The original Fraction, certificate,
plateau-chain and legacy resumption controls remain in `test_transitions.py`.

Historical commands that introduced the second segment at the preceding
checkpoint (do not repeat its producer):

```bash
ulimit -v 1048576
timeout 60s python3 -B research/phase13/overnight/test_transition_segments.py
timeout 60s python3 -B research/phase13/overnight/test_transitions.py
timeout 180s python3 -B research/phase13/overnight/verify_transitions.py --write
timeout 185s python3 -B research/phase13/overnight/witness_transition.py --start 87116 --through 90000 --seconds 180 --write
timeout 180s python3 -B research/phase13/overnight/verify_transitions.py --write
timeout 25s python3 -B research/phase13/overnight/summarize.py --write
timeout 35s python3 -B research/phase13/overnight/probe_basis_pattern.py --write
timeout 750s bash research/phase13/overnight/smoke.sh
```

The first replay above validates the new reader against the eleven historical
links before research; the second validates the new twelve-link stream.
See the command logs and journal for actual outcomes and resource observations.
The current thirteenth-link command is listed above under the bounded witness
transition; its logs are `transition-87118-compute.log`,
`transition-87118-replay.log` and `basis-87118-chain.log`.
The 8 MiB height cap is unchanged: twenty-one records use 7,649,382 bytes,
leaving 739,226 bytes. The second transition segment leaves 436,584 bytes.
Next scan only the stored `N=87120` witness through 90000, after checking
current local evidence and capacity, and certify only its first missing
failing prefix. Its next failure remains unresolved. Raw-shadow level 8 is
unchanged; level 9 still needs separately bounded resumable arithmetic.
Useful research remains, so no `COMPLETE` marker is justified.
