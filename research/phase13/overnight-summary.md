# Phase 13 overnight computation — owner handoff

The next witness transition after `L_5` is now certified:
**`H_87096 > H_87095 = H_87094 > H_87093 = H_87092`**,
although all five heights have 51,875 bits. The stored witness at 87094 first
fails at zero-based index 87095. Only the new minimum at 87096 was computed;
all nine previous height certificates, the earlier transition and raw-shadow
level 8 remain intact. A specific repeated-basis prediction is also falsified
by exact parity. These finite results do not determine an asymptotic exponent
or cancellation bound.

See [Issue #30](https://github.com/hipotures/collatz-lab/issues/30),
[PR #29](https://github.com/hipotures/collatz-lab/pull/29),
[the plan](overnight/PLAN.md) and [the journal](overnight-progress.md).
No remote issue or PR state was queried or changed.

## Certified witness transitions

The [bounded scan](overnight/witness_transition.py) uses literal substitution
and actual rational numerator iteration. The
[separate checker](overnight/verify_transitions.py) locates the same first
failure using reverse branches and an exact 2-adic discrepancy valuation.
Both endpoint minima have independently checked primitive witnesses, actual
parities and compact no-smaller-height certificates. The strict height
increases are verified from the exact integers; a changed witness alone would
not establish them. The latest positive height difference has 35,219 bits,
and `1 < H_87096/H_87094 < 2`. The previous difference has 35,217 bits.

The source witness's persistence and monotonicity give the exact plateau
`87092..87093`, and the new source gives `87094..87095`. Each interval has
two prefixes. No general plateau rule or asymptotic statement follows.

[transitions.jsonl](overnight/transitions.jsonl) stores two compact records,
87,545 bytes, SHA-256
`5d923526de3f5c9287e9a7dfd82dd38f96711e1016c9bf66bfb41e55d88766c8`.
The preceding 43,773 bytes are unchanged.
The [replay manifest](overnight/transition-verification.json) binds the
independent verification to its sources. The [small controls](overnight/transitions-tests.log)
passed 5404 signed Fraction/valuation cases, 68 small transition certificates
(including two equal-height witness changes), and eighteen corruption tests.
Three [publication/resumption controls](overnight/transition-resume-tests.log)
also passed in a temporary fixture that forbids new scans or optimization.

The [new computation](overnight/transition-87094-compute.log) passed in 7.94s,
peaking at 107,584 KiB resident memory. The
[independent replay of both links](overnight/transition-87094-replay.log)
passed in 6.80s, peaking at 66,580 KiB. Both ran under a 1 GiB child
address-space cap and a 180-second computation budget. The earlier command
logs are preserved; a located checkpoint permits resumption if a future
target exceeds its budget.

## Finite basis-pattern counterexample

Both observed selected-basis links have exactly `f'=4*f, g'=2*f+g`.
The [new probe](overnight/probe_basis_pattern.py) tests the explicit
prediction that this update repeats every two bits from 87092 through 90000.
Its closed formula and 1454 stepwise updates agree, but the resulting
primitive candidate first fails actual parity at **index 87097**, or prefix
length 87098. Forward numerator iteration and reverse-branch valuation
independently agree, including the failing numerator.

The [compact report](overnight/basis-pattern-probe.json) records this finite
rejection and binds it to the certified evidence. The candidate has lower
height than `H_90000` but fails its parity constraint; it supplies no new
minimum. It is a different vector from the actual 87096 witness, whose next
failure has not been located. No claim about plateau widths follows. Exact
arithmetic also rejects ratio four between the two actual height increments,
despite the repeated selected-basis update.

The final [probe command](overnight/basis-pattern-final.log) passed in 1.81s,
peaking at 66,704 KiB, under a 30-second signal budget, 35-second outer
timeout and 1 GiB child address-space cap. The module imports no project code
or optimizer; smoke checks its deterministic report by replaying both routes.

## Previously completed raw-shadow result

| Level k | S_k | L_k | Raw gcd | Raw numerator / denominator bits |
|---|---:|---:|---:|---:|
| 7 (inherited control) | 279936 | 3135283 | 347 | 1267684 / 1267682 |
| 8 (new) | 1679616 | 18811699 | 1 | 7606082 / 7606080 |

Both have negative numerators and positive odd denominators. At level 8 the
reduced coordinates have the same bit lengths as the raw coordinates.
The return from 347 to 1 falsifies nondecreasing raw gcd; it does not establish
any asymptotic cancellation bound.

The [matrix computation](overnight/raw_shadows.py) uses the ordered,
simultaneous substitution products. The [independent replay](overnight/verify_raw_shadows.py)
uses expanded positive-offset formulas and closed letter counts. It verifies
the gcd by splitting the denominator into its coprime power-of-three and
`b-2^S` factors. Both routes match inherited levels `0..7` and their coordinate
hashes. Ten literal inverse-branch maps provide additional independent controls.

[raw-shadows.jsonl](overnight/raw-shadows.jsonl) stores nine compact records,
6,288 bytes, SHA-256
`72088c34e8e8ac6666da741466fd8c244168350de12c124be38b086d849acad7`.
The [replay manifest](overnight/raw-shadow-verification.json) binds verification
to that file and the inherited source. The [small controls](overnight/raw-shadows-tests.log)
passed 37,800 signed gcd cases, five matrix/offset shadow comparisons,
twenty rejected corruptions and resumable checkpoint checks.

The [producer](overnight/raw-shadows-compute.log) passed in 54.27 seconds
with peak resident memory 38,908 KiB; the [replay](overnight/raw-shadows-replay.log)
passed in 41.79 seconds with peak 37,588 KiB. Both had a 180-second per-level
budget, a 420-second outer timeout and a 1 GiB child address-space cap.
The successful final checkpoint is compact; full raw integers are not stored.

The finite shadow separation inequality was also checked. No new independent
18,811,699-bit parity/minimality certificate is claimed; the all-level shadow
match and minimum interpretation remains the inherited written argument.

## Existing certified heights

| Prefix length N | Bit length of exact minimum H_N |
|---|---:|
| 80000 | 35217 |
| 87090 | 35217 |
| 87091 | 35217 |
| 87092 | 51875 |
| 87094 | 51875 |
| 87096 (new this iteration) | 51875 |
| 90000 | 51875 |
| 522546 | 211281 |
| 522547 | 211281 |
| 522548 | 311267 |

At `522546` and `522547`, the exact heights and primitive witnesses are
identical and match the inherited k=6 shadow coordinate hashes. The boundary
jump satisfies `2^99985 <= H_522548/H_522547 < 2^99986`, using exact integer
comparisons. No inference about the width of a larger plateau is made from
these two adjacent samples.

The earlier finite findings remain: the first three samples have the same
primitive witness, matching the k=5 shadow. Monotonicity gives a plateau
throughout `80000..87091`; the boundary jump lies in `[2^16657,2^16658)`.
The height and witness change again by `90000`, even though the height bit
length remains 51875. Equal bit lengths alone do not establish a plateau.
The known minima at `L_5` and `L_6` are controls for an inherited all-level
written theorem, not new theorems discovered by these samples.

Full hexadecimal witnesses and certificates are in
[heights.jsonl](overnight/heights.jsonl). The exact
[inventory](overnight/height-inventory.json) records witness comparisons,
jump bounds, and checks of inherited shadow hashes. The file is 6,264,543
bytes, below its fixed 8 MiB cap; SHA-256:
`328ad4fca68e27a84edd2f0cf1e9f3212f4ef4cc9a399a525c9b8aa372c628f1`.
The preceding 6,138,652 bytes are identical to the entry checkpoint; only
the new independently certified height record at 87096 was appended.

## Independent certificate and validation

The separate checker imports no optimizer or other project implementation.
It reconstructs the literal word and reverse-branch residue, checks every
actual numerator parity and a primitive positive odd-denominator witness,
and excludes every vector of height `H-1` or less.

The previous height checkpoint implemented the compact basis/interval certificate described
in [README.md](overnight/README.md). It checks lattice membership, determinant,
denominator parity, a complete coefficient bound and tight interval endpoint
inequalities. Each new sample needs one positive odd coefficient row. The
checker rejects bounds above 4095; automatic production falls back to the
preserved floor-sum certificate. All previous floor-sum records remain intact.

The exact direct-box tests passed 27,540 cases, including 8,748 nonempty boxes
that both producer and independent checker rejected. Signed/zero coordinates,
13 malformed/oversized cases, and the verified fallback are covered. Compact
certificates passed at the previous checkpoint for all 1,691 historical minima
and all eight then-stored overnight minima. The full extended regression also passed 511 brute-force residues,
all 1,691 historical floor-sum certificates, four prefix/residue controls,
seven rejected corruptions, `H_11=3`, and `H_12=513`.
Evidence: [basis validation](overnight/basis-validation.json),
[final basis log](overnight/basis-final.log),
[full regression log](overnight/compact-regression.log).

The earlier [triplet command](overnight/l6-triplet.log) passed under a 180-second
per-sample budget, a 750-second outer timeout and a 1 GiB child address-space
cap. New samples took 90.710–105.667 seconds including independent checking;
the full invocation took 499.28 seconds and peaked at 123,024 KiB resident
memory, including rechecking and skipping the five earlier records.

The updated [overnight smoke](overnight/smoke.log) **passed, exit 0**, in
404.91s, peaking at 99,312 KiB resident memory. It checked all ten stored
height certificates, baseline and compact-basis regressions, raw-shadow replay,
transition semantic/corruption/resumption controls, both large transitions
and the basis-pattern probe. It ran with a 750-second outer timeout and
1 GiB child address-space cap. The [checkpoint audit](overnight/checkpoint-audit.json)
records preservation, authorized scope, unchanged Git state and evidence
hashes. No calculation remains running. No Lean, Rust or remote CI result
is claimed.

## Evidence limits and next obligation

The computations and independent certificates use Python exact arithmetic.
The basis-exclusion argument and inherited shadow-minimum theorem are written
mathematics; no new Lean-kernel proposition or proof was added. Exact
`B=liminf log2(H_N)/N`, asymptotic gcd cancellation and control of competing
intermediate approximants remain open. No asymptotic or originality claim
follows from the finite samples.

The next bounded experiment is to locate the first actual parity mismatch of
the new stored witness at `N=87096` before or at 90000, then independently
certify the minimum at that first failing prefix if absent. This
tests witness persistence and basis transitions without a dense height scan.
A changed witness alone does not prove a strict height increase. The rejected
basis-pattern candidate's mismatch at 87097 is not the actual source witness's
first failure. The journal gives the precise continuation and evidence caps.
The actual source height and witness
still differ from the stored 90000 sample. Level 9 has not been attempted.
No `COMPLETE` marker is justified because useful bounded work remains.

Branch: `codex/phase13-overnight`; entry local HEAD/cached origin ref:
`a51c4fe0819a2ce5d6c6b18b21d679f414fbdb1f`. No commit, push, remote access,
issue/PR edit, integration or publication was performed. The host driver owns
the next validated checkpoint. All edits stay within the three authorized
paths; original Phase 13 engines, PR #29, main, CI and papers are unchanged.
