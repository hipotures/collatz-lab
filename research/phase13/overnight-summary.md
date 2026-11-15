# Phase 13 overnight computation — owner handoff

The next raw-shadow level is complete: **`gcd(|P_8|,Q_8)=1`**, verified by
two separate exact arithmetic constructions. All eight existing height
certificates around `L_5=87091` and `L_6=522547` are byte-for-byte preserved.
These finite results do not determine asymptotic cancellation or an exponent.

See [Issue #30](https://github.com/hipotures/collatz-lab/issues/30),
[PR #29](https://github.com/hipotures/collatz-lab/pull/29),
[the plan](overnight/PLAN.md) and [the journal](overnight-progress.md).
No remote issue or PR state was queried or changed.

## New raw-shadow result

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
jump bounds, and checks of inherited shadow hashes. The file is 6,012,761
bytes, below its fixed 8 MiB cap; SHA-256:
`fb2cc65ea9500a2d84f69c5c9db483143455d5058548400701e596f1f297db94`.

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
certificates passed for all 1,691 historical minima and all eight overnight
minima. The full extended regression also passed 511 brute-force residues,
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

The updated [overnight smoke](overnight/smoke.log) **passed, exit 0**, including
baseline arithmetic/parity regressions, quick extended and basis tests,
independent parity/minimality verification of all eight records, the exact
inventory, and the new raw-shadow controls/replay. It took 389.32 seconds
and peaked at 98,896 KiB resident memory. The [checkpoint audit](overnight/checkpoint-audit.json)
records preservation, authorized scope, unchanged Git state and evidence hashes.
No calculation remains running at handoff.

## Evidence limits and next obligation

The computations and independent certificates use Python exact arithmetic.
The basis-exclusion argument and inherited shadow-minimum theorem are written
mathematics; no new Lean-kernel proposition or proof was added. Exact
`B=liminf log2(H_N)/N`, asymptotic gcd cancellation and control of competing
intermediate approximants remain open. No asymptotic or originality claim
follows from the finite samples.

The next bounded experiment is to locate the first actual parity mismatch of
the stored witness at `N=87092` before or at 90000, then independently certify
the minimum at that first failing prefix if it is not already stored. This
tests witness persistence and basis transitions without a dense height scan.
A changed witness alone does not prove a strict height increase. The journal
gives the precise continuation and evidence cap. Level 9 has not been attempted.
No `COMPLETE` marker is justified because useful bounded work remains.

Branch: `codex/phase13-overnight`; entry local HEAD/cached origin ref:
`6a65207193376deafdf1e4f9480efba648a4faca`. No commit, push, remote access,
issue/PR edit, integration or publication was performed. The host driver owns
the next validated checkpoint. All edits stay within the three authorized
paths; original Phase 13 engines, PR #29, main, CI and papers are unchanged.
