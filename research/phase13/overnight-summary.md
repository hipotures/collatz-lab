# Phase 13 overnight computation — owner handoff

The sixth intermediate witness transition after `L_5` is certified:
**`H_87103 > H_87102 > H_87101 = H_87100`**.
The actual 87102 witness first fails at zero-based index 87102. This gives
another singleton maximal plateau and consecutive widths **2, 2, 3, 1, 2, 1**.
Its selected-basis update is `f'=2*f, g'=f+g`; the earlier singleton used
`f'=2*f, g'=g-f`. Thus equal maximal plateau widths do not determine equal
selected-basis update matrices on this finite chain. The earlier
width-decrease and constant-update counterexamples remain valid.
These finite observations determine no general width or basis law,
asymptotic exponent or cancellation bound.

Only the new minimum at 87103 was computed. All thirteen previous height
records, five earlier transition records, previous command logs and raw-shadow
level 8 are preserved. See [issue #30](https://github.com/hipotures/collatz-lab/issues/30),
[PR #29](https://github.com/hipotures/collatz-lab/pull/29),
[the local plan](overnight/PLAN.md) and [the journal](overnight-progress.md).
Remote issue/PR state was neither queried nor changed.

## New independent minimum and transition

The [bounded scan](overnight/witness_transition.py) uses literal substitution
and actual rational numerator iteration. The
[separate checker](overnight/verify_transitions.py) reconstructs the word by
indexed substitution, then finds the same failure using reverse integer
branches and an exact 2-adic discrepancy valuation. It independently verifies
both endpoint minima: primitive positive odd denominators, actual numerator
parities and compact no-smaller-height certificates.

The new height has 51,875 bits, its positive difference from `H_87102` has
35,226 bits, and exact comparison gives `1 < H_87103/H_87102 < 2`.
A witness change alone would not establish a strict increase; both minima
are certified. The positive failing numerator has 63,385 bits and SHA-256
`fb3c4d58361879930d9d71673fdb2d519ea4d50164b802b8b5b065bf4a5f2100`.
Both routes agree on this hash.

[transitions.jsonl](overnight/transitions.jsonl) contains six compact records,
262,612 bytes, SHA-256
`31ba1052a41468caf48be9966ae50380b1818db248d75abb658d5f8d29396c9f`.
The preceding 218,847 bytes are unchanged. The
[replay manifest](overnight/transition-verification.json) binds its results
to the height and transition files. The completed
[checkpoint](overnight/transition-checkpoint.json) records the latest request.

The [new computation](overnight/transition-87102-compute.log) passed in 7.88s,
peak 109,996 KiB. The [independent replay of all six links](overnight/transition-87102-replay.log)
passed in 19.94s, peak 67,812 KiB. Both had bounded timeouts and a 1 GiB child
address-space cap. Previous command logs are unchanged.

## Finite plateau and basis falsification

The exact consecutive maximal plateaux are `87092..87093`, `87094..87095`,
`87096..87098`, the singleton `87099..87099`, `87100..87101`, and the singleton
`87102..87102`. Witness persistence and monotonicity give each constant
interval; independently
certified strict height changes on both sides establish maximality. The earlier
widths 3 and 1 still reject nondecreasing widths; the latest widths 2 and 1
give another decrease.

The refreshed [probe](overnight/probe_basis_pattern.py) records five adjacent
maximal plateau comparisons and both decreases in
[its compact report](overnight/basis-pattern-probe.json). Both intervals must
have certified strict boundaries before a comparison is counted. Cramer's
coordinates, direct vector multiplication and signed determinants give
`[[2,0],[1,1]]` for the newest selected-basis update, following
`[[4,0],[2,1]]`, `[[4,0],[2,1]]`, `[[8,0],[4,1]]`, `[[2,0],[-1,1]]`,
`[[4,0],[2,1]]`.

The new explicit equal-width test compares four pairs of certified maximal
plateaux and finds different updates for the singletons at 87099 and 87102.
Both determinants are 2, but their shear signs differ. This concerns the
stored algorithm-selected bases, not all possible bases of those lattices.

The [final probe command](overnight/basis-equal-width-probe.log) passed in 1.90s,
peak 68,140 KiB. The [extended controls](overnight/equal-width-update-controls.log)
passed in 3.48s, peak 43,128 KiB. They independently enumerate complete small
height runs for eligibility and multiply raw vectors to check unequal updates.
Equal-height witness changes and unknown left boundaries cannot establish
maximality and are excluded. The existing
5404 Fraction/valuation cases, 68 small transition certificates, eighteen
corruptions, three resumption controls and four malformed chains also passed.
Smoke already invokes both extended checks.

The earlier failed extrapolation is preserved: repeating `f'=4*f, g'=2*f+g`
every two bits through 90000 produces a candidate that first fails actual
parity at index 87097. That candidate differs from the actual source witnesses;
it certifies no minimum or plateau. No optimizer is called by the probe.
The old result fields and command logs remain unchanged.

## Previously completed evidence

| Prefix length N | Bit length of exact minimum H_N |
|---|---:|
| 80000 | 35217 |
| 87090 | 35217 |
| 87091 | 35217 |
| 87092 | 51875 |
| 87094 | 51875 |
| 87096 | 51875 |
| 87099 | 51875 |
| 87100 | 51875 |
| 87102 | 51875 |
| 87103 (this iteration) | 51875 |
| 90000 | 51875 |
| 522546 | 211281 |
| 522547 | 211281 |
| 522548 | 311267 |

Full hexadecimal witnesses and minimum certificates are in
[heights.jsonl](overnight/heights.jsonl). Its fourteen records total 6,768,114
bytes, below the fixed 8 MiB cap, SHA-256
`d4c62516b401401821ce9af362094d62bf64eaf82dffe3a8f8cd7e3e87f4cd75`.
All preceding 6,642,220 bytes are identical to the entry checkpoint; the only
new line is the independently certified minimum at 87103 (125,894 bytes).
The [inventory](overnight/height-inventory.json) records exact comparisons and
inherited shadow hashes. Equal height bit lengths alone never imply a plateau.

The earlier shadow-boundary findings remain: `80000..87091` is a certified
plateau matching the k=5 shadow; the next jump lies in `[2^16657,2^16658)`.
At 522546 and 522547, exact heights and witnesses agree with the k=6 shadow;
the jump at 522548 lies in `[2^99985,2^99986)`. The known all-level shadow
minima are inherited written mathematics, not new theorems from these samples.

Raw-shadow levels 0..8 remain complete with gcds `[3,1,1,1,1,1,1,347,1]`.
At level 8, `S=1679616`, `L=18811699`, the raw numerator has 7,606,082 bits
and denominator 7,606,080 bits, with gcd 1. The return from 347 to 1 rejects
nondecreasing raw gcd; it establishes no asymptotic cancellation bound.
The nine-line [evidence](overnight/raw-shadows.jsonl), its
[independent replay](overnight/raw-shadow-verification.json), checkpoint and
original command logs remain unchanged. No raw-shadow producer was repeated.
Level 9 has not been attempted.

## Validation and evidence limits

The full [overnight smoke](overnight/smoke.log) **passed, exit 0**, in
421.25s, peak 100,404 KiB, under a 750-second timeout and 1 GiB child
address-space cap. It checked all fourteen height certificates, six
independent transitions, nine-level raw-shadow replay and baseline/basis/
transition controls, including the new equal-width test. The
[scope/preservation audit](overnight/checkpoint-audit.json) records unchanged
Git state, authorized paths, append-only evidence, all 31 preserved older
command logs, source references and hashes. Only the derived probe and its
controls were extended; height/transition producers, independent minimum
checkers and smoke are unchanged. No calculation remains running.

The new sample is exact computation plus an independent finite parity and
minimality certificate. The basis updates, width-decrease and equal-width
update tests are derived exact integer data; maximal-plateau interpretation
uses the inherited written
monotonicity argument. Python exact arithmetic and the written parity/basis
identities are the trust boundary. No new Lean-kernel theorem was added.
Exact `B`, asymptotic gcd cancellation and further intermediate minima remain
open. No asymptotic or originality claim follows from these finite samples.
No Lean, Rust or remote CI result is claimed.

## Next obligation and checkout

Locate the first actual parity mismatch of the stored `N=87103` witness
through 90000, then independently certify that prefix's minimum only if
absent. Exact arithmetic gives `H_87103 < H_90000`, with different primitive
witnesses. The next failure is unresolved. Earlier failures and plateau widths
do not determine it. The journal gives the concrete command and fixed evidence
caps. Useful bounded work remains, so no `COMPLETE` marker is justified.

Branch: `codex/phase13-overnight`; entry local HEAD/cached origin ref:
`c214654df812331ed659fbf418ab65003557b574`. No commit, push, remote access,
issue/PR edit, integration or publication was performed. The host driver
owns the next validated checkpoint. All edits stay within the three authorized
paths; original Phase 13 engines, PR #29, main, CI and papers are unchanged.
