# Phase 13 overnight computation — owner handoff

Eight sparse exact height samples around `L_5=87091` and `L_6=522547` are
complete. The three `L_6` samples were added this iteration; the five earlier
records are byte-for-byte preserved. These are finite exact results, with
independent certificates, and do not determine an asymptotic exponent.

See [Issue #30](https://github.com/hipotures/collatz-lab/issues/30),
[PR #29](https://github.com/hipotures/collatz-lab/pull/29),
[the plan](overnight/PLAN.md) and [the journal](overnight-progress.md).
No remote issue or PR state was queried or changed.

## Verified finite computation

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

This iteration implemented the compact basis/interval certificate described
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

The [triplet command](overnight/l6-triplet.log) passed under a 180-second
per-sample budget, a 750-second outer timeout and a 1 GiB child address-space
cap. New samples took 90.710–105.667 seconds including independent checking;
the full invocation took 499.28 seconds and peaked at 123,024 KiB resident
memory, including rechecking and skipping the five earlier records.

Final [overnight smoke](overnight/smoke.log) **passed, exit 0**, including
baseline arithmetic/parity regressions, quick extended and basis tests,
independent parity/minimality verification of all eight records and the exact
inventory check. It took 350.18 seconds and peaked at 98,492 KiB resident
memory. The [checkpoint audit](overnight/checkpoint-audit.json) records scope,
preservation, unchanged HEAD and evidence hashes. No calculation remains
running at handoff.

## Evidence limits and next obligation

The computations and independent certificates use Python exact arithmetic.
The basis-exclusion argument and inherited shadow-minimum theorem are written
mathematics; no new Lean-kernel proposition or proof was added. Exact
`B=liminf log2(H_N)/N`, asymptotic gcd cancellation and control of competing
intermediate approximants remain open. No asymptotic or originality claim
follows from the finite samples.

The next useful bounded experiment is raw-shadow gcd at k=8 using exact
noncommutative matrix recurrences, with inherited k=0..7 regression controls
and separate independent replay. Then investigate basis-transition
falsification. No gcd level beyond 7 has been computed here. A concrete
continuation and checkpoint requirements are in the journal. No `COMPLETE`
marker is justified because useful bounded work remains.

Branch: `codex/phase13-overnight`; entry local HEAD/cached origin ref:
`43a0f7c841851325fdd165611116224068fc54da`. No commit, push, remote access,
issue/PR edit, integration or publication was performed. The host driver owns
the next validated checkpoint. All edits stay within the three authorized
paths; original Phase 13 engines, PR #29, main, CI and papers are unchanged.
