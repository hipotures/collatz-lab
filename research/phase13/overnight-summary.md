# Phase 13 overnight computation — owner handoff

Five sparse exact height samples around `L_5=87091` are complete. This is
finite exact evidence, not a determination of an asymptotic exponent.

See [Issue #30](https://github.com/hipotures/collatz-lab/issues/30),
[PR #29](https://github.com/hipotures/collatz-lab/pull/29),
[the plan](overnight/PLAN.md) and [the journal](overnight-progress.md).

## Verified finite computation

| Prefix length N | Bit length of exact minimum H_N |
|---|---:|
| 80000 | 35217 |
| 87090 | 35217 |
| 87091 | 35217 |
| 87092 | 51875 |
| 90000 | 51875 |

The first three samples have the identical primitive witness, matching the
known k=5 shadow coordinate hashes. Monotonicity therefore gives a constant
minimum throughout `80000..87091`; this is a finite deduction from the
certified endpoints, not a dense experiment. The boundary jump satisfies
`2^16657 <= H_87092/H_87091 < 2^16658`. The exact minimum and witness change
again by `90000`, even though the height bit length stays 51875.

Full hexadecimal heights, primitive positive odd denominators, numerators,
bases, parity hashes, and no-smaller-height transcripts are in
[heights.jsonl](overnight/heights.jsonl). The compact
[inventory](overnight/height-inventory.json) records exact witness/jump
comparisons and checks the inherited shadow hashes. The known minimum at
`L_5` is a control; it is not a newly discovered all-level theorem.

## Falsified / unresolved hypotheses

`B=liminf log2(H_N)/N`, asymptotic odd-gcd cancellation, and other competing
subsequences remain unresolved. The equal bit lengths after the boundary do
not represent equal exact heights. No asymptotic conclusion, novelty claim,
or new Lean theorem follows from this table.

## Independent verification and resource use

The checker imports no producer/project implementation. It uses literal
substitution and reverse rational branches, checks every actual numerator
parity, and verifies primitive odd-denominator witnesses and zero lattice box
counts at `H-1`. This is independent Python exact arithmetic plus the written
floor-sum proof; it is not a new Lean-kernel verification.

The full regression matched all 1,691 historical minima/certificates, passed
511 brute-force residues and four prefix/residue controls, and rejected seven
corrupted certificates. `H_11=3`, `H_12=513` passed. Initial decimal parsing
failed and was fixed with a finite parsing limit; the failure and successful
rerun are preserved in the logs. Final [overnight smoke](overnight/smoke.log)
**passed, exit 0**, including baseline checks, the quick extended regression,
independent verification of all five overnight certificates, and the exact
inventory check. Smoke took 223.81s and peaked at 94,592 KiB resident memory.

Both experiment invocations passed with 180 seconds per sample, 550-second
outer timeouts, and a 1 GiB child address-space cap. New samples took
60.107–118.533 seconds each; peak resident memory across the invocations was
115,332 KiB. The complete evidence is 4,052,103 bytes, below the 8 MiB cap.
Detailed commands and logs are in the [journal](overnight-progress.md).

## Morning continuation

Implement and independently test the compact basis/box certificate proposed
in [README.md](overnight/README.md), then attempt `522546,522547,522548` near
`L_6`. Its coefficient-bound preflight is 1 at all five stored samples; the
argument is written mathematics and has no accepted verifier implementation
yet. Current floor-sum checking dominates the runtime already at `L_5`.
Raw-shadow gcd beyond k=7 is still pending, followed by basis-transition
falsification. No `COMPLETE` marker was created because useful bounded work
remains.

Branch: `codex/phase13-overnight`; starting local HEAD/cached origin ref:
`fbe7b6cd120ee2c93ecce30b50712978652965f8`. This turn performs no commit,
push, network access, issue/PR edits, merge, or publication. The host driver
owns the next safe checkpoint. All edits stay in the three authorized paths;
PR #29, main, original Phase 13 engines, CI and papers are unchanged.
