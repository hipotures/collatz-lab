# Phase 1: audited follow-up

Context: [`literature-cst.md`](literature-cst.md), primary-source audit for
issue #4. The parity classes, count recurrences and CST conjecture are known
objects. The historical argument already covers coefficient times through
2592; repeating a shallower exception search is tool calibration.

Notation: for a first coefficient crossing `p` of length `k` with `r` odd
steps, `d=2^k-3^r`, `c` is its integer offset, and `m` its least member
`>=2`. Set `slack(p)=d*m-c` and `rho(p)=c/(d*m)`. CST on this cylinder is
`slack>0`, equivalently `rho<1`.

## 1. P1a is refuted

**Predictions, and what became of them.**

- P1a: for each `r`, the maximum of `rho` over first crossings with `r` odd
  steps is attained by the cylinder with the smallest `m`. **Refuted**
  (issue #4). At `r = 6` (`k = 10`, `d = 2^10 - 3^6 = 295`) there are twelve
  first crossings. The least member of the family is `m = 287` (word
  `1111101000`, `c = 697`, `rho = 697/84665`), but the largest ratio belongs
  to `1101110100` with `m = 347`, `c = 989`, `rho = 989/102365`:
  `989 * 84665 - 697 * 102365 = 12385280 > 0`. Regression test:
  `tests/p1a_refutation.rs`, which enumerates all twelve words by direct
  iteration without the library's cylinder code.
- P1b: `max rho` at `r` is at most `max rho` at `r = 5` for every `r > 5`.
  **Not tested by any repository test.** Nothing is inferred about it here.

**Withdrawn strategy.** The earlier plan to find the maximum for larger `r`
"by following the small-`m` branch instead of enumerating" depended on P1a
and is removed. No search may assume that the extremal cylinder is the one
with the least member.

## 2. Disposition of the earlier proposals

| earlier proposal | audit finding | decision |
|---|---|---|
| P1: threshold slack and small power gaps | Terras Theorem 2.6 maximizes `c` at fixed crossing length; Corollary 2.8 bounds exceptional seeds. Garner §§5–6 already use finite relative power gaps. Neither identifies the maximizer of `c/(d*m)`. | P1a is refuted; P1b is not tested here. Retain only the bounded comparison below. |
| P2: geometric density decay per adaptive round | Terras Theorem 1.17 gives vanishing tail density; the finite recurrences can compute subtree densities. The weight/length asymptotics in the audit do not automatically give a uniform contraction per adaptive round. A finite trend or ten small fractions cannot refute existence of some all-round `q>0`. | Withdraw the old prediction and its invalid finite falsification rule. No adaptive search is scheduled. |
| P3: least surviving integer `M(K)` and cross-depth structure | Finite coverage and missing representatives are already treated in the coverage discussion cited in the audit. The equality with actual stopping records uses CST on the relevant finite domain. The structural results concern specified layers, not arbitrary changes of weight. | Retire this as a discovery experiment; optional calibration only, not another scheduled task. |

Here `M(K)` is the least `n>=2` with `tau(n)>K`. The earlier P3 wording
also omitted initial record holders: directly,
`M(1)=3`, `M(4)=7`, and `M(7)=27`; 27 is not the start of the sequence.
Counting or a shrinking density cannot show that every fixed integer
ultimately leaves the surviving set.

## 3. Selected experiment: tightness of the mini-max envelope

**Question.** How much is lost by bounding the numerator and the least
representative separately? For the first-crossing family at each `r`, define

```text
C_r = max c(p),  m_r = min m(p),  R_r = max c(p)/(d*m(p))
U_r = C_r/(d*m_r),  E_r = U_r/R_r >= 1.
```

Terras supplies `C_r`, but the cylinders attaining `C_r`, `m_r` and `R_r`
need not coincide: in the tested `r=6` family their least members are
507 (`c=1085`), 287 and 347 respectively. This experiment measures that
difference. It is a bounded engineering comparison of an upper bound with an exhaustive answer, with no
claim that the table or question is new.

**Domain and method.** Exactly `1<=r<=12` (crossing lengths at most 20).
Enumerate all first-crossing words using exact prefix comparisons. Compute
`C_r` independently from Terras's extremal word and require agreement.
Construct each residue with the modular-inverse formula, cross-check the
selected extremizers by direct iteration, and record all ties. Treat the
class of `1` using its least member `>=2` (namely 5 for `10`). Compare ratios
by integer cross multiplication; use neither floats nor the P1a shortcut.

**Deliverable and stopping rule.** One table of `r`, family count, the three
extremizing words with `(m,c)`, and reduced exact fractions `R_r`, `U_r`,
`E_r`. Require counts to agree with both existing recurrences. Stop at
`r=12`, or immediately on a consistency failure. Record whether the finite
inequality `E_r<=2` holds on the tested domain; a counterexample refutes only
that finite prediction. No extrapolation to P1b or to arbitrary `r`.

**Status.** Implemented for issue #5 after the issue #4 audit. The
[generated table](envelope/summary.md) and [exact evidence](envelope/evidence.json)
cover all 4,403 classes in the specified domain; all counts and Terras offsets
agree. The finite prediction `E_r<=2` is **refuted**: the first counterexample
is `r=11`, `k=18`, with `E_r=479207/179707 > 2`. Every other tested `r` satisfies
it. This result does not prove P1b or extend to arbitrary `r`.

Reproduce both artifacts with:

```text
cargo run --locked --release -- envelope --out-dir research/envelope
```

No deeper cover, large seed scan, autonomous hypothesis loop, or proof of
CST/Collatz is proposed.
