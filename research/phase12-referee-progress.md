# Phase 12 independent referee journal — issue #26

## Resume here

- Review branch: `review/phase12-independent-audit`, based on
  `47f34bdff38d876c394dc7326e457f686d112c13` (`origin/main`).
- Review clone: `/home/user/DEV/collatz-lab-phase12-referee`.
- Detached source checkout: `/home/user/DEV/collatz-lab-phase12-referee-source`,
  pinned to `37d94195119353799c69714a337c4ed2ac7c8752` (PR #25).
- Live issue #26, issue #24, PR #25 and remote heads were read on 14 November
  2026. PR #25 is open/unmerged; both source/base match the issue snapshot.
- First pushed review checkpoint:
  [`0688fce09e917e4362311b85f1016d0c24cc8eb5`](https://github.com/hipotures/collatz-lab/commit/0688fce09e917e4362311b85f1016d0c24cc8eb5).
  This report milestone follows it; `git log -1` gives its own later SHA.
- Independent derivations, exact interfaces, adversarial tests, source match
  and complete report are finished. **PASS** for the pinned mathematical
  statements and documented rational reductions; no blocking defect found.
  Publication of a new irrationality theorem is not supported by these results.
- Clean validation completed with exit 0. Raw output is
  `/tmp/phase12-referee-validation.log`; a separately executed Phase 12
  signature check also exited 0.
- The standalone checker exited 0: 574,327 return pairs, 16,368 signed
  witnesses, 36,868 affine-form checks, 335,915 maximal finite return checks
  over levels 0..7; smallest nonempty extra-bit witness is `0010`.
- All 593 axiom records were independently collected and parsed; the 564 old
  names remain in order, with exactly 29 new declarations. Every new interface
  and all six new definition bodies were printed and inspected.
- Fresh Allikvere TeX, De Jesús revision-1 PDF, Cassidy pinned note, Dubickas
  publisher PDF and Monks–Yazinski author PDF match the PR's SHA-256 hashes.
  Identified original statements and elementary proof portions were read;
  stronger external transcendence/automatic-word claims are not certified.
- Next: commit/push the report milestone; open a separate PR against main;
  record that URL and exact pushed SHA here, verify live refs/status and hand off.
- There is no outstanding proof obligation or validation blocker for issue #26.
  Owner decisions remain integration and any separate publication assessment.
- Only these new review artifacts may change. Preserve PR #25, existing
  issues/reports, proof files, manuscript and other checkouts. No Phase 13.

## Independent reconstruction before reading the existing proof line by line

The issue, exact basic rational semantics, CI and validation scripts were read
first. The following arguments were recorded in
`/tmp/phase12-independent-derivation.md` before reading `TwoReturn.lean`,
`FrontierSix.lean` or the Phase 12 findings line by line.

For bits b, the affine identity has r'=r+b and c'=3^b c+2^j b.
The actual rational inverse branches are `(2p,q)` and `(2p-q,3q)`.
Starting at zero supplies an eventually-zero rational witness for any finite
prefix. Matching prefixes force numerator congruence modulo 2^ell, so
`E_m=2^m(p-p_m)` has precision m+ell. Elimination gives
`a_n E_m-a_m E_n=(a_m c_n-a_n c_m)q`; cancel odd q. Truncating at
max(m+ell,n+f) transfers the result to any binary word with those matches.
The witness depends on the truncation length, not on an infinite seed.

For the literal six-letter substitution the columns are
`[1,1-x,1-x,1,1,x]`. Adjacent zeros occur only in columns one and two.
A match of length at least three therefore has shift divisible by six.
A match of length ell at shift 6d forces a parent match of length
floor((ell+4)/6), and ell <= 6 floor((ell+4)/6)+1. Strong induction
gives `5ell+1<=2m`; small ell and shifts 1..5 are explicit base cases.
Equality occurs at `(3*6^k,(6^(k+1)-1)/5)`. Eventual periods must be
divisible by six (preserve adjacent zeros), then descend through an injective
column. This proves aperiodicity independently of rationality.

## Environment and isolation

The original checkout was clean on main at the recorded base. No operation
changed it or the author checkout. The first fresh SSH clone failed because
the default key was unavailable; HTTPS clone succeeded. A detached worktree
of the fresh clone holds the pinned source. Build outputs there are untracked
and ignored; source files remain unmodified. Existing repository SSH settings
can be reused for an authorized ordinary push, without disclosing a secret.

No agents were spawned; this is a fresh independent AI-assisted review, not
human peer review. No source argument or checker implementation was copied
into the independent arithmetic checker.

## First verified checkpoint

`lake clean && bash research/phase12/validate.sh` exited 0 in the detached
checkout. The script includes the complete inherited matrix; commands inside
it are not claimed as separate invocations. The additional explicit
`lake env lean research/phase12/Signatures.lean` also exited 0.
An independent `FamilyAudit.lean | tee ... | check_axioms.py --expected-count
593` pipeline used `pipefail` and exited 0: all 593 exact records pass. All 564
baseline entries are preserved in order; exactly 29 new source declarations
are added, each audited once. The six new definition bodies and 23 theorem
interfaces were independently printed and inspected. New axiom profiles are
10 none, 18 propext/Quot.sound, one adding Classical.choice. No bypass found.

One reviewer-only interface command initially failed because Lean 4.18 does
not recognize `pp.width`. Removing that irrelevant formatting option made
the full 29-name `#check` / six-definition `#print` command exit 0. No source
or theorem changed. The first SSH clone failed; HTTPS succeeded as noted above.
These are reviewer environment failures, not failures of PR #25 validation.

## Completed report and independent evidence

The full [referee report](phase12-independent-referee-report.md) contains the
independent determinant/finite-cylinder proof, strong-induction return bound,
every residue case for aperiodicity, count/discrepancy/contraction audit, two
exact signed known-method reductions, all 29 source interfaces, each new
axiom profile, minimal hostile witnesses, and recommendations. It distinguishes
merge suitability from publication and records two nonblocking editorial
suggestions. All mandated source files and relevant dependencies were read.

The standalone `python3 research/phase12/referee_checks.py` exited 0. Its
complete deterministic output is `/tmp/phase12-referee-checks.json`, SHA-256
`1699d278be65c3a1a2d553ca9a3ab187dd7e8f93e69c71386abc0378d75c07bf`.
Its raw 0/1 byte hashes intentionally differ from the author's ASCII encoding.
The checker was authored before reading the author's `verify_returns.py`.
It uses reduced rational evaluation, backward zero-tail witnesses and an
independent base-six-digit evaluation; it imports no project implementation.

Required exact-head validation: `lake clean`, then
`bash research/phase12/validate.sh`, exit 0. That script actually executes
the full inherited Lean/Rust/Python/static-manuscript matrix, all 94 Rust
tests, 593-entry audit, escape scan, both signatures and new finite evidence.
The separate Phase 12 signature invocation also exited 0. Full individual
commands/results are in report §7; commands inside the script are labeled as
such, not claimed to have been separately run.

Supplementary logs and SHA-256 values:

- `/tmp/phase12-referee-validation.log`:
  `329fc68e3a2beded5a8e67de3c68637b7400159a14886dfae0dc2904e69173e3`.
- `/tmp/phase12-referee-axioms.log`:
  `d21b58b4544ffe1261730e366fd97a1e7fa79dbf22511f8bb3926c98c929e44e`.
- `/tmp/phase12-referee-interfaces.log`:
  `96257b93766cc82084a2e0c341ac24ebc09800f75b6790af65d9c73f2c3e5e75`.
- `/tmp/phase12-referee-signatures.log` and semantics log are empty, SHA-256
  `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`;
  their successful process exit codes were observed, not inferred from silence.

Report Appendix B preserves eight extra independently compiled Lean examples:
negative odd remainder, all signed normalization parameters, negative-q
`RealizesWord` safeguard, true minimal returns, extra-bit failures, even-q
cancellation failure, and the actual q=-5 81-step semantics. Compilation
exited 0. No extra proof file is added to the implementation or review branch.

The exact-head source CI run
[43638392392](https://github.com/hipotures/collatz-lab/actions/runs/43638392392)
was read live; both `lean` and `check` and every listed step completed/success.
This is supplemental to the independent local clean build. Source checkout
remained clean at 37d9419; remote main and source heads were rechecked and
unchanged. No unreviewed source revision is covered by the verdict.

Failed approaches / hostile controls: a one-bit stronger determinant fails
on the shortest nonempty two-return word `0010`; dropping an actual match
fails on `101`; dropping oddness fails at p=0,q=4,K=2. Increasing the global
return inequality's +1 fails at (3,1); a ceiling parent descent fails at
(18,7). None falsifies the exact pinned statements. No novel exclusion was
attempted or needed. No approval question or owner information blocks the
authorized review handoff.
