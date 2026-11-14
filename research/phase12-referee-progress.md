# Phase 12 independent referee journal — issue #26

## Resume here

- Review branch: `review/phase12-independent-audit`, based on
  `47f34bdff38d876c394dc7326e457f686d112c13` (`origin/main`).
- Review clone: `/home/user/DEV/collatz-lab-phase12-referee`.
- Detached source checkout: `/home/user/DEV/collatz-lab-phase12-referee-source`,
  pinned to `37d94195119353799c69714a337c4ed2ac7c8752` (PR #25).
- Live issue #26, issue #24, PR #25 and remote heads were read on 14 November
  2026. PR #25 is open/unmerged; both source/base match the issue snapshot.
- Latest review checkpoint: none yet; use `git log -1` after the first commit.
- Independent derivations of both priority results are complete. No defect
  found yet; verdict remains pending exact interfaces, tests and source checks.
- Clean validation completed with exit 0. Raw output is
  `/tmp/phase12-referee-validation.log`; a separately executed Phase 12
  signature check also exited 0.
- The standalone checker exited 0: 574,327 return pairs, 16,368 signed
  witnesses, 36,868 affine-form checks, 335,915 maximal finite return checks
  over levels 0..7; smallest nonempty extra-bit witness is `0010`.
- All 593 axiom records were independently collected and parsed; the 564 old
  names remain in order, with exactly 29 new declarations. Every new interface
  and all six new definition bodies were printed and inspected.
- Fresh Allikvere TeX and De Jesús revision-1 PDF downloads match the PR's
  SHA-256 hashes. Their relevant original statements/proofs are being checked.
- Next: finish narrow primary-source and dependency checks; write
  the complete report, commit/push, and open a separate PR against main.
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
593` pipeline uses `pipefail`; its result is recorded at completion.

One reviewer-only interface command initially failed because Lean 4.18 does
not recognize `pp.width`. Removing that irrelevant formatting option made
the full 29-name `#check` / six-definition `#print` command exit 0. No source
or theorem changed. The first SSH clone failed; HTTPS succeeded as noted above.
These are reviewer environment failures, not failures of PR #25 validation.
