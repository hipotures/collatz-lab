# Parallel independent engineering checks for issue #33

Reports identify the exact commit they checked. Baseline 5186975 checks passed
for evidence/acceptance and shallow/cache compatibility. The adversarial code
review then found the overbroad repository freeze and supplied tested commit
2da6fb71facefeebfca8c5727d630714246016c6, integrated as 0bd17a4. Its bounded
validation output is retained as guard-v4-agent-validation.log.

The final d585944 v4 acceptance and shallow/cache reports both PASS, with nine
bounded tests, unchanged scientific data, immutable original ledger/outputs,
and successful unrelated-edit refresh plus relevant-dependency rejection.
Experiments modifying Rust/CI/docs/source were performed only in the agents'
own disposable clones. No agent changed the parent checkout or pushed a ref.
The coding agent reached a usage limit after delivering its tested commit;
the root and two independent agents verified the integrated result. No required
check depends on that agent resuming.

These reports concern provenance engineering. They add no mathematical theorem,
novelty claim or human peer-review attribution. Actual final-head GitHub CI
and the open, unmerged PR are recorded by the parent delivery handoff.
