# Issue #33 integration validation records

All files in this directory were produced by the isolated integration review,
not by the original eight-hour run. The unchanged original experiment logs
remain in the parent directory. `validation.json` records the current complete
validation and input hashes; the final audit embeds that ledger. Commands are
run in order and stop on failure, preserving their observed output.

## Retained failed first attempt

`attempt-1/validation.json` and its `combined-matrix.log` / `.resources`
record exit **1**, elapsed **58.82 seconds**, peak RSS **3,847,384 KiB**.
The clean Lean build completed all but the final catalogue-dependent targets,
then `CollatzLab.FiniteCatalogueSix` terminated with `std::bad_alloc` / Lean
exit 134 under the runner's initial **4 GiB address-space cap**. The first
attempt is not a passing build or validation matrix. `finalize-refused.log`
records exit 1 when finalization correctly rejected that incomplete ledger.

The runner was corrected to allow a **24 GiB virtual-address-space cap** for
the full matrix and pinned reproduction, matching the historical driver cap.
This is a child-process limit, not reserved physical memory. Smoke and the
additional interface audit retain **1 GiB** address-space caps. No theorem,
certificate, source invariant or host configuration was changed. The full
matrix was restarted; the separate pinned reproduction starts from a new
clone and rebuilds Lean cleanly. Final actual results are in `validation.json`.

## Serializer correction during the retry

A code read found that generated summary table order depended on in-memory
dictionary insertion order, while the audit JSON is saved with sorted keys.
The renderer now sorts artifact keys explicitly; a round-trip regression
checks byte-stable rendering. The guard also requires the external ledger
to equal the copy embedded in the audit. These metadata-only corrections
were made while the retry was running. The unchanged mathematical matrix passed, exit **0**, **349.45 seconds**,
peak RSS **6,293,264 KiB**. The overall runner nevertheless correctly stopped
with exit **1** because those two metadata input files changed during the run.
`attempt-2/` retains the successful command output, its ledger and the exact
changed-path list; it is not presented as a completed final attestation.
A fresh run is required for the final corrected metadata code.

## CI cache portability correction

`attempt-3/` passed the full matrix (**270.28 seconds**) and additional
interfaces (**9.78 seconds**), then all 24/16/9 smoke checks (**467.37 seconds**,
peak RSS **103,628 KiB**), each command exit **0**. During smoke, a CI
compatibility read found that earlier workflow imports create Python bytecode
in directories without `.gitignore`; local validation suppresses these
outputs. The guard now excludes generated `__pycache__`, `.pyc` and `.pyo`
files. A sixth regression proves caches do not change the input fingerprint
while a changed Python source does. No certification script or data changed.
The runner again correctly refused finalization when those two metadata
source files changed. This is an incomplete overall attempt (runner exit 1),
not a failure of the successful mathematical checks. Its exact input changes
and all three command logs are retained. The final run freezes the corrected
metadata code before all four commands and must pass without input changes.

## Scope

`combined-matrix` runs the complete current repository matrix.
`combined-interfaces` repeats the exact 653-name axiom pipeline with pipefail,
compiles the unchanged reviewer semantic/declaration fixtures, independently
parses foundations and compares signatures/fixtures byte-for-byte.
`overnight-smoke` checks every stored finite certificate and all original
parity, corruption, capacity, segmentation, resume and basis regressions.
`pinned-referee` runs the unchanged merged review reproduction against its
exact two original refs, including independent minima/gcd checks and both
bytewise reviewer-output comparisons. No large-N optimizer was rerun. The pinned referee result intentionally
reproduces its historical provenance FAIL for the old 23/15 summary/audit.
That historical finding remains correct and is not edited; the new final
audit and current guard separately attest the repaired 24/16 handoff.

The provenance guard and hostile regression tests are run after finalization
and in PR CI. They hash/parse bounded data, require current successful smoke
outputs, reject a 23/15 summary or wrong source pin, and do not run simulations.
The input snapshot excludes only narrative Markdown, the current audit and
this output directory to avoid a self-hash cycle. Narrative handoff updates
therefore do not invalidate an unchanged successful arithmetic run. No PDF
build or visual inspection is claimed; static manuscript checks preserve the
existing matrix and are not a publication-readiness assertion.

## Completed frozen-code run

All four final commands passed with unchanged input fingerprints. The combined
matrix took 269.91 seconds; the independent interfaces 9.52 seconds; smoke
467.32 seconds at peak RSS 102,696 KiB; the complete pinned reproduction
585.64 seconds at peak RSS 6,288,872 KiB. Its independent arithmetic stage
took 193.739 seconds. Both reviewer JSON comparisons passed byte-for-byte.
The new final audit/summary were then generated, checked, and all six hostile
metadata/CI-cache regressions passed against the real final audit. The prior
attempts remain distinct from this completed validation.

## Parallel audit and scoped v4 correction

The 5186975 shallow/cache and acceptance reports are preserved under
`parallel/`, labeled with their actual reviewed commit. An adversarial agent
then found the v3 whole-repository equality check would block unrelated future
development. The v4 correction changes only metadata tools/README and generated
audit/summary. The mathematical sources, 24/16/9 evidence, full-run ledger and
all eight full-run log/resource files remain unchanged. V4 pins that immutable
ledger identity, checks 217 explicit relevant dependencies, binds four current
metadata tools separately, and cross-checks wall/RSS/exit values from hashed
resources. It permits unrelated existing/new Rust/CI/docs files without
rewriting historical inputs. Root v4 generation/check and all nine tests pass.
These are fresh bounded engineering checks, not a claim that the historical
full matrix executed later guard code. Actual final-head CI is checked in the PR.
