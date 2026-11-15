# Phase 13 overnight research journal — issue #30

## Resume here

- Status: **not started**. GitHub repository bootstrap only; no local
  computation or Codex session has been launched by this issue creation.
- Source checkpoint: PR #29, commit
  `65b087dc62e4950e1c504fe34865acaacb9188c9`.
- Dedicated branch: `codex/phase13-overnight`, forked from PR #29.
  It is intentionally separate from `main` and the original Phase 13 PR.
- First action: read `research/phase13/overnight/PLAN.md` and issue #30;
  implement a bounded independent height/minimality checker; verify against
  existing small and 16,384-bit checkpoints.
- Next exact target: sparse samples around `L_5=87091`, then
  `L_6=522547` if performance permits. A second route computes
  raw-shadow gcd at k=8 or beyond, with exact recurrence and hashes.
- Local execution: start `drive_codex.sh` in `tmux` in a dedicated clone
  after confirming Codex CLI is installed/authenticated. It stops after
  eight hours at most; local machine must remain on.
- **Usage-window reset handling:** an exhausted Codex 5-hour quota is
  detected from CLI error output and retried every 600 seconds, without
  resetting the 8-hour deadline or counting quota polls as failed research.
  Genuine authentication failures still stop the loop. A weekly usage
  limit might not reset during the overnight deadline.
- If this script was cloned **before** the retry fix, fast-forward the
  dedicated clone before starting; an already running shell cannot acquire
  the new loop semantics merely by a later Git fetch.
- Logs are written outside the checkout, under
  `~/DEV/collatz-lab-phase13-night-logs/latest/`.
- The driver is allowed to commit/push only to this dedicated branch after
  smoke testing. No PR merge or owner publication authorization exists.
- There are no overnight results, exact minima, modular discoveries or
  performance timings yet. Do not claim otherwise.
