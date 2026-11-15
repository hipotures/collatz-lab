#!/usr/bin/env bash
# Local, unattended, time-bounded Codex research driver for issue #30.
# Runs ONLY in a dedicated clone on codex/phase13-overnight.
# Codex edits permitted research files; this host script validates, commits and
# optionally pushes checkpoints. It never merges or writes to main / PR #29.
set -Eeuo pipefail

EXPECTED_BRANCH="codex/phase13-overnight"
PINNED_BASE="65b087dc62e4950e1c504fe34865acaacb9188c9"
MAX_SECONDS=28800
MAX_ROUNDS=64
ROOT="$(git rev-parse --show-toplevel)"
cd "$ROOT"

if [[ "$(git branch --show-current)" != "$EXPECTED_BRANCH" ]]; then
  echo "ERROR: checkout must be on $EXPECTED_BRANCH" >&2
  exit 2
fi
git merge-base --is-ancestor "$PINNED_BASE" HEAD || {
  echo "ERROR: checkout does not descend from pinned Phase 13 PR #29" >&2
  exit 2
}
if [[ -n "$(git status --porcelain)" ]]; then
  echo "ERROR: begin from a clean dedicated overnight clone" >&2
  git status --short >&2
  exit 2
fi
for cmd in codex timeout git python3 tee; do
  command -v "$cmd" >/dev/null || { echo "ERROR: missing $cmd" >&2; exit 2; }
done

LOG_PARENT="${HOME}/DEV/collatz-lab-phase13-night-logs"
RUN_ID="$(date -u +%Y%m%dT%H%M%SZ)"
LOG_DIR="$LOG_PARENT/$RUN_ID"
mkdir -p "$LOG_DIR"
ln -sfn "$LOG_DIR" "$LOG_PARENT/latest"
exec > >(tee -a "$LOG_DIR/driver.log") 2>&1

START="$(date +%s)"
DEADLINE=$((START + MAX_SECONDS))
INITIAL_HEAD="$(git rev-parse HEAD)"
ROUND=0
FAILED=0
NO_PROGRESS=0
echo "START_UTC=$(date -u -Is)"
echo "ROOT=$ROOT"
echo "BRANCH=$EXPECTED_BRANCH"
echo "PINNED_SOURCE=$PINNED_BASE"
echo "INITIAL_CHECKPOINT=$INITIAL_HEAD"
echo "DEADLINE_UTC=$(date -u -d "@$DEADLINE" -Is)"
echo "LOG_DIR=$LOG_DIR"
echo "Only an isolated overnight branch may be pushed."

PROMPT="$(cat <<'PROMPT_TEXT'
Continue GitHub issue #30: Phase 13 unattended exact-height and shadow-gcd research.
READ FIRST: AGENTS.md, research/phase13/overnight/PLAN.md,
research/phase13/overnight-progress.md, research/phase13-theory.md sections 5-9,
and the existing Phase 13 experiment/verifier modules.
Read the current local files before each research step: other Codex iterations
may already have completed part of the plan.

You are in a dedicated isolated overnight branch based on PR #29.
Work on the NEXT scientifically useful, bounded computation, not a rewrite of
the previous findings. Priority: sparse exact H_N near shadow transitions
L_5=87091 and L_6=522547 with independently verifiable minimality, then
raw-shadow gcd beyond k=7 using exact matrix recurrences, then basis-transition
falsification and further bounded experiments. Never imply finite data prove
asymptotic behavior, and never repeat an experiment already certified.

All edits MUST be confined to:
  research/phase13/overnight/
  research/phase13/overnight-progress.md
  research/phase13/overnight-summary.md

Do not edit original Phase 13 code, PR #29, main, papers, issues, CI,
or other worktrees. Do NOT git commit/push/merge/open PR; the host driver
validates, commits and pushes safe checkpoints outside the Codex sandbox.
Do not run destructive shell commands, use dangerous permissions, or spawn
detached child processes. No secrets, remote access or host reconfiguration.

Implement, run and independently check a bounded, useful step this turn.
Keep each individual computation time-bounded and memory-conscious; if it
would exceed the available time, implement a resumable checkpoint and stop.
Run the overnight smoke test. Update the 'Resume here' section with the
exact verified findings and next experiment. Classify exact computation,
independent certificate, written proof and open conjecture separately.

If further computation cannot be usefully completed or a hard blocker is
reached, document the reason in the progress file and create
research/phase13/overnight/COMPLETE with a truthful English summary.
Otherwise leave a concrete next obligation for the next Codex iteration.
End with a concise report of commands actually run and evidence written.
PROMPT_TEXT
)"

while (( ROUND < MAX_ROUNDS )); do
  NOW="$(date +%s)"
  REMAINING=$((DEADLINE - NOW))
  if (( REMAINING < 180 )); then
    echo "Stopping: deadline approaching, remaining=$REMAINING seconds."
    break
  fi
  if [[ -f research/phase13/overnight/COMPLETE ]]; then
    echo "Research reports completion / a hard stop."
    break
  fi
  if [[ "$(git branch --show-current)" != "$EXPECTED_BRANCH" ]]; then
    echo "ERROR: branch changed unexpectedly; aborting."
    exit 3
  fi
  ROUND=$((ROUND + 1))
  TAG="$(printf '%03d' "$ROUND")"
  BEFORE="$(git rev-parse HEAD)"
  echo "ROUND=$ROUND START_UTC=$(date -u -Is) REMAINING_SECONDS=$REMAINING"
  RESULT=0
  timeout --signal=TERM --kill-after=30s "${REMAINING}s" \
    codex exec --sandbox workspace-write --cd "$ROOT" --json "$PROMPT" \
    > "$LOG_DIR/round-$TAG.jsonl" 2> "$LOG_DIR/round-$TAG.stderr" || RESULT=$?
  echo "ROUND=$ROUND CODEX_EXIT=$RESULT FINISHED_UTC=$(date -u -Is)"

  if [[ "$(git branch --show-current)" != "$EXPECTED_BRANCH" ]] ||
     ! git merge-base --is-ancestor "$PINNED_BASE" HEAD; then
    echo "ERROR: unexpected branch ancestry; aborting to protect other work."
    exit 3
  fi

  OUTSIDE="$(git status --porcelain | grep -Ev '^.. research/phase13/(overnight/|overnight-progress\.md|overnight-summary\.md)' || true)"
  if [[ -n "$OUTSIDE" ]]; then
    echo "ERROR: unexpected files changed; refusing to stage or push."
    printf '%s\n' "$OUTSIDE"
    exit 3
  fi

  CHECK=0
  bash research/phase13/overnight/smoke.sh || CHECK=$?
  if (( CHECK != 0 )); then
    echo "ROUND=$ROUND smoke test failed (exit $CHECK); leaving files for repair."
    FAILED=$((FAILED + 1))
  else
    TOO_LARGE="$(find research/phase13/overnight -type f -size +20M -print -quit)"
    if [[ -n "$TOO_LARGE" ]]; then
      echo "ERROR: an output file exceeds 20 MiB; retain locally, do not auto-push: $TOO_LARGE"
      exit 4
    fi
    git add -A -- research/phase13/overnight \
      research/phase13/overnight-progress.md \
      research/phase13/overnight-summary.md
    if ! git diff --cached --check; then
      echo "ERROR: checkpoint whitespace/error check failed."
      exit 4
    fi
    if ! git diff --cached --quiet; then
      git commit -m "research: overnight Phase 13 checkpoint round $ROUND"
    fi
    if [[ "$(git rev-parse HEAD)" != "$BEFORE" ]]; then
      NO_PROGRESS=0
      echo "CHECKPOINT_SHA=$(git rev-parse HEAD)"
    else
      NO_PROGRESS=$((NO_PROGRESS + 1))
      echo "No new versioned research this round ($NO_PROGRESS consecutive)."
    fi
    # Run outside sandbox. Interactive prompts are forbidden during overnight work.
    if ! GIT_TERMINAL_PROMPT=0 timeout --signal=TERM --kill-after=10s 120s \
      git push origin "HEAD:refs/heads/$EXPECTED_BRANCH"; then
      echo "WARNING: push failed. Local commits remain safe; retry manually in morning."
    fi
    FAILED=0
  fi

  if (( RESULT == 124 || RESULT == 137 )); then
    echo "Deadline timeout; stopping."
    break
  fi
  if (( RESULT != 0 )); then
    if grep -Eiq 'rate.?limit|usage.?limit|quota|429|authentication|invalid.?token|not logged in|login required' \
        "$LOG_DIR/round-$TAG.stderr" "$LOG_DIR/round-$TAG.jsonl"; then
      echo "Authentication/quota error; stopping instead of looping."
      break
    fi
    FAILED=$((FAILED + 1))
    echo "Codex failed. Repeated failures will stop the driver."
  fi
  if (( FAILED >= 3 || NO_PROGRESS >= 3 )); then
    echo "Stopping after repeated failures or no useful versioned progress."
    break
  fi
  if [[ -f research/phase13/overnight/COMPLETE ]]; then
    echo "Research completion marker present."
    break
  fi
  sleep 15
done

echo "END_UTC=$(date -u -Is)"
echo "FINAL_LOCAL_SHA=$(git rev-parse HEAD)"
echo "FINAL_STATUS:"
git status --short --branch
echo "Logs: $LOG_DIR"
echo "Review the overnight progress and summary before integrating anything."
