# Historical snapshots extracted for issue #33

`summary-at-76bf613.md` and `checkpoint-audit-at-76bf613.json` are exact
byte copies of the two files at overnight source commit
`76bf6136c334c1db9e52e399fcc33fd4c20b9c24`. They describe the earlier
23-minima / 15-transition checkpoint. Their cached entry HEAD
`bcfc2a7d9f57b8001b3041453ada7dc6ff08ae10` and old hashes must not be
interpreted as attesting the final 24/16 source state. Their historical
next-experiment instructions are not active issue #33 instructions.

The current summary and audit supersede them for owner handoff. Their exact
original bytes and extraction paths are included in the new final audit.
All original computational logs, certificate files and original certification
scripts remain at their original paths unchanged. The current validation
logs are under `../integration/`, separately named and timestamped.

An additional independent prefix check identifies the actual older artifact
commit as `caaa37cf68e399b48dae0fa975a45f9cc2447d9f` (the final overnight head's parent). Both copied
metadata files are byte-identical to that commit. Its 23 height records,
11+4 transitions and smoke hash match the old audit, and all of its evidence
bytes remain prefixes of the final files. The old audit's `entry_head` is
the pre-commit entry state, not the artifact commit. Fresh observations are
in `../integration/historical-prefix-check.json`.
