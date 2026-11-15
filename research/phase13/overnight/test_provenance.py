#!/usr/bin/env python3
"""Small hostile regressions for final metadata; no simulation or optimizer."""

from copy import deepcopy
import json
from pathlib import Path
import tempfile
import unittest
import subprocess

import finalize_provenance as final


SMOKE = ("PASS: 24 independent primitive witnesses, actual parity prefixes, and zero box counts at H-1\n"
         "PASS: 9 independently replayed levels; 10 literal controls\n"
         "PASS: 16 independently verified witness failures and exact height comparisons\n"
         "PASS: overnight smoke checks\n")


class ProvenanceTests(unittest.TestCase):
    def test_ci_bytecode_cache_is_not_a_source_input(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            (root / "module.py").write_text("value = 1\n")
            before = final.inputs(root)
            cache = root / "__pycache__"
            cache.mkdir()
            (cache / "module.cpython-312.pyc").write_bytes(b"generated output")
            (root / "other.pyc").write_bytes(b"generated output")
            self.assertEqual(before, final.inputs(root))
            (root / "module.py").write_text("value = 2\n")
            self.assertNotEqual(before, final.inputs(root))

    def test_final_smoke(self):
        self.assertEqual(final.smoke_counts(SMOKE), {"heights": 24, "transitions": 16, "raw_shadow_levels": 9})
        for broken in (SMOKE.replace("24 independent", "23 independent"),
                       SMOKE.replace("16 independently", "15 independently"),
                       SMOKE.replace("9 independently", "8 independently"),
                       SMOKE.replace("PASS: overnight smoke checks\n", ""), SMOKE + SMOKE):
            with self.assertRaises(ValueError):
                final.smoke_counts(broken)

    def test_source_identity(self):
        audit = {"format": "phase13-overnight-final-audit-v3", "source_commit": final.SOURCE,
                 "integration_base": final.MAIN, "implementation_commit": final.IMPLEMENTATION,
                 "review_commit": final.REVIEW, "counts": final.smoke_counts(SMOKE)}
        final.check_identity(audit)
        for key in ("source_commit", "integration_base", "implementation_commit", "review_commit", "format"):
            broken = deepcopy(audit)
            broken[key] = "cached-or-wrong-head"
            with self.assertRaises(ValueError):
                final.check_identity(broken)
        broken = deepcopy(audit)
        broken["counts"]["transitions"] = 15
        with self.assertRaises(ValueError):
            final.check_identity(broken)

    def test_summary_round_trip_and_staleness(self):
        audit = {"evidence": {name: {"records": row[0], "bytes": row[1], "sha256": row[2]}
                              for name, row in final.EVIDENCE.items()}, "validation": {"commands": []}}
        text = final.summary(audit)
        self.assertEqual(text, final.summary(json.loads(final.encoded(audit))))
        final.check_summary(text, audit)
        for broken in (text.replace("**24 exact", "**23 exact"), text.replace(final.SOURCE, "0"*40),
                       text.replace("N=87124", "N=87122")):
            with self.assertRaises(ValueError):
                final.check_summary(broken, audit)

    def test_current_audit_and_hostile_mutations(self):
        # Before first finalization, the historical v2 audit intentionally is
        # rejected by the identity test above. Once finalized, exercise the
        # real ledger, protected files and summary without changing any file.
        audit = json.loads((final.ROOT / final.AUDIT).read_text())
        if audit["format"] != "phase13-overnight-final-audit-v3":
            with self.assertRaises(ValueError):
                final.check_identity(audit)
            return
        final.check_audit(final.ROOT, audit)
        changes = [
            lambda a: a["counts"].update(heights=23),
            lambda a: a.update(source_commit="bcfc2a7d9f57b8001b3041453ada7dc6ff08ae10"),
            lambda a: a["evidence"]["heights.jsonl"].update(sha256="0"*64),
            lambda a: a["validation"]["commands"][2].update(exit_code=124),
            lambda a: a["validation"]["commands"][2]["log"].update(sha256="0"*64),
            lambda a: a["validation"]["commands"][2].update(inputs_unchanged=False),
            lambda a: a["validation"].update(entry_head="bcfc2a7d9f57b8001b3041453ada7dc6ff08ae10"),
            lambda a: a["validation"]["inputs"].pop("CollatzLab/Word.lean"),
            lambda a: a["validation"]["commands"].pop(),
        ]
        for mutate in changes:
            broken = deepcopy(audit)
            mutate(broken)
            with self.assertRaises(ValueError):
                final.check_audit(final.ROOT, broken)
        text = final.summary(audit)
        self.assertEqual(text, final.summary(json.loads(final.encoded(audit))))
        final.check_summary(text, audit)
        for broken in (text.replace("**24 exact", "**23 exact"), text.replace(final.SOURCE, "0"*40),
                       text.replace("to the certified minimum at **N=87124**", "to the certified minimum at **N=87122**")):
            with self.assertRaises(ValueError):
                final.check_summary(broken, audit)

    def test_evidence_byte_mutation(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            destination = root / final.NIGHT
            destination.mkdir(parents=True)
            for name in final.EVIDENCE:
                (destination / name).write_bytes((final.ROOT / final.NIGHT / name).read_bytes())
            final.inventory(root)
            path = destination / "heights.jsonl"
            raw = path.read_bytes()
            path.write_bytes(raw[:-1] + b" ")
            with self.assertRaises(ValueError):
                final.inventory(root)


if __name__ == "__main__":
    unittest.main()
