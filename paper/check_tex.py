#!/usr/bin/env python3
"""Static consistency checks for paper/main.tex and paper/references.bib.

This is not a TeX engine.  It catches the mistakes that most often break a
build or leave a dangling reference:

  * unbalanced braces, mismatched \\begin/\\end, odd number of `$' in a
    paragraph (verbatim blocks and comments are skipped);
  * \\ref/\\eqref without \\label, duplicate labels;
  * \\cite keys missing from references.bib, bibliography entries that are
    never cited, duplicate or malformed entries;
  * non-ASCII characters (the sources are kept ASCII-only).

With --lean-names it prints a Lean file that `#check's every declaration
named in the manuscript through \\lean{...}; CI elaborates that file, so
the correspondence table cannot silently go stale.

Usage:
    python3 paper/check_tex.py
    python3 paper/check_tex.py --lean-names > NameCheck.lean
"""
import pathlib
import re
import sys

HERE = pathlib.Path(__file__).resolve().parent
TEX = HERE / "main.tex"
BIB = HERE / "references.bib"


def strip_comments(text):
    out = []
    for line in text.split("\n"):
        out.append(re.sub(r"(?<!\\)%.*", "", line))
    return "\n".join(out)


def strip_verbatim(text):
    text = re.sub(r"\\begin\{verbatim\}.*?\\end\{verbatim\}", "", text, flags=re.S)
    text = re.sub(r"\\(?:lean|path|url)\{[^{}]*\}", "", text)
    return text


def brace_errors(text, name):
    errors, depth = [], 0
    i = 0
    while i < len(text):
        ch = text[i]
        if ch == "\\":
            i += 2
            continue
        if ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
            if depth < 0:
                line = text.count("\n", 0, i) + 1
                errors.append(f"{name}: unmatched '}}' near stripped line {line}")
                depth = 0
        i += 1
    if depth:
        errors.append(f"{name}: {depth} unclosed '{{'")
    return errors


def environment_errors(text):
    errors, stack = [], []
    for m in re.finditer(r"\\(begin|end)\{([^}]*)\}", text):
        kind, env = m.groups()
        if kind == "begin":
            stack.append(env)
        elif not stack or stack.pop() != env:
            errors.append(f"main.tex: \\end{{{env}}} does not match")
    errors += [f"main.tex: \\begin{{{env}}} never closed" for env in stack]
    return errors


def dollar_errors(text):
    errors = []
    for number, para in enumerate(re.split(r"\n\s*\n", text), 1):
        if len(re.findall(r"(?<!\\)\$", para)) % 2:
            errors.append(f"main.tex: odd number of '$' in paragraph {number}: "
                          f"{para.strip()[:60]!r}")
    return errors


def bib_entries(text):
    keys = re.findall(r"^@\w+\{([^,\s]+),", text, flags=re.M)
    return keys


def main():
    raw = TEX.read_text(encoding="utf-8")
    bib_raw = BIB.read_text(encoding="utf-8")
    lean_names = sorted(set(re.findall(r"\\lean\{([^}]*)\}", raw)))

    if "--lean-names" in sys.argv[1:]:
        print("import CollatzLab")
        for name in lean_names:
            print(f"#check @CollatzLab.{name}")
        return 0

    errors = []
    for path, text in ((TEX, raw), (BIB, bib_raw)):
        for number, line in enumerate(text.split("\n"), 1):
            if any(ord(ch) > 126 or (ord(ch) < 32 and ch != "\t") for ch in line):
                errors.append(f"{path.name}:{number}: non-ASCII or control character")

    tex = strip_verbatim(strip_comments(raw))
    errors += brace_errors(tex, "main.tex")
    errors += environment_errors(strip_comments(raw))
    errors += dollar_errors(tex)

    labels = re.findall(r"\\label\{([^}]*)\}", tex)
    for label in sorted(set(labels)):
        if labels.count(label) > 1:
            errors.append(f"main.tex: duplicate label {label}")
    refs = re.findall(r"\\(?:eq)?ref\{([^}]*)\}", tex)
    for ref in sorted(set(refs)):
        if ref not in labels:
            errors.append(f"main.tex: reference to undefined label {ref}")

    bib = strip_comments(bib_raw)
    errors += brace_errors(bib, "references.bib")
    keys = bib_entries(bib)
    for key in sorted(set(keys)):
        if keys.count(key) > 1:
            errors.append(f"references.bib: duplicate key {key}")
    cited = set()
    for source in (tex, bib):
        for group in re.findall(r"\\cite(?:\[[^\]]*\])?\{([^}]*)\}", source):
            cited.update(k.strip() for k in group.split(","))
    for key in sorted(cited - set(keys)):
        errors.append(f"citation of missing bibliography key {key}")
    for key in sorted(set(keys) - cited):
        errors.append(f"references.bib: entry {key} is never cited")
    for entry in re.split(r"^@", bib, flags=re.M)[1:]:
        key = entry.split("{", 1)[1].split(",", 1)[0]
        for field in ("author", "title", "year"):
            if not re.search(rf"^\s*{field}\s*=", entry, flags=re.M):
                errors.append(f"references.bib: {key} lacks field {field}")

    if errors:
        print("\n".join(errors))
        return 1
    print(f"paper check passed: {len(set(labels))} labels, {len(set(refs))} "
          f"distinct references, {len(keys)} bibliography entries (all cited), "
          f"{len(lean_names)} Lean names")
    return 0


if __name__ == "__main__":
    sys.exit(main())
