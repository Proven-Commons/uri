#!/usr/bin/env python3
"""Tests for the Lean URI reference split and resolver.

Four parts.

1. Fixed resolution cases from RFC 3986: every example of
   section 5.4.1 (normal) and section 5.4.2 (abnormal) against
   the base `http://a/b/c/d;p?q`, with the results the RFC
   prints. The abnormal set is checked with the strict reading
   of section 5.2.2, so `http:g` resolves to `http:g`.

2. Fixed dot segment cases: the two examples of section
   5.2.4 and hand derived edge cases (empty paths, lone dots,
   trailing dots, consecutive slashes, dotted segments that
   are not dot segments). They run through `resolve` against
   an empty base, which returns the dot-removed path itself.
   Each hand written expectation is also checked against the
   oracle, so a mistake in the hand list shows as a
   disagreement, not a pass.

3. Fixed split cases: the section 3 example decomposed, the
   empty string, and a fragment-only reference. Plus malformed
   request lines, which must be answered `error`.

   One limit of the answer format: a split answer writes an
   absent component and a present component with no characters
   (the query of the reference `?`) both as an empty field, so
   the two cannot be told apart in a split answer. Split
   answers are therefore compared in the shown form, where a
   present empty component reads as absent. The distinction
   itself is real in the values and in resolution, and the
   fixed resolution cases and the differential run check it
   there: against the section 5.4 base, the reference `?`
   resolves with an empty query and the empty reference
   resolves with the base query.

4. A differential run: generated (base, reference) pairs
   checked against a Python oracle written in this harness.
   The oracle splits by the stepwise reading of Appendix B,
   merges by section 5.2.3, removes dot segments by the
   buffer algorithm of section 5.2.4 (a different algorithm
   from the segment walk the Lean code proves about), resolves
   by the strict transform of section 5.2.2, and recomposes by
   section 5.3. `urllib.parse.urljoin` runs as a second voice:
   where it disagrees with the tool while the oracle agrees
   with the tool, the case is counted apart as a named
   difference, with the disagreement shown.

    python3 tests/run_tests.py [--seed N] [--count N]

The tool is driven one batch process per chunk of requests,
input written and closed, output drained until the process
exits. It builds the executable first, writes
tests/TEST-RESULTS.md, and exits non-zero if any check fails.
It needs Python 3.11 or later.
"""

import argparse
import platform
import random
import subprocess
import sys
from pathlib import Path
from urllib.parse import urljoin

ROOT = Path(__file__).resolve().parent.parent
EXE = ROOT / ".lake" / "build" / "bin" / "uri"

# ---------------------------------------------------------------- oracle

SCHEME_CHARS = set("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789+-.")


def scheme_ok(pre):
    if not pre:
        return False
    if not ("a" <= pre[0] <= "z" or "A" <= pre[0] <= "Z"):
        return False
    return all(c in SCHEME_CHARS for c in pre)


def split_ref(s):
    """The stepwise split: fragment at the first hash, query at
    the first question mark in what remains, a scheme when the
    run before the first colon follows the scheme rule, an
    authority when what remains starts with two slashes."""
    frag = None
    if "#" in s:
        s, frag = s.split("#", 1)
    query = None
    if "?" in s:
        s, query = s.split("?", 1)
    scheme = None
    if ":" in s:
        pre, rest = s.split(":", 1)
        if scheme_ok(pre):
            scheme, s = pre, rest
    authority = None
    if s.startswith("//"):
        rest = s[2:]
        if "/" in rest:
            authority, tail = rest.split("/", 1)
            s = "/" + tail
        else:
            authority, s = rest, ""
    return (scheme, authority, s, query, frag)


def remove_dot_segments(path):
    """The buffer algorithm of section 5.2.4, as written there."""
    inp = path
    out = ""
    while inp:
        if inp.startswith("../"):
            inp = inp[3:]
        elif inp.startswith("./"):
            inp = inp[2:]
        elif inp.startswith("/./"):
            inp = "/" + inp[3:]
        elif inp == "/.":
            inp = "/"
        elif inp.startswith("/../"):
            inp = "/" + inp[4:]
            out = out[: out.rfind("/")] if "/" in out else ""
        elif inp == "/..":
            inp = "/"
            out = out[: out.rfind("/")] if "/" in out else ""
        elif inp in (".", ".."):
            inp = ""
        else:
            if inp.startswith("/"):
                nxt = inp.find("/", 1)
            else:
                nxt = inp.find("/")
            if nxt == -1:
                out += inp
                inp = ""
            else:
                out += inp[:nxt]
                inp = inp[nxt:]
    return out


def merge_paths(base, ref_path):
    """Section 5.2.3."""
    bs, ba, bp, bq, bf = base
    if ba is not None and bp == "":
        return "/" + ref_path
    idx = bp.rfind("/")
    if idx == -1:
        return ref_path
    return bp[: idx + 1] + ref_path


def recompose(u):
    """Section 5.3."""
    scheme, authority, path, query, frag = u
    out = ""
    if scheme is not None:
        out += scheme + ":"
    if authority is not None:
        out += "//" + authority
    out += path
    if query is not None:
        out += "?" + query
    if frag is not None:
        out += "#" + frag
    return out


def resolve_ref(base_s, ref_s):
    """The strict transform of section 5.2.2, on strings."""
    base = split_ref(base_s)
    ref = split_ref(ref_s)
    bs, ba, bp, bq, bf = base
    rs, ra, rp, rq, rf = ref
    if rs is not None:
        t = (rs, ra, remove_dot_segments(rp), rq, rf)
    elif ra is not None:
        t = (bs, ra, remove_dot_segments(rp), rq, rf)
    else:
        if rp == "":
            tp = bp
            tq = rq if rq is not None else bq
        elif rp.startswith("/"):
            tp = remove_dot_segments(rp)
            tq = rq
        else:
            tp = remove_dot_segments(merge_paths(base, rp))
            tq = rq
        t = (bs, ba, tp, tq, rf)
    return recompose(t)


def shown(u):
    """A split in the shown form of a split answer: a present
    component with no characters reads as absent."""
    scheme, authority, path, query, frag = u
    return (
        scheme if scheme else None,
        authority if authority else None,
        path,
        query if query else None,
        frag if frag else None,
    )


# ---------------------------------------------------------------- the tool


def codes(s):
    return ",".join(str(ord(c)) for c in s)


def decodes(field):
    if field == "":
        return ""
    return "".join(chr(int(n)) for n in field.split(","))


class Tool:
    def __init__(self):
        self.requests = []
        self.answers = []

    def ask(self, line):
        self.requests.append(line)
        return len(self.requests) - 1

    def run(self):
        inp = "\n".join(self.requests) + "\n"
        proc = subprocess.run(
            [str(EXE)], input=inp, capture_output=True, text=True, timeout=600
        )
        if proc.returncode != 0:
            raise RuntimeError(f"tool exited {proc.returncode}: {proc.stderr[:400]}")
        self.answers = proc.stdout.splitlines()
        if len(self.answers) != len(self.requests):
            raise RuntimeError(
                f"tool gave {len(self.answers)} answers for {len(self.requests)} requests"
            )

    def resolve(self, base, ref):
        i = self.ask(f"resolve {codes(base)};{codes(ref)}")
        return lambda: self._string_answer(i)

    def split(self, s):
        i = self.ask(f"split {codes(s)}")
        return lambda: self._split_answer(i)

    def raw(self, line):
        i = self.ask(line)
        return lambda: self.answers[i]

    def _string_answer(self, i):
        a = self.answers[i]
        if not a.startswith("ok:"):
            return None
        return decodes(a[3:])

    def _split_answer(self, i):
        a = self.answers[i]
        if not a.startswith("ok:"):
            return None
        fields = a[3:].split(";")
        if len(fields) != 5:
            return None
        vals = [decodes(f) for f in fields]
        # absent is an empty field; the path field is the path itself
        return (
            vals[0] if fields[0] != "" else None,
            vals[1] if fields[1] != "" else None,
            vals[2],
            vals[3] if fields[3] != "" else None,
            vals[4] if fields[4] != "" else None,
        )


# ---------------------------------------------------------------- fixed cases

BASE54 = "http://a/b/c/d;p?q"

CASES_541 = [
    ("g:h", "g:h"),
    ("g", "http://a/b/c/g"),
    ("./g", "http://a/b/c/g"),
    ("g/", "http://a/b/c/g/"),
    ("/g", "http://a/g"),
    ("//g", "http://g"),
    ("?y", "http://a/b/c/d;p?y"),
    ("g?y", "http://a/b/c/g?y"),
    ("#s", "http://a/b/c/d;p?q#s"),
    ("g#s", "http://a/b/c/g#s"),
    ("g?y#s", "http://a/b/c/g?y#s"),
    (";x", "http://a/b/c/;x"),
    ("g;x", "http://a/b/c/g;x"),
    ("g;x?y#s", "http://a/b/c/g;x?y#s"),
    ("", "http://a/b/c/d;p?q"),
    (".", "http://a/b/c/"),
    ("./", "http://a/b/c/"),
    ("..", "http://a/b/"),
    ("../", "http://a/b/"),
    ("../g", "http://a/b/g"),
    ("../..", "http://a/"),
    ("../../", "http://a/"),
    ("../../g", "http://a/g"),
]

CASES_542 = [
    ("../../../g", "http://a/g"),
    ("../../../../g", "http://a/g"),
    ("/./g", "http://a/g"),
    ("/../g", "http://a/g"),
    ("g.", "http://a/b/c/g."),
    (".g", "http://a/b/c/.g"),
    ("g..", "http://a/b/c/g.."),
    ("..g", "http://a/b/c/..g"),
    ("./../g", "http://a/b/g"),
    ("./g/.", "http://a/b/c/g/"),
    ("g/./h", "http://a/b/c/g/h"),
    ("g/../h", "http://a/b/c/h"),
    ("g;x=1/./y", "http://a/b/c/g;x=1/y"),
    ("g;x=1/../y", "http://a/b/c/y"),
    ("g?y/./x", "http://a/b/c/g?y/./x"),
    ("g?y/../x", "http://a/b/c/g?y/../x"),
    ("g#s/./x", "http://a/b/c/g#s/./x"),
    ("g#s/../x", "http://a/b/c/g#s/../x"),
    ("http:g", "http:g"),
]

# (input path, expected output) for removeDotSegments, run
# through resolve against an empty base.
DOT_CASES = [
    ("/a/b/c/./../../g", "/a/g"),
    ("mid/content=5/../6", "mid/6"),
    ("", ""),
    ("/", "/"),
    (".", ""),
    ("..", ""),
    ("/.", "/"),
    ("/..", "/"),
    ("./", ""),
    ("../", ""),
    ("/./", "/"),
    ("/../", "/"),
    ("a/./b", "a/b"),
    ("a/../b", "/b"),
    ("a/.", "a/"),
    ("a/..", "/"),
    ("a/b/./", "a/b/"),
    ("a/b/../", "a/"),
    ("a//b", "a//b"),
    ("/a//b", "/a//b"),
    ("a//../b", "a/b"),
    ("./a", "a"),
    ("../a", "a"),
    ("a/./", "a/"),
    ("a/../", "/"),
    ("/a/./b", "/a/b"),
    ("/a/../b", "/b"),
    ("g.", "g."),
    (".g", ".g"),
    ("g..", "g.."),
    ("..g", "..g"),
    ("/a/b/c/.", "/a/b/c/"),
    ("/a/b/c/..", "/a/b/"),
    ("a/b/c/../../g", "a/g"),
    ("../..", ""),
    ("/../..", "/"),
]

# (input, (scheme, authority, path, query, fragment)) in the
# shown form of a split answer: a present empty component
# reads as absent, as the module note explains. The case `?`
# is the one that shows it.
SPLIT_CASES = [
    (
        "foo://example.com:8042/over/there?name=ferret#nose",
        ("foo", "example.com:8042", "/over/there", "name=ferret", "nose"),
    ),
    ("", (None, None, "", None, None)),
    ("#nose", (None, None, "", None, "nose")),
    ("?", (None, None, "", None, None)),
    ("//g", (None, "g", "", None, None)),
    ("a:b", ("a", None, "b", None, None)),
    ("a/b:c", (None, None, "a/b:c", None, None)),
    ("1a:b", (None, None, "1a:b", None, None)),
    ("//a/b?c#d", (None, "a", "/b", "c", "d")),
    ("g;x?y#s", (None, None, "g;x", "y", "s")),
]

# Resolution cases beyond the RFC lists: the absent versus
# empty distinction, which a split answer cannot show, is
# visible here. Against the section 5.4 base, `?` brings its
# own empty query and `#` its own empty fragment, while the
# empty reference (in the 5.4.1 list) keeps the base query.
EXTRA_RESOLVE = [
    ("?", "http://a/b/c/d;p?"),
    ("#", "http://a/b/c/d;p?q#"),
    ("?#", "http://a/b/c/d;p?#"),
]

MALFORMED = [
    "",
    "bogus",
    "bogus 1,2",
    "split 1,2,,3",
    "split 97 98",
    "split 1114112",
    "split 55296",
    "split 97;",
    "resolve",
    "resolve 97",
    "resolve 97;98;99",
    "resolve 97;x",
    "resolve ;97;98",
    " split 97",
    "split  97",
]


# ---------------------------------------------------------------- generated

SEGMENTS = [
    "", "a", "b", "g", "h", ".", "..", ".g", "g.", "g..", "..g",
    "d;p", "x=1", "%41", "mid", "content=5", "-", "_", "~", "seg",
    "a b".replace(" ", "%20"), ":", "@", "a:b", "...", "..a..",
]
SCHEMES = ["http", "https", "g", "foo", "a+b-c.d", "A1", "z"]
BAD_SCHEME_HEADS = ["1a", "+x", "9", ".a"]
AUTHORITIES = ["a", "g", "example.com:8042", "user@host", "", "a.b.c", "h:80"]
QUERIES = ["q", "y", "name=ferret", "y/./x", "y/../x", "", "p;q", "a?b".replace("?", "%3F")]
FRAGMENTS = ["s", "nose", "s/./x", "s/../x", "", "frag"]


def gen_path(rng):
    n = rng.randrange(0, 5)
    parts = [rng.choice(SEGMENTS) for _ in range(n)]
    p = "/".join(parts)
    if rng.random() < 0.4:
        p = "/" + p
    if rng.random() < 0.2:
        p += "/"
    return p


def gen_ref(rng):
    r = rng.random()
    if r < 0.06:
        # raw chaos string
        pool = "abg:/?#;.=&%xy01"
        return "".join(rng.choice(pool) for _ in range(rng.randrange(0, 10)))
    out = ""
    if rng.random() < 0.3:
        if rng.random() < 0.15:
            out += rng.choice(BAD_SCHEME_HEADS) + ":"
        else:
            out += rng.choice(SCHEMES) + ":"
    if rng.random() < 0.3:
        out += "//" + rng.choice(AUTHORITIES)
    out += gen_path(rng)
    if rng.random() < 0.35:
        out += "?" + rng.choice(QUERIES)
    if rng.random() < 0.3:
        out += "#" + rng.choice(FRAGMENTS)
    return out


def gen_base(rng):
    out = rng.choice(SCHEMES) + ":"
    if rng.random() < 0.75:
        out += "//" + rng.choice(AUTHORITIES)
    out += gen_path(rng)
    if rng.random() < 0.3:
        out += "?" + rng.choice(QUERIES)
    return out


# ---------------------------------------------------------------- main


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=20261026)
    ap.add_argument("--count", type=int, default=3200)
    args = ap.parse_args()

    build = subprocess.run(
        ["lake", "build"], cwd=ROOT, capture_output=True, text=True, timeout=1200
    )
    if build.returncode != 0:
        print(build.stdout[-2000:], build.stderr[-2000:])
        print("lake build failed")
        return 1
    lean_version = subprocess.run(
        ["lake", "env", "lean", "--version"],
        cwd=ROOT, capture_output=True, text=True, timeout=120,
    ).stdout.strip()

    tool = Tool()
    jobs = []  # (kind, label, thunk, expected)

    for ref, expected in CASES_541:
        jobs.append(("541", ref, tool.resolve(BASE54, ref), expected))
    for ref, expected in CASES_542:
        jobs.append(("542", ref, tool.resolve(BASE54, ref), expected))
    for path, expected in DOT_CASES:
        jobs.append(("dot", path, tool.resolve("", path), expected))
    for s, expected in SPLIT_CASES:
        jobs.append(("split", s, tool.split(s), expected))
    for ref, expected in EXTRA_RESOLVE:
        jobs.append(("extra", ref, tool.resolve(BASE54, ref), expected))
    for line in MALFORMED:
        jobs.append(("malformed", line, tool.raw(line), "error"))

    rng = random.Random(args.seed)
    pairs = [(gen_base(rng), gen_ref(rng)) for _ in range(args.count)]
    gen_jobs = []
    for base, ref in pairs:
        gen_jobs.append((base, ref, tool.resolve(base, ref), resolve_ref(base, ref)))
    gen_split_jobs = []
    seen = set()
    for base, ref in pairs:
        for s in (base, ref):
            if s not in seen:
                seen.add(s)
                gen_split_jobs.append((s, tool.split(s), shown(split_ref(s))))

    tool.run()

    failures = []
    counts = {}

    def record(kind, ok, label, got, expected):
        counts[kind] = counts.get(kind, 0) + (1 if ok else 0)
        counts[kind + "_total"] = counts.get(kind + "_total", 0) + 1
        if not ok:
            failures.append(f"{kind} {label!r}: got {got!r}, expected {expected!r}")

    for kind, label, thunk, expected in jobs:
        got = thunk()
        record(kind, got == expected, label, got, expected)

    # hand written dot expectations must also match the oracle
    oracle_dot_bad = 0
    for path, expected in DOT_CASES:
        if remove_dot_segments(path) != expected:
            oracle_dot_bad += 1
            failures.append(
                f"dot-oracle {path!r}: oracle gives {remove_dot_segments(path)!r}, "
                f"hand expectation {expected!r}"
            )

    urljoin_agree = 0
    urljoin_named = {}  # (base, ref) -> (tool result, urljoin result)
    for base, ref, thunk, expected in gen_jobs:
        got = thunk()
        record("gen", got == expected, f"{base} + {ref}", got, expected)
        if got == expected:
            uj = urljoin(base, ref)
            if uj == got:
                urljoin_agree += 1
            else:
                urljoin_named[(base, ref)] = (got, uj)
    for s, thunk, expected in gen_split_jobs:
        got = thunk()
        record("gensplit", got == expected, s, got, expected)

    # the fixed http:g case, as a named urljoin difference
    httpg_tool = resolve_ref(BASE54, "http:g")
    httpg_uj = urljoin(BASE54, "http:g")

    total = sum(v for k, v in counts.items() if k.endswith("_total"))
    agreed = sum(v for k, v in counts.items() if not k.endswith("_total"))
    lines = []
    lines.append("# Test results")
    lines.append("")
    lines.append("Written by `tests/run_tests.py`. Rerun it to check these numbers.")
    lines.append("")
    lines.append(
        "- Oracle: a strict Python reading of RFC 3986 written in the harness "
        f"(Python {platform.python_version()}): the stepwise split of Appendix B, "
        "merge by section 5.2.3, dot segment removal by the buffer algorithm of "
        "section 5.2.4, the strict transform of section 5.2.2, recomposition by "
        "section 5.3"
    )
    lines.append(
        "- Second voice: urllib.parse.urljoin from the same Python; disagreements "
        "with the tool where the oracle sides with the tool are counted apart as "
        "named differences, never as failures"
    )
    lines.append(f"- Lean: {lean_version}")
    lines.append(f"- Seed: {args.seed}")
    lines.append(
        f"- Section 5.4.1 normal cases: {counts.get('541', 0)} of "
        f"{counts.get('541_total', 0)} agreements"
    )
    lines.append(
        f"- Section 5.4.2 abnormal cases (strict): {counts.get('542', 0)} of "
        f"{counts.get('542_total', 0)} agreements"
    )
    lines.append(
        f"- Section 5.2.4 dot cases (with the oracle checked against the same "
        f"hand written expectations): {counts.get('dot', 0)} of "
        f"{counts.get('dot_total', 0)} agreements, {oracle_dot_bad} oracle "
        f"disagreements with the hand list"
    )
    lines.append(
        f"- Split fixed cases (shown form, see the harness note): "
        f"{counts.get('split', 0)} of {counts.get('split_total', 0)} agreements"
    )
    lines.append(
        f"- Absent versus empty resolution cases: {counts.get('extra', 0)} of "
        f"{counts.get('extra_total', 0)} agreements"
    )
    lines.append(
        f"- Malformed requests answered error: {counts.get('malformed', 0)} of "
        f"{counts.get('malformed_total', 0)}"
    )
    lines.append(
        f"- Generated pairs: {args.count} (resolve {counts.get('gen', 0)} of "
        f"{counts.get('gen_total', 0)} agreements; split of every distinct "
        f"generated string {counts.get('gensplit', 0)} of "
        f"{counts.get('gensplit_total', 0)} agreements)"
    )
    lines.append(
        f"- urljoin agreements on generated pairs the oracle settled for the "
        f"tool: {urljoin_agree}; counted apart as named differences: "
        f"{len(urljoin_named)}"
    )
    lines.append(f"- Differential inputs: {total}")
    lines.append(f"- Differential agreements: {agreed}")
    lines.append("- Named differences:")
    lines.append(
        f"  - `http:g` against `http://a/b/c/d;p?q` (fixed case): the strict "
        f"reading keeps the reference as it stands, giving `{httpg_tool}`; "
        f"urljoin drops a scheme that matches the base and gives `{httpg_uj}`."
    )
    kinds = {}
    for (base, ref), (got, uj) in urljoin_named.items():
        if uj == ref:
            kind = "urljoin returns the reference unchanged; the base takes no part"
        elif split_ref(ref)[0] is not None and split_ref(ref)[0] == split_ref(base)[0]:
            kind = "urljoin reads a reference whose scheme matches the base in the non-strict way"
        else:
            kind = "other urljoin readings"
        kinds.setdefault(kind, []).append((base, ref, got, uj))
    for kind, items in sorted(kinds.items(), key=lambda kv: -len(kv[1])):
        lines.append(f"  - {kind}: {len(items)} cases")
        for base, ref, got, uj in sorted(items)[:3]:
            lines.append(
                f"    - base `{base}`, reference `{ref}`: tool and oracle give "
                f"`{got}`; urljoin gives `{uj}`"
            )
    lines.append(f"- Failures: {len(failures)}")
    for f in failures[:30]:
        lines.append(f"  - {f}")
    lines.append("")
    (ROOT / "tests" / "TEST-RESULTS.md").write_text("\n".join(lines))

    print("\n".join(lines))
    return 0 if not failures else 1


if __name__ == "__main__":
    sys.exit(main())
