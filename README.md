# uri: a URI reference split and resolver, with proved round trips

A split and resolver for URI references, in Lean, following
RFC 3986: the decomposition of section 3 and Appendix B,
recomposition as in section 5.3, and resolution as in
section 5.2. The definitions are in `Uri/Value.lean` (the
value, recomposition, and the well formed predicate),
`Uri/Parse.lean` (the split), and `Uri/Resolve.lean` (merge,
dot segment removal, and resolution). The proofs are in
`Proofs/RoundTrip.lean` and `Proofs/Resolve.lean`. Percent
escapes are left exactly as written. A full grammar check is
the second slice, and normalization, as in section 6, comes
later.

Status: the specification has not been approved by a
reviewer, so do not call this verified. The statements a
reviewer approves (the bar's `Spec.lean`) have not been
added yet.

## What is proved

| Claim | Theorem |
|-------|---------|
| Recomposing a split gives the original string back, for every string. | `print_split` |
| Splitting a recomposed value gives the value back, for well formed values. | `split_print` |
| After dot segment removal, a path taken apart again has no `.` or `..` segment. | `Uri.Proofs.removeDotSegments_noDots` |
| Removing dot segments a second time changes nothing. | `Uri.Proofs.removeDotSegments_idempotent` |
| Resolving against a base that has a scheme gives a target that has a scheme. | `Uri.Proofs.resolve_scheme` |

A value is well formed when a present scheme follows the
scheme rule, a present authority holds no slash, question
mark, or hash, the path holds no question mark or hash, with
an authority the path is empty or starts with a slash, with
no authority the path does not start with two slashes, a
present query holds no hash, and with neither scheme nor
authority the path has no scheme prefix: before any colon
there is either a slash or a run that fails the scheme rule.
`SPEC.md` states the same conditions in its own section.

The no-dot-segments claim is stated about the path taken
apart again, because a dot segment is a segment: the claim
is that the segment list of the result holds neither `.`
nor `..`. The absoluteness claim is the part of section
5.2.2 that says the target is an absolute URI whenever the
base is one.

These theorems check against the standard axioms only. Each
depends on `propext` and `Quot.sound`, or a subset of them;
none depends on `Classical.choice` and none on any added
axiom. A reader can confirm this with `#print axioms` on the
five theorems; `Proofs/Verify.lean` prints them at build
time.

The command-line tool in `Main.lean` calls these functions
directly.

## What is not proved

- That resolution as a whole matches the RFC. The three
  claims in the table about removal and resolution are
  proved; merge, the query rule, and the rest of the
  transform are not. The tests check the whole transform
  against a Python oracle instead, including every worked
  example of sections 5.4.1 and 5.4.2 under the strict
  reading, and the results file records the outcome.
- That the split accepts exactly the strings the section 3
  grammar allows. By design it accepts more: the grammar
  check is the second slice, and `SPEC.md` says what this
  slice does instead.
- The spelling of percent escapes, the forms of hosts and
  ports, and normalization of any kind.
- Reading requests and printing answers in `Main.lean`:
  splitting lines, the field separator, the decimal parser.
  The tests cover them, malformed requests included.
- Speed. The code works on lists of characters, which suits
  proofs, not large data.

## What you must trust

- The Lean kernel, which checks the proofs.
- The Lean compiler, with the C compiler and linker shipped
  with it, and the runtime, which turn the proved
  definitions into the program that runs.
- Lean's core library, including the compiled code it puts
  in place of some definitions the proofs reason about.
- The operating system and hardware it runs on.
- The strict Python reading of RFC 3986 written in the test
  harness, as the oracle in the differential tests. Its dot
  segment removal is the buffer algorithm of section 5.2.4,
  a different algorithm from the segment walk the Lean code
  proves about, so the two readings check each other.
  `urllib.parse.urljoin` ran as a second voice; where it
  disagrees with the tool while the oracle agrees with the
  tool, the results file counts the case apart as a named
  difference. The plan named uriparser and Go's
  `URL.ResolveReference` as oracles; neither is present in
  the build environment, so neither was run, and the results
  file says what ran instead.

This project has no dependencies beyond Lean itself.

## Run it

Needs Linux and [elan](https://github.com/leanprover/elan).
Build, then feed request lines to the tool:

```
lake build
printf 'split 102,111,111,58,47,47,97,47,98\n' | .lake/build/bin/uri
```

That request splits the reference `foo://a/b`, and the
answer is `ok:102,111,111;97;47,98;;`: the scheme `foo`, the
authority `a`, the path `/b`, and no query or fragment.

```
printf 'resolve 104,116,116,112,58,47,47,97,47,98;103\n' | .lake/build/bin/uri
```

That request resolves the reference `g` against the base
`http://a/b`, and the answer is the codes of
`http://a/g`. A malformed request, such as `resolve` with
one field, answers `error`. See `SPEC.md` for the full
protocol.

## Re-check it

```
lake build
python3 tests/run_tests.py
```

The test run rebuilds the tool, runs the fixed cases (every
example of sections 5.4.1 and 5.4.2 against the RFC's base,
the dot segment cases of section 5.2.4 and their edge cases,
the split cases, and malformed requests), then a
differential run of generated base and reference pairs
against the Python oracle, with `urljoin` as a second voice,
and rewrites `tests/TEST-RESULTS.md`. The numbers in that
file are the record of the run described there.
