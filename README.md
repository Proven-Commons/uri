# uri: a URI reference split and resolver, with proved round trips

Status: in-progress

A split and resolver for URI references, in Lean, following
RFC 3986: the decomposition of section 3 and Appendix B,
recomposition as in section 5.3, and resolution as in
section 5.2. The definitions are in `Uri/Value.lean` (the
value, recomposition, and the well formed predicate),
`Uri/Parse.lean` (the split), and `Uri/Resolve.lean`
(paths, dot segment removal, merge, and resolution). The
rules are written out in `SPEC.md`. Percent escapes are
left exactly as written. A full grammar check is the
second slice, and normalization, as in section 6, comes
later.

The statements a reviewer approves are in `Spec.lean`,
with their proofs in `Proofs/SpecProofs.lean`. No reviewer
has approved them yet, so this project is not called
verified.

## How to run it

`lake build` builds the library, the proofs, and the
command line tool. The tool reads one request per line: an
operation, a space, and its input fields, each field a
string written as comma-separated decimal character
codes. The `split` operation takes one field, a URI
reference, and answers `ok:` and the five components of
the split. The `resolve` operation takes two fields, a
base and a reference, and answers `ok:` and the character
codes of the resolved reference, recomposed as section
5.3 directs. A malformed request answers `error`. See
`SPEC.md` for the full protocol.

```
lake build
printf 'split 102,111,111,58,47,47,97,47,98\n' | .lake/build/bin/uri
```

That request splits the reference `foo://a/b`, and the
answer is `ok:102,111,111;97;47,98;;`: the scheme `foo`,
the authority `a`, the path `/b`, and no query or
fragment.

```
printf 'resolve 104,116,116,112,58,47,47,97,47,98;103\n' | .lake/build/bin/uri
```

That request resolves the reference `g` against the base
`http://a/b`, and the answer is the codes of
`http://a/g`.

`python3 tests/run_tests.py` rebuilds the tool, runs the
fixed cases (every example of sections 5.4.1 and 5.4.2
against the RFC's base, the dot segment cases of section
5.2.4 and their edge cases, the split cases, and
malformed requests), then a differential run of generated
base and reference pairs against the Python oracle, with
`urljoin` as a second voice, and writes the outcome to
`tests/TEST-RESULTS.md`.

## What is proved

Each claim below names the theorem behind it. The
theorems are stated in `Spec.lean` (the challenge file,
where they end in `sorry`) and proved in
`Proofs/SpecProofs.lean`, under the same names.
`comparator.json` lists all of them.

| Claim | Theorem |
|-------|---------|
| Recomposing a split gives the original string back, for every string. | `Spec.print_split` |
| Splitting a recomposed value gives the value back, for well formed values. | `Spec.split_print` |
| After dot segment removal, a path taken apart again has no `.` or `..` segment. | `Spec.removeDotSegments_noDots` |
| Removing dot segments a second time changes nothing. | `Spec.removeDotSegments_idempotent` |
| Resolving against a base that has a scheme gives a target that has a scheme. | `Spec.resolve_scheme` |
| Against the base `http://a/b/c/d;p?q`, the reference `g` resolves to `http://a/b/c/g`. | `Spec.resolves_g` |
| Against the same base, the reference `./g` resolves to `http://a/b/c/g`. | `Spec.resolves_dot_slash_g` |
| Against the same base, the reference `g/` resolves to `http://a/b/c/g/`. | `Spec.resolves_g_slash` |
| Against the same base, the reference `/g` resolves to `http://a/g`. | `Spec.resolves_slash_g` |
| Against the same base, the reference `//g` resolves to `http://g`. | `Spec.resolves_slashes_g` |
| Against the same base, the reference `?y` resolves to `http://a/b/c/d;p?y`. | `Spec.resolves_query_y` |
| Against the same base, the reference `g?y` resolves to `http://a/b/c/g?y`. | `Spec.resolves_g_query_y` |
| Against the same base, the reference `#s` resolves to `http://a/b/c/d;p?q#s`. | `Spec.resolves_fragment_s` |
| Against the same base, the reference `g#s` resolves to `http://a/b/c/g#s`. | `Spec.resolves_g_fragment_s` |
| Against the same base, the reference `..` resolves to `http://a/b/`. | `Spec.resolves_dotdot` |
| Against the same base, the reference `../g` resolves to `http://a/b/g`. | `Spec.resolves_dotdot_g` |
| Removing dot segments from `/a/b/c/./../../g` gives `/a/g`, the first worked example of section 5.2.4. | `Spec.removes_dots_rfc_example` |
| Removing dot segments from `mid/content=5/../6` gives `mid/6`, the second worked example of section 5.2.4. | `Spec.removes_dots_mid_example` |

A value is well formed when a present scheme follows the
scheme rule, a present authority holds no slash, question
mark, or hash, the path holds no question mark or hash,
with an authority the path is empty or starts with a
slash, with no authority the path does not start with two
slashes, a present query holds no hash, and with neither
scheme nor authority the path has no scheme prefix:
before any colon there is either a slash or a run that
fails the scheme rule. `SPEC.md` states the same
conditions in its own section.

The no-dot-segments claim is stated about the path taken
apart again, because a dot segment is a segment: the
claim is that the segment list of the result holds
neither `.` nor `..`. The absoluteness claim is the part
of section 5.2.2 that says the target is an absolute URI
whenever the base is one.

The five claims rest on the proofs in
`Proofs/RoundTrip.lean` and `Proofs/Resolve.lean`, where
they are `print_split`, `split_print`,
`Uri.Proofs.removeDotSegments_noDots`,
`Uri.Proofs.removeDotSegments_idempotent`, and
`Uri.Proofs.resolve_scheme`. Each checks against the
standard axioms only: each depends on `propext` and
`Quot.sound`, or a subset of them; none depends on
`Classical.choice`, and none on any added axiom. A reader
can confirm this with `#print axioms` on the five
theorems; `Proofs/Verify.lean` prints them at build time.
The worked example theorems are single inputs checked in
the kernel with `decide +kernel`.

The command line tool in `Main.lean` calls `Uri.split`,
`Uri.resolve`, and `Uri.print` directly, the same
functions the theorems are about.

## What is not proved

- That resolution as a whole matches the RFC. The three
  claims in the table about removal and resolution, and
  the worked examples, are proved; merge, the query rule,
  and the rest of the transform are not. The tests check
  the whole transform against a Python oracle instead,
  including every worked example of sections 5.4.1 and
  5.4.2 under the strict reading, and the results file
  records the outcome.
- That the split accepts exactly the strings the section
  3 grammar allows. By design it accepts more: the
  grammar check is the second slice, and `SPEC.md` says
  what this slice does instead.
- The split operation's answer cannot tell a present
  empty component from an absent one: both are written as
  an empty field. The values keep the two apart, and so
  does resolution: the reference `?` brings an empty
  query where the empty reference brings none, and the
  tests pin that difference. The limit is in the tool's
  split answers, not in the values or the proofs.
- The second voice in the tests, `urllib.parse.urljoin`,
  disagreed with the tool on 1,997 of the 3,200 generated
  pairs, while the strict RFC oracle sided with the tool
  in every one of those cases. The disagreements are
  counted apart in the results file as named differences,
  never as failures.
- A differential against uriparser or Go's
  `URL.ResolveReference`, the oracles the plan named.
  Neither is present in the build environment, so neither
  was run, and the results file says what ran instead.
- The spelling of percent escapes, the forms of hosts and
  ports, and normalization of any kind.
- Reading requests and printing answers in `Main.lean`:
  splitting lines, the field separator, the decimal
  parser. The tests cover them, malformed requests
  included.
- Speed. The code works on lists of characters, which
  suits proofs, not large data.

## What you must trust

- The Lean kernel (Lean 4.35.0, pinned in
  `lean-toolchain`), which checks every proof.
- The Lean compiler, with the C compiler and linker
  shipped with it, which turns the proved definitions
  into the program that runs.
- The Lean runtime, which runs that program.
- The hardware the program runs on.
- Every dependency in `lake-manifest.json`: the manifest
  lists no packages, so there are no library dependencies
  to trust beyond the Lean toolchain itself.
- Lean's core library, including the compiled code it
  puts in place of some definitions the proofs reason
  about.
- The operating system the program runs on.
- That `SPEC.md` states the reading of RFC 3986 you
  intend. The proofs are about the split, the resolver,
  and recomposition following each other exactly; the
  fidelity of the spec to the RFC is a reading, pinned in
  `SPEC.md` where the RFC leaves a choice open, such as
  the strict reading of section 5.2.2.
- The strict Python reading of RFC 3986 written in the
  test harness, as the oracle in the differential tests.
  Its dot segment removal is the buffer algorithm of
  section 5.2.4, a different algorithm from the segment
  walk the Lean code proves about, so the two readings
  check each other. `urllib.parse.urljoin` ran only as a
  second voice; its disagreements are counted apart, as
  What is not proved records.
- The line handling in `Main.lean` (splitting a request
  line, the field separator, reading decimal codes). The
  tests drive it, and no proof covers it.
- There are no exceptions to item 4 of the bar: the
  project uses none of the features it forbids.

## Re-check it

1. `lake comparator --paranoid`: builds the challenge
   file `Spec.lean` and the proofs in a sandbox and
   checks that each theorem named in `comparator.json`
   proves exactly the statement in the challenge file,
   uses no axiom but the three standard ones, and is
   accepted by Lean's kernel and every other kernel
   shipped with Lean.
2. `python3 tests/run_tests.py`: the fixed cases, the
   differential against the strict oracle, and the
   `urljoin` second voice, with counts and any failures
   written to `tests/TEST-RESULTS.md`.
3. `lake build`: the library, the proofs, and the tool
   build clean, and `lake env lean Proofs/Verify.lean`
   prints the axiom list for the five claims.
4. Read `SPEC.md` against RFC 3986 and check the pinned
   readings are the ones you want.
