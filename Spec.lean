/-
  The specification as Lean statements: the challenge file.

  A reviewer who did not write this file approves it, and `bar.toml`
  records the SHA-256 it had then. The proofs live in `Proofs`
  (`Proofs/SpecProofs.lean`); `lake comparator` checks that each one
  proves exactly the statement written here. The `sorry` below is
  expected in this file only.

  The statements use only the definitions in `Uri/Value.lean`,
  `Uri/Parse.lean`, and `Uri/Resolve.lean`, the code under proof
  named in `bar.toml`. No definition of their own is needed, so
  this project has no `Spec/Defs.lean`: the one predicate the
  statements use besides the functions themselves, `Uri.NoDots`,
  stands in `Uri/Resolve.lean` with the code it speaks of.
-/

import Uri

/-! ## The round trips

The two statements the split stands on. Each one is the statement
of the proved theorem of the same shape in `Proofs/RoundTrip.lean`,
over the same well formedness predicate, `Uri.WF`. -/

/-- Recomposition of a split: the printed form of the split of
    any string is the string itself. So a split that dropped or
    added a character fails this statement. -/
theorem Spec.print_split (s : List Char) :
    Uri.print (Uri.split s) = s := sorry

/-- Splitting a recomposed value gives the value back, for
    values that satisfy `Uri.WF`. Without the conditions of
    `WF` a printed value can be genuinely ambiguous: a path of
    `a:b` printed with no scheme reads back as the scheme `a`
    and the path `b`. -/
theorem Spec.split_print (u : Uri.Uri) (h : Uri.WF u) :
    Uri.split (Uri.print u) = u := sorry

/-! ## Dot segment removal and resolution

The three claims of `Proofs/Resolve.lean`, stated as they are
proved there. -/

/-- After dot segment removal, a path taken apart again has no
    `.` or `..` segment. The claim is stated about the path
    taken apart again, because a dot segment is a segment. -/
theorem Spec.removeDotSegments_noDots (p : List Char) :
    Uri.NoDots (Uri.splitPath (Uri.removeDotSegments p)).2 := sorry

/-- Removing dot segments a second time changes nothing. -/
theorem Spec.removeDotSegments_idempotent (p : List Char) :
    Uri.removeDotSegments (Uri.removeDotSegments p) =
      Uri.removeDotSegments p := sorry

/-- Resolving against a base that has a scheme gives a target
    that has a scheme, as section 5.2.2 directs: the target
    scheme is the reference's own scheme when it has one, and
    the base's otherwise. -/
theorem Spec.resolve_scheme (base ref : Uri.Uri)
    (h : base.scheme.isSome = true) :
    (Uri.resolve base ref).scheme.isSome = true := sorry

/-! ## Worked examples of section 5.4.1

Single resolutions against the RFC's base, `http://a/b/c/d;p?q`,
stated the way the command line tool computes them: split the
base and the reference, resolve, and recompose. Each expected
result is the one section 5.4.1 prints. The differential tests
cover every example of sections 5.4.1 and 5.4.2; these
statements pin the normal cases a reader is most likely to
check by hand. -/

/-- The reference `g` resolves to `http://a/b/c/g`. -/
theorem Spec.resolves_g :
    Uri.print (Uri.resolve (Uri.split "http://a/b/c/d;p?q".toList)
      (Uri.split "g".toList)) = "http://a/b/c/g".toList := sorry

/-- The reference `./g` resolves to `http://a/b/c/g`. -/
theorem Spec.resolves_dot_slash_g :
    Uri.print (Uri.resolve (Uri.split "http://a/b/c/d;p?q".toList)
      (Uri.split "./g".toList)) = "http://a/b/c/g".toList := sorry

/-- The reference `g/` resolves to `http://a/b/c/g/`. -/
theorem Spec.resolves_g_slash :
    Uri.print (Uri.resolve (Uri.split "http://a/b/c/d;p?q".toList)
      (Uri.split "g/".toList)) = "http://a/b/c/g/".toList := sorry

/-- The reference `/g` resolves to `http://a/g`. -/
theorem Spec.resolves_slash_g :
    Uri.print (Uri.resolve (Uri.split "http://a/b/c/d;p?q".toList)
      (Uri.split "/g".toList)) = "http://a/g".toList := sorry

/-- The reference `//g` resolves to `http://g`: the reference
    brings its own authority, and the base gives the scheme. -/
theorem Spec.resolves_slashes_g :
    Uri.print (Uri.resolve (Uri.split "http://a/b/c/d;p?q".toList)
      (Uri.split "//g".toList)) = "http://g".toList := sorry

/-- The reference `?y` resolves to `http://a/b/c/d;p?y`: an
    empty path keeps the base path, and the query comes from
    the reference. -/
theorem Spec.resolves_query_y :
    Uri.print (Uri.resolve (Uri.split "http://a/b/c/d;p?q".toList)
      (Uri.split "?y".toList)) =
        "http://a/b/c/d;p?y".toList := sorry

/-- The reference `g?y` resolves to `http://a/b/c/g?y`. -/
theorem Spec.resolves_g_query_y :
    Uri.print (Uri.resolve (Uri.split "http://a/b/c/d;p?q".toList)
      (Uri.split "g?y".toList)) = "http://a/b/c/g?y".toList := sorry

/-- The reference `#s` resolves to `http://a/b/c/d;p?q#s`: the
    base stands as it is, query included, and the fragment
    comes from the reference. -/
theorem Spec.resolves_fragment_s :
    Uri.print (Uri.resolve (Uri.split "http://a/b/c/d;p?q".toList)
      (Uri.split "#s".toList)) =
        "http://a/b/c/d;p?q#s".toList := sorry

/-- The reference `g#s` resolves to `http://a/b/c/g#s`. -/
theorem Spec.resolves_g_fragment_s :
    Uri.print (Uri.resolve (Uri.split "http://a/b/c/d;p?q".toList)
      (Uri.split "g#s".toList)) =
        "http://a/b/c/g#s".toList := sorry

/-- The reference `..` resolves to `http://a/b/`. -/
theorem Spec.resolves_dotdot :
    Uri.print (Uri.resolve (Uri.split "http://a/b/c/d;p?q".toList)
      (Uri.split "..".toList)) = "http://a/b/".toList := sorry

/-- The reference `../g` resolves to `http://a/b/g`. -/
theorem Spec.resolves_dotdot_g :
    Uri.print (Uri.resolve (Uri.split "http://a/b/c/d;p?q".toList)
      (Uri.split "../g".toList)) = "http://a/b/g".toList := sorry

/-! ## Worked examples of section 5.2.4

The two worked examples of dot segment removal that `SPEC.md`
prints, stated on `Uri.removeDotSegments` itself. -/

/-- Removing dot segments from `/a/b/c/./../../g` gives
    `/a/g`. -/
theorem Spec.removes_dots_rfc_example :
    Uri.removeDotSegments "/a/b/c/./../../g".toList =
      "/a/g".toList := sorry

/-- Removing dot segments from `mid/content=5/../6` gives
    `mid/6`. -/
theorem Spec.removes_dots_mid_example :
    Uri.removeDotSegments "mid/content=5/../6".toList =
      "mid/6".toList := sorry
