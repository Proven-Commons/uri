/-
  Proofs of the statements in `Spec.lean`, under the same names.

  The five claims are the theorems proved in
  `Proofs/RoundTrip.lean` and `Proofs/Resolve.lean`. The worked
  examples are single inputs, checked in the kernel with
  `decide +kernel`: no native evaluation, which the bar forbids.
-/

import Uri
import Proofs.RoundTrip
import Proofs.Resolve

theorem Spec.print_split (s : List Char) :
    Uri.print (Uri.split s) = s :=
  _root_.print_split s

theorem Spec.split_print (u : Uri.Uri) (h : Uri.WF u) :
    Uri.split (Uri.print u) = u :=
  _root_.split_print u h

theorem Spec.removeDotSegments_noDots (p : List Char) :
    Uri.NoDots (Uri.splitPath (Uri.removeDotSegments p)).2 :=
  Uri.Proofs.removeDotSegments_noDots p

theorem Spec.removeDotSegments_idempotent (p : List Char) :
    Uri.removeDotSegments (Uri.removeDotSegments p) =
      Uri.removeDotSegments p :=
  Uri.Proofs.removeDotSegments_idempotent p

theorem Spec.resolve_scheme (base ref : Uri.Uri)
    (h : base.scheme.isSome = true) :
    (Uri.resolve base ref).scheme.isSome = true :=
  Uri.Proofs.resolve_scheme base ref h

theorem Spec.resolves_g :
    Uri.print (Uri.resolve (Uri.split "http://a/b/c/d;p?q".toList)
      (Uri.split "g".toList)) = "http://a/b/c/g".toList := by
  decide +kernel

theorem Spec.resolves_dot_slash_g :
    Uri.print (Uri.resolve (Uri.split "http://a/b/c/d;p?q".toList)
      (Uri.split "./g".toList)) = "http://a/b/c/g".toList := by
  decide +kernel

theorem Spec.resolves_g_slash :
    Uri.print (Uri.resolve (Uri.split "http://a/b/c/d;p?q".toList)
      (Uri.split "g/".toList)) = "http://a/b/c/g/".toList := by
  decide +kernel

theorem Spec.resolves_slash_g :
    Uri.print (Uri.resolve (Uri.split "http://a/b/c/d;p?q".toList)
      (Uri.split "/g".toList)) = "http://a/g".toList := by
  decide +kernel

theorem Spec.resolves_slashes_g :
    Uri.print (Uri.resolve (Uri.split "http://a/b/c/d;p?q".toList)
      (Uri.split "//g".toList)) = "http://g".toList := by
  decide +kernel

theorem Spec.resolves_query_y :
    Uri.print (Uri.resolve (Uri.split "http://a/b/c/d;p?q".toList)
      (Uri.split "?y".toList)) =
        "http://a/b/c/d;p?y".toList := by
  decide +kernel

theorem Spec.resolves_g_query_y :
    Uri.print (Uri.resolve (Uri.split "http://a/b/c/d;p?q".toList)
      (Uri.split "g?y".toList)) = "http://a/b/c/g?y".toList := by
  decide +kernel

theorem Spec.resolves_fragment_s :
    Uri.print (Uri.resolve (Uri.split "http://a/b/c/d;p?q".toList)
      (Uri.split "#s".toList)) =
        "http://a/b/c/d;p?q#s".toList := by
  decide +kernel

theorem Spec.resolves_g_fragment_s :
    Uri.print (Uri.resolve (Uri.split "http://a/b/c/d;p?q".toList)
      (Uri.split "g#s".toList)) =
        "http://a/b/c/g#s".toList := by
  decide +kernel

theorem Spec.resolves_dotdot :
    Uri.print (Uri.resolve (Uri.split "http://a/b/c/d;p?q".toList)
      (Uri.split "..".toList)) = "http://a/b/".toList := by
  decide +kernel

theorem Spec.resolves_dotdot_g :
    Uri.print (Uri.resolve (Uri.split "http://a/b/c/d;p?q".toList)
      (Uri.split "../g".toList)) = "http://a/b/g".toList := by
  decide +kernel

theorem Spec.removes_dots_rfc_example :
    Uri.removeDotSegments "/a/b/c/./../../g".toList =
      "/a/g".toList := by
  decide +kernel

theorem Spec.removes_dots_mid_example :
    Uri.removeDotSegments "mid/content=5/../6".toList =
      "mid/6".toList := by
  decide +kernel
