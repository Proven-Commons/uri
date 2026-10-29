/-
  The split and recomposition round trips.

  `print_split`: recomposing a split gives the original string
  back, for every string. This is the round trip of the Appendix
  B decomposition: each step of the split takes a prefix of the
  string and a delimiter, and recomposition puts exactly those
  pieces back.

  `split_print`: splitting a recomposed value gives the value
  back, for values that satisfy `WF`. The conditions of `WF` are
  what the reading needs: without them a printed value can be
  genuinely ambiguous, for instance a path of `a:b` printed with
  no scheme reads back as the scheme `a` and the path `b`.

  Helper lemmas live in `Uri.Proofs`.
-/

import Uri

namespace Uri.Proofs

open Uri

/-- The two parts of a first split join back into the string,
    with the delimiter restored by `withDelim`, the same helper
    recomposition uses. -/
theorem splitFirst_suffix (c : Char) : ∀ s : List Char,
    (splitFirst c s).1 ++ withDelim c (splitFirst c s).2 = s
  | [] => rfl
  | x :: xs => by
    by_cases h : x = c
    · subst h
      simp [splitFirst, withDelim]
    · have ih := splitFirst_suffix c xs
      simp only [splitFirst, h]
      exact congrArg (x :: ·) ih

/-- When a first split finds its delimiter, the string is the
    first part, the delimiter, and the rest. -/
theorem splitFirst_eq_some {c : Char} {s a b : List Char}
    (h : splitFirst c s = (a, some b)) : s = a ++ c :: b := by
  have hs := splitFirst_suffix c s
  rw [h] at hs
  exact hs.symm

/-- A first split that finds no delimiter returns the string and
    `none`. -/
theorem splitFirst_notMem {c : Char} : ∀ {s : List Char},
    c ∉ s → splitFirst c s = (s, none)
  | [], _ => rfl
  | x :: xs, h => by
    have hx : x ≠ c :=
      fun he => h (List.mem_cons.mpr (Or.inl he.symm))
    have hxs : c ∉ xs := fun hm => h (List.mem_cons_of_mem x hm)
    simp [splitFirst, hx, splitFirst_notMem hxs]

/-- A first split over an append whose first part is free of the
    delimiter splits inside the second part. -/
theorem splitFirst_append_notMem {c : Char} {xs : List Char}
    (h : c ∉ xs) : ∀ ys : List Char,
    splitFirst c (xs ++ ys) =
      (xs ++ (splitFirst c ys).1, (splitFirst c ys).2)
  | _ => by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      have hx : x ≠ c :=
        fun he => h (List.mem_cons.mpr (Or.inl he.symm))
      have hxs : c ∉ xs := fun hm => h (List.mem_cons_of_mem x hm)
      simp [List.cons_append, splitFirst, hx, ih hxs]

/-- A first split that reaches its delimiter after a free prefix
    stops there. -/
theorem splitFirst_append_hit {c : Char} {xs : List Char}
    (h : c ∉ xs) (ys : List Char) :
    splitFirst c (xs ++ c :: ys) = (xs, some ys) := by
  rw [splitFirst_append_notMem h]
  have h1 : splitFirst c (c :: ys) = ([], some ys) := by
    simp [splitFirst]
  rw [h1]
  simp

/-- A split at the first delimiter, when the delimiter stands at
    the head, stops at once. Taken through `splitFirst_append_hit`
    with an empty prefix it reads: the parts of `c :: ys` are the
    empty part and `ys`. -/
theorem splitFirst_cons_self (c : Char) (ys : List Char) :
    splitFirst c (c :: ys) = ([], some ys) :=
  splitFirst_append_hit (xs := []) (by simp) ys

/-- The two parts of a split at a delimiter join back into the
    string. -/
theorem takeUntil_app (c : Char) : ∀ s : List Char,
    (takeUntil c s).1 ++ (takeUntil c s).2 = s
  | [] => rfl
  | x :: xs => by
    by_cases h : x = c
    · subst h
      simp [takeUntil]
    · have ih := takeUntil_app c xs
      simp only [takeUntil, h]
      exact congrArg (x :: ·) ih

/-- A split at a delimiter that does not occur returns the
    string and the empty rest. -/
theorem takeUntil_of_notMem {c : Char} : ∀ {s : List Char},
    c ∉ s → takeUntil c s = (s, [])
  | [], _ => rfl
  | x :: xs, h => by
    have hx : x ≠ c :=
      fun he => h (List.mem_cons.mpr (Or.inl he.symm))
    have hxs : c ∉ xs := fun hm => h (List.mem_cons_of_mem x hm)
    simp [takeUntil, hx, takeUntil_of_notMem hxs]

/-- A split at a delimiter, over an append whose first part is
    free of the delimiter and whose second part is empty or
    starts with it, stops at the join. -/
theorem takeUntil_append_hit {c : Char} : ∀ {xs : List Char},
    c ∉ xs → ∀ {ys : List Char},
    ys = [] ∨ ys.head? = some c → takeUntil c (xs ++ ys) = (xs, ys)
  | [], _, [], _ => rfl
  | [], _, y :: ys, hor => by
    have hy : y = c := by
      cases hor with
      | inl he => simp at he
      | inr hh => simpa using hh
    subst hy
    simp [takeUntil]
  | x :: xs, h, ys, hor => by
    have hx : x ≠ c :=
      fun he => h (List.mem_cons.mpr (Or.inl he.symm))
    have hxs : c ∉ xs := fun hm => h (List.mem_cons_of_mem x hm)
    have ih := takeUntil_append_hit hxs hor
    simp [List.cons_append, takeUntil, hx, ih]

/-- Every character of a scheme that passes the scheme rule is a
    scheme character. -/
theorem isSchemeChar_of_schemeOk {l : List Char}
    (h : schemeOk l = true) : ∀ c ∈ l, isSchemeChar c = true := by
  cases l with
  | nil => intro c hc; simp at hc
  | cons x xs =>
    intro c hc
    have h2 : isAlpha x = true ∧ (xs.all isSchemeChar) = true := by
      have := h
      simp only [schemeOk, Bool.and_eq_true] at this
      exact this
    cases hc with
    | head =>
      simp [isSchemeChar, h2.1]
    | tail _ hm =>
      exact (List.all_eq_true.mp h2.2) c hm

/-- A character that is not a scheme character cannot appear in
    a scheme that passes the scheme rule. -/
theorem schemeOk_eq_false_of_mem {l : List Char} {c : Char}
    (hc : isSchemeChar c = false) (hm : c ∈ l) : schemeOk l = false := by
  cases h : schemeOk l with
  | false => rfl
  | true =>
    have h1 := isSchemeChar_of_schemeOk h c hm
    rw [hc] at h1
    exact absurd h1 (by decide)

/-- A scheme that passes the scheme rule holds none of the four
    delimiters: each of them fails the scheme character test. -/
theorem schemeOk_notMem {l : List Char} (h : schemeOk l = true) :
    ':' ∉ l ∧ '/' ∉ l ∧ '?' ∉ l ∧ '#' ∉ l := by
  have hc : ∀ c : Char, isSchemeChar c = false → c ∉ l :=
    fun c hc hm => by
      have hf := schemeOk_eq_false_of_mem hc hm
      rw [h] at hf
      exact absurd hf (by decide)
  exact ⟨hc ':' (by decide), hc '/' (by decide),
         hc '?' (by decide), hc '#' (by decide)⟩

/-- What `schemeOf` returns, in terms of the first split at a
    colon, when the split finds one. -/
theorem schemeOf_of_splitFirst_some {s pre rest : List Char}
    (hf : splitFirst ':' s = (pre, some rest)) :
    schemeOf s = if schemeOk pre then some (pre, rest) else none := by
  unfold schemeOf
  rw [hf]

/-- What `schemeOf` returns, in terms of the first split at a
    colon, when the split finds none. -/
theorem schemeOf_of_splitFirst_none {s pre : List Char}
    (hf : splitFirst ':' s = (pre, none)) : schemeOf s = none := by
  unfold schemeOf
  rw [hf]

/-- When the first split finds a colon but the run before it
    fails the scheme rule, `schemeOf` finds no scheme. -/
theorem schemeOf_none_of_splitFirst_false {s pre rest : List Char}
    (hf : splitFirst ':' s = (pre, some rest)) (h : schemeOk pre = false) :
    schemeOf s = none := by
  rw [schemeOf_of_splitFirst_some hf, if_neg (by simp [h])]

/-- When `schemeOf` finds a scheme, the string is the scheme, a
    colon, and the rest. -/
theorem schemeOf_eq_some {s sch r : List Char}
    (h : schemeOf s = some (sch, r)) : s = sch ++ ':' :: r := by
  cases hf : splitFirst ':' s with
  | mk pre rest =>
    cases rest with
    | none =>
      rw [schemeOf_of_splitFirst_none hf] at h
      simp at h
    | some rest =>
      rw [schemeOf_of_splitFirst_some hf] at h
      by_cases hok : schemeOk pre = true
      · rw [if_pos hok] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨h1, h2⟩ := h
        subst h1
        subst h2
        exact splitFirst_eq_some hf
      · have hok2 : schemeOk pre = false := by
          cases hb : schemeOk pre with
          | false => rfl
          | true => exact absurd hb hok
        rw [hok2] at h
        simp at h

/-- A string that starts with the scheme and a colon has that
    scheme, when the scheme passes the rule and holds no colon. -/
theorem schemeOf_hit {sch rest : List Char}
    (hok : schemeOk sch = true) (hcolon : ':' ∉ sch) :
    schemeOf (sch ++ ':' :: rest) = some (sch, rest) := by
  unfold schemeOf
  rw [splitFirst_append_hit hcolon]
  simp [hok]

/-- A string starting with a slash has no scheme: the run before
    any colon starts with the slash, and a slash is not a scheme
    character, so the scheme rule fails. -/
theorem schemeOf_none_of_head_slash {s : List Char}
    (h : s.head? = some '/') : schemeOf s = none := by
  cases s with
  | nil => simp at h
  | cons x xs =>
    have hx : x = '/' := by simpa using h
    subst hx
    cases hf : splitFirst ':' xs with
    | mk pre rest =>
      have hsplit : splitFirst ':' ('/' :: xs) = ('/' :: pre, rest) := by
        have hne : ('/' : Char) ≠ ':' := by decide
        rw [show splitFirst ':' ('/' :: xs) =
            (if ('/' : Char) = ':' then ([], some xs)
             else ('/' :: (splitFirst ':' xs).1, (splitFirst ':' xs).2))
            from rfl, if_neg hne, hf]
      cases rest with
      | none => exact schemeOf_of_splitFirst_none hsplit
      | some r =>
        have hα : isAlpha '/' = false := by decide
        have hsc : schemeOk ('/' :: pre) = false := by
          simp [schemeOk, hα]
        exact schemeOf_none_of_splitFirst_false hsplit hsc

/-- A string whose path reading forbids a scheme prefix has no
    scheme. -/
theorem schemeOf_none_of_noSchemePrefix {s : List Char}
    (h : NoSchemePrefix s) : schemeOf s = none := by
  cases hf : splitFirst ':' s with
  | mk pre rest =>
    cases rest with
    | none => exact schemeOf_of_splitFirst_none hf
    | some r =>
      have hs : s = pre ++ ':' :: r := splitFirst_eq_some hf
      rcases h pre r hs with hm | hok
      · exact schemeOf_none_of_splitFirst_false hf
          (schemeOk_eq_false_of_mem (by decide) hm)
      · exact schemeOf_none_of_splitFirst_false hf hok

/-- The scheme step of the split, when no scheme is found. -/
theorem splitScheme_of_none {t : List Char} (h : schemeOf t = none) :
    splitScheme t = (none, t) := by
  unfold splitScheme
  rw [h]

/-- The scheme step of the split, when a scheme is found. -/
theorem splitScheme_of_some {t sch r : List Char}
    (h : schemeOf t = some (sch, r)) : splitScheme t = (some sch, r) := by
  unfold splitScheme
  rw [h]

/-- A string whose first two characters are two slashes: the
    string is the two slashes and what follows them. -/
theorem take2_eq {t : List Char} (h : t.take 2 = ['/', '/']) :
    t = '/' :: '/' :: t.drop 2 := by
  have htd := List.take_append_drop 2 t
  rw [h] at htd
  exact htd.symm

/-- The authority step of the split, when the string starts with
    two slashes. -/
theorem splitAuthority_of_take2 {t : List Char}
    (h : t.take 2 = ['/', '/']) :
    splitAuthority t =
      (some (takeUntil '/' (t.drop 2)).1, (takeUntil '/' (t.drop 2)).2) := by
  unfold splitAuthority
  rw [if_pos h]

/-- The authority step of the split, when the string does not
    start with two slashes. -/
theorem splitAuthority_of_notake2 {t : List Char}
    (h : t.take 2 ≠ ['/', '/']) : splitAuthority t = (none, t) := by
  unfold splitAuthority
  rw [if_neg h]

end Uri.Proofs

/-- The last step of `print_split`, factored out: when the first
    three recomposition parts join to the string before the
    query, that string joins with the query part to the string
    before the fragment, and that joins with the fragment part
    to the whole string, then the five parts in recomposition
    order join to the whole string. Only associativity of
    append is used. -/
theorem finish5 {a b c d e x y z : List Char}
    (h1 : (a ++ b) ++ c = x) (h2 : x ++ d = y) (h3 : y ++ e = z) :
    (((a ++ b) ++ c) ++ d) ++ e = z := by
  rw [h1, h2, h3]

/-- Recomposition of a split: the printed form of the split of
    any string is the string itself. The proof follows the split:
    the fragment and query parts rejoin by the first split
    lemmas, and the scheme, authority, and path parts rejoin by
    the step equations and the two take until pieces. -/
theorem print_split (s : List Char) : Uri.print (Uri.split s) = s := by
  have A := Uri.Proofs.splitFirst_suffix '#' s
  have B := Uri.Proofs.splitFirst_suffix '?' (Uri.splitFirst '#' s).1
  cases hsc : Uri.schemeOf (Uri.splitFirst '?' (Uri.splitFirst '#' s).1).1 with
  | none =>
    by_cases h2 :
        ((Uri.splitFirst '?' (Uri.splitFirst '#' s).1).1).take 2 = ['/', '/']
    · have hC :
          (([] : List Char) ++
              (['/', '/'] ++
                (Uri.takeUntil '/'
                  ((Uri.splitFirst '?' (Uri.splitFirst '#' s).1).1.drop 2)).1)) ++
            (Uri.takeUntil '/'
              ((Uri.splitFirst '?' (Uri.splitFirst '#' s).1).1.drop 2)).2 =
          (Uri.splitFirst '?' (Uri.splitFirst '#' s).1).1 := by
        have htd : (Uri.splitFirst '?' (Uri.splitFirst '#' s).1).1 =
            '/' :: '/' ::
              ((Uri.splitFirst '?' (Uri.splitFirst '#' s).1).1.drop 2) :=
          Uri.Proofs.take2_eq h2
        have htu := Uri.Proofs.takeUntil_app '/'
          ((Uri.splitFirst '?' (Uri.splitFirst '#' s).1).1.drop 2)
        calc (([] : List Char) ++
                (['/', '/'] ++
                  (Uri.takeUntil '/'
                    ((Uri.splitFirst '?' (Uri.splitFirst '#' s).1).1.drop 2)).1)) ++
              (Uri.takeUntil '/'
                ((Uri.splitFirst '?' (Uri.splitFirst '#' s).1).1.drop 2)).2
            = '/' :: '/' ::
                ((Uri.takeUntil '/'
                    ((Uri.splitFirst '?' (Uri.splitFirst '#' s).1).1.drop 2)).1 ++
                 (Uri.takeUntil '/'
                    ((Uri.splitFirst '?' (Uri.splitFirst '#' s).1).1.drop 2)).2) :=
              rfl
          _ = '/' :: '/' ::
                ((Uri.splitFirst '?' (Uri.splitFirst '#' s).1).1.drop 2) := by
              rw [htu]
          _ = (Uri.splitFirst '?' (Uri.splitFirst '#' s).1).1 := htd.symm
      simp only [Uri.split, Uri.print,
        Uri.Proofs.splitScheme_of_none hsc,
        Uri.Proofs.splitAuthority_of_take2 h2]
      exact finish5 hC B A
    · have hC :
          (([] : List Char) ++ ([] : List Char)) ++
              (Uri.splitFirst '?' (Uri.splitFirst '#' s).1).1 =
            (Uri.splitFirst '?' (Uri.splitFirst '#' s).1).1 := by
        simp
      simp only [Uri.split, Uri.print,
        Uri.Proofs.splitScheme_of_none hsc,
        Uri.Proofs.splitAuthority_of_notake2 h2]
      exact finish5 hC B A
  | some pr =>
    obtain ⟨sch, r⟩ := pr
    by_cases h2 : r.take 2 = ['/', '/']
    · have hC :
          ((sch ++ [':']) ++
              (['/', '/'] ++ (Uri.takeUntil '/' (r.drop 2)).1)) ++
            (Uri.takeUntil '/' (r.drop 2)).2 =
          (Uri.splitFirst '?' (Uri.splitFirst '#' s).1).1 := by
        have hsch : (Uri.splitFirst '?' (Uri.splitFirst '#' s).1).1 =
            sch ++ ':' :: r :=
          Uri.Proofs.schemeOf_eq_some hsc
        have hr2 : r = '/' :: '/' :: r.drop 2 := Uri.Proofs.take2_eq h2
        have htu := Uri.Proofs.takeUntil_app '/' (r.drop 2)
        calc ((sch ++ [':']) ++
                (['/', '/'] ++ (Uri.takeUntil '/' (r.drop 2)).1)) ++
              (Uri.takeUntil '/' (r.drop 2)).2
            = sch ++ ':' :: ('/' :: '/' ::
                ((Uri.takeUntil '/' (r.drop 2)).1 ++
                 (Uri.takeUntil '/' (r.drop 2)).2)) := by
              simp [List.append_assoc]
          _ = sch ++ ':' :: ('/' :: '/' :: r.drop 2) := by rw [htu]
          _ = sch ++ ':' :: r := by rw [← hr2]
          _ = (Uri.splitFirst '?' (Uri.splitFirst '#' s).1).1 := hsch.symm
      simp only [Uri.split, Uri.print,
        Uri.Proofs.splitScheme_of_some hsc,
        Uri.Proofs.splitAuthority_of_take2 h2]
      exact finish5 hC B A
    · have hC :
          ((sch ++ [':']) ++ ([] : List Char)) ++ r =
            (Uri.splitFirst '?' (Uri.splitFirst '#' s).1).1 := by
        have hsch : (Uri.splitFirst '?' (Uri.splitFirst '#' s).1).1 =
            sch ++ ':' :: r :=
          Uri.Proofs.schemeOf_eq_some hsc
        calc ((sch ++ [':']) ++ ([] : List Char)) ++ r
            = sch ++ ':' :: r := by simp [List.append_assoc]
          _ = (Uri.splitFirst '?' (Uri.splitFirst '#' s).1).1 := hsch.symm
      simp only [Uri.split, Uri.print,
        Uri.Proofs.splitScheme_of_some hsc,
        Uri.Proofs.splitAuthority_of_notake2 h2]
      exact finish5 hC B A

/-- Append of a one character list reassociates to a cons. -/
theorem append_singleton_cons {s rest : List Char} {c : Char} :
    (s ++ [c]) ++ rest = s ++ c :: rest := by
  induction s with
  | nil => rfl
  | cons x xs ih => exact congrArg (x :: ·) ih

/-- The scheme prefix of a recomposition, reassociated: the
    scheme and its colon, then the rest as one string. -/
theorem scheme_prefix_eq {s ap path : List Char} :
    ((s ++ [':']) ++ ap) ++ path = s ++ ':' :: (ap ++ path) := by
  induction s with
  | nil => rfl
  | cons x xs ih => exact congrArg (x :: ·) ih

/-- A first split over a string that ends in a delimited part:
    when the delimiter does not occur in the head part, the
    split is the head part and the delimited component. -/
theorem splitFirst_withDelim {c : Char} {xs : List Char}
    {o : Option (List Char)} (h : c ∉ xs) :
    Uri.splitFirst c (xs ++ Uri.withDelim c o) = (xs, o) := by
  cases o with
  | none =>
    rw [show Uri.withDelim c (none : Option (List Char)) = [] from rfl,
      List.append_nil]
    exact Uri.Proofs.splitFirst_notMem h
  | some y =>
    rw [show Uri.withDelim c (some y) = c :: y from rfl]
    exact Uri.Proofs.splitFirst_append_hit h y

/-- A character absent from both parts of an append is absent
    from the append. -/
theorem notMem_append2 {c : Char} {xs ys : List Char}
    (h1 : c ∉ xs) (h2 : c ∉ ys) : c ∉ xs ++ ys :=
  fun hm => (List.mem_append.mp hm).elim h1 h2

/-- A character other than the delimiter is absent from a
    delimited part when it is absent from the component. -/
theorem notMem_withDelim {c d : Char} {o : Option (List Char)}
    (hcd : c ≠ d) (h : ∀ x, o = some x → c ∉ x) :
    c ∉ Uri.withDelim d o := by
  cases o with
  | none => simp [Uri.withDelim]
  | some x =>
    have hx : c ∉ x := h x rfl
    simp [Uri.withDelim, List.mem_cons, hcd, hx]

/-- Splitting a recomposed value gives the value back, for
    values that satisfy `WF`. The proof follows the split in
    reverse: the fragment and query parts split off by the
    first split lemmas, since their delimiters cannot occur in
    the parts before them; the scheme step reads the scheme
    back, or finds none for the two reasons `WF` allows; the
    authority step reads the authority back, or finds none
    because the path does not start with two slashes. -/
theorem split_print (u : Uri.Uri) (h : Uri.WF u) :
    Uri.split (Uri.print u) = u := by
  obtain ⟨sch, auth, path, q, f⟩ := u
  have hpq : '?' ∉ path := h.2.2.1.1
  have hph : '#' ∉ path := h.2.2.1.2
  have hA6 : ∀ x, q = some x → '#' ∉ x :=
    fun x hx => h.2.2.2.2.2.1 x hx
  have hwq : '#' ∉ Uri.withDelim '?' q :=
    notMem_withDelim (by decide) hA6
  cases sch with
  | none =>
    cases auth with
    | none =>
      have hns : Uri.NoSchemePrefix (([] ++ []) ++ path) :=
        h.2.2.2.2.2.2 rfl rfl
      have hS : Uri.splitScheme (([] ++ []) ++ path) = (none, path) :=
        Uri.Proofs.splitScheme_of_none
          (Uri.Proofs.schemeOf_none_of_noSchemePrefix hns)
      have hA5 : ¬ ∃ r, path = '/' :: '/' :: r := h.2.2.2.2.1 rfl
      have hA : Uri.splitAuthority path = (none, path) :=
        Uri.Proofs.splitAuthority_of_notake2 (fun hcon =>
          hA5 ⟨path.drop 2, Uri.Proofs.take2_eq hcon⟩)
      have hQ : Uri.splitFirst '?' ((([] ++ []) ++ path) ++
            Uri.withDelim '?' q) = (([] ++ []) ++ path, q) :=
        splitFirst_withDelim hpq
      have hF : Uri.splitFirst '#' (Uri.print ⟨none, none, path, q, f⟩) =
            ((([] ++ []) ++ path) ++ Uri.withDelim '?' q, f) := by
        have hprt : Uri.print ⟨none, none, path, q, f⟩ =
            ((([] ++ []) ++ path) ++ Uri.withDelim '?' q) ++
              Uri.withDelim '#' f := rfl
        rw [hprt]
        exact splitFirst_withDelim
          (notMem_append2 (notMem_append2 (notMem_append2
            (by decide) (by decide)) hph) hwq)
      simp only [Uri.split, hF, hQ, hS, hA]
    | some a =>
      have ha2 : '/' ∉ a ∧ '?' ∉ a ∧ '#' ∉ a := h.2.1 a rfl
      have hS : Uri.splitScheme (([] ++ (['/', '/'] ++ a)) ++ path) =
            (none, (['/', '/'] ++ a) ++ path) :=
        Uri.Proofs.splitScheme_of_none
          (Uri.Proofs.schemeOf_none_of_head_slash (by rfl))
      have hA : Uri.splitAuthority ((['/', '/'] ++ a) ++ path) =
            (some a, path) := by
        have htu : Uri.takeUntil '/'
              (List.drop 2 ((['/', '/'] ++ a) ++ path)) = (a, path) :=
          Uri.Proofs.takeUntil_append_hit ha2.1 (h.2.2.2.1 a rfl)
        have hst := Uri.Proofs.splitAuthority_of_take2
          (t := (['/', '/'] ++ a) ++ path) (by rfl)
        rw [htu] at hst
        exact hst
      have hQ : Uri.splitFirst '?' ((([] ++ (['/', '/'] ++ a)) ++
              path) ++ Uri.withDelim '?' q) =
            (([] ++ (['/', '/'] ++ a)) ++ path, q) :=
        splitFirst_withDelim (notMem_append2 (notMem_append2
          (by decide)
          (notMem_append2 (by decide) ha2.2.1)) hpq)
      have hF : Uri.splitFirst '#' (Uri.print ⟨none, some a, path, q, f⟩) =
            ((([] ++ (['/', '/'] ++ a)) ++ path) ++ Uri.withDelim '?' q,
            f) := by
        have hprt : Uri.print ⟨none, some a, path, q, f⟩ =
            ((([] ++ (['/', '/'] ++ a)) ++ path) ++ Uri.withDelim '?' q) ++
              Uri.withDelim '#' f := rfl
        rw [hprt]
        exact splitFirst_withDelim
          (notMem_append2 (notMem_append2 (notMem_append2
            (by decide)
            (notMem_append2 (by decide) ha2.2.2)) hph) hwq)
      simp only [Uri.split, hF, hQ, hS, hA]
  | some s =>
    have hok : Uri.schemeOk s = true := h.1 s rfl
    have hsn := Uri.Proofs.schemeOk_notMem hok
    cases auth with
    | none =>
      have hS : Uri.splitScheme (((s ++ [':']) ++ []) ++ path) =
            (some s, [] ++ path) := by
        have hsch : Uri.schemeOf (((s ++ [':']) ++ []) ++ path) =
            some (s, [] ++ path) := by
          rw [scheme_prefix_eq]
          exact Uri.Proofs.schemeOf_hit hok hsn.1
        exact Uri.Proofs.splitScheme_of_some hsch
      have hA5 : ¬ ∃ r, path = '/' :: '/' :: r := h.2.2.2.2.1 rfl
      have hA : Uri.splitAuthority ([] ++ path) = (none, path) :=
        Uri.Proofs.splitAuthority_of_notake2 (t := [] ++ path) (fun hcon =>
          hA5 ⟨path.drop 2, Uri.Proofs.take2_eq hcon⟩)
      have hQ : Uri.splitFirst '?' ((((s ++ [':']) ++ []) ++ path) ++
            Uri.withDelim '?' q) = (((s ++ [':']) ++ []) ++ path, q) :=
        splitFirst_withDelim (notMem_append2 (notMem_append2
          (notMem_append2 hsn.2.2.1 (by decide)) (by decide)) hpq)
      have hF : Uri.splitFirst '#' (Uri.print ⟨some s, none, path, q, f⟩) =
            ((((s ++ [':']) ++ []) ++ path) ++ Uri.withDelim '?' q, f) := by
        have hprt : Uri.print ⟨some s, none, path, q, f⟩ =
            ((((s ++ [':']) ++ []) ++ path) ++ Uri.withDelim '?' q) ++
              Uri.withDelim '#' f := rfl
        rw [hprt]
        exact splitFirst_withDelim
          (notMem_append2 (notMem_append2 (notMem_append2
            (notMem_append2 hsn.2.2.2 (by decide))
            (by decide)) hph) hwq)
      simp only [Uri.split, hF, hQ, hS, hA]
    | some a =>
      have ha2 : '/' ∉ a ∧ '?' ∉ a ∧ '#' ∉ a := h.2.1 a rfl
      have hS : Uri.splitScheme (((s ++ [':']) ++ (['/', '/'] ++ a)) ++
            path) = (some s, (['/', '/'] ++ a) ++ path) := by
        have hsch : Uri.schemeOf (((s ++ [':']) ++ (['/', '/'] ++ a)) ++
              path) = some (s, (['/', '/'] ++ a) ++ path) := by
          rw [scheme_prefix_eq]
          exact Uri.Proofs.schemeOf_hit hok hsn.1
        exact Uri.Proofs.splitScheme_of_some hsch
      have hA : Uri.splitAuthority ((['/', '/'] ++ a) ++ path) =
            (some a, path) := by
        have htu : Uri.takeUntil '/'
              (List.drop 2 ((['/', '/'] ++ a) ++ path)) = (a, path) :=
          Uri.Proofs.takeUntil_append_hit ha2.1 (h.2.2.2.1 a rfl)
        have hst := Uri.Proofs.splitAuthority_of_take2
          (t := (['/', '/'] ++ a) ++ path) (by rfl)
        rw [htu] at hst
        exact hst
      have hQ : Uri.splitFirst '?' ((((s ++ [':']) ++
              (['/', '/'] ++ a)) ++ path) ++ Uri.withDelim '?' q) =
            (((s ++ [':']) ++ (['/', '/'] ++ a)) ++ path, q) :=
        splitFirst_withDelim (notMem_append2 (notMem_append2
          (notMem_append2 hsn.2.2.1 (by decide))
          (notMem_append2 (by decide) ha2.2.1)) hpq)
      have hF : Uri.splitFirst '#' (Uri.print ⟨some s, some a, path, q, f⟩) =
            ((((s ++ [':']) ++ (['/', '/'] ++ a)) ++ path) ++
              Uri.withDelim '?' q, f) := by
        have hprt : Uri.print ⟨some s, some a, path, q, f⟩ =
            ((((s ++ [':']) ++ (['/', '/'] ++ a)) ++ path) ++
              Uri.withDelim '?' q) ++ Uri.withDelim '#' f := rfl
        rw [hprt]
        exact splitFirst_withDelim
          (notMem_append2 (notMem_append2 (notMem_append2
            (notMem_append2 hsn.2.2.2 (by decide))
            (notMem_append2 (by decide) ha2.2.2)) hph) hwq)
      simp only [Uri.split, hF, hQ, hS, hA]
