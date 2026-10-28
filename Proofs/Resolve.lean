/-
  The claims about dot segment removal and resolution.

  `removeDotSegments_noDots`: after dot segment removal, the
  path taken apart again has no `.` or `..` segment.

  `removeDotSegments_idempotent`: removing dot segments a
  second time changes nothing.

  `resolve_scheme`: resolving against a base that has a scheme
  gives a target that has a scheme, as section 5.2.2 directs:
  the target scheme is the reference's own scheme when it has
  one, and the base's otherwise.

  The middle of each argument is the dot segment walk itself.
  `foldRds_mem` says every kept segment either came from the
  stack it started with, is the trailing empty segment a dot
  piece leaves behind, or is a non-dot piece of the input.
  `foldRds_clean` says the walk over pieces that hold no dot
  segment keeps every piece, in order.
-/

import Uri

namespace Uri.Proofs

open Uri

/-- Membership survives dropping a prefix. -/
theorem mem_of_mem_drop {x : List Char} {l : List (List Char)} :
    ∀ {n : Nat}, x ∈ l.drop n → x ∈ l := by
  intro n
  induction n generalizing l with
  | zero => intro hx; exact hx
  | succ n ih =>
    intro hx
    cases l with
    | nil =>
      have hx2 : x ∈ ([] : List (List Char)) := hx
      cases hx2
    | cons y ys => exact List.mem_cons_of_mem y (ih hx)

/-- What membership in the result of the last piece step means:
    a kept segment came from the stack, or is the trailing
    empty segment, or is the piece itself, which is then no
    dot segment. -/
theorem lastPiece_mem {out : List (List Char)} {abs : Bool} {b : Bool}
    {s x : List Char} (hx : x ∈ (lastPiece out abs b s).2) :
    x ∈ out ∨ x = [] ∨ (x = s ∧ s ≠ ['.'] ∧ s ≠ ['.', '.']) := by
  by_cases hdot : s = ['.'] ∨ s = ['.', '.']
  · by_cases hb : b = true
    · have e : (lastPiece out abs b s).2 =
          (if s = ['.', '.'] then out.drop 1 else out).reverse ++ [[]] := by
        unfold lastPiece
        rw [if_pos hdot, if_pos hb]
      rw [e] at hx
      rcases List.mem_append.mp hx with h | h
      · by_cases hdd : s = ['.', '.']
        · rw [if_pos hdd] at h
          exact Or.inl (mem_of_mem_drop (List.mem_reverse.mp h))
        · rw [if_neg hdd] at h
          exact Or.inl (List.mem_reverse.mp h)
      · exact Or.inr (Or.inl (List.mem_singleton.mp h))
    · have e : (lastPiece out abs b s).2 = out.reverse := by
        unfold lastPiece
        rw [if_pos hdot, if_neg hb]
      rw [e] at hx
      exact Or.inl (List.mem_reverse.mp hx)
  · have e : (lastPiece out abs b s).2 = out.reverse ++ [s] := by
      unfold lastPiece
      rw [if_neg hdot]
    rw [e] at hx
    rcases List.mem_append.mp hx with h | h
    · exact Or.inl (List.mem_reverse.mp h)
    · exact Or.inr (Or.inr ⟨List.mem_singleton.mp h,
        fun h1 => hdot (Or.inl h1), fun h2 => hdot (Or.inr h2)⟩)

/-- Every segment the walk keeps either came from the stack it
    started with, is the trailing empty segment a final dot
    piece leaves behind, or is a non-dot piece of the input. -/
theorem foldRds_mem : ∀ (pieces : List (Bool × List Char))
    (out : List (List Char)) (abs : Bool) (x : List Char),
    x ∈ (foldRds out abs pieces).2 →
    x ∈ out ∨ x = [] ∨
      ∃ b, (b, x) ∈ pieces ∧ x ≠ ['.'] ∧ x ≠ ['.', '.'] := by
  intro pieces
  induction pieces with
  | nil =>
    intro out abs x hx
    exact Or.inl (List.mem_reverse.mp hx)
  | cons p ps ih =>
    intro out abs x hx
    obtain ⟨b, s⟩ := p
    cases ps with
    | nil =>
      rcases lastPiece_mem hx with h | h | ⟨h, h1, h2⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨b, by rw [h]; exact List.mem_cons_self,
          by rw [h]; exact h1, by rw [h]; exact h2⟩)
    | cons p2 ps2 =>
      have step : foldRds out abs ((b, s) :: p2 :: ps2) =
          (if s = ['.'] then foldRds out abs (p2 :: ps2)
           else if s = ['.', '.'] then foldRds (out.drop 1) abs (p2 :: ps2)
           else foldRds (s :: out) (abs ∨ (b ∧ out.isEmpty)) (p2 :: ps2)) := rfl
      rw [step] at hx
      by_cases h1 : s = ['.']
      · rw [if_pos h1] at hx
        rcases ih out abs x hx with h | h | ⟨b', hb', h2, h3⟩
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr ⟨b', List.mem_cons_of_mem _ hb', h2, h3⟩)
      · by_cases h2 : s = ['.', '.']
        · rw [if_neg h1, if_pos h2] at hx
          rcases ih (out.drop 1) abs x hx with h | h | ⟨b', hb', h3, h4⟩
          · exact Or.inl (mem_of_mem_drop h)
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr ⟨b', List.mem_cons_of_mem _ hb', h3, h4⟩)
        · rw [if_neg h1, if_neg h2] at hx
          rcases ih (s :: out) _ x hx with h | h | ⟨b', hb', h3, h4⟩
          · rcases List.mem_cons.mp h with he | hm
            · exact Or.inr (Or.inr ⟨b, by rw [he]; exact List.mem_cons_self,
                by rw [he]; exact h1, by rw [he]; exact h2⟩)
            · exact Or.inl hm
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr ⟨b', List.mem_cons_of_mem _ hb', h3, h4⟩)

/-- The walk over pieces that hold no dot segment keeps every
    piece: the result is the stack it started with, in order,
    then all the pieces. -/
theorem foldRds_clean : ∀ (b : Bool) (s : List Char)
    (rest : List (Bool × List Char)) (out : List (List Char)) (abs : Bool),
    s ≠ ['.'] → s ≠ ['.', '.'] →
    (∀ y ∈ rest, y.2 ≠ ['.'] ∧ y.2 ≠ ['.', '.']) →
    foldRds out abs ((b, s) :: rest) =
      (decide (abs = true ∨ (b = true ∧ out.isEmpty = true)),
        out.reverse ++ s :: rest.map Prod.snd) := by
  intro b s rest
  induction rest generalizing b s with
  | nil =>
    intro out abs h1 h2 _
    have e : lastPiece out abs b s =
        (decide (abs = true ∨ (b = true ∧ out.isEmpty = true)),
          out.reverse ++ [s]) := by
      unfold lastPiece
      rw [if_neg (not_or.mpr ⟨h1, h2⟩)]
    exact e
  | cons p2 ps2 ih =>
    intro out abs h1 h2 hrest
    obtain ⟨b2, s2⟩ := p2
    have hhead := hrest (b2, s2) (List.mem_cons_self)
    have step : foldRds out abs ((b, s) :: (b2, s2) :: ps2) =
        foldRds (s :: out) (abs ∨ (b ∧ out.isEmpty)) ((b2, s2) :: ps2) := by
      rw [show foldRds out abs ((b, s) :: (b2, s2) :: ps2) =
          (if s = ['.'] then foldRds out abs ((b2, s2) :: ps2)
           else if s = ['.', '.'] then foldRds (out.drop 1) abs ((b2, s2) :: ps2)
           else foldRds (s :: out) (abs ∨ (b ∧ out.isEmpty)) ((b2, s2) :: ps2)) from rfl,
        if_neg h1, if_neg h2]
    have ih' := ih (b := b2) (s := s2) (out := s :: out)
      (abs := abs ∨ (b ∧ out.isEmpty)) hhead.1 hhead.2
      (fun y hy => hrest y (List.mem_cons_of_mem _ hy))
    rw [step, ih']
    congr 1
    · simp
    · simp only [List.reverse_cons, List.map_cons, List.append_assoc,
        List.cons_append, List.nil_append]

/-- Stripping the leading dot pieces of a list that has none
    changes nothing. -/
theorem stripLeadDots_of_noDots {segs : List (List Char)}
    (hnd : NoDots segs) : stripLeadDots segs = segs := by
  cases segs with
  | nil => rfl
  | cons s ss =>
    have hs : ¬ (s = ['.'] ∨ s = ['.', '.']) :=
      not_or.mpr (hnd s (List.mem_cons_self))
    rw [show stripLeadDots (s :: ss) =
        (if (s = ['.'] ∨ s = ['.', '.']) then
          (if ss = [] then [] else stripLeadDots ss)
         else s :: ss) from rfl, if_neg hs]

/-- Membership survives stripping leading dot pieces. -/
theorem mem_of_stripLeadDots {x : List Char} :
    ∀ {l : List (List Char)}, x ∈ stripLeadDots l → x ∈ l := by
  intro l
  induction l with
  | nil =>
    intro hx
    rw [show stripLeadDots ([] : List (List Char)) = [] from rfl] at hx
    cases hx
  | cons s ss ih =>
    intro hx
    by_cases hd : s = ['.'] ∨ s = ['.', '.']
    · by_cases he : ss = []
      · subst he
        have e : stripLeadDots (s :: []) = [] := by
          rw [show stripLeadDots (s :: ([] : List (List Char))) =
              (if (s = ['.'] ∨ s = ['.', '.']) then
                (if ([] : List (List Char)) = [] then [] else stripLeadDots [])
               else s :: []) from rfl, if_pos hd, if_pos rfl]
        rw [e] at hx
        cases hx
      · have e : stripLeadDots (s :: ss) = stripLeadDots ss := by
          rw [show stripLeadDots (s :: ss) =
              (if (s = ['.'] ∨ s = ['.', '.']) then
                (if ss = [] then [] else stripLeadDots ss)
               else s :: ss) from rfl, if_pos hd, if_neg he]
        rw [e] at hx
        exact List.mem_cons_of_mem s (ih hx)
    · have e : stripLeadDots (s :: ss) = s :: ss := by
        rw [show stripLeadDots (s :: ss) =
            (if (s = ['.'] ∨ s = ['.', '.']) then
              (if ss = [] then [] else stripLeadDots ss)
             else s :: ss) from rfl, if_neg hd]
      rw [e] at hx
      exact hx

/-- A segment built by `consSeg` from slash-free segments, with
    a character that is no slash, is slash-free. -/
theorem consSeg_slashFree {c : Char} (hc : c ≠ '/') :
    ∀ {segs : List (List Char)}, (∀ s ∈ segs, '/' ∉ s) →
    ∀ {x : List Char}, x ∈ consSeg c segs → '/' ∉ x := by
  intro segs hsegs x hx
  cases segs with
  | nil =>
    have hx2 : x = [c] := List.mem_singleton.mp hx
    subst hx2
    intro hm
    exact hc (List.mem_singleton.mp hm).symm
  | cons s0 ss =>
    have hx' : x ∈ (c :: s0) :: ss := hx
    cases hx' with
    | head =>
      intro hm
      rcases List.mem_cons.mp hm with he | hm'
      · exact hc he.symm
      · exact hsegs s0 (List.mem_cons_self) hm'
    | tail _ hm => exact hsegs x (List.mem_cons_of_mem s0 hm)

/-- Every segment of a path body is slash-free: a segment is a
    piece between slashes. -/
theorem splitSegs_slashFree_mem : ∀ {l : List Char} {s : List Char},
    s ∈ splitSegs l → '/' ∉ s := by
  intro l
  induction l with
  | nil =>
    intro s hs
    have hs2 : s = [] := List.mem_singleton.mp hs
    subst hs2
    exact (by decide : ('/' : Char) ∉ ([] : List Char))
  | cons c cs ih =>
    intro s hs
    have e : splitSegs (c :: cs) =
        (if c = '/' then [] :: splitSegs cs else consSeg c (splitSegs cs)) := rfl
    rw [e] at hs
    by_cases hc : c = '/'
    · rw [if_pos hc] at hs
      cases hs with
      | head => exact (by decide : ('/' : Char) ∉ ([] : List Char))
      | tail _ hm => exact ih hm
    · rw [if_neg hc] at hs
      exact consSeg_slashFree hc (fun y hy => ih hy) hs

/-- The body of a slash-free path is the path itself, as one
    segment. -/
theorem splitSegs_eq_self {l : List Char} (h : '/' ∉ l) :
    splitSegs l = [l] := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    have hc : c ≠ '/' := fun he => h (List.mem_cons.mpr (Or.inl he.symm))
    have hcs : '/' ∉ cs := fun hm => h (List.mem_cons_of_mem c hm)
    have e : splitSegs (c :: cs) =
        (if c = '/' then [] :: splitSegs cs else consSeg c (splitSegs cs)) := rfl
    calc splitSegs (c :: cs) = consSeg c (splitSegs cs) := by rw [e, if_neg hc]
      _ = consSeg c [cs] := by rw [ih hcs]
      _ = [c :: cs] := rfl

/-- Splitting a string at a slash that follows a slash-free
    run: the run is the first segment. -/
theorem splitSegs_append {l : List Char} (h : '/' ∉ l) (t : List Char) :
    splitSegs (l ++ '/' :: t) = l :: splitSegs t := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    have hc : c ≠ '/' := fun he => h (List.mem_cons.mpr (Or.inl he.symm))
    have hcs : '/' ∉ cs := fun hm => h (List.mem_cons_of_mem c hm)
    have e : splitSegs (c :: (cs ++ '/' :: t)) =
        (if c = '/' then [] :: splitSegs (cs ++ '/' :: t)
         else consSeg c (splitSegs (cs ++ '/' :: t))) := rfl
    calc splitSegs ((c :: cs) ++ '/' :: t)
        = splitSegs (c :: (cs ++ '/' :: t)) := rfl
      _ = consSeg c (splitSegs (cs ++ '/' :: t)) := by rw [e, if_neg hc]
      _ = consSeg c (cs :: splitSegs t) := by rw [ih hcs]
      _ = (c :: cs) :: splitSegs t := rfl

/-- Joining slash-free segments and splitting the result gives
    the segments back. -/
theorem splitSegs_joinSegs : ∀ (segs : List (List Char)), segs ≠ [] →
    (∀ s ∈ segs, '/' ∉ s) → splitSegs (joinSegs segs) = segs := by
  intro segs
  induction segs with
  | nil => intro hne; exact absurd rfl hne
  | cons s ss ih =>
    intro _ hslash
    cases ss with
    | nil =>
      have e : joinSegs [s] = s := rfl
      rw [e]
      exact splitSegs_eq_self (hslash s (List.mem_cons_self))
    | cons s2 ss2 =>
      have e : joinSegs (s :: s2 :: ss2) = s ++ '/' :: joinSegs (s2 :: ss2) := rfl
      rw [e, splitSegs_append (hslash s (List.mem_cons_self)) (joinSegs (s2 :: ss2)),
        ih (List.cons_ne_nil s2 ss2) (fun y hy => hslash y (List.mem_cons_of_mem _ hy))]

/-- The pieces with the marker heads removed print back. -/
theorem map_snd_map_true : ∀ (ss : List (List Char)),
    (ss.map (fun x => (true, x))).map Prod.snd = ss
  | [] => rfl
  | s :: ss => congrArg (s :: ·) (map_snd_map_true ss)

/-- Dot segment removal on segments, unfolded: the walk over
    the stripped segments, or the empty result. -/
theorem rdsSegs_cases (lead : Bool) (segs : List (List Char)) :
    rdsSegs lead segs =
      match (if lead then segs else stripLeadDots segs) with
      | [] => (lead, [])
      | s :: ss => foldRds [] lead ((lead, s) :: ss.map (fun x => (true, x))) := rfl

/-- Dot segment removal on segments leaves no dot segment. -/
theorem rdsSegs_noDots (lead : Bool) (segs : List (List Char)) :
    NoDots (rdsSegs lead segs).2 := by
  intro x hx
  cases hss : (if lead then segs else stripLeadDots segs) with
  | nil =>
    have e : rdsSegs lead segs = (lead, []) := by
      rw [rdsSegs_cases, hss]
    rw [e] at hx
    have hx2 : x ∈ ([] : List (List Char)) := hx
    cases hx2
  | cons s ss =>
    have e : rdsSegs lead segs =
        foldRds [] lead ((lead, s) :: ss.map (fun x => (true, x))) := by
      rw [rdsSegs_cases, hss]
    rw [e] at hx
    rcases foldRds_mem _ _ _ _ hx with h | h | ⟨b, hb, h1, h2⟩
    · have hx2 : x ∈ ([] : List (List Char)) := h
      cases hx2
    · subst h
      exact ⟨by decide, by decide⟩
    · exact ⟨h1, h2⟩

/-- The segments dot segment removal keeps are slash-free when
    the input segments are: they are input segments. -/
theorem rdsSegs_slashFree (lead : Bool) {segs : List (List Char)}
    (hslash : ∀ s ∈ segs, '/' ∉ s) :
    ∀ s ∈ (rdsSegs lead segs).2, '/' ∉ s := by
  intro x hx
  cases hss : (if lead then segs else stripLeadDots segs) with
  | nil =>
    have e : rdsSegs lead segs = (lead, []) := by
      rw [rdsSegs_cases, hss]
    rw [e] at hx
    have hx2 : x ∈ ([] : List (List Char)) := hx
    cases hx2
  | cons s ss =>
    have e : rdsSegs lead segs =
        foldRds [] lead ((lead, s) :: ss.map (fun x => (true, x))) := by
      rw [rdsSegs_cases, hss]
    rw [e] at hx
    rcases foldRds_mem _ _ _ _ hx with h | h | ⟨b, hb, h1, h2⟩
    · have hx2 : x ∈ ([] : List (List Char)) := h
      cases hx2
    · subst h
      exact (by decide : ('/' : Char) ∉ ([] : List Char))
    · have hxss : x ∈ s :: ss := by
        rcases List.mem_cons.mp hb with he | hm
        · have hxs : x = s := congrArg Prod.snd he
          subst hxs
          exact List.mem_cons_self
        · rcases List.mem_map.mp hm with ⟨y, hy, hyx⟩
          have hxy : y = x := by
            have h2 := congrArg Prod.snd hyx
            exact h2
          subst hxy
          exact List.mem_cons_of_mem s hy
      have hxsegs : x ∈ segs := by
        cases lead with
        | true =>
          have hss2 : segs = s :: ss := hss
          rw [hss2]
          exact hxss
        | false =>
          have hss2 : stripLeadDots segs = s :: ss := hss
          apply mem_of_stripLeadDots
          rw [hss2]
          exact hxss
      exact hslash x hxsegs

/-- Dot segment removal on segments that hold no dot segment
    keeps them all: the walk is the identity there. -/
theorem rdsSegs_clean (lead : Bool) {segs : List (List Char)}
    (hnd : NoDots segs) (hne : segs ≠ []) :
    rdsSegs lead segs = (lead, segs) := by
  cases segs with
  | nil => exact (hne rfl).elim
  | cons s ss =>
    have hstrip : (if lead then (s :: ss) else stripLeadDots (s :: ss)) = s :: ss := by
      cases lead with
      | true => rfl
      | false => exact stripLeadDots_of_noDots hnd
    have e : rdsSegs lead (s :: ss) =
        foldRds [] lead ((lead, s) :: ss.map (fun x => (true, x))) := by
      rw [rdsSegs_cases, hstrip]
    rw [e]
    have hrest : ∀ y ∈ ss.map (fun x => (true, x)),
        y.2 ≠ ['.'] ∧ y.2 ≠ ['.', '.'] := by
      intro y hy
      rcases List.mem_map.mp hy with ⟨z, hz, hzy⟩
      have hy2 : y = (true, z) := hzy.symm
      subst hy2
      exact hnd z (List.mem_cons_of_mem s hz)
    have hclean := foldRds_clean lead s (ss.map (fun x => (true, x))) [] lead
      (hnd s (List.mem_cons_self)).1 (hnd s (List.mem_cons_self)).2 hrest
    rw [hclean, map_snd_map_true]
    cases lead <;> rfl

/-- A path that does not start with a slash splits with the
    flag false, when its first character is no slash. -/
theorem splitPath_of_head_ne {c : Char} {rest : List Char} (hc : c ≠ '/') :
    splitPath (c :: rest) = (false, splitSegs (c :: rest)) := by
  unfold splitPath
  split
  · rename_i h
    cases h
    exact absurd rfl hc
  · rfl

/-- Taking a printed path apart again gives the flag and
    segments back, except in two named shapes: a relative path
    whose first segment is empty gains its slash back as the
    flag (the empty segment and the slash before it are the
    same character on paper), and the empty path prints and
    splits as one empty segment. -/
theorem splitPath_printPath (lead : Bool) (segs : List (List Char))
    (hslash : ∀ s ∈ segs, '/' ∉ s) :
    splitPath (printPath lead segs) = (lead, segs) ∨
    (∃ rest, segs = [] :: rest ∧ rest ≠ [] ∧ lead = false ∧
      splitPath (printPath lead segs) = (true, rest)) ∨
    (segs = [] ∧ splitPath (printPath lead segs) = (lead, [[]])) := by
  cases lead with
  | true =>
    cases segs with
    | nil => exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    | cons s ss =>
      left
      exact congrArg (fun x => (true, x))
        (splitSegs_joinSegs (s :: ss) (List.cons_ne_nil s ss) hslash)
  | false =>
    cases segs with
    | nil => exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    | cons s ss =>
      cases s with
      | nil =>
        cases ss with
        | nil =>
          left
          rfl
        | cons s2 ss2 =>
          right
          left
          refine ⟨s2 :: ss2, rfl, List.cons_ne_nil s2 ss2, rfl, ?_⟩
          exact congrArg (fun x => (true, x))
            (splitSegs_joinSegs (s2 :: ss2) (List.cons_ne_nil s2 ss2)
              (fun y hy => hslash y (List.mem_cons_of_mem _ hy)))
      | cons c s' =>
        left
        have hc : c ≠ '/' :=
          fun he => hslash (c :: s') (List.mem_cons_self)
            (List.mem_cons.mpr (Or.inl he.symm))
        cases ss with
        | nil =>
          calc splitPath (printPath false [c :: s'])
              = splitPath (c :: s') := rfl
            _ = (false, splitSegs (c :: s')) := splitPath_of_head_ne hc
            _ = (false, [c :: s']) :=
                congrArg (fun x => (false, x))
                  (splitSegs_eq_self (hslash _ (List.mem_cons_self)))
        | cons s2 ss2 =>
          calc splitPath (printPath false ((c :: s') :: s2 :: ss2))
              = splitPath ((c :: s') ++ '/' :: joinSegs (s2 :: ss2)) := rfl
            _ = (false, splitSegs ((c :: s') ++ '/' :: joinSegs (s2 :: ss2))) :=
                splitPath_of_head_ne hc
            _ = (false, (c :: s') :: s2 :: ss2) :=
                congrArg (fun x => (false, x))
                  (splitSegs_joinSegs _ (List.cons_ne_nil _ _) hslash)

/-- Every segment of a split path is slash-free. -/
theorem splitPath_slashFree (l : List Char) :
    ∀ s ∈ (splitPath l).2, '/' ∉ s := by
  cases l with
  | nil => intro s hs; exact splitSegs_slashFree_mem hs
  | cons c cs =>
    by_cases hc : c = '/'
    · subst hc
      intro s hs
      exact splitSegs_slashFree_mem hs
    · intro s hs
      have e := splitPath_of_head_ne (rest := cs) hc
      rw [e] at hs
      exact splitSegs_slashFree_mem hs

/-- One empty segment has no dot segment. -/
theorem noDots_singleton_nil : NoDots [[]] := by
  intro x hx
  have hx2 : x = [] := List.mem_singleton.mp hx
  subst hx2
  exact ⟨by decide, by decide⟩

/-- Dot segment removal, unfolded: the print of the removed
    segments of the split path. -/
theorem removeDotSegments_eq (p : List Char) :
    removeDotSegments p =
      printPath (rdsSegs (splitPath p).1 (splitPath p).2).1
                (rdsSegs (splitPath p).1 (splitPath p).2).2 := rfl

/-- Printing the result of dot segment removal on segments
    that hold no dot segment gives the print of the segments
    themselves. -/
theorem printPath_rdsSegs (lead : Bool) (segs : List (List Char))
    (hnd : NoDots segs) :
    printPath (rdsSegs lead segs).1 (rdsSegs lead segs).2 =
      printPath lead segs := by
  have hc : rdsSegs lead segs = (lead, segs) := by
    cases segs with
    | nil => cases lead <;> rfl
    | cons s ss => exact rdsSegs_clean lead hnd (List.cons_ne_nil s ss)
  exact congrArg (fun q : Bool × List (List Char) => printPath q.1 q.2) hc

/-- Dot segment removal on a printed path whose segments hold
    no dot segment is the identity. -/
theorem removeDotSegments_fixed (lead : Bool) (segs : List (List Char))
    (hnd : NoDots segs) (hslash : ∀ s ∈ segs, '/' ∉ s) :
    removeDotSegments (printPath lead segs) = printPath lead segs := by
  rw [removeDotSegments_eq]
  rcases splitPath_printPath lead segs hslash with
    h | ⟨rest, hsegs, hrest, hlead, h⟩ | ⟨hsegs, h⟩
  · rw [h]
    exact printPath_rdsSegs lead segs hnd
  · subst hsegs
    subst hlead
    cases rest with
    | nil => exact absurd rfl hrest
    | cons s2 ss2 =>
      rw [h]
      exact printPath_rdsSegs true (s2 :: ss2)
        (fun x hx => hnd x (List.mem_cons_of_mem _ hx))
  · subst hsegs
    rw [h]
    exact printPath_rdsSegs lead [[]] noDots_singleton_nil

/-- After dot segment removal, a path taken apart has no `.`
    or `..` segment. -/
theorem removeDotSegments_noDots (p : List Char) :
    NoDots (splitPath (removeDotSegments p)).2 := by
  have hnd : NoDots (rdsSegs (splitPath p).1 (splitPath p).2).2 :=
    rdsSegs_noDots _ _
  rw [removeDotSegments_eq p]
  rcases splitPath_printPath _ _ (rdsSegs_slashFree _ (splitPath_slashFree p)) with
    h | ⟨rest, hsegs, hrest, hlead, h⟩ | ⟨hsegs, h⟩
  · rw [h]
    exact hnd
  · rw [h]
    exact fun x hx => hnd x (by
      rw [hsegs]
      exact List.mem_cons_of_mem _ hx)
  · rw [h]
    exact noDots_singleton_nil

/-- Removing dot segments a second time changes nothing. -/
theorem removeDotSegments_idempotent (p : List Char) :
    removeDotSegments (removeDotSegments p) = removeDotSegments p := by
  rw [removeDotSegments_eq p]
  exact removeDotSegments_fixed _ _
    (rdsSegs_noDots _ _) (rdsSegs_slashFree _ (splitPath_slashFree p))

/-- Resolving against a base that has a scheme gives a target
    that has a scheme: the reference's own when it has one, and
    the base's otherwise. -/
theorem resolve_scheme (base ref : Uri) (h : base.scheme.isSome = true) :
    (resolve base ref).scheme.isSome = true := by
  unfold resolve
  by_cases h1 : ref.scheme.isSome
  · rw [if_pos h1]
    exact h1
  · by_cases h2 : ref.authority.isSome
    · rw [if_neg h1, if_pos h2]
      exact h
    · rw [if_neg h1, if_neg h2]
      exact h

end Uri.Proofs
