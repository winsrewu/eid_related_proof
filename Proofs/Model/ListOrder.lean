import Proofs.Model.Basic

open List

/-! # List-order lemmas

First-occurrence position (`_root_.findIdx? (fun a => decide (a = x))` with a
junk `getD 0`) is order-preserving along a sublist of a nodup list. Shared by
the order-preservation and clustering capstones. -/

/-- A present element has a `findIdx?` position. -/
theorem findIdx?_some_of_mem {α : Type} [DecidableEq α] (l : List α) (a : α)
    (h : a ∈ l) : ∃ k, _root_.findIdx? (fun x => decide (x = a)) l = some k := by
  induction l with
  | nil => cases h
  | cons b bs ih =>
      dsimp [_root_.findIdx?]
      by_cases hb : b = a
      · exact ⟨0, by simp [hb]⟩
      · have ha : a ∈ bs := by
          rcases List.mem_cons.mp h with h | h
          · exfalso; exact hb h.symm
          · exact h
        obtain ⟨k, hk⟩ := ih ha
        exact ⟨k + 1, by simp [hb, hk]⟩

/-- Skipping a non-matching head shifts the position by one. -/
theorem findIdx?_getD_cons {α : Type} [DecidableEq α] (a x : α) (l : List α)
    (hx : x ∈ l) (hxa : a ≠ x) :
    (_root_.findIdx? (fun y => decide (y = x)) (a :: l)).getD 0 =
      (_root_.findIdx? (fun y => decide (y = x)) l).getD 0 + 1 := by
  dsimp [_root_.findIdx?]
  have hne : ¬ decide (a = x) := by
    intro hd
    exact hxa (of_decide_eq_true hd)
  rw [if_neg hne]
  obtain ⟨k, hk⟩ := findIdx?_some_of_mem l x hx
  rw [hk]
  rfl

/-- The head element's first-occurrence position is zero. -/
theorem findIdx?_getD_self_cons {α : Type} [DecidableEq α] (a : α) (l : List α) :
    (_root_.findIdx? (fun z => decide (z = a)) (a :: l)).getD 0 = 0 := by
  simp [_root_.findIdx?]

/-- First-occurrence position is order-preserving along a sublist of a nodup
    list. -/
theorem findIdx?_getD_lt_sublist {α : Type} [DecidableEq α] {l₁ l₂ : List α}
    (hsub : l₁ <+ l₂) (hnodup : l₂.Nodup) {x y : α} (hx : x ∈ l₁) (hy : y ∈ l₁) :
    (_root_.findIdx? (fun a => decide (a = x)) l₂).getD 0 <
        (_root_.findIdx? (fun a => decide (a = y)) l₂).getD 0 ↔
      (_root_.findIdx? (fun a => decide (a = x)) l₁).getD 0 <
        (_root_.findIdx? (fun a => decide (a = y)) l₁).getD 0 := by
  induction hsub with
  | slnil => cases hx
  | cons a hs ih =>
      rename_i l₁s l₂s
      have hnd : l₂s.Nodup := (List.nodup_cons.mp hnodup).2
      have han : a ∉ l₂s := (List.nodup_cons.mp hnodup).1
      have hx₂ : x ∈ l₂s := List.Sublist.mem hx hs
      have hy₂ : y ∈ l₂s := List.Sublist.mem hy hs
      have hxa : a ≠ x := by
        intro h
        exact han (by rwa [h])
      have hya : a ≠ y := by
        intro h
        exact han (by rwa [h])
      rw [findIdx?_getD_cons a x l₂s hx₂ hxa, findIdx?_getD_cons a y l₂s hy₂ hya]
      rw [Nat.add_lt_add_iff_right]
      exact ih hnd hx hy
  | cons_cons a hs ih =>
      rename_i l₁s l₂s
      have hnd : l₂s.Nodup := (List.nodup_cons.mp hnodup).2
      have han : a ∉ l₂s := (List.nodup_cons.mp hnodup).1
      rcases List.mem_cons.mp hx with hxa | hx'
      · subst x
        rcases List.mem_cons.mp hy with hya | hy'
        · subst y
          simp
        · have hy₂ : y ∈ l₂s := List.Sublist.mem hy' hs
          have hay : a ≠ y := by
            intro h
            exact han (by rwa [h])
          simp [findIdx?_getD_self_cons a l₂s, findIdx?_getD_self_cons a l₁s,
            findIdx?_getD_cons a y l₂s hy₂ hay, findIdx?_getD_cons a y l₁s hy' hay]
      · rcases List.mem_cons.mp hy with hya | hy'
        · subst y
          have hx₂ : x ∈ l₂s := List.Sublist.mem hx' hs
          have hax : a ≠ x := by
            intro h
            exact han (by rwa [h])
          simp [findIdx?_getD_self_cons a l₂s, findIdx?_getD_self_cons a l₁s,
            findIdx?_getD_cons a x l₂s hx₂ hax, findIdx?_getD_cons a x l₁s hx' hax]
        · have hx₂ : x ∈ l₂s := List.Sublist.mem hx' hs
          have hy₂ : y ∈ l₂s := List.Sublist.mem hy' hs
          have hax : a ≠ x := by
            intro h
            exact han (by rwa [h])
          have hay : a ≠ y := by
            intro h
            exact han (by rwa [h])
          rw [findIdx?_getD_cons a x l₂s hx₂ hax, findIdx?_getD_cons a y l₂s hy₂ hay,
            findIdx?_getD_cons a x l₁s hx' hax, findIdx?_getD_cons a y l₁s hy' hay]
          have hih := ih hnd hx' hy'
          simpa [Nat.add_lt_add_iff_right] using hih

/-- A `some i` position is a valid index holding the searched element. -/
theorem findIdx?_eq_some_getElem {α : Type} [DecidableEq α] (l : List α) (a : α)
    (i : Nat) (h : _root_.findIdx? (fun x => decide (x = a)) l = some i) :
    ∃ hi : i < l.length, l[i]'hi = a := by
  induction l generalizing i with
  | nil => cases h
  | cons b bs ih =>
      dsimp [_root_.findIdx?] at h
      by_cases hb : decide (b = a)
      · simp [hb] at h
        subst h
        refine ⟨by simp, ?_⟩
        exact of_decide_eq_true hb
      · simp [hb] at h
        cases i with
        | zero =>
          cases hf : _root_.findIdx? (fun x => decide (x = a)) bs <;>
            simp [hf] at h
        | succ i' =>
          have h' : _root_.findIdx? (fun x => decide (x = a)) bs = some i' := by
            cases hf : _root_.findIdx? (fun x => decide (x = a)) bs with
            | none => simp [hf] at h
            | some k =>
                simp [hf] at h
                simp [h]
          obtain ⟨hi', hget⟩ := ih i' h'
          refine ⟨by simpa using Nat.succ_lt_succ hi', ?_⟩
          simpa using hget

/-- A `some i` position means the element is present. -/
theorem findIdx?_mem_of_some {α : Type} [DecidableEq α] (l : List α) (a : α)
    (i : Nat) (h : _root_.findIdx? (fun x => decide (x = a)) l = some i) :
    a ∈ l := by
  obtain ⟨hi, hget⟩ := findIdx?_eq_some_getElem l a i h
  exact List.mem_iff_getElem.mpr ⟨i, hi, hget⟩

/-- The `getD 0` of a `some i` position is `i`. -/
theorem findIdx?_getD_eq_of_some {α : Type} [DecidableEq α] (l : List α) (a : α)
    (i : Nat) (h : _root_.findIdx? (fun x => decide (x = a)) l = some i) :
    (_root_.findIdx? (fun x => decide (x = a)) l).getD 0 = i := by
  rw [h]
  rfl

/-- Distinct present elements have distinct first-occurrence positions. -/
theorem findIdx?_ne_of_ne {α : Type} [DecidableEq α] (l : List α) {x y : α}
    (hx : x ∈ l) (hy : y ∈ l) (hne : x ≠ y) :
    (_root_.findIdx? (fun a => decide (a = x)) l).getD 0 ≠
      (_root_.findIdx? (fun a => decide (a = y)) l).getD 0 := by
  intro h
  obtain ⟨ix, hix⟩ := findIdx?_some_of_mem l x hx
  obtain ⟨iy, hiy⟩ := findIdx?_some_of_mem l y hy
  have hxpos : (_root_.findIdx? (fun a => decide (a = x)) l).getD 0 = ix :=
    findIdx?_getD_eq_of_some l x ix hix
  have hypos : (_root_.findIdx? (fun a => decide (a = y)) l).getD 0 = iy :=
    findIdx?_getD_eq_of_some l y iy hiy
  have hixy : ix = iy := by rw [hxpos, hypos] at h; exact h
  obtain ⟨_, hxeq⟩ := findIdx?_eq_some_getElem l x ix hix
  have hiy' : _root_.findIdx? (fun a => decide (a = y)) l = some ix := by
    rw [← hixy] at hiy
    exact hiy
  obtain ⟨_, hyeq'⟩ := findIdx?_eq_some_getElem l y ix hiy'
  have hxy : x = y := hxeq.symm.trans hyeq'
  exact hne hxy

/-- A pairwise-sorted list relates any two elements in position order. -/
theorem pairwise_le_of_findIdx_lt {α : Type} [DecidableEq α] (l : List α)
    (f : α → Int) (hsorted : l.Pairwise (fun a b => f a ≤ f b))
    {x y : α} (hx : x ∈ l) (hy : y ∈ l)
    (hxy : (_root_.findIdx? (fun a => decide (a = x)) l).getD 0 <
           (_root_.findIdx? (fun a => decide (a = y)) l).getD 0) :
    f x ≤ f y := by
  obtain ⟨ix, hix⟩ := findIdx?_some_of_mem l x hx
  obtain ⟨iy, hiy⟩ := findIdx?_some_of_mem l y hy
  have hxpos : (_root_.findIdx? (fun a => decide (a = x)) l).getD 0 = ix :=
    findIdx?_getD_eq_of_some l x ix hix
  have hypos : (_root_.findIdx? (fun a => decide (a = y)) l).getD 0 = iy :=
    findIdx?_getD_eq_of_some l y iy hiy
  have hij : ix < iy := by
    rw [hxpos, hypos] at hxy
    exact hxy
  obtain ⟨hixb, hxeq⟩ := findIdx?_eq_some_getElem l x ix hix
  obtain ⟨hiyb, hyeq⟩ := findIdx?_eq_some_getElem l y iy hiy
  have hijb : ix < l.length := lt_trans hij hiyb
  have hrel := Pairwise.rel_get_of_lt hsorted
    (a := ⟨ix, hijb⟩) (b := ⟨iy, hiyb⟩) (by simpa using hij)
  simpa [hxeq, hyeq] using hrel

/-- Priority sandwich: in a priority-sorted list, an element sitting
    strictly between two equal-priority elements has that same priority. -/
theorem pairwise_le_sandwich {α : Type} [DecidableEq α] (l : List α)
    (f : α → Int) (hsorted : l.Pairwise (fun a b => f a ≤ f b))
    {x y z : α} (hx : x ∈ l) (hy : y ∈ l) (hz : z ∈ l)
    (hxy : (_root_.findIdx? (fun a => decide (a = x)) l).getD 0 <
           (_root_.findIdx? (fun a => decide (a = y)) l).getD 0)
    (hyz : (_root_.findIdx? (fun a => decide (a = y)) l).getD 0 <
           (_root_.findIdx? (fun a => decide (a = z)) l).getD 0)
    (hxz : f x = f z) : f y = f x := by
  have hxy_le : f x ≤ f y :=
    pairwise_le_of_findIdx_lt l f hsorted hx hy hxy
  have hyz_le : f y ≤ f z :=
    pairwise_le_of_findIdx_lt l f hsorted hy hz hyz
  omega

/-- An element in a prefix of a list precedes an element present only in the
    suffix. -/
theorem findIdx?_lt_of_prefix_mem {α : Type} [DecidableEq α] (pre rest : List α)
    {x y : α} (hx : x ∈ pre) (hy : y ∈ pre ++ rest) (hy_not : y ∉ pre) :
    (_root_.findIdx? (fun a => decide (a = x)) (pre ++ rest)).getD 0 <
      (_root_.findIdx? (fun a => decide (a = y)) (pre ++ rest)).getD 0 := by
  induction pre generalizing x y with
  | nil => cases hx
  | cons a pre' ih =>
      rw [List.cons_append] at hy ⊢
      by_cases hxa : a = x
      · subst x
        have hya : a ≠ y := by
          intro h
          exact hy_not (by rw [h]; exact List.mem_cons.mpr (Or.inl rfl))
        have hy' : y ∈ pre' ++ rest := by
          rw [List.mem_cons] at hy
          rcases hy with hy | hy
          · exact absurd hy.symm hya
          · exact hy
        rw [findIdx?_getD_self_cons a (pre' ++ rest),
          findIdx?_getD_cons a y (pre' ++ rest) hy' hya]
        omega
      · have hx' : x ∈ pre' := by
          rw [List.mem_cons] at hx
          rcases hx with hx | hx
          · exact absurd hx.symm hxa
          · exact hx
        have hy_not' : y ∉ pre' := by
          intro h
          exact hy_not (List.mem_cons.mpr (Or.inr h))
        have hya : a ≠ y := by
          intro h
          exact hy_not (by rw [h]; exact List.mem_cons.mpr (Or.inl rfl))
        have hy' : y ∈ pre' ++ rest := by
          rw [List.mem_cons] at hy
          rcases hy with hy | hy
          · exact absurd hy.symm hya
          · exact hy
        rw [findIdx?_getD_cons a x (pre' ++ rest) (List.mem_append.mpr (Or.inl hx')) hxa,
          findIdx?_getD_cons a y (pre' ++ rest) hy' hya]
        have hih := ih hx' hy' hy_not'
        omega

/-- If `x`'s first occurrence precedes `y`'s (both present), then `[x, y]`
    embeds as a sublist. -/
theorem sublist_pair_of_findIdx_lt {α : Type} [DecidableEq α] (l : List α)
    {x y : α} (hx : x ∈ l) (hy : y ∈ l)
    (hxy : (_root_.findIdx? (fun a => decide (a = x)) l).getD 0 <
           (_root_.findIdx? (fun a => decide (a = y)) l).getD 0) :
    [x, y] <+ l := by
  induction l with
  | nil => cases hx
  | cons a rest ih =>
      by_cases hxa : a = x
      · subst x
        have hxy_ne : a ≠ y := by
          intro heq
          subst y
          have hself := findIdx?_getD_self_cons a rest
          rw [hself] at hxy
          omega
        have hy_rest : y ∈ rest := by
          rw [List.mem_cons] at hy
          rcases hy with h | h
          · exact absurd h.symm hxy_ne
          · exact h
        exact Sublist.cons_cons a (List.singleton_sublist.mpr hy_rest)
      · have hx_rest : x ∈ rest := by
          rw [List.mem_cons] at hx
          rcases hx with h | h
          · exact absurd h.symm hxa
          · exact h
        by_cases hya : a = y
        · subst y
          have hself := findIdx?_getD_self_cons a rest
          have hcons := findIdx?_getD_cons a x rest hx_rest hxa
          rw [hself, hcons] at hxy
          omega
        · have hy_rest : y ∈ rest := by
            rw [List.mem_cons] at hy
            rcases hy with h | h
            · exact absurd h.symm hya
            · exact h
          have hcons_x := findIdx?_getD_cons a x rest hx_rest hxa
          have hcons_y := findIdx?_getD_cons a y rest hy_rest hya
          have hxy' : (_root_.findIdx? (fun a => decide (a = x)) rest).getD 0 <
              (_root_.findIdx? (fun a => decide (a = y)) rest).getD 0 := by
            rw [hcons_x, hcons_y] at hxy
            omega
          exact Sublist.cons a (ih hx_rest hy_rest hxy')
