import BasicProofs.GroupClustering.Stage0BaseOrder

set_option linter.unusedVariables false

open BasicRedstoneSim List

/-! # Group clustering — order facts for filtered activation lists

The burst order of two groups is the order of their indices in the
filtered activation list. When the group order is a permutation of all
group indices, two distinct active groups appear in the filtered list
in one order or the other. The capstone case split uses this
disjunction.
-/

/-- Permutations preserve duplicate-freeness (backwards). -/
theorem Nodup.of_perm {α : Type} {l₁ l₂ : List α}
    (h : List.Perm l₁ l₂) (h_nd : l₂.Nodup) : l₁.Nodup := by
  induction h with
  | nil => exact h_nd
  | cons a p ih =>
    rw [List.nodup_cons] at h_nd ⊢
    refine ⟨?_, ih h_nd.2⟩
    intro h_mem
    exact h_nd.1 ((List.Perm.mem_iff p (a := a)).mp h_mem)
  | swap a b l =>
    rw [List.nodup_cons] at h_nd ⊢
    rcases h_nd with ⟨h_a_out, h_nd_tail⟩
    rw [List.nodup_cons] at h_nd_tail
    rcases h_nd_tail with ⟨h_b_out, h_nd_l⟩
    refine ⟨?_, ?_⟩
    · intro h_mem
      rw [List.mem_cons] at h_mem
      rcases h_mem with rfl | h_mem
      · exact h_a_out (List.mem_cons.mpr (Or.inl rfl))
      · exact h_b_out h_mem
    · rw [List.nodup_cons]
      refine ⟨?_, h_nd_l⟩
      intro h_mem
      exact h_a_out (List.mem_cons.mpr (Or.inr h_mem))
  | trans p₁ p₂ ih₁ ih₂ =>
    exact ih₁ (ih₂ h_nd)

/-- Membership in a permutation of `range n` is the same as being below
    `n`. -/
theorem Perm.mem_range_iff {l : List Nat} {n : Nat}
    (h_perm : List.Perm l (List.range n)) (h_len : l.length = n) (gi : Nat) :
    gi ∈ l ↔ gi < n := by
  constructor
  · intro h_mem
    exact List.mem_range.mp ((List.Perm.mem_iff h_perm (a := gi)).mp h_mem)
  · intro h_lt
    exact (List.Perm.mem_iff h_perm (a := gi)).mpr (List.mem_range.mpr h_lt)

/-- Two distinct members of a list sit in one order or the other. -/
theorem two_order_of_mem {α : Type} (l : List α) (a b : α)
    (h_a : a ∈ l) (h_b : b ∈ l) (h_ne : a ≠ b) :
    (∃ pre mid post, l = pre ++ a :: mid ++ b :: post) ∨
    (∃ pre mid post, l = pre ++ b :: mid ++ a :: post) := by
  induction l generalizing a b with
  | nil => simp at h_a
  | cons x xs ih =>
    simp only [List.mem_cons] at h_a h_b
    cases h_a with
    | inl h_eq =>
      subst h_eq
      cases h_b with
      | inl h_eq =>
        exfalso
        exact h_ne h_eq.symm
      | inr h_b =>
        left
        obtain ⟨mid, post, h_split⟩ := split_at_mem xs b h_b
        exact ⟨[], mid, post, by rw [h_split]; rfl⟩
    | inr h_a =>
      cases h_b with
      | inl h_eq =>
        subst h_eq
        right
        obtain ⟨mid, post, h_split⟩ := split_at_mem xs a h_a
        exact ⟨[], mid, post, by rw [h_split]; rfl⟩
      | inr h_b =>
        obtain h | h := ih a b h_a h_b h_ne
        · obtain ⟨pre, mid, post, h_split⟩ := h
          left
          exact ⟨x :: pre, mid, post, by rw [h_split]; rfl⟩
        · obtain ⟨pre, mid, post, h_split⟩ := h
          right
          exact ⟨x :: pre, mid, post, by rw [h_split]; rfl⟩

/-- A filter keeps the two named elements and their relative order. -/
theorem filter_keeps_between {α : Type} (p : α → Bool)
    (l₁ l₂ l₃ : List α) (a b : α)
    (h_pa : p a = true) (h_pb : p b = true) :
    (l₁ ++ a :: l₂ ++ b :: l₃).filter p =
      l₁.filter p ++ a :: l₂.filter p ++ b :: l₃.filter p := by
  have h_cons_a : ∀ l, (a :: l).filter p = a :: l.filter p := by
    intro l
    simp [List.filter, h_pa]
  have h_cons_b : ∀ l, (b :: l).filter p = b :: l.filter p := by
    intro l
    simp [List.filter, h_pb]
  rw [List.filter_append, h_cons_b, List.filter_append, h_cons_a]

/-- Two distinct active groups appear in the filtered activation list in
    one order or the other. -/
theorem burst_order_total (groups : List GroupSpec) (actTick : Nat → Nat)
    (groupOrd : List Nat) (ga gb t : Nat)
    (h_perm : List.Perm groupOrd (List.range groups.length))
    (h_ga : ga < groups.length) (h_gb : gb < groups.length)
    (h_ne : ga ≠ gb)
    (h_act_a : actTick ga = t) (h_act_b : actTick gb = t) :
    (∃ pre mid post,
        groupOrd.filter (fun gi =>
            decide (gi < (buildGroups groups).2.length) &&
            (actTick gi == t)) =
        pre ++ ga :: mid ++ gb :: post) ∨
    (∃ pre mid post,
        groupOrd.filter (fun gi =>
            decide (gi < (buildGroups groups).2.length) &&
            (actTick gi == t)) =
        pre ++ gb :: mid ++ ga :: post) := by
  set p : Nat → Bool := fun gi =>
    decide (gi < (buildGroups groups).2.length) && (actTick gi == t)
    with hp_def
  have h_len : groupOrd.length = groups.length := by
    have h := List.Perm.length_eq h_perm
    rw [List.length_range] at h
    exact h
  have h_ga_mem : ga ∈ groupOrd :=
    (Perm.mem_range_iff h_perm h_len ga).mpr h_ga
  have h_gb_mem : gb ∈ groupOrd :=
    (Perm.mem_range_iff h_perm h_len gb).mpr h_gb
  have h_pa : p ga = true := by
    rw [hp_def]
    dsimp only
    have h_dec : decide (ga < (buildGroups groups).2.length) = true := by
      rw [decide_eq_true_eq, buildGroups_snd_length]
      exact h_ga
    have h_beq : (actTick ga == t) = true := by
      simpa [Nat.beq_eq] using h_act_a
    rw [h_dec, h_beq]
    rfl
  have h_pb : p gb = true := by
    rw [hp_def]
    dsimp only
    have h_dec : decide (gb < (buildGroups groups).2.length) = true := by
      rw [decide_eq_true_eq, buildGroups_snd_length]
      exact h_gb
    have h_beq : (actTick gb == t) = true := by
      simpa [Nat.beq_eq] using h_act_b
    rw [h_dec, h_beq]
    rfl
  obtain h_ord | h_ord := two_order_of_mem groupOrd ga gb h_ga_mem h_gb_mem
    h_ne
  · obtain ⟨pre, mid, post, h_split⟩ := h_ord
    left
    refine ⟨pre.filter p, mid.filter p, post.filter p, ?_⟩
    rw [h_split]
    exact filter_keeps_between p pre mid post ga gb h_pa h_pb
  · obtain ⟨pre, mid, post, h_split⟩ := h_ord
    right
    refine ⟨pre.filter p, mid.filter p, post.filter p, ?_⟩
    rw [h_split]
    exact filter_keeps_between p pre mid post gb ga h_pb h_pa
