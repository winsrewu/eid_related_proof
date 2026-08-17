import Proofs.Model.DescentStep

open BasicRedstoneSim
open World
open List

/-! # The descent conclusion: last-repeaters fire in class-activation order

Starting from the observer base (`classObsEvts_due_sublist`), iterate the
descent step (`classStageEvts_next_due`) down to the last stage. At the
last stage the class's last-repeater events are due at the common output
tick `T`, and appear in `classActOrder` order inside the tick-`T` pop
sequence. -/

/-- The cascade spawns of a class's observer events are exactly its
    stage-0 events. -/
private theorem spawnFold_cascade_map_obs (T : Nat) (specs : List ChainSpec)
    (l : List Nat) (hi_class : ∀ i ∈ l, i < specs.length) :
    spawnFold (cascadeSpawn T specs) (l.map (obsEventOf T specs)) =
      l.map (stageEventOf T specs · 0) := by
  induction l with
  | nil => dsimp [spawnFold, List.map]
  | cons i rest ih =>
    dsimp [spawnFold, List.map]
    rw [cascadeSpawn_obs T specs i (hi_class i (List.mem_cons.mpr (Or.inl rfl)))]
    have ih' := ih (fun j hj => hi_class j (List.mem_cons.mpr (Or.inr hj)))
    dsimp [spawnFold] at ih'
    rw [ih']
    rfl

theorem spawnFold_classObsEvts_stage0 (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (c : ChainSpec)
    (hi_class : ∀ i ∈ classActOrder specs actOrd c, i < specs.length) :
    spawnFold (cascadeSpawn T specs) (classObsEvts T specs actOrd c) =
      classStageEvts T specs actOrd c 0 := by
  dsimp [classObsEvts, classStageEvts]
  exact spawnFold_cascade_map_obs T specs (classActOrder specs actOrd c) hi_class

/-- A class's stage-0 events reach their firing tick in activation
    order. -/
theorem classStageEvts_zero_due (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat) (c : ChainSpec) (i₀ : Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (hi₀ : i₀ ∈ classActOrder specs actOrd c)
    (hi_class : ∀ i ∈ classActOrder specs actOrd c, i < specs.length) :
    classStageEvts T specs actOrd c 0 <+
      (simWorld T specs actOrd pos (stageTickOf T specs i₀ 0)).events.filter
        (fun e => e.targetTick == stageTickOf T specs i₀ 0 &&
          e.priority == stagePriAt specs i₀ 0) := by
  set a := actTickOf T specs i₀
  have hspec : ∀ i ∈ classActOrder specs actOrd c, specAt specs i = c := by
    intro i hi
    dsimp [classActOrder] at hi
    exact of_decide_eq_true (List.mem_filter.mp hi).2
  have hact : ∀ i ∈ classActOrder specs actOrd c, actTickOf T specs i = a := by
    intro i hi
    dsimp [a]
    rw [actTickOf_spec T specs i i₀ (by rw [hspec i hi, hspec i₀ hi₀])]
  have hobs_due := classObsEvts_due_sublist T specs actOrd pos c h_perm a hact
  have hobsT : obsTickOf T specs i₀ = a + 2 := by
    dsimp [obsTickOf, a]
  have h_ind : classObsEvts T specs actOrd c <+
      (simWorld T specs actOrd pos (obsTickOf T specs i₀)).events.filter
        (fun e => e.targetTick == obsTickOf T specs i₀ && e.priority == 0) := by
    simpa [hobsT] using hobs_due
  set τ := obsTickOf T specs i₀
  set τ' := stageTickOf T specs i₀ 0
  set d := (stageDelayAt specs i₀ 0 : Nat)
  have h_ind_pop : classObsEvts T specs actOrd c <+
      (popSeq (simWorld T specs actOrd pos τ)).filter
        (fun e => e.priority == 0) := by
    have hpp := filter_popSeq_priority (simWorld T specs actOrd pos τ) 0
    rw [simWorld_tick] at hpp
    rw [hpp]
    exact h_ind
  have h_ind_pseq : classObsEvts T specs actOrd c <+
      popSeq (simWorld T specs actOrd pos τ) :=
    Sublist.trans h_ind_pop
      (List.filter_sublist (l := popSeq (simWorld T specs actOrd pos τ))
        (p := fun e => e.priority == 0))
  have hspawn : spawnFold (cascadeSpawn T specs)
      (classObsEvts T specs actOrd c) <+
      spawnFold (cascadeSpawn T specs) (popSeq (simWorld T specs actOrd pos τ)) :=
    spawnFold_sublist (cascadeSpawn T specs) h_ind_pseq
  have htrans : spawnFold (cascadeSpawn T specs)
      (popSeq (simWorld T specs actOrd pos τ)) <+
      (simWorld T specs actOrd pos (τ + 1)).events :=
    simWorld_popSeq_spawn_sublist T specs actOrd pos τ h_valid h_perm
  have heq : spawnFold (cascadeSpawn T specs) (classObsEvts T specs actOrd c) =
      classStageEvts T specs actOrd c 0 :=
    spawnFold_classObsEvts_stage0 T specs actOrd c hi_class
  have hnext : classStageEvts T specs actOrd c 0 <+
      (simWorld T specs actOrd pos (τ + 1)).events := by
    rw [← heq]
    exact Sublist.trans hspawn htrans
  have hd : 1 ≤ d := by
    dsimp [d]
    have h2 : 2 ≤ (stageDelayAt specs i₀ 0 : Nat) :=
      ValidDelay.ge2 (stageDelayAt_valid specs h_valid i₀ 0 (hi_class i₀ hi₀))
    omega
  have hτd : τ' = τ + d := by
    dsimp [τ', τ, d]
    rw [stageTickOf_zero]
    dsimp [obsTickOf]
  have hgt : ∀ e ∈ classStageEvts T specs actOrd c 0,
      (τ + 1) + (d - 1) ≤ e.targetTick := by
    intro e he
    obtain ⟨i, hi, heq⟩ := List.mem_map.mp he
    rw [← heq]
    dsimp [stageEventOf]
    rw [stageTickOf_spec T specs i i₀ 0 (by rw [hspec i hi, hspec i₀ hi₀])]
    rw [stageTickOf_zero]
    dsimp [τ, d]
    omega
  have hsurv := simWorld_sublist_survive_delta T specs actOrd pos (τ + 1)
    (d - 1) (classStageEvts T specs actOrd c 0) hnext hgt
  have hsurv' : classStageEvts T specs actOrd c 0 <+
      (simWorld T specs actOrd pos τ').events := by
    have harg : (τ + 1) + (d - 1) = τ' := by omega
    simpa [harg] using hsurv
  apply sublist_filter_of_forall
    (fun e => e.targetTick == τ' && e.priority == stagePriAt specs i₀ 0) hsurv'
  intro e he
  obtain ⟨i, hi, heq⟩ := List.mem_map.mp he
  rw [← heq]
  dsimp [stageEventOf]
  rw [Bool.and_eq_true]
  constructor
  · change decide (stageTickOf T specs i 0 = τ') = true
    rw [decide_eq_true_eq]
    rw [stageTickOf_spec T specs i i₀ 0 (by rw [hspec i hi, hspec i₀ hi₀])]
  · change decide (stagePriAt specs i 0 = stagePriAt specs i₀ 0) = true
    rw [decide_eq_true_eq]
    rw [stagePriAt_spec specs i i₀ 0 (by rw [hspec i hi, hspec i₀ hi₀])]

/-- A class's last-repeater events are due at the common output tick `T`,
    in activation order. -/
theorem classLastReps_due (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat) (c : ChainSpec) (i₀ : Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (h_fit : ∀ i < specs.length, chainDelay (specAt specs i) ≤ T)
    (hi₀ : i₀ ∈ classActOrder specs actOrd c)
    (hi_class : ∀ i ∈ classActOrder specs actOrd c, i < specs.length) :
    classStageEvts T specs actOrd c (repLenAt specs i₀) <+
      (simWorld T specs actOrd pos T).events.filter
        (fun e => e.targetTick == T &&
          e.priority == stagePriAt specs i₀ (repLenAt specs i₀)) := by
  have hspec : ∀ i ∈ classActOrder specs actOrd c, specAt specs i = c := by
    intro i hi
    dsimp [classActOrder] at hi
    exact of_decide_eq_true (List.mem_filter.mp hi).2
  have hstage : ∀ s, s ≤ repLenAt specs i₀ →
      classStageEvts T specs actOrd c s <+
        (simWorld T specs actOrd pos (stageTickOf T specs i₀ s)).events.filter
          (fun e => e.targetTick == stageTickOf T specs i₀ s &&
            e.priority == stagePriAt specs i₀ s) := by
    intro s
    induction s with
    | zero =>
        intro _
        exact classStageEvts_zero_due T specs actOrd pos c i₀ h_valid h_perm hi₀ hi_class
    | succ s' ih =>
        intro hsle
        have hs' : s' < repLenAt specs i₀ := Nat.lt_of_succ_le hsle
        exact classStageEvts_next_due T specs actOrd pos c s' i₀ h_valid
          h_perm hi₀ hi_class
          (fun i hi => by
            rw [repLenAt_spec specs i i₀ (by rw [hspec i hi, hspec i₀ hi₀])]
            exact hs')
          (ih (Nat.le_of_lt hs'))
  have hlast := hstage (repLenAt specs i₀) le_rfl
  have htickLast : stageTickOf T specs i₀ (repLenAt specs i₀) = T :=
    stageTickOf_last T specs i₀ (h_fit i₀ (hi_class i₀ hi₀))
  simpa [htickLast] using hlast

/-- A same-spec class's last-repeater events appear in activation order
    inside the tick-`T` pop sequence. -/
theorem classLastReps_popSeq_sublist (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat) (c : ChainSpec) (i₀ : Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (h_fit : ∀ i < specs.length, chainDelay (specAt specs i) ≤ T)
    (hi₀ : i₀ ∈ classActOrder specs actOrd c)
    (hi_class : ∀ i ∈ classActOrder specs actOrd c, i < specs.length) :
    classStageEvts T specs actOrd c (repLenAt specs i₀) <+
      popSeq (simWorld T specs actOrd pos T) := by
  have hdue := classLastReps_due T specs actOrd pos c i₀ h_valid h_perm h_fit
    hi₀ hi_class
  have hpp := filter_popSeq_priority (simWorld T specs actOrd pos T)
    (stagePriAt specs i₀ (repLenAt specs i₀))
  rw [simWorld_tick] at hpp
  rw [← hpp] at hdue
  exact Sublist.trans hdue
    (List.filter_sublist (l := popSeq (simWorld T specs actOrd pos T))
      (p := fun e => e.priority == stagePriAt specs i₀ (repLenAt specs i₀)))

