import BasicProofs.GroupClustering.Stage1BaseGeneral

open BasicRedstoneSim List

/-! # Group clustering — the induction step's early-parent intruder case

First piece of the general (arbitrary-`pos`) stage-induction step.
At the pop tick `τⱼ` of stage `j`,
an intruder `e` that is a stage event whose parent popped strictly
before `τⱼ` is already queued at `τⱼ`, while the reference
stage-`(j + 1)` event `sA₁` is absent there
(`stageEvent_succ_not_mem_gSimWorld`) and appears only when its parent
is popped during tick `τⱼ`. Hence `e` precedes `sA₁` in the
tick-`(τⱼ + 1)` queue, contradicting any assumed `sA₁` before `e`.
This is the step-level analogue of Case 1 of Stage1BaseGeneral's trichotomy, with
no pop-order reasoning. -/

/-- An intruder present in the tick-`(τⱼ + 1)` queue whose parent
    popped strictly before `τⱼ` precedes the reference stage-`(j + 1)`
    event there. -/
theorem intruder_before_sA_of_early_parent (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat)
    (h_valid : ∀ gi (c : ChainSpec), gi < groups.length →
        c ∈ groupAt groups gi →
        (∀ d ∈ c.middleDelays, ValidDelay d) ∧ ValidDelay c.lastDelay)
    (h_ord : List.Perm groupOrd (List.range groups.length))
    (h_within : ∀ gi, gi < groups.length →
        List.Perm (withinOrd gi) (List.range (groupAt groups gi).length))
    (g₁ c₁ j : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_j₁ : j + 1 ≤ (chainAt groups g₁ c₁).middleDelays.length)
    (e : ScheduledEvent) (g c j' : Nat)
    (h_g : g < groups.length) (h_c : c < (groupAt groups g).length)
    (h_e_mem : e ∈ (gSimWorld groups actTick groupOrd withinOrd pos
        (stageTarget actTick groups g₁ c₁ j + 1)).events)
    (h_e_eq : e = stageEvent actTick groups g c j')
    (h_pri : e.priority = (-3 : Int))
    (h_early : stageTarget actTick groups g c (j' - 1) <
        stageTarget actTick groups g₁ c₁ j) :
    evBefore (gSimWorld groups actTick groupOrd withinOrd pos
      (stageTarget actTick groups g₁ c₁ j + 1)).events e
      (stageEvent actTick groups g₁ c₁ (j + 1)) := by
  set τⱼ := stageTarget actTick groups g₁ c₁ j
  set sA₁ := stageEvent actTick groups g₁ c₁ (j + 1)
  -- e is a middle stage event: 1 ≤ j' ≤ middleDelays.length
  have h_j'_mid : 1 ≤ j' ∧ j' ≤ (chainAt groups g c).middleDelays.length := by
    have h_pri' : (stageEvent actTick groups g c j').priority = (-3 : Int) := by
      rw [← h_e_eq]
      exact h_pri
    dsimp [stageEvent, stagePri] at h_pri'
    have h_ne0 : j' ≠ 0 := by
      intro h₀
      rw [h₀] at h_pri'
      dsimp at h_pri'
      omega
    have h_le : j' ≤ (chainAt groups g c).middleDelays.length := by
      by_contra h_gt
      have h_val : (if j' = 0 then 0
          else if j' ≤ (chainAt groups g c).middleDelays.length then (-3 : Int)
          else (-1 : Int)) = (-1 : Int) := by
        split_ifs <;> omega
      rw [h_val] at h_pri'
      omega
    exact ⟨by omega, h_le⟩
  -- stage-window characterization at τⱼ + 1 gives the target equation
  obtain ⟨g'', c'', j'', _, _, _, h_e_eq'', h_win⟩ :=
    gSimWorld_events_stageWindow groups actTick groupOrd withinOrd pos
      (τⱼ + 1) e h_e_mem
  have h_st : stageTarget actTick groups g c j' =
      stageTarget actTick groups g'' c'' j'' := by
    have h_eq_events : stageEvent actTick groups g c j' =
        stageEvent actTick groups g'' c'' j'' := by
      rw [← h_e_eq, h_e_eq'']
    exact congr_arg ScheduledEvent.targetTick h_eq_events
  dsimp [stageWindow] at h_win
  have h_pri_j'' : stagePri groups g'' c'' j'' = (-3 : Int) := by
    rw [h_e_eq''] at h_pri
    dsimp [stageEvent] at h_pri
    exact h_pri
  have h_win' : stageTarget actTick groups g'' c'' (j'' - 1) < τⱼ + 1 ∧
      τⱼ + 1 ≤ stageTarget actTick groups g'' c'' j'' := by
    split_ifs at h_win with h_j''0
    · rw [h_j''0] at h_pri_j''
      dsimp [stagePri] at h_pri_j''
      omega
    · exact h_win
  -- e sits in the tick-τⱼ queue: its parent popped before τⱼ
  have h_e_τⱼ : e ∈
      (gSimWorld groups actTick groupOrd withinOrd pos τⱼ).events := by
    convert stageEvent_succ_mem_range_complete groups actTick groupOrd
      withinOrd pos h_valid h_ord h_within g c (j' - 1) h_g h_c
      (by omega) τⱼ (by omega) (by
        rw [Nat.sub_add_cancel (show 1 ≤ j' by omega), h_st]
        omega) using 1
    · rw [h_e_eq, Nat.sub_add_cancel (show 1 ≤ j' by omega)]
  -- sA₁ is absent from the tick-τⱼ queue, present at τⱼ + 1
  have h_sA_absent : sA₁ ∉
      (gSimWorld groups actTick groupOrd withinOrd pos τⱼ).events :=
    stageEvent_succ_not_mem_gSimWorld groups actTick groupOrd withinOrd
      pos g₁ c₁ j τⱼ h_g₁ h_c₁ (by omega) rfl
  have h_sA_mem : sA₁ ∈
      (gSimWorld groups actTick groupOrd withinOrd pos (τⱼ + 1)).events :=
    stageEvent_succ_mem_range_complete groups actTick groupOrd withinOrd
      pos h_valid h_ord h_within g₁ c₁ j h_g₁ h_c₁ (by omega) (τⱼ + 1)
      (by omega) (by
        exact Nat.succ_le_of_lt (stageTarget_lt_succ actTick groups g₁ c₁
          j (by omega)))
  -- e is non-due at τⱼ, so it is the survivor and sA₁ the spawn
  have h_e_nd : e.targetTick ≠ τⱼ := by
    rw [h_e_eq]
    dsimp [stageEvent]
    rw [h_st]
    omega
  exact evBefore_survivor_before_spawn groups actTick groupOrd withinOrd pos
    τⱼ h_valid e sA₁ h_e_τⱼ h_e_nd h_sA_mem h_sA_absent
