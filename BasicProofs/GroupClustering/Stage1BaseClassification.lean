import BasicProofs.GroupClustering.ConverseStage0

open BasicRedstoneSim List

/-! # Group clustering — base-case classification at stage 1

An event that sits between the two reference stage-`1` spawns in the
post-drain queue at the stage-`0` pop tick, carries priority `-3`, and
targets the stage-`1` tick of the first chain, is a same-prefix stage-`1`
event (a middle block). This wraps the stage-`0` stepUNT converse
(ConverseStage0) with the prefix-extension arithmetic of MiddleBlockInvariant and forms the
core of the `MiddleBlockOk` base case at stage 1. -/

/-- Core of the base case at stage 1. An event `e` between the two
    reference stage-`1` spawns in `w.stepUntilNextTick.events` (with `w`
    the world at the stage-`0` pop tick), carrying priority `-3` and
    targeting the stage-`1` tick of the first chain, is a same-prefix
    stage-`1` event. -/
theorem MiddleBlock_of_stage0_between (groups : List GroupSpec)
    (actTick : Nat → Nat) (T : Nat) (w : World) (g₁ c₁ g₂ c₂ : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_m₁ : 1 ≤ (chainAt groups g₁ c₁).middleDelays.length)
    (h_layout : NodeLayoutOk groups w)
    (h_due : w.tick = stageTarget actTick groups g₁ c₁ 0)
    (h_tgt0 : stageTarget actTick groups g₂ c₂ 0 =
        stageTarget actTick groups g₁ c₁ 0)
    (h_nodup : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup)
    (h_stage : StageMemAt groups actTick w w.tick)
    (h_sA_absent : stageEvent actTick groups g₁ c₁ 1 ∉ w.events)
    (h_sD_absent : stageEvent actTick groups g₂ c₂ 1 ∉ w.events)
    (e : ScheduledEvent)
    (h_e_absent : e ∉ w.events)
    (h_pri : e.priority = (-3 : Int))
    (h_tgt : e.targetTick = stageTarget actTick groups g₁ c₁ 1)
    (h_b1 : evBefore w.stepUntilNextTick.events
        (stageEvent actTick groups g₁ c₁ 1) e)
    (h_b2 : evBefore w.stepUntilNextTick.events e
        (stageEvent actTick groups g₂ c₂ 1)) :
    MiddleBlock groups actTick T g₁ c₁ 1 e := by
  -- classify the spawn via the stage-0 stepUNT converse
  obtain ⟨g, c, h_g, h_c, h_e_eq, h_left, h_right⟩ :=
    converse_spawn_stepUNT_stage0 groups actTick w g₁ c₁ g₂ c₂
      h_g₁ h_c₁ h_g₂ h_c₂ h_layout h_due h_tgt0 h_nodup h_stage
      h_sA_absent h_sD_absent e h_e_absent h_b1 h_b2
  -- the parent stage-0 event is due at the stage-0 pop tick
  have h_tgt_stage0 : stageTarget actTick groups g c 0 =
      stageTarget actTick groups g₁ c₁ 0 := by
    have h_mem : stageEvent actTick groups g c 0 ∈
        w.events.filter (fun ev => ev.targetTick == w.tick) :=
      evBefore.mem_right h_left
    have h_due_e : (stageEvent actTick groups g c 0).targetTick = w.tick := by
      simpa [Nat.beq_eq] using (List.mem_filter.mp h_mem).2
    dsimp [stageEvent] at h_due_e
    rw [h_due] at h_due_e
    exact h_due_e
  -- e targets the stage-1 tick of the first chain
  have h_tgt_stage1 : stageTarget actTick groups g c 1 =
      stageTarget actTick groups g₁ c₁ 1 := by
    have h_st : e.targetTick = stageTarget actTick groups g c 1 := by
      rw [h_e_eq]
      dsimp [stageEvent]
    exact h_st.symm.trans h_tgt
  -- e's priority forces chain (g, c) to have at least one middle delay
  have h_m_gc : 1 ≤ (chainAt groups g c).middleDelays.length := by
    have h_p : stagePri groups g c 1 = (-3 : Int) := by
      have h := congr_arg ScheduledEvent.priority h_e_eq.symm
      dsimp [stageEvent] at h
      rw [h_pri] at h
      exact h
    dsimp only [stagePri] at h_p
    split_ifs at h_p
    all_goals omega
  -- the empty prefix at stage 0 matches trivially
  have h_pref0 : prefixDelays groups g c 0 = prefixDelays groups g₁ c₁ 0 := by
    simp [prefixDelays]
  -- equal targets at stages 0 and 1 extend the prefix to stage 1
  have h_pref1 : prefixDelays groups g c 1 = prefixDelays groups g₁ c₁ 1 :=
    prefixDelays_ext_of_targets_eq groups actTick g c g₁ c₁ 0
      (by omega) (by omega) h_pref0 h_tgt_stage0 h_tgt_stage1
  exact Or.inr ⟨g, c, h_g, h_c, h_e_eq, h_pri, h_tgt, h_pref1⟩
