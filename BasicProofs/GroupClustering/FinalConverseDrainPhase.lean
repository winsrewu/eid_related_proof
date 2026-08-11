import BasicProofs.GroupClustering.FinalStageAssemblySetup
import BasicProofs.GroupClustering.FinalsBackwardTransportII
import BasicProofs.GroupClustering.ConverseFinalUnconditional
import BasicProofs.GroupClustering.InterloperIsSpawn
import BasicProofs.GroupClustering.StageEventCompleteness
import BasicProofs.GroupClustering.SameSpecLockstep

open BasicRedstoneSim List

/-! # Group clustering — drain phase of the final converse

Both reference stage-`m` events survive the burst and pop during the
drain: their stage-`(m + 1)` finals are absent from the post-burst
queue and appear only after `stepUntilNextTick`. The drain consumer
`ConverseSpawnFinal_stepUNT_converse` (ConverseFinalUnconditional) is discharged here:

* layout, nodup, `StageMemAt`, and `MiddleBlockOk` at the post-burst
  due filter come from FinalStageAssemblySetup;
* the `FinalBlockBetween` block premise comes from FinalsBackwardTransportII;
* the middle final's absence from the post-burst queue follows from
  `spawn_not_survivor_of_between` (InterloperIsSpawn) with the drain
  filter-split.
-/

/-- A filter that keeps every element of a list is the identity
    (reproven; private in ConverseFinalUnconditional). -/
private theorem filter_eq_self_of_forall' {α : Type} (p : α → Bool)
    (l : List α) (h : ∀ x ∈ l, p x = true) : l.filter p = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have h_x := h x (List.mem_cons.mpr (Or.inl rfl))
    simp [List.filter, h_x, ih (fun y hy => h y (List.mem_cons.mpr (Or.inr hy)))]

/-- The drain of any world splits the result queue into the non-due
    survivors followed by the spawn accumulator. -/
private theorem stepUNT_filter_split (w : World) :
    w.stepUntilNextTick.events =
      w.events.filter (fun ev => ev.targetTick ≠ w.tick) ++
        World.popSpawnAcc w
          ((w.events.filter (fun e => e.targetTick == w.tick)).length) := by
  set n := (w.events.filter (fun e => e.targetTick == w.tick)).length
  set W := processNEvents w n
  have h_drain : W.events.filter (fun ev => ev.targetTick == w.tick) = [] :=
    drain_due_filter w
  have h_no : ∀ ev ∈ W.events, ev.targetTick ≠ W.tick := by
    intro ev h_ev h_eq
    have h_mem : ev ∈ W.events.filter (fun e => e.targetTick == w.tick) := by
      rw [List.mem_filter]
      exact ⟨h_ev, by
        rw [processNEvents_tick] at h_eq
        rw [h_eq]
        simp⟩
    rw [h_drain] at h_mem
    cases h_mem
  have h_post_events : w.stepUntilNextTick.events = W.events := by
    have h_pop_none : W.popNextEvent = none :=
      World.popNextEvent_none_of_no_due W h_no
    have h_step_none : W.step = none := by
      simp only [World.step, h_pop_none]
    rw [← processNEvents_stepUntilNextTick_eq w n,
      stepUntilNextTick_of_step_none W h_step_none]
  have h_split : W.events =
      w.events.filter (fun ev => ev.targetTick ≠ w.tick) ++
        World.popSpawnAcc w n := by
    have h_f := (World.popSeqWorldFuel_filter_split w n).1
    rw [← processNEvents_eq_popSeqWorldFuel] at h_f
    have h_keep : W.events.filter (fun ev => ev.targetTick ≠ w.tick) =
        W.events := by
      apply filter_eq_self_of_forall'
      intro ev h_ev
      have h_ne : ev.targetTick ≠ w.tick := by
        have h := h_no ev h_ev
        rwa [processNEvents_tick] at h
      rw [decide_eq_true_eq]
      exact h_ne
    rw [← h_keep]
    exact h_f
  rw [h_post_events, h_split]

/-- The drain phase of the final converse. Both reference finals are
    absent from the post-burst queue; the middle final lies between
    them after the drain. Concludes `ConverseSpawnFinal` at the
    post-burst queue. -/
theorem drainPhase_ConverseSpawnFinal (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat)
    (h_valid : ∀ gi (c : ChainSpec), gi < groups.length →
        c ∈ groupAt groups gi →
        (∀ d ∈ c.middleDelays, ValidDelay d) ∧ ValidDelay c.lastDelay)
    (h_uniform : ∀ gi (c₁ c₂ : ChainSpec), gi < groups.length →
        c₁ ∈ groupAt groups gi → c₂ ∈ groupAt groups gi →
        chainDelay c₁ = chainDelay c₂)
    (T : Nat)
    (h_act : ∀ gi, gi < groups.length → groupAt groups gi ≠ [] →
        actTick gi + groupDelay (groupAt groups gi) = T)
    (h_ord : List.Perm groupOrd (List.range groups.length))
    (h_within : ∀ gi, gi < groups.length →
        List.Perm (withinOrd gi) (List.range (groupAt groups gi).length))
    (g₁ c₁ gm cm g₂ c₂ m : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_gm : gm < groups.length) (h_cm : cm < (groupAt groups gm).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_spec : chainAt groups g₁ c₁ = chainAt groups g₂ c₂)
    (h_act_eq : actTick g₁ = actTick g₂)
    (h_m₁ : (chainAt groups g₁ c₁).middleDelays.length = m)
    (h_m₂ : (chainAt groups g₂ c₂).middleDelays.length = m)
    (h_m_ge : 1 ≤ m)
    (h_mb_full : MiddleBlockOk groups actTick T
        ((gSimWorld groups actTick groupOrd withinOrd pos
          (stageTarget actTick groups g₁ c₁ m)).events) g₁ c₁ g₂ c₂ m)
    (h_sA : stageEvent actTick groups g₁ c₁ (m + 1) ∉
        (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ m).events)
    (h_sD : stageEvent actTick groups g₂ c₂ (m + 1) ∉
        (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ m).events)
    (h_spawn_e : stageTarget actTick groups gm cm
        ((chainAt groups gm cm).middleDelays.length) ≤
      stageTarget actTick groups g₁ c₁ m)
    (h_ne_left : stageEvent actTick groups g₁ c₁ (m + 1) ≠
      stageEvent actTick groups gm cm
        ((chainAt groups gm cm).middleDelays.length + 1))
    (h_ne_right : stageEvent actTick groups gm cm
        ((chainAt groups gm cm).middleDelays.length + 1) ≠
      stageEvent actTick groups g₂ c₂ (m + 1))
    (h_due_left : evBefore
        ((gSimWorld groups actTick groupOrd withinOrd pos T).events.filter
          (fun ev => ev.targetTick == T))
        (stageEvent actTick groups g₁ c₁ (m + 1))
        (stageEvent actTick groups gm cm
          ((chainAt groups gm cm).middleDelays.length + 1)))
    (h_due_right : evBefore
        ((gSimWorld groups actTick groupOrd withinOrd pos T).events.filter
          (fun ev => ev.targetTick == T))
        (stageEvent actTick groups gm cm
          ((chainAt groups gm cm).middleDelays.length + 1))
        (stageEvent actTick groups g₂ c₂ (m + 1))) :
    ConverseSpawnFinal groups actTick
      (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ m)
      g₁ c₁ g₂ c₂ m
      (stageEvent actTick groups gm cm
        ((chainAt groups gm cm).middleDelays.length + 1)) := by
  set W_B := preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ m
  set e := stageEvent actTick groups gm cm
    ((chainAt groups gm cm).middleDelays.length + 1)
  have h_gord_nd : groupOrd.Nodup := Nodup.of_perm h_ord List.nodup_range
  have h_within_nd : ∀ gi, gi < groups.length → (withinOrd gi).Nodup :=
    fun gi h_gi => Nodup.of_perm (h_within gi h_gi) List.nodup_range
  obtain ⟨h_ok_B, h_layout_B⟩ := preStepWorld_tickQueueOk groups actTick
    groupOrd withinOrd pos h_gord_nd h_within_nd g₁ c₁ m
  have h_nodup_B : (W_B.events.filter
      (fun ev => ev.targetTick == W_B.tick)).Nodup :=
    List.Nodup.filter (fun ev => ev.targetTick == W_B.tick) h_ok_B.1
  have h_stage_B : StageMemAt groups actTick W_B W_B.tick :=
    StageMemAt_of_TickQueueOk groups actTick W_B _ h_ok_B
  have h_mb_B : MiddleBlockOk groups actTick T
      (W_B.events.filter (fun ev => ev.targetTick == W_B.tick))
      g₁ c₁ g₂ c₂ m := by
    dsimp [W_B]
    exact MiddleBlockOk_preStepWorld groups actTick groupOrd withinOrd pos
      T g₁ c₁ g₂ c₂ m h_mb_full h_gord_nd h_within_nd
  have h_tgt₂ : stageTarget actTick groups g₂ c₂ m =
      stageTarget actTick groups g₁ c₁ m :=
    (sameSpec_stageTarget groups actTick g₁ c₁ g₂ c₂ m h_act_eq h_spec).symm
  have h_blk : FinalBlockBetween groups actTick T
      W_B.stepUntilNextTick.events g₁ c₁ g₂ c₂ m e := by
    dsimp [W_B, e]
    exact FinalBlockBetween_final_stepUNT_of_dueFilter groups actTick
      groupOrd withinOrd pos T h_valid h_uniform h_act h_ord h_within
      g₁ c₁ gm cm g₂ c₂ m h_g₁ h_c₁ h_gm h_cm h_g₂ h_c₂ h_m₁ h_m₂
      h_spawn_e (le_of_eq h_tgt₂) h_ne_left h_ne_right h_due_left
      h_due_right
  have h_T : stageTarget actTick groups g₁ c₁ (m + 1) = T := by
    rw [← h_m₁]
    exact stageTarget_final_eq_T groups actTick T g₁ c₁ h_g₁ h_c₁
      h_uniform h_act
  have h_e_tgt : e.targetTick = T := by
    dsimp [e]
    exact stageTarget_final_eq_T groups actTick T gm cm h_gm h_cm
      h_uniform h_act
  have h_tick_B : W_B.tick = stageTarget actTick groups g₁ c₁ m :=
    preStepWorld_tick_eq groups actTick groupOrd withinOrd pos g₁ c₁ m
  have h_e_absent : e ∉ W_B.events := by
    refine spawn_not_survivor_of_between W_B
      (stageEvent actTick groups g₁ c₁ (m + 1)) e
      (World.popSpawnAcc W_B
        ((W_B.events.filter
          (fun ev => ev.targetTick == W_B.tick)).length))
      (stepUNT_filter_split W_B) h_sA ?_ ?_ ?_
    · rw [h_e_tgt, h_tick_B]
      intro h_eq
      have h_lt := stageTarget_lt_succ actTick groups g₁ c₁ m (by omega)
      omega
    · exact h_blk.2.2.1
    · rw [← gSimWorld_succ_events_eq_preStepWorld groups actTick
        groupOrd withinOrd pos g₁ c₁ m]
      exact gSimWorld_events_Nodup groups actTick groupOrd withinOrd pos
        (stageTarget actTick groups g₁ c₁ m + 1) h_gord_nd h_within_nd
  exact ConverseSpawnFinal_stepUNT_converse groups actTick T W_B
    g₁ c₁ g₂ c₂ m h_g₁ h_c₁ h_g₂ h_c₂ h_layout_B h_m_ge h_m₁ h_m₂
    h_tick_B h_tgt₂ h_nodup_B h_mb_B h_stage_B h_sA h_sD h_T
    e h_e_absent h_blk
