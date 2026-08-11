import BasicProofs.GroupClustering.FinalsBackwardTransportII

set_option linter.unusedVariables false

open BasicRedstoneSim List

/-! # Group clustering — backward betweenness transport for finals, III

Transport of the tick-`T` due-filter betweenness of the final events
(OutputBetweennessBridge output) into the POST-BURST queue at the reference stage-`m`
pop tick, in the shape the burst-phase converse consumers need.

## Consumer sub-goal decomposition

`Pri1FinalOf_of_between` and `ConverseSpawnFinal_converse` (ConverseFinalUnconditional) are
instantiated with `w` the tick-start world at the pop tick
`τ := stageTarget actTick groups g₁ c₁ m` and read betweenness in
`(gSimBurst τ obsAll withinOrd pos w' pairs).events`. With
`obsAll := (buildGroups groups).2`,
`w' := (popQueueWorld … g₁ c₁ m).logOutput …` and
`pairs := (popActive … g₁ c₁ m).zipIdx`, that burst world is exactly
`preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ m` (QSideOrder
definitions), whose tick is `τ` (`preStepWorld_tick_eq`, PreStepWorldFacts).

FinalsBackwardTransportII provides the betweenness in the drain queue
`(preStepWorld … g₁ c₁ m).stepUntilNextTick.events`; BackwardTransport's
`evBefore_stepUNT_backward` moves it one step further back into the
post-burst queue, given:

* all three final events sit in the post-burst queue (premises
  `h_mem₁` / `h_mem_e` / `h_mem₂`; discharged at assembly by the
  burst/drain phase split — membership holds exactly when the burst
  pops the corresponding stage-`m` parent during `processNEvents`);
* duplicate-freedom of the post-burst queue (premise `h_nd`);
* none of the three events is due at `τ` — unconditional, since all
  three target `T` and `τ < T` (`stageTarget_lt_T_of_middleLen`,
  FinalsBackwardTransportI).

The duplicate-freedom of the drain queue that the backward step also
needs is derived inside: by PreStepWorldFacts the drain queue is the tick-start
queue at `τ + 1`, which is duplicate-free by NodupChain. -/

/-- Betweenness of the three final events in the tick-`T` due filter,
    transported into the post-burst queue at the reference stage-`m`
    pop tick. The three membership premises and the post-burst nodup
    are supplied by the assembly's burst/drain phase split. -/
theorem evBefore_final_preStep_of_dueFilter (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (T : Nat)
    (h_valid : ∀ gi (c : ChainSpec), gi < groups.length →
        c ∈ groupAt groups gi →
        (∀ d ∈ c.middleDelays, ValidDelay d) ∧ ValidDelay c.lastDelay)
    (h_uniform : ∀ gi (c₁ c₂ : ChainSpec), gi < groups.length →
        c₁ ∈ groupAt groups gi → c₂ ∈ groupAt groups gi →
        chainDelay c₁ = chainDelay c₂)
    (h_act : ∀ gi, gi < groups.length → groupAt groups gi ≠ [] →
        actTick gi + groupDelay (groupAt groups gi) = T)
    (h_ord : List.Perm groupOrd (List.range groups.length))
    (h_within : ∀ gi, gi < groups.length →
        List.Perm (withinOrd gi) (List.range (groupAt groups gi).length))
    (g₁ c₁ gm cm g₂ c₂ m : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_gm : gm < groups.length) (h_cm : cm < (groupAt groups gm).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_m₁ : (chainAt groups g₁ c₁).middleDelays.length = m)
    (h_m₂ : (chainAt groups g₂ c₂).middleDelays.length = m)
    (h_spawn_e : stageTarget actTick groups gm cm
        ((chainAt groups gm cm).middleDelays.length) ≤
      stageTarget actTick groups g₁ c₁ m)
    (h_spawn₂ : stageTarget actTick groups g₂ c₂ m ≤
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
        (stageEvent actTick groups g₂ c₂ (m + 1)))
    (h_mem₁ : stageEvent actTick groups g₁ c₁ (m + 1) ∈
        (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ m).events)
    (h_mem_e : stageEvent actTick groups gm cm
        ((chainAt groups gm cm).middleDelays.length + 1) ∈
        (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ m).events)
    (h_mem₂ : stageEvent actTick groups g₂ c₂ (m + 1) ∈
        (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ m).events)
    (h_nd : (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ m).events.Nodup) :
    evBefore
      ((preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ m).events)
      (stageEvent actTick groups g₁ c₁ (m + 1))
      (stageEvent actTick groups gm cm
        ((chainAt groups gm cm).middleDelays.length + 1)) ∧
    evBefore
      ((preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ m).events)
      (stageEvent actTick groups gm cm
        ((chainAt groups gm cm).middleDelays.length + 1))
      (stageEvent actTick groups g₂ c₂ (m + 1)) := by
  set w := preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ m
  set e := stageEvent actTick groups gm cm
    ((chainAt groups gm cm).middleDelays.length + 1)
  obtain ⟨h_l, h_r⟩ := evBefore_final_stepUNT_of_dueFilter groups actTick
    groupOrd withinOrd pos T h_valid h_uniform h_act h_ord h_within
    g₁ c₁ gm cm g₂ c₂ m h_g₁ h_c₁ h_gm h_cm h_g₂ h_c₂ h_m₁ h_m₂
    h_spawn_e h_spawn₂ h_ne_left h_ne_right h_due_left h_due_right
  -- the drain queue is the tick-(τ + 1) queue, hence duplicate-free
  have h_nd_post : w.stepUntilNextTick.events.Nodup := by
    rw [show w.stepUntilNextTick.events =
        (gSimWorld groups actTick groupOrd withinOrd pos
          (stageTarget actTick groups g₁ c₁ m + 1)).events from
      (gSimWorld_succ_events_eq_preStepWorld groups actTick groupOrd
        withinOrd pos g₁ c₁ m).symm]
    exact gSimWorld_events_Nodup groups actTick groupOrd withinOrd pos
      (stageTarget actTick groups g₁ c₁ m + 1)
      (Nodup.of_perm h_ord List.nodup_range)
      (fun gi h_gi => Nodup.of_perm (h_within gi h_gi) List.nodup_range)
  -- τ is strictly before T, and all three events target T
  have h_τ_lt_T : stageTarget actTick groups g₁ c₁ m < T :=
    stageTarget_lt_T_of_middleLen groups actTick T g₁ c₁ m h_g₁ h_c₁
      h_uniform h_act h_m₁
  have h_tick : w.tick = stageTarget actTick groups g₁ c₁ m :=
    preStepWorld_tick_eq groups actTick groupOrd withinOrd pos g₁ c₁ m
  have h_tgt₁ : (stageEvent actTick groups g₁ c₁ (m + 1)).targetTick = T := by
    dsimp [stageEvent]
    rw [show m + 1 = (chainAt groups g₁ c₁).middleDelays.length + 1 by
      omega]
    exact stageTarget_final_eq_T groups actTick T g₁ c₁ h_g₁ h_c₁
      h_uniform h_act
  have h_tgt_e : e.targetTick = T := by
    dsimp [e, stageEvent]
    exact stageTarget_final_eq_T groups actTick T gm cm h_gm h_cm
      h_uniform h_act
  have h_tgt₂ : (stageEvent actTick groups g₂ c₂ (m + 1)).targetTick = T := by
    dsimp [stageEvent]
    rw [show m + 1 = (chainAt groups g₂ c₂).middleDelays.length + 1 by
      omega]
    exact stageTarget_final_eq_T groups actTick T g₂ c₂ h_g₂ h_c₂
      h_uniform h_act
  have h_nd₁ : (stageEvent actTick groups g₁ c₁ (m + 1)).targetTick ≠
      w.tick := by
    rw [h_tgt₁, h_tick]
    exact h_τ_lt_T.ne'
  have h_nd_e : e.targetTick ≠ w.tick := by
    rw [h_tgt_e, h_tick]
    exact h_τ_lt_T.ne'
  have h_nd₂ : (stageEvent actTick groups g₂ c₂ (m + 1)).targetTick ≠
      w.tick := by
    rw [h_tgt₂, h_tick]
    exact h_τ_lt_T.ne'
  -- one backward drain step
  constructor
  · exact evBefore_stepUNT_backward w
      (stageEvent actTick groups g₁ c₁ (m + 1)) e
      h_nd h_nd_post h_mem₁ h_mem_e h_nd₁ h_nd_e h_ne_left h_l
  · exact evBefore_stepUNT_backward w e
      (stageEvent actTick groups g₂ c₂ (m + 1))
      h_nd h_nd_post h_mem_e h_mem₂ h_nd_e h_nd₂ h_ne_right h_r

/-- The burst-path block premise of `FinalBlockBetween_converse` /
    `Pri1FinalOf_of_between` (ConverseFinalUnconditional), assembled from the transported
    betweenness. The middle final carries priority -1 and targets `T`
    unconditionally. -/
theorem FinalBlockBetween_final_preStep_of_dueFilter
    (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (T : Nat)
    (h_valid : ∀ gi (c : ChainSpec), gi < groups.length →
        c ∈ groupAt groups gi →
        (∀ d ∈ c.middleDelays, ValidDelay d) ∧ ValidDelay c.lastDelay)
    (h_uniform : ∀ gi (c₁ c₂ : ChainSpec), gi < groups.length →
        c₁ ∈ groupAt groups gi → c₂ ∈ groupAt groups gi →
        chainDelay c₁ = chainDelay c₂)
    (h_act : ∀ gi, gi < groups.length → groupAt groups gi ≠ [] →
        actTick gi + groupDelay (groupAt groups gi) = T)
    (h_ord : List.Perm groupOrd (List.range groups.length))
    (h_within : ∀ gi, gi < groups.length →
        List.Perm (withinOrd gi) (List.range (groupAt groups gi).length))
    (g₁ c₁ gm cm g₂ c₂ m : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_gm : gm < groups.length) (h_cm : cm < (groupAt groups gm).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_m₁ : (chainAt groups g₁ c₁).middleDelays.length = m)
    (h_m₂ : (chainAt groups g₂ c₂).middleDelays.length = m)
    (h_spawn_e : stageTarget actTick groups gm cm
        ((chainAt groups gm cm).middleDelays.length) ≤
      stageTarget actTick groups g₁ c₁ m)
    (h_spawn₂ : stageTarget actTick groups g₂ c₂ m ≤
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
        (stageEvent actTick groups g₂ c₂ (m + 1)))
    (h_mem₁ : stageEvent actTick groups g₁ c₁ (m + 1) ∈
        (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ m).events)
    (h_mem_e : stageEvent actTick groups gm cm
        ((chainAt groups gm cm).middleDelays.length + 1) ∈
        (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ m).events)
    (h_mem₂ : stageEvent actTick groups g₂ c₂ (m + 1) ∈
        (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ m).events)
    (h_nd : (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ m).events.Nodup) :
    FinalBlockBetween groups actTick T
      ((preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ m).events)
      g₁ c₁ g₂ c₂ m
      (stageEvent actTick groups gm cm
        ((chainAt groups gm cm).middleDelays.length + 1)) := by
  obtain ⟨h_l, h_r⟩ := evBefore_final_preStep_of_dueFilter groups actTick
    groupOrd withinOrd pos T h_valid h_uniform h_act h_ord h_within
    g₁ c₁ gm cm g₂ c₂ m h_g₁ h_c₁ h_gm h_cm h_g₂ h_c₂ h_m₁ h_m₂
    h_spawn_e h_spawn₂ h_ne_left h_ne_right h_due_left h_due_right
    h_mem₁ h_mem_e h_mem₂ h_nd
  refine ⟨?_, ?_, h_l, h_r⟩
  · dsimp [stageEvent]
    exact stagePri_last groups gm cm
  · dsimp [stageEvent]
    exact stageTarget_final_eq_T groups actTick T gm cm h_gm h_cm
      h_uniform h_act
