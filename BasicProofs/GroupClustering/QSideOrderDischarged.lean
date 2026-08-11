import BasicProofs.GroupClustering.SuccessorSurvival
import BasicProofs.GroupClustering.NodupChain
import BasicProofs.GroupClustering.Stage0BaseOrder

open BasicRedstoneSim List

/-! # Group clustering — successor survival and the discharged Q-side order
preservation

SameSpecBeforeness and QSideOrder carry a survival premise `h_surv`: the reference event
of stage `k` must stay in `preStepWorld k` through the burst phase. The
reference event at stage `k` is due at its pop tick. The burst phase
pops due events through `processNEvents`. So the burst may pop the
reference event, and `h_surv` does not hold in general.

This file reformulates the premise. The successor event of stage
`k + 1` has a strictly later target tick, so it is non-due at the pop
tick of stage `k`. When the burst pops the stage-`k` event, the spawn
is the stage-`(k + 1)` event, and it stays in `preStepWorld k`
(SuccessorSurvival). The induction then tracks the successors instead of the
reference events.

The stage step splits on the fate of the two reference events at the
pop tick:

* both survive the burst: SameSpecBeforeness `sameSpec_stage_evBefore_nextTick`
  applies;
* the burst pops both: `gSimBurst_spawn_evBefore` (LockstepComposition) gives the
  spawn order in the post-burst queue, and both spawns are non-due, so
  the drain keeps the order;
* the burst pops the first event and keeps the second: the first
  successor already sits in the post-burst queue by the reformulated
  premise, and `World.presentNotDue_before_dueSpawn_layout` (LockstepComposition)
  keeps it before the spawn of the second event.

The fourth case (the burst pops the second event and keeps the first)
cannot occur: `gSimBurst_not_pop_later_samePri` (LockstepComposition) forbids it.

Contents:

* `h_surv_succ_discharge` — the reformulated survival premise for both
  chains and all stages up to the last middle stage;
* `sameSpec_stage_evBefore_ind_succ` — the stage induction of SameSpecBeforeness
  with the successor survival premise;
* `sameSpec_orderPreservation_discharged` — the Q-side order
  preservation of QSideOrder with the base order (Stage0BaseOrder), the Nodup
  premise (NodupChain), and the survival premise all discharged.
-/

/-! ## Re-proved private helpers -/

/-- `NodeLayoutOk` holds at every tick-start world. Reproved here
    because the QSideOrder version is private. -/
private theorem NodeLayoutOk_gSimWorld (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (t : Nat) :
    NodeLayoutOk groups
      (gSimWorld groups actTick groupOrd withinOrd pos t) := by
  dsimp [gSimWorld]
  exact NodeLayoutOk_gSimFoldl groups actTick (buildGroups groups).2 groupOrd
    withinOrd pos (buildGroups groups).1 t (NodeLayoutOk_buildGroups groups)

/-- The layout premise holds at every stage below `j`. Reproved here
    because the QSideOrder version is private. -/
private theorem popQueueWorld_layout (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (g₁ c₁ j : Nat) :
    ∀ k, k < j →
      NodeLayoutOk groups
        (popQueueWorld groups actTick groupOrd withinOrd pos g₁ c₁ k) := by
  intro k _
  dsimp [popQueueWorld]
  exact NodeLayoutOk_gSimWorld groups actTick groupOrd withinOrd pos
    (stageTarget actTick groups g₁ c₁ k)

/-- One tick after the pop tick of stage `j`, the queue equals the
    queue after the drain step of the pre-step world. Reproved here
    because the SameSpecBeforeness version is private. -/
private theorem gSimWorld_succ_events_eq_preStep (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (g₁ c₁ j : Nat) :
    (gSimWorld groups actTick groupOrd withinOrd pos
        (stageTarget actTick groups g₁ c₁ j + 1)).events =
    (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ j).stepUntilNextTick.events := by
  dsimp [gSimWorld, preStepWorld, popQueueWorld, popActive]
  set t := stageTarget actTick groups g₁ c₁ j
  simp only [gSimFoldl, List.range_succ, List.foldl_append, List.foldl_cons,
    List.foldl_nil]
  set W : World := List.foldl
    (gSimBody actTick (buildGroups groups).2 groupOrd withinOrd pos)
    (buildGroups groups).1 (List.range t)
  have h_tick_W : W.tick = t := by
    change (gSimFoldl actTick (buildGroups groups).2 groupOrd withinOrd pos
      (buildGroups groups).1 t).tick = t
    rw [gSimFoldl_tick, buildGroups_tick]
    omega
  dsimp [gSimBody]
  simp only [h_tick_W]
  split_ifs with h_active
  · -- the active list is empty: the burst phase folds over no pair
    have h_act_nil : groupOrd.filter (fun gi =>
        decide (gi < (buildGroups groups).2.length) && (actTick gi == t)) = [] := by
      simpa using h_active
    rw [h_act_nil]
    simp [gSimBurst]
  · rfl

/-! ## The reformulated survival premise -/

/-- The reformulated survival premise. When the burst phase pops a
    reference event of stage `k`, the stage-`(k + 1)` event of that
    chain is in `preStepWorld k`. This holds for both reference chains
    and every stage up to the last middle stage. The membership and the
    pop of each reference event are the premises of SuccessorSurvival
    `stageEvent_succ_mem_preStepWorld`. -/
theorem h_surv_succ_discharge (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (g₁ c₁ g₂ c₂ : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_spec : chainAt groups g₁ c₁ = chainAt groups g₂ c₂)
    (h_act_eq : actTick g₁ = actTick g₂)
    (h_mem : ∀ k, k ≤ (chainAt groups g₁ c₁).middleDelays.length →
      stageEvent actTick groups g₁ c₁ k ∈
        (popQueueWorld groups actTick groupOrd withinOrd pos g₁ c₁ k).events ∧
      stageEvent actTick groups g₂ c₂ k ∈
        (popQueueWorld groups actTick groupOrd withinOrd pos g₁ c₁ k).events)
    (h_gone : ∀ k, k ≤ (chainAt groups g₁ c₁).middleDelays.length →
      stageEvent actTick groups g₁ c₁ k ∉
        (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ k).events ∧
      stageEvent actTick groups g₂ c₂ k ∉
        (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ k).events) :
    ∀ k, k ≤ (chainAt groups g₁ c₁).middleDelays.length →
      stageEvent actTick groups g₁ c₁ (k + 1) ∈
        (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ k).events ∧
      stageEvent actTick groups g₂ c₂ (k + 1) ∈
        (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ k).events := by
  intro k h_k
  have h_k₂ : k ≤ (chainAt groups g₂ c₂).middleDelays.length := by
    rw [← h_spec]
    exact h_k
  -- chain 1: SuccessorSurvival applies directly
  have h₁ : stageEvent actTick groups g₁ c₁ (k + 1) ∈
      (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ k).events :=
    stageEvent_succ_mem_preStepWorld groups actTick groupOrd withinOrd pos
      g₁ c₁ k h_g₁ h_c₁ h_k (h_mem k h_k).1 (h_gone k h_k).1
  -- chain 2: the worlds keyed by chain 2 equal the worlds keyed by
  -- chain 1, because same-spec chains share the stage target
  have h_tgt : stageTarget actTick groups g₂ c₂ k =
      stageTarget actTick groups g₁ c₁ k :=
    (sameSpec_stageTarget groups actTick g₁ c₁ g₂ c₂ k h_act_eq h_spec).symm
  have h_pqw : popQueueWorld groups actTick groupOrd withinOrd pos g₂ c₂ k =
      popQueueWorld groups actTick groupOrd withinOrd pos g₁ c₁ k := by
    dsimp [popQueueWorld]
    rw [h_tgt]
  have h_psw : preStepWorld groups actTick groupOrd withinOrd pos g₂ c₂ k =
      preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ k := by
    dsimp [preStepWorld, popQueueWorld, popActive]
    rw [h_tgt]
  have h₂ : stageEvent actTick groups g₂ c₂ (k + 1) ∈
      (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ k).events := by
    have h_raw := stageEvent_succ_mem_preStepWorld groups actTick groupOrd
      withinOrd pos g₂ c₂ k h_g₂ h_c₂ h_k₂
      (h_pqw.symm ▸ (h_mem k h_k).2) (h_psw.symm ▸ (h_gone k h_k).2)
    exact h_psw ▸ h_raw
  exact ⟨h₁, h₂⟩

/-! ## The stage induction with successor survival -/

/-- The stage induction of SameSpecBeforeness, reformulated with successor
    survival. The premise at stage `k` requires the stage-`(k + 1)`
    events in `preStepWorld k`, not the stage-`k` events. The step
    splits on whether the burst phase pops the reference events. When
    the burst pops the first reference event, its successor in
    `preStepWorld k` carries the order across the tick. -/
theorem sameSpec_stage_evBefore_ind_succ (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (g₁ c₁ g₂ c₂ j : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_spec : chainAt groups g₁ c₁ = chainAt groups g₂ c₂)
    (h_act_eq : actTick g₁ = actTick g₂)
    (h_j : j ≤ (chainAt groups g₁ c₁).middleDelays.length + 1)
    (h_base : evBefore
      ((popQueueWorld groups actTick groupOrd withinOrd pos g₁ c₁ 0).events)
      (stageEvent actTick groups g₁ c₁ 0) (stageEvent actTick groups g₂ c₂ 0))
    (h_layout : ∀ k, k < j →
      NodeLayoutOk groups
        (popQueueWorld groups actTick groupOrd withinOrd pos g₁ c₁ k))
    (h_nodup : ∀ k, k < j →
      ((popQueueWorld groups actTick groupOrd withinOrd pos g₁ c₁ k).events.filter
        (fun e => e.targetTick == stageTarget actTick groups g₁ c₁ k)).Nodup)
    (h_surv : ∀ k, k < j →
      stageEvent actTick groups g₁ c₁ (k + 1) ∈
        (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ k).events ∧
      stageEvent actTick groups g₂ c₂ (k + 1) ∈
        (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ k).events) :
    evBefore
      ((popQueueWorld groups actTick groupOrd withinOrd pos g₁ c₁ j).events)
      (stageEvent actTick groups g₁ c₁ j) (stageEvent actTick groups g₂ c₂ j) := by
  induction j with
  | zero =>
    exact h_base
  | succ k ih =>
    have h_k : k ≤ (chainAt groups g₁ c₁).middleDelays.length := by omega
    have h_k₂ : k ≤ (chainAt groups g₂ c₂).middleDelays.length := by
      rw [← h_spec]
      exact h_k
    -- the induction hypothesis at stage k
    have h_Pk : evBefore
        ((popQueueWorld groups actTick groupOrd withinOrd pos g₁ c₁ k).events)
        (stageEvent actTick groups g₁ c₁ k)
        (stageEvent actTick groups g₂ c₂ k) :=
      ih (by omega)
        (fun k' hk' => h_layout k' (by omega))
        (fun k' hk' => h_nodup k' (by omega))
        (fun k' hk' => h_surv k' (by omega))
    -- restrict the queue order at stage k to the due-filter
    have h_before_due : evBefore
        ((popQueueWorld groups actTick groupOrd withinOrd pos g₁ c₁ k).events.filter
          (fun e => e.targetTick == stageTarget actTick groups g₁ c₁ k))
        (stageEvent actTick groups g₁ c₁ k)
        (stageEvent actTick groups g₂ c₂ k) := by
      apply evBefore.filter
        (fun e => e.targetTick == stageTarget actTick groups g₁ c₁ k)
      · show ((stageEvent actTick groups g₁ c₁ k).targetTick ==
          stageTarget actTick groups g₁ c₁ k) = true
        dsimp [stageEvent]
        simp
      · show ((stageEvent actTick groups g₂ c₂ k).targetTick ==
          stageTarget actTick groups g₁ c₁ k) = true
        dsimp [stageEvent]
        rw [← sameSpec_stageTarget groups actTick g₁ c₁ g₂ c₂ k h_act_eq
          h_spec]
        simp
      · exact h_Pk
    -- the pop-tick worlds
    set t := stageTarget actTick groups g₁ c₁ k
    set W : World := gSimWorld groups actTick groupOrd withinOrd pos t
    set W₁ : World := W.logOutput s!"tick {t}"
    set active : List Nat := groupOrd.filter (fun gi =>
      decide (gi < (buildGroups groups).2.length) && (actTick gi == t))
    set W_B : World := gSimBurst t (buildGroups groups).2 withinOrd pos W₁
      (active.zipIdx)
    set A : ScheduledEvent := stageEvent actTick groups g₁ c₁ k
    set D : ScheduledEvent := stageEvent actTick groups g₂ c₂ k
    set sA : ScheduledEvent := stageEvent actTick groups g₁ c₁ (k + 1)
    set sD : ScheduledEvent := stageEvent actTick groups g₂ c₂ (k + 1)
    -- tick bookkeeping
    have h_tick_W : W.tick = t :=
      gSimWorld_tick groups actTick groupOrd withinOrd pos t
    have h_tick_W₁ : W₁.tick = t := by
      show W.tick = t
      exact h_tick_W
    have h_tick_WB : W_B.tick = t := by
      dsimp [W_B]
      rw [gSimBurst_tick, h_tick_W₁]
    have h_tgt_eq : stageTarget actTick groups g₂ c₂ k = t := by
      rw [← sameSpec_stageTarget groups actTick g₁ c₁ g₂ c₂ k h_act_eq h_spec]
    -- layout at the pop-tick worlds
    have h_layout_W : NodeLayoutOk groups W := h_layout k (by omega)
    have h_layout_W₁ : NodeLayoutOk groups W₁ :=
      NodeLayoutOk_logOutput groups W s!"tick {t}" h_layout_W
    have h_layout_WB : NodeLayoutOk groups W_B :=
      NodeLayoutOk_gSimBurst groups t (buildGroups groups).2 withinOrd pos W₁
        (active.zipIdx) h_layout_W₁
    -- membership and due-ness at the burst-start world
    have hA_W₁ : A ∈ W₁.events := by
      show A ∈ W.events
      exact evBefore.mem_left h_Pk
    have hD_W₁ : D ∈ W₁.events := by
      show D ∈ W.events
      exact evBefore.mem_right h_Pk
    have hA_due_W₁ : A.targetTick = W₁.tick := by
      dsimp [A, stageEvent]
      rw [h_tick_W₁]
    have hD_due_W₁ : D.targetTick = W₁.tick := by
      dsimp [D, stageEvent]
      rw [h_tgt_eq, h_tick_W₁]
    -- order and Nodup at the burst-start world
    have h_nodup_W₁ :
        (W₁.events.filter (fun e => e.targetTick == W₁.tick)).Nodup := by
      show (W.events.filter (fun e => e.targetTick == W.tick)).Nodup
      rw [h_tick_W]
      exact h_nodup k (by omega)
    have h_before_W₁ : evBefore
        (W₁.events.filter (fun e => e.targetTick == W₁.tick)) A D := by
      show evBefore (W.events.filter (fun e => e.targetTick == W.tick)) A D
      rw [h_tick_W]
      exact h_before_due
    -- the successors are non-due at the pop tick
    have h_sA_nd : sA.targetTick ≠ t := by
      dsimp [sA, stageEvent]
      intro h_eq
      have h_lt := stageTarget_lt_succ actTick groups g₁ c₁ k h_k
      omega
    have h_sD_nd : sD.targetTick ≠ t := by
      dsimp [sD, stageEvent]
      intro h_eq
      have h_lt := stageTarget_lt_succ actTick groups g₂ c₂ k h_k₂
      rw [h_tgt_eq] at h_lt
      omega
    by_cases hA_B : A ∈ W_B.events
    · -- Case 1: A survives the burst. Then D also survives the burst,
      -- and the SameSpecBeforeness step applies.
      have h_pri_le : A.priority ≤ D.priority := by
        dsimp [A, D, stageEvent]
        rw [sameSpec_stagePri groups g₁ c₁ g₂ c₂ k h_spec]
      have hD_B : D ∈ W_B.events :=
        gSimBurst_not_pop_later_samePri t (buildGroups groups).2 withinOrd pos
          W₁ (active.zipIdx) A D hA_due_W₁ hD_due_W₁ h_pri_le h_nodup_W₁
          h_before_W₁ hA_W₁ hA_B
      have h_next : evBefore
          ((gSimWorld groups actTick groupOrd withinOrd pos (t + 1)).events)
          sA sD :=
        sameSpec_stage_evBefore_nextTick groups actTick groupOrd withinOrd pos
          g₁ c₁ g₂ c₂ k h_g₁ h_c₁ h_g₂ h_c₂ h_spec h_act_eq h_k
          (h_layout k (by omega)) (h_nodup k (by omega)) h_before_due hA_B
          hD_B
      dsimp [popQueueWorld]
      exact sameSpec_stage_evBefore_const groups actTick groupOrd withinOrd pos
        g₁ c₁ g₂ c₂ (k + 1) (t + 1)
        (stageTarget actTick groups g₁ c₁ (k + 1)) h_act_eq h_spec
        (Nat.succ_le_of_lt (stageTarget_lt_succ actTick groups g₁ c₁ k h_k))
        (Nat.le_refl (stageTarget actTick groups g₁ c₁ (k + 1))) h_next
    · -- Case 2: the burst pops A.
      by_cases hD_B : D ∈ W_B.events
      · -- Case 2a: the burst pops A and keeps D. The successor sA sits
        -- in the post-burst queue by the survival premise. It stays
        -- before the spawn of D through the drain.
        have h_sA_B : sA ∈ W_B.events := (h_surv k (by omega)).1
        have h_spawnD : ∀ (v : World), v.tick = W_B.tick →
            NodeLayoutOk groups v →
            (v.onScheduledTick D.nodeId).events = v.events ++ [sD] := by
          intro v h_v h_lay
          have h_v_tick : v.tick = stageTarget actTick groups g₂ c₂ k := by
            rw [h_v, h_tick_WB, ← h_tgt_eq]
          simpa [D, sD, stageEvent] using
            stage_spawn groups actTick v g₂ c₂ k h_g₂ h_c₂ h_k₂ h_v_tick h_lay
        have h_step : evBefore W_B.stepUntilNextTick.events sA sD :=
          World.presentNotDue_before_dueSpawn_layout groups W_B sA D sD
            h_layout_WB h_sA_B (by rw [h_tick_WB]; exact h_sA_nd) hD_B
            (by dsimp [D, stageEvent]; rw [h_tgt_eq, h_tick_WB])
            (by rw [h_tick_WB]; exact h_sD_nd) h_spawnD
        have h_next : evBefore
            ((gSimWorld groups actTick groupOrd withinOrd pos (t + 1)).events)
            sA sD := by
          rw [gSimWorld_succ_events_eq_preStep groups actTick groupOrd
            withinOrd pos g₁ c₁ k]
          exact h_step
        dsimp [popQueueWorld]
        exact sameSpec_stage_evBefore_const groups actTick groupOrd withinOrd
          pos g₁ c₁ g₂ c₂ (k + 1) (t + 1)
          (stageTarget actTick groups g₁ c₁ (k + 1)) h_act_eq h_spec
          (Nat.succ_le_of_lt (stageTarget_lt_succ actTick groups g₁ c₁ k h_k))
          (Nat.le_refl (stageTarget actTick groups g₁ c₁ (k + 1))) h_next
      · -- Case 2b: the burst pops both A and D. The spawns keep the
        -- due-filter order, and both spawns are non-due, so the drain
        -- keeps the order.
        have h_spawnA : ∀ (v : World), v.tick = W₁.tick →
            NodeLayoutOk groups v →
            (v.onScheduledTick A.nodeId).events = v.events ++ [sA] := by
          intro v h_v h_lay
          have h_v_tick : v.tick = stageTarget actTick groups g₁ c₁ k := by
            rw [h_v, h_tick_W₁]
          simpa [A, sA, stageEvent] using
            stage_spawn groups actTick v g₁ c₁ k h_g₁ h_c₁ h_k h_v_tick h_lay
        have h_spawnD : ∀ (v : World), v.tick = W₁.tick →
            NodeLayoutOk groups v →
            (v.onScheduledTick D.nodeId).events = v.events ++ [sD] := by
          intro v h_v h_lay
          have h_v_tick : v.tick = stageTarget actTick groups g₂ c₂ k := by
            rw [h_v, h_tick_W₁, ← h_tgt_eq]
          simpa [D, sD, stageEvent] using
            stage_spawn groups actTick v g₂ c₂ k h_g₂ h_c₂ h_k₂ h_v_tick h_lay
        have h_pri_eq : A.priority = D.priority := by
          dsimp [A, D, stageEvent]
          exact sameSpec_stagePri groups g₁ c₁ g₂ c₂ k h_spec
        have h_ord_B : evBefore W_B.events sA sD :=
          gSimBurst_spawn_evBefore groups t (buildGroups groups).2 withinOrd
            pos W₁ (active.zipIdx) A D sA sD h_layout_W₁ hA_W₁ hD_W₁
            hA_due_W₁ hD_due_W₁ h_pri_eq h_nodup_W₁ h_before_W₁ hA_B hD_B
            (by dsimp [W₁]; rw [h_tick_W]; exact h_sA_nd)
            (by dsimp [W₁]; rw [h_tick_W]; exact h_sD_nd)
            h_spawnA h_spawnD
        have h_step : evBefore W_B.stepUntilNextTick.events sA sD :=
          World.stepUntilNextTick_notDue_order W_B sA sD
            (evBefore.mem_left h_ord_B) (evBefore.mem_right h_ord_B)
            (by rw [h_tick_WB]; exact h_sA_nd)
            (by rw [h_tick_WB]; exact h_sD_nd) h_ord_B
        have h_next : evBefore
            ((gSimWorld groups actTick groupOrd withinOrd pos (t + 1)).events)
            sA sD := by
          rw [gSimWorld_succ_events_eq_preStep groups actTick groupOrd
            withinOrd pos g₁ c₁ k]
          exact h_step
        dsimp [popQueueWorld]
        exact sameSpec_stage_evBefore_const groups actTick groupOrd withinOrd
          pos g₁ c₁ g₂ c₂ (k + 1) (t + 1)
          (stageTarget actTick groups g₁ c₁ (k + 1)) h_act_eq h_spec
          (Nat.succ_le_of_lt (stageTarget_lt_succ actTick groups g₁ c₁ k h_k))
          (Nat.le_refl (stageTarget actTick groups g₁ c₁ (k + 1))) h_next

/-! ## The fully discharged Q-side order preservation -/

/-- Q-side order preservation for same-spec chains, with all three
    premises of QSideOrder discharged. The base order comes from Stage0BaseOrder
    `sameSpec_stage_evBefore_base`. The Nodup premise comes from NodupChain
    `sameSpec_h_nodup_discharge`. The survival premise is the
    successor survival of `h_surv_succ_discharge`. The remaining
    hypotheses are the simulation facts: the withinOrd membership and
    the burst order for the base, the Nodup of the orders, and the
    membership and the burst pop of each reference event. -/
theorem sameSpec_orderPreservation_discharged (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (g₁ c₁ g₂ c₂ : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_spec : chainAt groups g₁ c₁ = chainAt groups g₂ c₂)
    (h_act_eq : actTick g₁ = actTick g₂)
    (h_c₁_in : c₁ ∈ withinOrd g₁) (h_c₂_in : c₂ ∈ withinOrd g₂)
    (h_burst : ∃ pre mid post,
        groupOrd.filter (fun gi =>
            decide (gi < (buildGroups groups).2.length) &&
            (actTick gi == actTick g₁)) =
        pre ++ g₁ :: mid ++ g₂ :: post)
    (h_gord_nd : groupOrd.Nodup)
    (h_within_nd : ∀ gi, gi < groups.length → (withinOrd gi).Nodup)
    (h_mem : ∀ k, k ≤ (chainAt groups g₁ c₁).middleDelays.length →
      stageEvent actTick groups g₁ c₁ k ∈
        (popQueueWorld groups actTick groupOrd withinOrd pos g₁ c₁ k).events ∧
      stageEvent actTick groups g₂ c₂ k ∈
        (popQueueWorld groups actTick groupOrd withinOrd pos g₁ c₁ k).events)
    (h_gone : ∀ k, k ≤ (chainAt groups g₁ c₁).middleDelays.length →
      stageEvent actTick groups g₁ c₁ k ∉
        (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ k).events ∧
      stageEvent actTick groups g₂ c₂ k ∉
        (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ k).events) :
    let m := (chainAt groups g₁ c₁).middleDelays.length
    evBefore
      ((popQueueWorld groups actTick groupOrd withinOrd pos g₁ c₁ (m + 1)).events)
      (stageEvent actTick groups g₁ c₁ (m + 1))
      (stageEvent actTick groups g₂ c₂ (m + 1)) := by
  intro m
  refine sameSpec_stage_evBefore_ind_succ groups actTick groupOrd withinOrd pos
    g₁ c₁ g₂ c₂ (m + 1) h_g₁ h_c₁ h_g₂ h_c₂ h_spec h_act_eq (by omega)
    ?_ ?_ ?_ ?_
  · -- h_base: Stage0BaseOrder
    exact sameSpec_stage_evBefore_base groups actTick groupOrd withinOrd pos
      g₁ c₁ g₂ c₂ h_g₁ h_c₁ h_g₂ h_c₂ h_c₁_in h_c₂_in h_act_eq h_burst
  · -- h_layout: discharged from the simulation setup
    exact popQueueWorld_layout groups actTick groupOrd withinOrd pos g₁ c₁
      (m + 1)
  · -- h_nodup: NodupChain
    intro k hk
    exact sameSpec_h_nodup_discharge groups actTick groupOrd withinOrd pos
      g₁ c₁ h_gord_nd h_within_nd k (by omega)
  · -- h_surv: the reformulated successor survival
    intro k hk
    exact h_surv_succ_discharge groups actTick groupOrd withinOrd pos
      g₁ c₁ g₂ c₂ h_g₁ h_c₁ h_g₂ h_c₂ h_spec h_act_eq h_mem h_gone k
      (by omega)
