import BasicProofs.GroupClustering.LockstepComposition


open BasicRedstoneSim List

/-! # Group clustering — same-spec beforeness across ticks and stages

Same-spec chains move in lockstep. LockstepComposition proves the single-tick lockstep
step and the transport of non-due events across ticks. This file composes
those facts into queue-order statements for two same-spec chains:

* cross-tick transport: an order between two same-spec stage-`j` events at
  one tick-start queue holds at every later queue before their pop tick;
* the stage step: at the pop tick, an order between the two stage-`j`
  events carries over to the two stage-`j + 1` events one tick later;
* the induction over stages: the order at stage 0 propagates to every
  later stage.

The stage step assumes that both events survive the burst phase of their
pop tick. The final-pop order of two chains is the order at the last
stage, so these facts feed the order-preservation theorem.
-/

/-! ## Pop-tick worlds -/

/-- The queue at the start of the pop tick of stage `j` of chain
    `(g₁, c₁)`. -/
private def popQueueWorld (groups : List GroupSpec) (actTick : Nat → Nat)
    (groupOrd : List Nat) (withinOrd pos : Nat → List Nat)
    (g₁ c₁ j : Nat) : World :=
  gSimWorld groups actTick groupOrd withinOrd pos
    (stageTarget actTick groups g₁ c₁ j)

/-- The groups that activate at the pop tick of stage `j` of chain
    `(g₁, c₁)`. -/
private def popActive (groups : List GroupSpec) (actTick : Nat → Nat)
    (groupOrd : List Nat) (g₁ c₁ j : Nat) : List Nat :=
  groupOrd.filter (fun gi =>
    decide (gi < (buildGroups groups).2.length) &&
    (actTick gi == stageTarget actTick groups g₁ c₁ j))

/-- The world just before the final drain step of the pop tick of stage
    `j` of chain `(g₁, c₁)`: after the log entry and the burst phase. -/
private def preStepWorld (groups : List GroupSpec) (actTick : Nat → Nat)
    (groupOrd : List Nat) (withinOrd pos : Nat → List Nat)
    (g₁ c₁ j : Nat) : World :=
  gSimBurst (stageTarget actTick groups g₁ c₁ j) (buildGroups groups).2
    withinOrd pos
    ((popQueueWorld groups actTick groupOrd withinOrd pos g₁ c₁ j).logOutput
      s!"tick {stageTarget actTick groups g₁ c₁ j}")
    ((popActive groups actTick groupOrd g₁ c₁ j).zipIdx)

/-- One tick after the pop tick of stage `j`, the queue equals the queue
    after the drain step of the pre-step world. -/
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

/-! ## Cross-tick transport of same-spec stage events -/

/-- An order between two same-spec stage-`j` events at tick-start `a`
    holds at every tick-start `b` with `a ≤ b` before their pop tick.
    Same-spec chains share one target tick, so one bound covers both
    events. -/
theorem sameSpec_stage_evBefore_const (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (g₁ c₁ g₂ c₂ j a b : Nat)
    (h_act_eq : actTick g₁ = actTick g₂)
    (h_spec : chainAt groups g₁ c₁ = chainAt groups g₂ c₂)
    (h_le : a ≤ b)
    (h_b : b ≤ stageTarget actTick groups g₁ c₁ j)
    (h_before : evBefore
      ((gSimWorld groups actTick groupOrd withinOrd pos a).events)
      (stageEvent actTick groups g₁ c₁ j) (stageEvent actTick groups g₂ c₂ j)) :
    evBefore
      ((gSimWorld groups actTick groupOrd withinOrd pos b).events)
      (stageEvent actTick groups g₁ c₁ j) (stageEvent actTick groups g₂ c₂ j) := by
  apply gSimWorld_evBefore_const groups actTick groupOrd withinOrd pos a b
    (stageEvent actTick groups g₁ c₁ j) (stageEvent actTick groups g₂ c₂ j)
    h_le h_before
  · -- target bound for chain (g₁, c₁)
    exact h_b
  · -- target bound for chain (g₂, c₂): same spec means same target
    dsimp [stageEvent]
    rw [← sameSpec_stageTarget groups actTick g₁ c₁ g₂ c₂ j h_act_eq h_spec]
    exact h_b

/-! ## The stage step at the pop tick -/

/-- At their pop tick, two same-spec stage-`j` events in queue order spawn
    stage-`j + 1` events in the same order one tick later. The burst
    phase of the pop tick must keep both events queued. -/
theorem sameSpec_stage_evBefore_nextTick (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (g₁ c₁ g₂ c₂ j : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_spec : chainAt groups g₁ c₁ = chainAt groups g₂ c₂)
    (h_act_eq : actTick g₁ = actTick g₂)
    (h_j : j ≤ (chainAt groups g₁ c₁).middleDelays.length)
    (h_layout : NodeLayoutOk groups
      (popQueueWorld groups actTick groupOrd withinOrd pos g₁ c₁ j))
    (h_nodup : ((popQueueWorld groups actTick groupOrd withinOrd pos g₁ c₁ j).events.filter
        (fun e => e.targetTick == stageTarget actTick groups g₁ c₁ j)).Nodup)
    (h_before : evBefore
      ((popQueueWorld groups actTick groupOrd withinOrd pos g₁ c₁ j).events.filter
        (fun e => e.targetTick == stageTarget actTick groups g₁ c₁ j))
      (stageEvent actTick groups g₁ c₁ j) (stageEvent actTick groups g₂ c₂ j))
    (h_surv₁ : stageEvent actTick groups g₁ c₁ j ∈
      (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ j).events)
    (h_surv₂ : stageEvent actTick groups g₂ c₂ j ∈
      (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ j).events) :
    evBefore
      ((gSimWorld groups actTick groupOrd withinOrd pos
          (stageTarget actTick groups g₁ c₁ j + 1)).events)
      (stageEvent actTick groups g₁ c₁ (j + 1))
      (stageEvent actTick groups g₂ c₂ (j + 1)) := by
  dsimp [popQueueWorld, preStepWorld, popActive] at h_layout h_nodup h_before h_surv₁ h_surv₂
  set t := stageTarget actTick groups g₁ c₁ j
  set W : World := gSimWorld groups actTick groupOrd withinOrd pos t
  set W₁ : World := W.logOutput s!"tick {t}"
  set active : List Nat := groupOrd.filter (fun gi =>
    decide (gi < (buildGroups groups).2.length) && (actTick gi == t))
  set W_B : World := gSimBurst t (buildGroups groups).2 withinOrd pos W₁
    (active.zipIdx)
  set A : ScheduledEvent := stageEvent actTick groups g₁ c₁ j
  set D : ScheduledEvent := stageEvent actTick groups g₂ c₂ j
  -- tick bookkeeping
  have h_tick_W : W.tick = t := by
    change (gSimFoldl actTick (buildGroups groups).2 groupOrd withinOrd pos
      (buildGroups groups).1 t).tick = t
    rw [gSimFoldl_tick, buildGroups_tick]
    omega
  have h_tick_W₁ : W₁.tick = t := by
    show W.tick = t
    exact h_tick_W
  have h_tick_WB : W_B.tick = t := by
    dsimp [W_B]
    rw [gSimBurst_tick, h_tick_W₁]
  have h_tgt_eq : stageTarget actTick groups g₂ c₂ j = t := by
    rw [← sameSpec_stageTarget groups actTick g₁ c₁ g₂ c₂ j h_act_eq h_spec]
  -- both stage events are due at the pre-step world
  have hA_due₁ : A.targetTick = W₁.tick := by
    rw [h_tick_W₁]
    rfl
  have hD_due₁ : D.targetTick = W₁.tick := by
    rw [h_tick_W₁]
    exact h_tgt_eq
  -- order, health and layout carry from the tick-start queue to the
  -- pre-step world
  have h_nodup_W₁ : (W₁.events.filter (fun e => e.targetTick == W₁.tick)).Nodup := by
    show (W.events.filter (fun e => e.targetTick == W.tick)).Nodup
    rw [h_tick_W]
    exact h_nodup
  have h_before_W₁ : evBefore
      (W₁.events.filter (fun e => e.targetTick == W₁.tick)) A D := by
    show evBefore (W.events.filter (fun e => e.targetTick == W.tick)) A D
    rw [h_tick_W]
    exact h_before
  have h_layout_W₁ : NodeLayoutOk groups W₁ :=
    NodeLayoutOk_logOutput groups W s!"tick {t}" h_layout
  have h_nodup_WB : (W_B.events.filter (fun e => e.targetTick == W_B.tick)).Nodup :=
    gSimBurst_due_nodup t (buildGroups groups).2 withinOrd pos W₁
      (active.zipIdx) h_nodup_W₁
  have h_before_WB : evBefore
      (W_B.events.filter (fun e => e.targetTick == W_B.tick)) A D :=
    evBefore_due_gSimBurst_of_mem t (buildGroups groups).2 withinOrd pos W₁
      (active.zipIdx) A D hA_due₁ hD_due₁ h_nodup_W₁ h_before_W₁ h_surv₁
      h_surv₂
  have h_layout_WB : NodeLayoutOk groups W_B :=
    NodeLayoutOk_gSimBurst groups t (buildGroups groups).2 withinOrd pos W₁
      (active.zipIdx) h_layout_W₁
  -- the single-tick lockstep step of LockstepComposition
  have h_step : evBefore W_B.stepUntilNextTick.events
      (stageEvent actTick groups g₁ c₁ (j + 1))
      (stageEvent actTick groups g₂ c₂ (j + 1)) :=
    sameSpec_stage_lockstep_step groups actTick W_B g₁ c₁ g₂ c₂ j
      h_g₁ h_c₁ h_g₂ h_c₂ h_spec h_act_eq h_layout_WB h_j
      (by rw [h_tick_WB]) h_surv₁ h_surv₂ h_nodup_WB h_before_WB
  rw [gSimWorld_succ_events_eq_preStep groups actTick groupOrd withinOrd pos
    g₁ c₁ j]
  exact h_step

/-! ## Induction over the stages -/

/-- The queue order of two same-spec chains propagates through the stages.
    The base fact holds at the stage-0 pop tick. Every stage keeps both
    events alive through the burst phase of its pop tick. -/
theorem sameSpec_stage_evBefore_ind (groups : List GroupSpec)
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
      stageEvent actTick groups g₁ c₁ k ∈
        (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ k).events ∧
      stageEvent actTick groups g₂ c₂ k ∈
        (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ k).events) :
    evBefore
      ((popQueueWorld groups actTick groupOrd withinOrd pos g₁ c₁ j).events)
      (stageEvent actTick groups g₁ c₁ j) (stageEvent actTick groups g₂ c₂ j) := by
  induction j with
  | zero =>
    exact h_base
  | succ k ih =>
    have h_k : k ≤ (chainAt groups g₁ c₁).middleDelays.length := by omega
    -- the induction hypothesis at stage k
    have h_Pk : evBefore
        ((popQueueWorld groups actTick groupOrd withinOrd pos g₁ c₁ k).events)
        (stageEvent actTick groups g₁ c₁ k)
        (stageEvent actTick groups g₂ c₂ k) :=
      ih (by omega)
        (fun k' hk' => h_layout k' (by omega))
        (fun k' hk' => h_nodup k' (by omega))
        (fun k' hk' => h_surv k' (by omega))
    obtain ⟨h_surv₁, h_surv₂⟩ := h_surv k (by omega)
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
    -- the stage step: order at stage k + 1 one tick after the pop
    have h_next : evBefore
        ((gSimWorld groups actTick groupOrd withinOrd pos
            (stageTarget actTick groups g₁ c₁ k + 1)).events)
        (stageEvent actTick groups g₁ c₁ (k + 1))
        (stageEvent actTick groups g₂ c₂ (k + 1)) :=
      sameSpec_stage_evBefore_nextTick groups actTick groupOrd withinOrd pos
        g₁ c₁ g₂ c₂ k h_g₁ h_c₁ h_g₂ h_c₂ h_spec h_act_eq h_k
        (h_layout k (by omega)) (h_nodup k (by omega)) h_before_due
        h_surv₁ h_surv₂
    -- transport to the pop tick of stage k + 1
    dsimp [popQueueWorld]
    exact sameSpec_stage_evBefore_const groups actTick groupOrd withinOrd pos
      g₁ c₁ g₂ c₂ (k + 1) (stageTarget actTick groups g₁ c₁ k + 1)
      (stageTarget actTick groups g₁ c₁ (k + 1)) h_act_eq h_spec
      (Nat.succ_le_of_lt (stageTarget_lt_succ actTick groups g₁ c₁ k h_k))
      (Nat.le_refl (stageTarget actTick groups g₁ c₁ (k + 1))) h_next
