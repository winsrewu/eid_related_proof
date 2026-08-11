import BasicProofs.GroupClustering.StageEventCompleteness

set_option linter.unusedVariables false

open BasicRedstoneSim List

/-! # Group clustering — forward transport from a pop-tick burst queue

The spawn-tick squeeze argues by contradiction: if the middle final
event spawned strictly before (or after) the reference finals' common
pop tick, an ordering lemma puts it before (or after) both references
in the post-burst queue, and that order must still hold in the
tick-`T` due filter, contradicting the given betweenness. This file
supplies the forward half of that argument: betweenness in the
post-burst queue at a reference pop tick propagates to the tick-`T`
queue, provided both events target at least `T`.

The chain is: survive the drain step at the pop tick
(`evBefore_stepUNT_of_notDue`), cross to the next tick-start queue
(`gSimWorld_succ_events_eq_preStep`), then run the constant-target
forward transport (`evBefore_gSimWorld_const`). -/

/-- The tick-`(τ + 1)` queue is the drain of the post-burst world at the
    pop tick `τ = stageTarget j`. Reproved here because the QSideOrderDischarged /
    StageEventCompleteness versions are private. -/
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
  · have h_act_nil : groupOrd.filter (fun gi =>
        decide (gi < (buildGroups groups).2.length) && (actTick gi == t)) = [] := by
      simpa using h_active
    rw [h_act_nil]
    simp [gSimBurst]
  · rfl

/-- The post-burst world at the pop tick of stage `j` has tick
    `stageTarget j`. -/
private theorem preStepWorld_tick (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (g₁ c₁ j : Nat) :
    (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ j).tick =
      stageTarget actTick groups g₁ c₁ j := by
  dsimp [preStepWorld, popQueueWorld]
  rw [gSimBurst_tick, World.logOutput_tick, gSimWorld_tick]

/-- Forward transport from a pop-tick post-burst queue to the tick-`T`
    queue. Two events that are ordered in
    `preStepWorld j`, are non-due at the pop tick, and target at least
    `T` keep that order in the tick-`T` queue. -/
theorem evBefore_preStepWorld_forward (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (g₁ c₁ j T : Nat)
    (x y : ScheduledEvent)
    (h_before : evBefore
        (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ j).events
        x y)
    (h_nd_x : x.targetTick ≠ stageTarget actTick groups g₁ c₁ j)
    (h_nd_y : y.targetTick ≠ stageTarget actTick groups g₁ c₁ j)
    (h_le : stageTarget actTick groups g₁ c₁ j + 1 ≤ T)
    (h_bx : T ≤ x.targetTick) (h_by : T ≤ y.targetTick) :
    evBefore
      (gSimWorld groups actTick groupOrd withinOrd pos T).events x y := by
  set Wpre := preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ j
  set τ := stageTarget actTick groups g₁ c₁ j
  have h_tick : Wpre.tick = τ := preStepWorld_tick groups actTick groupOrd
    withinOrd pos g₁ c₁ j
  have h_x : x ∈ Wpre.events := evBefore.mem_left h_before
  have h_y : y ∈ Wpre.events := evBefore.mem_right h_before
  -- survive the drain step at the pop tick
  have h_sunt : evBefore Wpre.stepUntilNextTick.events x y :=
    evBefore_stepUNT_of_notDue Wpre x y h_x h_y
      (by rw [h_tick]; exact h_nd_x) (by rw [h_tick]; exact h_nd_y) h_before
  -- cross to the next tick-start queue
  have h_next : evBefore
      (gSimWorld groups actTick groupOrd withinOrd pos (τ + 1)).events x y := by
    rw [gSimWorld_succ_events_eq_preStep groups actTick groupOrd withinOrd
      pos g₁ c₁ j]
    exact h_sunt
  -- forward to T
  exact evBefore_gSimWorld_const groups actTick groupOrd withinOrd pos
    (τ + 1) T x y h_le h_next h_bx h_by

/-- A spawned successor is present at the next tick-start queue. When
    the burst phase pops the stage-`j` event of chain `(g₁, c₁)`, the
    stage-`(j + 1)` event is in the post-burst queue (SuccessorSurvival); it is
    non-due there, so it survives the drain into the
    tick-`(stageTarget j + 1)` queue. -/
theorem stageEvent_succ_mem_nextTick (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat)
    (h_valid : ∀ gi (c : ChainSpec), gi < groups.length →
        c ∈ groupAt groups gi →
        (∀ d ∈ c.middleDelays, ValidDelay d) ∧ ValidDelay c.lastDelay)
    (g₁ c₁ j : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_j : j ≤ (chainAt groups g₁ c₁).middleDelays.length)
    (h_mem : stageEvent actTick groups g₁ c₁ j ∈
        (popQueueWorld groups actTick groupOrd withinOrd pos g₁ c₁ j).events)
    (h_gone : stageEvent actTick groups g₁ c₁ j ∉
        (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ j).events) :
    stageEvent actTick groups g₁ c₁ (j + 1) ∈
      (gSimWorld groups actTick groupOrd withinOrd pos
        (stageTarget actTick groups g₁ c₁ j + 1)).events := by
  -- SuccessorSurvival: the successor is in the post-burst queue
  have h_pre : stageEvent actTick groups g₁ c₁ (j + 1) ∈
      (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ j).events :=
    stageEvent_succ_mem_preStepWorld groups actTick groupOrd withinOrd pos
      g₁ c₁ j h_g₁ h_c₁ h_j h_mem h_gone
  -- non-due at the pop tick
  have h_nd : (stageEvent actTick groups g₁ c₁ (j + 1)).targetTick ≠
      (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ j).tick := by
    rw [preStepWorld_tick groups actTick groupOrd withinOrd pos g₁ c₁ j]
    dsimp [stageEvent]
    intro h_eq
    have h_lt := stageTarget_lt_succ actTick groups g₁ c₁ j h_j
    omega
  -- delay ≥ 2 at the post-burst world
  have h_delay : ∀ nid nd,
      (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ j).getNode
        nid = some nd →
      ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
    dsimp [preStepWorld, popQueueWorld, popActive]
    apply gSimBurst_delay_preserved
    intro nid nd h_gn d p h_kind
    apply gSimWorld_delay_ge2 groups actTick groupOrd withinOrd pos
      (stageTarget actTick groups g₁ c₁ j) h_valid nid nd _ d p h_kind
    rw [World.logOutput_getNode] at h_gn
    exact h_gn
  -- survive the drain into the next tick-start queue
  set Wpre := preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ j
  have h_sunt : stageEvent actTick groups g₁ c₁ (j + 1) ∈
      Wpre.stepUntilNextTick.events :=
    mem_stepUNT_of_notDue
      (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ j)
      (stageEvent actTick groups g₁ c₁ (j + 1)) h_pre h_nd h_delay
  rw [gSimWorld_succ_events_eq_preStep groups actTick groupOrd withinOrd
    pos g₁ c₁ j]
  exact h_sunt

/-- A spawned successor is present at every tick-start queue from the
    tick after its spawn until its own target tick. Composes the
    next-tick presence with the non-due survival range (SimulationLevelFacts). -/
theorem stageEvent_succ_mem_range (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat)
    (h_valid : ∀ gi (c : ChainSpec), gi < groups.length →
        c ∈ groupAt groups gi →
        (∀ d ∈ c.middleDelays, ValidDelay d) ∧ ValidDelay c.lastDelay)
    (g₁ c₁ j : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_j : j ≤ (chainAt groups g₁ c₁).middleDelays.length)
    (h_mem : stageEvent actTick groups g₁ c₁ j ∈
        (popQueueWorld groups actTick groupOrd withinOrd pos g₁ c₁ j).events)
    (h_gone : stageEvent actTick groups g₁ c₁ j ∉
        (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ j).events)
    (t : Nat)
    (h_lo : stageTarget actTick groups g₁ c₁ j + 1 ≤ t)
    (h_hi : t ≤ stageTarget actTick groups g₁ c₁ (j + 1)) :
    stageEvent actTick groups g₁ c₁ (j + 1) ∈
      (gSimWorld groups actTick groupOrd withinOrd pos t).events := by
  have h_base : stageEvent actTick groups g₁ c₁ (j + 1) ∈
      (gSimWorld groups actTick groupOrd withinOrd pos
        (stageTarget actTick groups g₁ c₁ j + 1)).events :=
    stageEvent_succ_mem_nextTick groups actTick groupOrd withinOrd pos
      h_valid g₁ c₁ j h_g₁ h_c₁ h_j h_mem h_gone
  have h_ab : stageTarget actTick groups g₁ c₁ j + 1 ≤
      stageTarget actTick groups g₁ c₁ (j + 1) := by
    have h_lt := stageTarget_lt_succ actTick groups g₁ c₁ j h_j
    omega
  exact mem_gSimWorld_of_notDue_range groups actTick groupOrd withinOrd pos
    (stageTarget actTick groups g₁ c₁ j + 1)
    (stageTarget actTick groups g₁ c₁ (j + 1))
    (stageEvent actTick groups g₁ c₁ (j + 1)) h_base
    (by dsimp [stageEvent]) h_ab h_valid t h_lo h_hi

/-- A survivor of tick `t` precedes every event that first appears at
    tick `t + 1`. The queue evolves as `survivors ++ new` (StageEvents split),
    so a surviving event sits in the survivor part, and an event present
    at `t + 1` but absent at `t` is a new spawn in the appended part. -/
theorem evBefore_survivor_before_spawn (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (t : Nat)
    (h_valid : ∀ gi (c : ChainSpec), gi < groups.length →
        c ∈ groupAt groups gi →
        (∀ d ∈ c.middleDelays, ValidDelay d) ∧ ValidDelay c.lastDelay)
    (x y : ScheduledEvent)
    (h_x : x ∈ (gSimWorld groups actTick groupOrd withinOrd pos t).events)
    (h_x_nd : x.targetTick ≠ t)
    (h_y_next : y ∈ (gSimWorld groups actTick groupOrd withinOrd pos
        (t + 1)).events)
    (h_y_not : y ∉ (gSimWorld groups actTick groupOrd withinOrd pos t).events) :
    evBefore (gSimWorld groups actTick groupOrd withinOrd pos
      (t + 1)).events x y := by
  obtain ⟨new, h_split, _⟩ := gSimWorld_events_filter_split groups actTick
    groupOrd withinOrd pos t h_valid
  have h_x_surv : x ∈ (gSimWorld groups actTick groupOrd withinOrd pos
      t).events.filter (fun ev => ev.targetTick ≠ t) := by
    rw [List.mem_filter]
    exact ⟨h_x, decide_eq_true_eq.mpr h_x_nd⟩
  have h_y_new : y ∈ new := by
    have h_mem : y ∈ (gSimWorld groups actTick groupOrd withinOrd pos
        t).events.filter (fun ev => ev.targetTick ≠ t) ++ new := by
      rwa [← h_split]
    rw [List.mem_append] at h_mem
    rcases h_mem with h_y_s | h_y_n
    · exact absurd (List.mem_filter.mp h_y_s).1 h_y_not
    · exact h_y_n
  rw [h_split]
  exact evBefore.of_mem_append h_x_surv h_y_new

/-- Spawn order across ticks. An event `x` present as a survivor at the
    tick `t_r` when `y` first appears precedes `y`, and that order
    persists to any later tick `τ` both target. Composes
    `evBefore_survivor_before_spawn` with `evBefore_gSimWorld_const`. -/
theorem evBefore_spawn_order (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (t_r τ : Nat)
    (h_valid : ∀ gi (c : ChainSpec), gi < groups.length →
        c ∈ groupAt groups gi →
        (∀ d ∈ c.middleDelays, ValidDelay d) ∧ ValidDelay c.lastDelay)
    (x y : ScheduledEvent)
    (h_x : x ∈ (gSimWorld groups actTick groupOrd withinOrd pos t_r).events)
    (h_x_nd : x.targetTick ≠ t_r)
    (h_y_next : y ∈ (gSimWorld groups actTick groupOrd withinOrd pos
        (t_r + 1)).events)
    (h_y_not : y ∉ (gSimWorld groups actTick groupOrd withinOrd pos t_r).events)
    (h_le : t_r + 1 ≤ τ)
    (h_bx : τ ≤ x.targetTick) (h_by : τ ≤ y.targetTick) :
    evBefore (gSimWorld groups actTick groupOrd withinOrd pos τ).events
      x y := by
  have h_step : evBefore (gSimWorld groups actTick groupOrd withinOrd pos
      (t_r + 1)).events x y :=
    evBefore_survivor_before_spawn groups actTick groupOrd withinOrd pos t_r
      h_valid x y h_x h_x_nd h_y_next h_y_not
  exact evBefore_gSimWorld_const groups actTick groupOrd withinOrd pos
    (t_r + 1) τ x y h_le h_step h_bx h_by
