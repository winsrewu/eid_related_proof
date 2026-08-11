import BasicProofs.GroupClustering.StageEventCompleteness

open BasicRedstoneSim List

/-! # Group clustering — unconditional successor membership range

The stage-`(j + 1)` event of a valid chain spawns when the stage-`j`
event is popped at `stageTarget j`. The pop happens either during the
burst phase (`processNEvents` steps, handled by SuccessorSurvival) or during the
drain step (`mem_stepUNT_of_due_spawn`). In either case the successor
is present in the tick-`(stageTarget j + 1)` queue, and being non-due
it survives to its own target tick (SimulationLevelFacts). This extracts the
successor case of StageEventCompleteness's completeness proof as a public range lemma;
it supplies the `hA_mem` / `hD_mem` premises of the stage-`1` base case
(Stage1BaseCase) without needing to know whether the burst popped the parent. -/

/-! ## Private helpers (reproven from StageEventCompleteness, where they are private) -/

/-- `NodeLayoutOk` holds at every tick-start world. -/
private theorem NodeLayoutOk_gSimWorld (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (t : Nat) :
    NodeLayoutOk groups
      (gSimWorld groups actTick groupOrd withinOrd pos t) := by
  dsimp [gSimWorld]
  exact NodeLayoutOk_gSimFoldl groups actTick (buildGroups groups).2 groupOrd
    withinOrd pos (buildGroups groups).1 t (NodeLayoutOk_buildGroups groups)

/-- One tick after tick `t`, the queue equals the queue after the drain
    step of the post-burst world at tick `t`. -/
private theorem gSimWorld_succ_events_eq_burst (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (t : Nat) :
    (gSimWorld groups actTick groupOrd withinOrd pos (t + 1)).events =
    (gSimBurst t (buildGroups groups).2 withinOrd pos
        ((gSimWorld groups actTick groupOrd withinOrd pos t).logOutput
          s!"tick {t}")
        ((groupOrd.filter (fun gi =>
          decide (gi < (buildGroups groups).2.length) &&
          (actTick gi == t))).zipIdx)).stepUntilNextTick.events := by
  dsimp [gSimWorld]
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

/-- The delay ≥ 2 invariant survives the log step and the burst phase
    of a tick whose tick-start world satisfies it. -/
private theorem delay_ge2_burst (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (t : Nat)
    (h_valid : ∀ gi (c : ChainSpec), gi < groups.length →
        c ∈ groupAt groups gi →
        (∀ d ∈ c.middleDelays, ValidDelay d) ∧ ValidDelay c.lastDelay) :
    ∀ nid nd,
      (gSimBurst t (buildGroups groups).2 withinOrd pos
          ((gSimWorld groups actTick groupOrd withinOrd pos t).logOutput
            s!"tick {t}")
          ((groupOrd.filter (fun gi =>
            decide (gi < (buildGroups groups).2.length) &&
            (actTick gi == t))).zipIdx)).getNode nid = some nd →
      ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
  apply gSimBurst_delay_preserved t (buildGroups groups).2 withinOrd pos
    ((gSimWorld groups actTick groupOrd withinOrd pos t).logOutput
      s!"tick {t}")
    ((groupOrd.filter (fun gi =>
      decide (gi < (buildGroups groups).2.length) &&
      (actTick gi == t))).zipIdx)
  intro nid nd h_nd d p h_kind
  have h_nd' : (gSimWorld groups actTick groupOrd withinOrd pos t).getNode
      nid = some nd := by
    rwa [World.logOutput_getNode] at h_nd
  exact gSimWorld_delay_ge2 groups actTick groupOrd withinOrd pos t h_valid
    nid nd h_nd' d p h_kind

/-! ## The range lemma -/

/-- The stage-`(j + 1)` event of a valid chain sits in every tick-start
    queue from the tick after its spawn (`stageTarget j + 1`) until its
    own target tick `stageTarget (j + 1)` (inclusive). -/
theorem stageEvent_succ_mem_range_complete (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat)
    (h_valid : ∀ gi (c : ChainSpec), gi < groups.length →
        c ∈ groupAt groups gi →
        (∀ d ∈ c.middleDelays, ValidDelay d) ∧ ValidDelay c.lastDelay)
    (h_ord : List.Perm groupOrd (List.range groups.length))
    (h_within : ∀ gi, gi < groups.length →
        List.Perm (withinOrd gi) (List.range (groupAt groups gi).length))
    (gi ci j : Nat)
    (h_gi : gi < groups.length) (h_ci : ci < (groupAt groups gi).length)
    (h_j : j ≤ (chainAt groups gi ci).middleDelays.length)
    (t : Nat)
    (h_lo : stageTarget actTick groups gi ci j + 1 ≤ t)
    (h_hi : t ≤ stageTarget actTick groups gi ci (j + 1)) :
    stageEvent actTick groups gi ci (j + 1) ∈
      (gSimWorld groups actTick groupOrd withinOrd pos t).events := by
  set τ := stageTarget actTick groups gi ci j
  set W : World := gSimWorld groups actTick groupOrd withinOrd pos τ
  set active : List Nat := groupOrd.filter (fun gi' =>
    decide (gi' < (buildGroups groups).2.length) && (actTick gi' == τ))
  set W₁ : World := W.logOutput s!"tick {τ}"
  set W_B : World := gSimBurst τ (buildGroups groups).2 withinOrd pos W₁
    (active.zipIdx)
  set e : ScheduledEvent := stageEvent actTick groups gi ci j
  set s : ScheduledEvent := stageEvent actTick groups gi ci (j + 1)
  -- completeness (StageEventCompleteness): e sits in the tick-τ queue
  have h_e_W : e ∈ W.events :=
    stageEvent_mem_gSimWorld groups actTick groupOrd withinOrd pos h_valid
      h_ord h_within gi ci h_gi h_ci j (by omega)
  -- tick bookkeeping
  have h_tick_W : W.tick = τ :=
    gSimWorld_tick groups actTick groupOrd withinOrd pos τ
  have h_tick_W₁ : W₁.tick = τ := by
    dsimp only [W₁]
    rw [World.logOutput_tick, h_tick_W]
  have h_tick_WB : W_B.tick = τ := by
    dsimp only [W_B]
    rw [gSimBurst_tick, h_tick_W₁]
  -- the drain result is the tick-(τ + 1) queue
  have h_succ_eq : (gSimWorld groups actTick groupOrd withinOrd pos
      (τ + 1)).events = W_B.stepUntilNextTick.events := by
    dsimp only [W_B, W₁, W]
    exact gSimWorld_succ_events_eq_burst groups actTick groupOrd withinOrd
      pos τ
  -- layout and delay health at the post-burst world
  have h_layout_WB : NodeLayoutOk groups W_B :=
    NodeLayoutOk_gSimBurst groups τ (buildGroups groups).2 withinOrd pos W₁
      (active.zipIdx)
      (NodeLayoutOk_logOutput groups W s!"tick {τ}"
        (NodeLayoutOk_gSimWorld groups actTick groupOrd withinOrd pos τ))
  have h_delay_WB : ∀ nid nd, W_B.getNode nid = some nd → ∀ d p,
      nd.kind = .repeater d p → d ≥ 2 := by
    dsimp only [W_B, W₁, W]
    exact delay_ge2_burst groups actTick groupOrd withinOrd pos τ h_valid
  -- e is due at the post-burst world; s is not
  have h_e_due : e.targetTick = W_B.tick := by
    dsimp only [e, stageEvent]
    rw [h_tick_WB]
  have h_s_nd : s.targetTick ≠ W_B.tick := by
    dsimp only [s, stageEvent]
    intro h_eq
    have h_lt := stageTarget_lt_succ actTick groups gi ci j h_j
    rw [h_eq, h_tick_WB] at h_lt
    omega
  -- the successor reaches the tick-(τ + 1) queue
  have h_s_sunt : s ∈ W_B.stepUntilNextTick.events := by
    by_cases h_e_B : e ∈ W_B.events
    · -- e survives the burst: the drain fires it and spawns s
      have h_spawn : ∀ (v : World), v.tick = W_B.tick →
          NodeLayoutOk groups v →
          (v.onScheduledTick e.nodeId).events = v.events ++ [s] := by
        intro v h_v h_lay
        have h_v_tick : v.tick = stageTarget actTick groups gi ci j := by
          rw [h_v, h_tick_WB]
        simpa [e, s, stageEvent] using
          stage_spawn groups actTick v gi ci j h_gi h_ci h_j h_v_tick h_lay
      exact mem_stepUNT_of_due_spawn groups W_B e s h_layout_WB h_delay_WB
        h_e_B h_e_due h_s_nd h_spawn
    · -- the burst pops e: SuccessorSurvival puts s in the post-burst queue
      have h_s_B : s ∈ W_B.events := by
        change stageEvent actTick groups gi ci (j + 1) ∈
          (preStepWorld groups actTick groupOrd withinOrd pos gi ci j).events
        exact stageEvent_succ_mem_preStepWorld groups actTick groupOrd
          withinOrd pos gi ci j h_gi h_ci h_j h_e_W h_e_B
      exact mem_stepUNT_of_notDue W_B s h_s_B h_s_nd h_delay_WB
  have h_s_t1 : s ∈
      (gSimWorld groups actTick groupOrd withinOrd pos (τ + 1)).events := by
    rw [h_succ_eq]
    exact h_s_sunt
  -- carry from tick τ + 1 to t
  have h_ab : τ + 1 ≤ stageTarget actTick groups gi ci (j + 1) :=
    Nat.succ_le_of_lt (stageTarget_lt_succ actTick groups gi ci j h_j)
  exact mem_gSimWorld_of_notDue_range groups actTick groupOrd withinOrd pos
    (τ + 1) (stageTarget actTick groups gi ci (j + 1)) s h_s_t1 rfl h_ab
    h_valid t h_lo h_hi
