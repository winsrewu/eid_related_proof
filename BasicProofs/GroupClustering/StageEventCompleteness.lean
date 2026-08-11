import BasicProofs.GroupClustering.SimulationLevelFacts

open BasicRedstoneSim List

/-! # Group clustering — capstone completeness of stage events

Chains fire stage by stage: the stage-`j` event targets
`stageTarget j`, and firing it spawns the stage-`(j + 1)` event
(`stage_spawn`). In the capstone setup, every group `gi` activates at
`actTick gi` (its observer events — the stage-0 events — are enqueued
during the burst of tick `actTick gi`), and the hypotheses `h_act` and
`h_uniform` force every chain's final stage
(`j = middleDelays.length + 1`) to target the common output tick `T`.

This file proves:

* `mem_stepUNT_of_due_spawn` — a general drain-spawn membership fact:
  a due event whose firing appends exactly `s` (non-due) puts `s` into
  the drained queue;
* `stageTarget_final_eq_T` — every chain's final stage targets `T`;
* `stageEvent_mem_gSimWorld` — COMPLETENESS: for every valid chain
  `(gi, ci)` and every `j ≤ middleDelays.length + 1`, the stage-`j`
  event sits in the queue at its target tick;
* `due_events_at_T_are_final` — the due events of the tick-`T` queue
  are exactly the final-stage events.
-/

/-! ## Private helpers -/

/-- `NodeLayoutOk` holds at every tick-start world. Reproved here
    because the QSideOrder/SuccessorSurvival versions are private. -/
private theorem NodeLayoutOk_gSimWorld (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (t : Nat) :
    NodeLayoutOk groups
      (gSimWorld groups actTick groupOrd withinOrd pos t) := by
  dsimp [gSimWorld]
  exact NodeLayoutOk_gSimFoldl groups actTick (buildGroups groups).2 groupOrd
    withinOrd pos (buildGroups groups).1 t (NodeLayoutOk_buildGroups groups)

/-- One tick after tick `t`, the queue equals the queue after the drain
    step of the post-burst world at tick `t`. The active branch of
    `gSimBody` is the burst followed by the drain; when no group is
    active the burst over no pair is the identity. Adapted from
    QSideOrderDischarged's private `gSimWorld_succ_events_eq_preStep`. -/
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
  · -- the active list is empty: the burst phase folds over no pair
    have h_act_nil : groupOrd.filter (fun gi =>
        decide (gi < (buildGroups groups).2.length) && (actTick gi == t)) = [] := by
      simpa using h_active
    rw [h_act_nil]
    simp [gSimBurst]
  · rfl

/-- Stage targets grow strictly with the stage index while the larger
    index stays in range. Iterates `stageTarget_lt_succ`. -/
private theorem stageTarget_strictMono_of_lt (actTick : Nat → Nat)
    (groups : List GroupSpec) (gi ci j k : Nat)
    (h_jk : j < k)
    (h_k : k ≤ (chainAt groups gi ci).middleDelays.length + 1) :
    stageTarget actTick groups gi ci j <
      stageTarget actTick groups gi ci k := by
  induction k generalizing j with
  | zero => omega
  | succ k' ih =>
    have h_k'_le : k' ≤ (chainAt groups gi ci).middleDelays.length := by
      omega
    by_cases h_eq : j = k'
    · rw [h_eq]
      exact stageTarget_lt_succ actTick groups gi ci k' h_k'_le
    · have h_jk' : j < k' := by omega
      exact Nat.lt_trans (ih j h_jk' (by omega))
        (stageTarget_lt_succ actTick groups gi ci k' h_k'_le)

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

/-! ## A general drain-spawn membership fact -/

/-- When a due event `e` is present in the queue and firing `e` appends
    exactly the non-due event `s` (in every reachable world of the
    current tick with a good layout), then `s` survives the whole drain
    of the tick. The proof follows the drain by induction: either `e`
    itself is popped (then `s` appears and is non-due for the rest of
    the tick), or another event is popped (then `e` stays due and the
    induction continues). -/
theorem mem_stepUNT_of_due_spawn (groups : List GroupSpec) (w : World)
    (e s : ScheduledEvent)
    (h_layout : NodeLayoutOk groups w)
    (h_delay : ∀ nid nd, w.getNode nid = some nd → ∀ d p,
        nd.kind = .repeater d p → d ≥ 2)
    (h_mem : e ∈ w.events) (h_due : e.targetTick = w.tick)
    (h_s_nd : s.targetTick ≠ w.tick)
    (h_spawn : ∀ (v : World), v.tick = w.tick → NodeLayoutOk groups v →
        (v.onScheduledTick e.nodeId).events = v.events ++ [s]) :
    s ∈ w.stepUntilNextTick.events := by
  induction w using World.stepUntilNextTick.induct with
  | case1 x h_step =>
    -- no pop possible, but e is due and present
    dsimp [World.step] at h_step
    cases h_pop : x.popNextEvent with
    | none =>
      exact False.elim (popNextEvent_none_no_events x h_pop e h_mem h_due)
    | some p =>
      simp only [h_pop] at h_step
      cases h_step
  | case2 x w' h_step ih =>
    have h_layout_w' : NodeLayoutOk groups w' :=
      NodeLayoutOk_step groups x w' h_step h_layout
    have h_delay_w' : ∀ nid nd, w'.getNode nid = some nd → ∀ d p,
        nd.kind = .repeater d p → d ≥ 2 :=
      step_delay_preserved x w' h_step h_delay
    have h_sunt : x.stepUntilNextTick = w'.stepUntilNextTick := by
      rw [World.stepUntilNextTick, h_step]
    dsimp [World.step] at h_step
    cases h_pop : x.popNextEvent with
    | none =>
      simp only [h_pop] at h_step
      cases h_step
    | some p =>
      rcases p with ⟨ev₀, w_pop⟩
      simp only [h_pop] at h_step
      injection h_step with h_w'
      obtain ⟨idx, h_idx, h_erase, h_tick_ev, _, h_get_idx⟩ :=
        World.popNextEvent_eraseIdx x ev₀ w_pop h_pop
      have h_tick_pop : w_pop.tick = x.tick :=
        World.popNextEvent_tick x ev₀ w_pop h_pop
      have h_layout_pop : NodeLayoutOk groups w_pop :=
        NodeLayoutOk_of_nodes_eq groups x w_pop
          (World.popNextEvent_nodes x ev₀ w_pop h_pop) h_layout
      have h_tick_w' : w'.tick = x.tick := by
        rw [← h_w', World.onScheduledTick_tick, h_tick_pop]
      by_cases h_ev_e : ev₀ = e
      · -- the popped event is e itself: s is appended now and survives
        -- the rest of the drain as a non-due event
        have h_w'_events : w'.events = w_pop.events ++ [s] := by
          rw [← h_w', h_ev_e]
          exact h_spawn w_pop h_tick_pop h_layout_pop
        have h_s_w' : s ∈ w'.events := by
          rw [h_w'_events]
          exact List.mem_append_right _ (by simp)
        have h_s_nd_w' : s.targetTick ≠ w'.tick := by
          rw [h_tick_w']
          exact h_s_nd
        have h_s_sunt : s ∈ w'.stepUntilNextTick.events :=
          mem_stepUNT_of_notDue w' s h_s_w' h_s_nd_w' h_delay_w'
        rwa [h_sunt]
      · -- another event is popped: e survives the pop and the firing
        have h_e_pop : e ∈ w_pop.events := by
          rw [h_erase]
          exact mem_eraseIdx_of_ne x.events idx h_idx ev₀ e h_get_idx h_mem
            (Ne.symm h_ev_e)
        obtain ⟨new₀, h_app_new, _⟩ :=
          World.onScheduledTick_appends_future w_pop ev₀.nodeId
        have h_e_w' : e ∈ w'.events := by
          rw [← h_w', h_app_new]
          exact List.mem_append_left _ h_e_pop
        have h_due_w' : e.targetTick = w'.tick := by
          rw [h_tick_w']
          exact h_due
        have h_s_nd_w' : s.targetTick ≠ w'.tick := by
          rw [h_tick_w']
          exact h_s_nd
        have h_spawn_w' : ∀ (v : World), v.tick = w'.tick →
            NodeLayoutOk groups v →
            (v.onScheduledTick e.nodeId).events = v.events ++ [s] :=
          fun v h_v => h_spawn v (h_v.trans h_tick_w')
        have h_ih := ih h_layout_w' h_delay_w' h_e_w' h_due_w' h_s_nd_w'
          h_spawn_w'
        rwa [h_sunt]

/-! ## The final stage targets the common output tick -/

/-- Under the uniformity and activation hypotheses, the final stage of
    every valid chain targets the common output tick `T`. -/
theorem stageTarget_final_eq_T (groups : List GroupSpec)
    (actTick : Nat → Nat)
    (T gi ci : Nat)
    (h_gi : gi < groups.length) (h_ci : ci < (groupAt groups gi).length)
    (h_uniform : ∀ gi (c₁ c₂ : ChainSpec), gi < groups.length →
        c₁ ∈ groupAt groups gi → c₂ ∈ groupAt groups gi →
        chainDelay c₁ = chainDelay c₂)
    (h_act : ∀ gi, gi < groups.length → groupAt groups gi ≠ [] →
        actTick gi + groupDelay (groupAt groups gi) = T) :
    stageTarget actTick groups gi ci
        ((chainAt groups gi ci).middleDelays.length + 1) = T := by
  have h_c_mem : chainAt groups gi ci ∈ groupAt groups gi :=
    chainAt_mem groups gi ci h_ci
  have h_ne : groupAt groups gi ≠ [] := by
    intro h_nil
    rw [h_nil] at h_ci
    cases h_ci
  -- the group is nonempty, so its chain at index 0 is valid
  have h₀ : 0 < (groupAt groups gi).length := by omega
  -- the group delay is the head chain delay, which by uniformity is
  -- the delay of every chain of the group
  have h_gd : groupDelay (groupAt groups gi) =
      chainDelay (chainAt groups gi 0) := by
    dsimp only [groupDelay, chainAt]
    cases h_g : groupAt groups gi with
    | nil => rw [h_g] at h₀; cases h₀
    | cons c cs => simp
  have h_chain_eq : chainDelay (chainAt groups gi ci) =
      chainDelay (chainAt groups gi 0) :=
    (h_uniform gi (chainAt groups gi 0) (chainAt groups gi ci) h_gi
      (chainAt_mem groups gi 0 h₀) h_c_mem).symm
  rw [stageTarget_last actTick groups gi ci, h_chain_eq, ← h_gd]
  exact h_act gi h_gi h_ne

/-! ## Completeness: every stage event arrives -/

/-- COMPLETENESS. For every valid chain `(gi, ci)` and every stage
    `j ≤ middleDelays.length + 1`, the stage-`j` event sits in the
    queue at its target tick. Induction on the stage: the stage-0
    event is enqueued by the activation burst of tick `actTick gi`
    (Stage0BaseOrder); a stage-`(k + 1)` event either spawns when the burst
    drains the stage-`k` event (`mem_stepUNT_of_due_spawn`) or already
    sits in the post-burst queue because the burst popped the stage-`k`
    event during its `processNEvents` steps (SuccessorSurvival). Non-due events
    then survive to the stage's target tick (SimulationLevelFacts). -/
theorem stageEvent_mem_gSimWorld (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat)
    (h_valid : ∀ gi (c : ChainSpec), gi < groups.length →
        c ∈ groupAt groups gi →
        (∀ d ∈ c.middleDelays, ValidDelay d) ∧ ValidDelay c.lastDelay)
    (h_ord : List.Perm groupOrd (List.range groups.length))
    (h_within : ∀ gi, gi < groups.length →
        List.Perm (withinOrd gi) (List.range (groupAt groups gi).length))
    (gi ci : Nat)
    (h_gi : gi < groups.length) (h_ci : ci < (groupAt groups gi).length) :
    ∀ j, j ≤ (chainAt groups gi ci).middleDelays.length + 1 →
      stageEvent actTick groups gi ci j ∈
        (gSimWorld groups actTick groupOrd withinOrd pos
          (stageTarget actTick groups gi ci j)).events := by
  intro j
  induction j with
  | zero =>
    intro _
    set t₀ := actTick gi
    set W₀ : World := gSimWorld groups actTick groupOrd withinOrd pos t₀
    set active : List Nat := groupOrd.filter (fun gi' =>
      decide (gi' < (buildGroups groups).2.length) && (actTick gi' == t₀))
    set W₁ : World := W₀.logOutput s!"tick {t₀}"
    set W_B : World := gSimBurst t₀ (buildGroups groups).2 withinOrd pos W₁
      (active.zipIdx)
    -- gi is in the activation list of tick t₀
    have h_gi_ord : gi ∈ groupOrd :=
      (List.Perm.mem_iff h_ord (a := gi)).mpr (List.mem_range.mpr h_gi)
    have h_gi_active : gi ∈ active := by
      dsimp [active]
      rw [List.mem_filter]
      refine ⟨h_gi_ord, ?_⟩
      have h_dec : decide (gi < (buildGroups groups).2.length) = true := by
        rw [buildGroups_snd_length, decide_eq_true_eq]
        exact h_gi
      rw [h_dec]
      simp
      rfl
    -- the (gi, k) pair appears in active.zipIdx
    obtain ⟨k, hk_lt, hk_eq⟩ := List.mem_iff_getElem.mp h_gi_active
    have h_pair : (gi, k) ∈ active.zipIdx := by
      have h_len : k < active.zipIdx.length := by
        simp [List.length_zipIdx, hk_lt]
      have h_elem : active.zipIdx[k] = (gi, k) := by
        rw [List.getElem_zipIdx (by simp [List.length_zipIdx, hk_lt])]
        simp [hk_eq]
      rw [← h_elem]
      exact List.getElem_mem h_len
    -- ci is in the withinOrd list
    have h_ci_in : ci ∈ withinOrd gi :=
      (List.Perm.mem_iff (h_within gi h_gi) (a := ci)).mpr
        (List.mem_range.mpr h_ci)
    -- the stage-0 event is enqueued by the burst
    have h_tick_W₁ : W₁.tick = t₀ := by
      dsimp only [W₁, W₀]
      rw [World.logOutput_tick, gSimWorld_tick]
    have h_e_B : stageEvent actTick groups gi ci 0 ∈ W_B.events :=
      stageEvent0_mem_burst t₀ withinOrd pos W₁ (active.zipIdx) gi k
        actTick groups ci h_tick_W₁ rfl h_gi h_ci h_ci_in h_pair
    -- it is non-due at tick t₀, so it survives the drain
    have h_tick_WB : W_B.tick = t₀ := by
      dsimp only [W_B]
      rw [gSimBurst_tick, h_tick_W₁]
    have h_nd : (stageEvent actTick groups gi ci 0).targetTick ≠ W_B.tick := by
      dsimp only [stageEvent]
      rw [stageTarget_zero_eq, h_tick_WB]
      omega
    have h_delay_WB : ∀ nid nd, W_B.getNode nid = some nd → ∀ d p,
        nd.kind = .repeater d p → d ≥ 2 := by
      dsimp only [W_B, W₁, W₀]
      exact delay_ge2_burst groups actTick groupOrd withinOrd pos t₀ h_valid
    have h_e_sunt : stageEvent actTick groups gi ci 0 ∈
        W_B.stepUntilNextTick.events :=
      mem_stepUNT_of_notDue W_B (stageEvent actTick groups gi ci 0) h_e_B
        h_nd h_delay_WB
    -- the drain result is the tick-(t₀ + 1) queue
    have h_mem_t1 : stageEvent actTick groups gi ci 0 ∈
        (gSimWorld groups actTick groupOrd withinOrd pos (t₀ + 1)).events := by
      rw [show (gSimWorld groups actTick groupOrd withinOrd pos
            (t₀ + 1)).events = W_B.stepUntilNextTick.events from by
        dsimp only [W_B, W₁, W₀]
        exact gSimWorld_succ_events_eq_burst groups actTick groupOrd
          withinOrd pos t₀]
      exact h_e_sunt
    -- carry from tick t₀ + 1 to the target tick t₀ + 2
    show stageEvent actTick groups gi ci 0 ∈
      (gSimWorld groups actTick groupOrd withinOrd pos
        (stageTarget actTick groups gi ci 0)).events
    exact mem_gSimWorld_of_notDue_range groups actTick groupOrd withinOrd pos
      (t₀ + 1) (t₀ + 2) (stageEvent actTick groups gi ci 0) h_mem_t1
      (by dsimp only [stageEvent]; rw [stageTarget_zero_eq]) (by omega)
      h_valid (t₀ + 2) (by omega) (by omega)
  | succ k ih =>
    intro h_j
    have h_k : k ≤ (chainAt groups gi ci).middleDelays.length := by omega
    set t := stageTarget actTick groups gi ci k
    set W : World := gSimWorld groups actTick groupOrd withinOrd pos t
    set active : List Nat := groupOrd.filter (fun gi' =>
      decide (gi' < (buildGroups groups).2.length) && (actTick gi' == t))
    set W₁ : World := W.logOutput s!"tick {t}"
    set W_B : World := gSimBurst t (buildGroups groups).2 withinOrd pos W₁
      (active.zipIdx)
    set e : ScheduledEvent := stageEvent actTick groups gi ci k
    set s : ScheduledEvent := stageEvent actTick groups gi ci (k + 1)
    -- the induction hypothesis: e sits in the tick-t queue
    have h_e_W : e ∈ W.events := by
      dsimp only [e]
      exact ih (by omega)
    -- tick bookkeeping
    have h_tick_W : W.tick = t :=
      gSimWorld_tick groups actTick groupOrd withinOrd pos t
    have h_tick_W₁ : W₁.tick = t := by
      dsimp only [W₁]
      rw [World.logOutput_tick, h_tick_W]
    have h_tick_WB : W_B.tick = t := by
      dsimp only [W_B]
      rw [gSimBurst_tick, h_tick_W₁]
    -- the drain result is the tick-(t + 1) queue
    have h_succ_eq : (gSimWorld groups actTick groupOrd withinOrd pos
        (t + 1)).events = W_B.stepUntilNextTick.events := by
      dsimp only [W_B, W₁, W]
      exact gSimWorld_succ_events_eq_burst groups actTick groupOrd withinOrd
        pos t
    -- layout and delay health at the post-burst world
    have h_layout_WB : NodeLayoutOk groups W_B :=
      NodeLayoutOk_gSimBurst groups t (buildGroups groups).2 withinOrd pos W₁
        (active.zipIdx)
        (NodeLayoutOk_logOutput groups W s!"tick {t}"
          (NodeLayoutOk_gSimWorld groups actTick groupOrd withinOrd pos t))
    have h_delay_WB : ∀ nid nd, W_B.getNode nid = some nd → ∀ d p,
        nd.kind = .repeater d p → d ≥ 2 := by
      dsimp only [W_B, W₁, W]
      exact delay_ge2_burst groups actTick groupOrd withinOrd pos t h_valid
    -- e is due at the post-burst world; s is not
    have h_e_due : e.targetTick = W_B.tick := by
      dsimp only [e, stageEvent]
      rw [h_tick_WB]
    have h_s_nd : s.targetTick ≠ W_B.tick := by
      dsimp only [s, stageEvent]
      intro h_eq
      have h_lt := stageTarget_lt_succ actTick groups gi ci k h_k
      rw [h_eq, h_tick_WB] at h_lt
      omega
    -- the successor reaches the tick-(t + 1) queue
    have h_s_sunt : s ∈ W_B.stepUntilNextTick.events := by
      by_cases h_e_B : e ∈ W_B.events
      · -- e survives the burst: the drain fires it and spawns s
        have h_spawn : ∀ (v : World), v.tick = W_B.tick →
            NodeLayoutOk groups v →
            (v.onScheduledTick e.nodeId).events = v.events ++ [s] := by
          intro v h_v h_lay
          have h_v_tick : v.tick = stageTarget actTick groups gi ci k := by
            rw [h_v, h_tick_WB]
          simpa [e, s, stageEvent] using
            stage_spawn groups actTick v gi ci k h_gi h_ci h_k h_v_tick h_lay
        exact mem_stepUNT_of_due_spawn groups W_B e s h_layout_WB h_delay_WB
          h_e_B h_e_due h_s_nd h_spawn
      · -- the burst pops e: SuccessorSurvival puts s in the post-burst queue
        have h_s_B : s ∈ W_B.events := by
          change stageEvent actTick groups gi ci (k + 1) ∈
            (preStepWorld groups actTick groupOrd withinOrd pos gi ci k).events
          exact stageEvent_succ_mem_preStepWorld groups actTick groupOrd
            withinOrd pos gi ci k h_gi h_ci h_k h_e_W h_e_B
        exact mem_stepUNT_of_notDue W_B s h_s_B h_s_nd h_delay_WB
    have h_s_t1 : s ∈
        (gSimWorld groups actTick groupOrd withinOrd pos (t + 1)).events := by
      rw [h_succ_eq]
      exact h_s_sunt
    -- carry from tick t + 1 to the successor's target tick
    show s ∈ (gSimWorld groups actTick groupOrd withinOrd pos
        (stageTarget actTick groups gi ci (k + 1))).events
    have h_ab : t + 1 ≤ stageTarget actTick groups gi ci (k + 1) :=
      Nat.succ_le_of_lt (stageTarget_lt_succ actTick groups gi ci k h_k)
    exact mem_gSimWorld_of_notDue_range groups actTick groupOrd withinOrd pos
      (t + 1) (stageTarget actTick groups gi ci (k + 1)) s h_s_t1 rfl h_ab
      h_valid (stageTarget actTick groups gi ci (k + 1)) h_ab (Nat.le_refl _)

/-! ## The due events at the output tick -/

/-- At the common output tick `T`, the due events are exactly the
    final-stage events. QueueMembership characterizes every queued event as a
    stage event inside its stage window; `ev.targetTick = T` pins the
    stage target to `T`, which by `stageTarget_final_eq_T` and strict
    monotonicity of stage targets forces the stage to be the final
    one. -/
theorem due_events_at_T_are_final (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (T : Nat)
    (h_uniform : ∀ gi (c₁ c₂ : ChainSpec), gi < groups.length →
        c₁ ∈ groupAt groups gi → c₂ ∈ groupAt groups gi →
        chainDelay c₁ = chainDelay c₂)
    (h_act : ∀ gi, gi < groups.length → groupAt groups gi ≠ [] →
        actTick gi + groupDelay (groupAt groups gi) = T) :
    ∀ ev ∈ (gSimWorld groups actTick groupOrd withinOrd pos T).events,
      ev.targetTick = T →
      ∃ gi ci, gi < groups.length ∧ ci < (groupAt groups gi).length ∧
        ev = stageEvent actTick groups gi ci
          ((chainAt groups gi ci).middleDelays.length + 1) := by
  intro ev h_ev h_tgt
  obtain ⟨gi, ci, j, h_gi, h_ci, _, h_ev_eq, _⟩ :=
    gSimWorld_events_stageWindow groups actTick groupOrd withinOrd pos T ev
      h_ev
  have h_st : stageTarget actTick groups gi ci j = T := by
    rw [h_ev_eq] at h_tgt
    dsimp [stageEvent] at h_tgt
    exact h_tgt
  have h_final : stageTarget actTick groups gi ci
      ((chainAt groups gi ci).middleDelays.length + 1) = T :=
    stageTarget_final_eq_T groups actTick T gi ci h_gi h_ci h_uniform h_act
  refine ⟨gi, ci, h_gi, h_ci, ?_⟩
  by_cases h_jm : j = (chainAt groups gi ci).middleDelays.length + 1
  · subst h_jm
    exact h_ev_eq
  · have h_j_lt : j < (chainAt groups gi ci).middleDelays.length + 1 := by
      omega
    have h_lt : stageTarget actTick groups gi ci j <
        stageTarget actTick groups gi ci
          ((chainAt groups gi ci).middleDelays.length + 1) :=
      stageTarget_strictMono_of_lt actTick groups gi ci j
        ((chainAt groups gi ci).middleDelays.length + 1) h_j_lt (by omega)
    rw [h_st, h_final] at h_lt
    exact absurd h_lt (Nat.lt_irrefl T)
