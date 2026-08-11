import BasicProofs.GroupClustering.LogShape
import BasicProofs.GroupClustering.QSideOrderDischarged
import BasicProofs.GroupClustering.Stage0BaseOrder
import BasicProofs.GroupClustering.SuccessorSurvival

open BasicRedstoneSim List

/-! # Group clustering — simulation-level facts for capstone assembly

This file proves the simulation-level facts needed to discharge
the remaining hypotheses of QSideOrderDischarged and LogShape.
-/

/-! ## Survival across one tick -/

/-- A non-due event in the tick-start queue survives to the
    next tick-start queue. -/
theorem mem_gSimWorld_succ_of_notDue
    (groups : List GroupSpec) (actTick : Nat → Nat)
    (groupOrd : List Nat) (withinOrd pos : Nat → List Nat)
    (t : Nat) (ev : ScheduledEvent)
    (h_mem : ev ∈ (gSimWorld groups actTick groupOrd withinOrd pos t).events)
    (h_notDue : ev.targetTick ≠ t)
    (h_valid : ∀ gi (c : ChainSpec), gi < groups.length →
        c ∈ groupAt groups gi →
        (∀ d ∈ c.middleDelays, ValidDelay d) ∧ ValidDelay c.lastDelay) :
    ev ∈ (gSimWorld groups actTick groupOrd withinOrd pos (t + 1)).events := by
  set W := gSimWorld groups actTick groupOrd withinOrd pos t with hW
  have h_succ : gSimWorld groups actTick groupOrd withinOrd pos (t + 1) =
      gSimBody actTick (buildGroups groups).2 groupOrd withinOrd pos W t := by
    dsimp [gSimWorld, W]
    set obsAll := (buildGroups groups).2
    set w₀ := (buildGroups groups).1
    simp only [gSimFoldl, List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil]
  rw [h_succ]
  have h_tick_W : W.tick = t := by
    show (gSimWorld groups actTick groupOrd withinOrd pos t).tick = t
    dsimp [gSimWorld]
    rw [gSimFoldl_tick, buildGroups_tick]
    omega
  have h_notDue_W : ev.targetTick ≠ W.tick := by rwa [h_tick_W]
  have h_delay_W : ∀ nid nd, W.getNode nid = some nd → ∀ d p,
      nd.kind = .repeater d p → d ≥ 2 :=
    gSimWorld_delay_ge2 groups actTick groupOrd withinOrd pos t h_valid
  have h_mem_log : ev ∈ (W.logOutput s!"tick {t}").events := by
    simpa [W] using h_mem
  have h_notDue_log : ev.targetTick ≠ (W.logOutput s!"tick {t}").tick := by
    simpa [W] using h_notDue_W
  have h_delay_log : ∀ nid nd, (W.logOutput s!"tick {t}").getNode nid =
      some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
    intro nid nd h_nd d p h_kind
    have h_nd_W : W.getNode nid = some nd := by
      rwa [World.logOutput_getNode] at h_nd
    exact h_delay_W nid nd h_nd_W d p h_kind
  unfold gSimBody
  dsimp
  simp only [h_tick_W]
  split_ifs with h_active
  · -- active == []: just stepUNT
    exact mem_stepUNT_of_notDue _ ev h_mem_log h_notDue_log h_delay_log
  · -- active ≠ []: gSimBurst then stepUNT
    set W_B := gSimBurst t (buildGroups groups).2 withinOrd pos
      (W.logOutput s!"tick {t}")
      ((groupOrd.filter (fun gi =>
        decide (gi < (buildGroups groups).2.length) &&
        (actTick gi == t))).zipIdx) with hW_B
    have h_mem_burst : ev ∈ W_B.events :=
      mem_gSimBurst_of_notDue t (buildGroups groups).2 withinOrd pos
        (W.logOutput s!"tick {t}")
        ((groupOrd.filter (fun gi =>
          decide (gi < (buildGroups groups).2.length) &&
          (actTick gi == t))).zipIdx) ev h_mem_log h_notDue_log
    have h_delay_burst : ∀ nid nd, W_B.getNode nid = some nd →
        ∀ d p, nd.kind = .repeater d p → d ≥ 2 :=
      gSimBurst_delay_preserved t (buildGroups groups).2 withinOrd pos
        (W.logOutput s!"tick {t}")
        ((groupOrd.filter (fun gi =>
          decide (gi < (buildGroups groups).2.length) &&
          (actTick gi == t))).zipIdx) h_delay_log
    exact mem_stepUNT_of_notDue _ ev h_mem_burst (by
      show ev.targetTick ≠ W_B.tick
      rw [gSimBurst_tick]
      exact h_notDue_log) h_delay_burst

/-! ## Survival across multiple ticks -/

/-- A non-due event survives across multiple ticks: if ev is in
    gSimWorld(a) and targets tick b > a, then ev is in
    gSimWorld(t) for all t with a ≤ t ≤ b. -/
theorem mem_gSimWorld_of_notDue_range
    (groups : List GroupSpec) (actTick : Nat → Nat)
    (groupOrd : List Nat) (withinOrd pos : Nat → List Nat)
    (a b : Nat) (ev : ScheduledEvent)
    (h_mem : ev ∈ (gSimWorld groups actTick groupOrd withinOrd pos a).events)
    (h_target : ev.targetTick = b)
    (h_ab : a ≤ b)
    (h_valid : ∀ gi (c : ChainSpec), gi < groups.length →
        c ∈ groupAt groups gi →
        (∀ d ∈ c.middleDelays, ValidDelay d) ∧ ValidDelay c.lastDelay) :
    ∀ t, a ≤ t → t ≤ b →
      ev ∈ (gSimWorld groups actTick groupOrd withinOrd pos t).events := by
  intro t h_at h_tb
  induction t with
  | zero =>
    have h_a0 : a = 0 := by omega
    subst h_a0
    exact h_mem
  | succ t ih =>
    by_cases h_ta : t < a
    · -- t < a, but a ≤ t+1, so a = t+1
      have h_a_eq : a = t + 1 := by omega
      subst h_a_eq
      exact h_mem
    · -- a ≤ t
      have h_t_le_b : t ≤ b := by omega
      have h_ih := ih (by omega) h_t_le_b
      -- ev is non-due at tick t since t < b (from t+1 ≤ b)
      have h_notDue : ev.targetTick ≠ t := by
        rw [h_target]
        omega
      exact mem_gSimWorld_succ_of_notDue groups actTick groupOrd withinOrd pos
        t ev h_ih h_notDue h_valid

/-! ## Reference events are in the pop-tick queue -/

/-- The stage-0 event is in the pop-tick queue. Uses Stage0BaseOrder's
    sameSpec_stage_evBefore_base with a second chain, then extracts
    membership via evBefore.mem_left. -/
theorem stageEvent0_mem_popQueueWorld
    (groups : List GroupSpec) (actTick : Nat → Nat)
    (groupOrd : List Nat) (withinOrd pos : Nat → List Nat)
    (g₁ c₁ g₂ c₂ : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_c₁_in : c₁ ∈ withinOrd g₁) (h_c₂_in : c₂ ∈ withinOrd g₂)
    (h_act_eq : actTick g₁ = actTick g₂)
    (h_burst : ∃ pre mid post,
        groupOrd.filter (fun gi =>
            decide (gi < (buildGroups groups).2.length) &&
            (actTick gi == actTick g₁)) =
        pre ++ g₁ :: mid ++ g₂ :: post) :
    stageEvent actTick groups g₁ c₁ 0 ∈
      (popQueueWorld groups actTick groupOrd withinOrd pos g₁ c₁ 0).events := by
  -- Stage0BaseOrder gives evBefore, which implies membership
  have h_evBefore := sameSpec_stage_evBefore_base groups actTick groupOrd
    withinOrd pos g₁ c₁ g₂ c₂ h_g₁ h_c₁ h_g₂ h_c₂ h_c₁_in h_c₂_in
    h_act_eq h_burst
  exact evBefore.mem_left h_evBefore

/-! ## Full h_mem by induction on stages

The full h_mem proof uses QSideOrderDischarged's sameSpec_stage_evBefore_ind_succ
which gives evBefore at popQueueWorld(j) for same-spec chains.
evBefore implies membership via evBefore.mem_left.
-/

/-- The stage-j event of a same-spec chain pair is in the
    pop-tick queue. Uses QSideOrderDischarged's induction which gives evBefore,
    then extracts membership. -/
theorem stageEvent_mem_popQueueWorld_ind
    (groups : List GroupSpec) (actTick : Nat → Nat)
    (groupOrd : List Nat) (withinOrd pos : Nat → List Nat)
    (g₁ c₁ g₂ c₂ j : Nat)
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
    stageEvent actTick groups g₁ c₁ j ∈
      (popQueueWorld groups actTick groupOrd withinOrd pos g₁ c₁ j).events := by
  -- QSideOrderDischarged gives evBefore, which implies membership
  have h_evBefore := sameSpec_stage_evBefore_ind_succ groups actTick groupOrd
    withinOrd pos g₁ c₁ g₂ c₂ j h_g₁ h_c₁ h_g₂ h_c₂ h_spec h_act_eq h_j
    h_base h_layout h_nodup h_surv
  exact evBefore.mem_left h_evBefore
