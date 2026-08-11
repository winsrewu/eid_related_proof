import BasicProofs.GroupClustering.MiddleBlockOkStageInduction
import BasicProofs.GroupClustering.MiddleBlockOkActiveTick

open BasicRedstoneSim List

/-! # Group clustering — survival-free stage induction

The MiddleBlockOkStageInduction stage induction threads `MiddleBlockOk_gSimFoldl_stage_succ`,
whose body step consumes the survival of the stage-(j+1) reference events
through the burst. That survival is not provable in general: successors
may be spawned by the drain instead of the burst. This file repeats the
MiddleBlockOkStageInduction development with the survival-free body step of MiddleBlockOkActiveTick.

* `MiddleBlockOk_gSimBody_step_general` — idle/burst split without
  survival premises;
* `MiddleBlockOk_gSimFoldl_stage_succ_general` — one stage step;
* `MBStepSideGeneral` — per-stage side hypotheses (no survival fields);
* `MiddleBlockOk_gSimFoldl_stage_general` — the full stage induction.
-/

/-- The successor tick of `gSimWorld` equals one `gSimBody` step. -/
private theorem gSimWorld_succ_eq_body (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (t : Nat) :
    gSimWorld groups actTick groupOrd withinOrd pos (t + 1) =
    gSimBody actTick (buildGroups groups).2 groupOrd withinOrd pos
      (gSimWorld groups actTick groupOrd withinOrd pos t) t := by
  dsimp [gSimWorld]
  set obsAll := (buildGroups groups).2
  set w₀ := (buildGroups groups).1
  simp only [gSimFoldl, List.range_succ, List.foldl_append, List.foldl_cons,
    List.foldl_nil]

/-- MiddleBlockOk on the full event list implies MiddleBlockOk on the
    due-filter. Events between the reference events in the due-filter
    are also between them in the full list. -/
private theorem MiddleBlockOk_restrict_dueFilter
    (groups : List GroupSpec) (actTick : Nat → Nat) (T : Nat)
    (w : World) (g₁ c₁ g₂ c₂ j : Nat)
    (h_mb : MiddleBlockOk groups actTick T w.events g₁ c₁ g₂ c₂ j) :
    MiddleBlockOk groups actTick T
      (w.events.filter (fun e => e.targetTick == w.tick))
      g₁ c₁ g₂ c₂ j := by
  intro e h_b1 h_b2 h_pri h_tgt
  have h_b1_full : evBefore w.events
      (stageEvent actTick groups g₁ c₁ j) e :=
    evBefore.of_filter (fun ev => ev.targetTick == w.tick) h_b1
  have h_b2_full : evBefore w.events e
      (stageEvent actTick groups g₂ c₂ j) :=
    evBefore.of_filter (fun ev => ev.targetTick == w.tick) h_b2
  exact h_mb e h_b1_full h_b2_full h_pri h_tgt

/-- One `gSimBody` tick advances the middle-block invariant from stage
    `j` to stage `j + 1` at a pop tick, without survival premises.
    Splits on whether any group activates at the tick. -/
theorem MiddleBlockOk_gSimBody_step_general (groups : List GroupSpec)
    (actTick : Nat → Nat) (T : Nat)
    (obsAll : List (List Nat)) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat)
    (w : World) (i : Nat) (g₁ c₁ g₂ c₂ j : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_layout : NodeLayoutOk groups w)
    (h_j_ge : 1 ≤ j)
    (h_j₁ : j + 1 ≤ (chainAt groups g₁ c₁).middleDelays.length)
    (h_j₂ : j + 1 ≤ (chainAt groups g₂ c₂).middleDelays.length)
    (h_due : w.tick = stageTarget actTick groups g₁ c₁ j)
    (h_tgt₂ : stageTarget actTick groups g₂ c₂ j =
        stageTarget actTick groups g₁ c₁ j)
    (hA_mem : stageEvent actTick groups g₁ c₁ j ∈ w.events)
    (hD_mem : stageEvent actTick groups g₂ c₂ j ∈ w.events)
    (h_nodup : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup)
    (hAD : evBefore (w.events.filter (fun e => e.targetTick == w.tick))
        (stageEvent actTick groups g₁ c₁ j)
        (stageEvent actTick groups g₂ c₂ j))
    (h_mb : MiddleBlockOk groups actTick T
        (w.events.filter (fun e => e.targetTick == w.tick))
        g₁ c₁ g₂ c₂ j)
    (h_stage : StageMemAt groups actTick w w.tick)
    (h_sA_absent : stageEvent actTick groups g₁ c₁ (j + 1) ∉ w.events)
    (h_sD_absent : stageEvent actTick groups g₂ c₂ (j + 1) ∉ w.events)
    (h_nd_post :
        (gSimBody actTick obsAll groupOrd withinOrd pos w i).events.Nodup)
    (h_nd_burst :
      let w_log := w.logOutput s!"tick {w.tick}"
      let active := groupOrd.filter (fun gi =>
        decide (gi < obsAll.length) && (actTick gi == w.tick))
      (gSimBurst w.tick obsAll withinOrd pos w_log
        active.zipIdx).events.Nodup) :
    MiddleBlockOk groups actTick T
      (gSimBody actTick obsAll groupOrd withinOrd pos w i).events
      g₁ c₁ g₂ c₂ (j + 1) := by
  set active := groupOrd.filter (fun gi =>
    decide (gi < obsAll.length) && (actTick gi == w.tick))
  by_cases h_active : active = []
  · -- idle branch
    exact MiddleBlockOk_gSimBody_step_idle groups actTick T obsAll groupOrd
      withinOrd pos w i g₁ c₁ g₂ c₂ j
      h_g₁ h_c₁ h_g₂ h_c₂ h_layout h_j_ge h_j₁ h_j₂
      h_due h_tgt₂ hA_mem hD_mem h_nodup hAD h_mb h_stage
      h_sA_absent h_sD_absent h_active h_nd_post
  · -- burst branch (survival-free, MiddleBlockOkActiveTick)
    exact MiddleBlockOk_gSimBody_step_burst_general groups actTick T
      obsAll groupOrd withinOrd pos w i g₁ c₁ g₂ c₂ j
      h_g₁ h_c₁ h_g₂ h_c₂ h_layout h_j_ge h_j₁ h_j₂
      h_due h_tgt₂ hA_mem hD_mem h_nodup hAD h_mb h_stage
      h_sA_absent h_sD_absent h_active h_nd_burst h_nd_post

/-- One stage step for middle stages, survival-free: at the pop tick of
    stage `j` (with `j ≥ 1`), the general step advances to stage
    `j + 1`, then the carry transports across non-pop ticks to the pop
    tick of stage `j + 1`. -/
theorem MiddleBlockOk_gSimFoldl_stage_succ_general
    (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat)
    (g₁ c₁ g₂ c₂ j : Nat) (T : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_j_ge : 1 ≤ j)
    (h_j₁ : j + 1 ≤ (chainAt groups g₁ c₁).middleDelays.length)
    (h_j₂ : j + 1 ≤ (chainAt groups g₂ c₂).middleDelays.length)
    (h_tgt₂ : stageTarget actTick groups g₂ c₂ j =
        stageTarget actTick groups g₁ c₁ j)
    (h_tgt₂_next : stageTarget actTick groups g₂ c₂ (j + 1) =
        stageTarget actTick groups g₁ c₁ (j + 1))
    -- MiddleBlockOk on the full events at stage j, at pop tick j
    (h_mb_full : MiddleBlockOk groups actTick T
        (gSimWorld groups actTick groupOrd withinOrd pos
          (stageTarget actTick groups g₁ c₁ j)).events
        g₁ c₁ g₂ c₂ j)
    -- Reference events are members at pop tick j
    (hA_mem_j : stageEvent actTick groups g₁ c₁ j ∈
        (gSimWorld groups actTick groupOrd withinOrd pos
          (stageTarget actTick groups g₁ c₁ j)).events)
    (hD_mem_j : stageEvent actTick groups g₂ c₂ j ∈
        (gSimWorld groups actTick groupOrd withinOrd pos
          (stageTarget actTick groups g₁ c₁ j)).events)
    -- Due-filter Nodup at pop tick j
    (h_nodup_due :
        ((gSimWorld groups actTick groupOrd withinOrd pos
          (stageTarget actTick groups g₁ c₁ j)).events.filter
          (fun e => e.targetTick == stageTarget actTick groups g₁ c₁ j)).Nodup)
    -- evBefore on the due-filter at pop tick j
    (hAD : evBefore
        ((gSimWorld groups actTick groupOrd withinOrd pos
          (stageTarget actTick groups g₁ c₁ j)).events.filter
          (fun e => e.targetTick ==
            stageTarget actTick groups g₁ c₁ j))
        (stageEvent actTick groups g₁ c₁ j)
        (stageEvent actTick groups g₂ c₂ j))
    -- StageMemAt at pop tick j
    (h_stage_mem : StageMemAt groups actTick
        (gSimWorld groups actTick groupOrd withinOrd pos
          (stageTarget actTick groups g₁ c₁ j))
        (stageTarget actTick groups g₁ c₁ j))
    -- NodeLayoutOk at pop tick j
    (h_layout : NodeLayoutOk groups
        (gSimWorld groups actTick groupOrd withinOrd pos
          (stageTarget actTick groups g₁ c₁ j)))
    -- Stage-(j+1) events absent from pre-tick queue at pop tick j
    (h_sA_absent : stageEvent actTick groups g₁ c₁ (j + 1) ∉
        (gSimWorld groups actTick groupOrd withinOrd pos
          (stageTarget actTick groups g₁ c₁ j)).events)
    (h_sD_absent : stageEvent actTick groups g₂ c₂ (j + 1) ∉
        (gSimWorld groups actTick groupOrd withinOrd pos
          (stageTarget actTick groups g₁ c₁ j)).events)
    -- Post-body Nodup at pop tick j
    (h_nd_post_j :
        (gSimWorld groups actTick groupOrd withinOrd pos
          (stageTarget actTick groups g₁ c₁ j + 1)).events.Nodup)
    -- Burst Nodup at pop tick j
    (h_nd_burst :
      let w := gSimWorld groups actTick groupOrd withinOrd pos
        (stageTarget actTick groups g₁ c₁ j)
      let w_log := w.logOutput s!"tick {w.tick}"
      let active := groupOrd.filter (fun gi =>
        decide (gi < (buildGroups groups).2.length) && (actTick gi == w.tick))
      (gSimBurst w.tick (buildGroups groups).2 withinOrd pos w_log
        active.zipIdx).events.Nodup)
    -- Carry hypotheses from tick t_j + 1 to pop tick of stage j + 1
    (hA_mem_carry : ∀ k,
        stageTarget actTick groups g₁ c₁ j + 1 ≤ k →
        k < stageTarget actTick groups g₁ c₁ (j + 1) →
        stageEvent actTick groups g₁ c₁ (j + 1) ∈
          (gSimWorld groups actTick groupOrd withinOrd pos k).events)
    (hD_mem_carry : ∀ k,
        stageTarget actTick groups g₁ c₁ j + 1 ≤ k →
        k < stageTarget actTick groups g₁ c₁ (j + 1) →
        stageEvent actTick groups g₂ c₂ (j + 1) ∈
          (gSimWorld groups actTick groupOrd withinOrd pos k).events)
    (h_nd_post_carry : ∀ k,
        stageTarget actTick groups g₁ c₁ j + 1 ≤ k →
        k < stageTarget actTick groups g₁ c₁ (j + 1) →
        (gSimWorld groups actTick groupOrd withinOrd pos (k + 1)).events.Nodup) :
    MiddleBlockOk groups actTick T
      (gSimWorld groups actTick groupOrd withinOrd pos
        (stageTarget actTick groups g₁ c₁ (j + 1))).events
      g₁ c₁ g₂ c₂ (j + 1) := by
  set t_j := stageTarget actTick groups g₁ c₁ j
  set t_j₁ := stageTarget actTick groups g₁ c₁ (j + 1)
  set W_j := gSimWorld groups actTick groupOrd withinOrd pos t_j
  set obsAll := (buildGroups groups).2
  -- Step 1: restrict MiddleBlockOk to the due-filter
  have h_mb_due : MiddleBlockOk groups actTick T
      (W_j.events.filter (fun e => e.targetTick == W_j.tick))
      g₁ c₁ g₂ c₂ j :=
    MiddleBlockOk_restrict_dueFilter groups actTick T W_j
      g₁ c₁ g₂ c₂ j h_mb_full
  -- Step 2: prepare hypotheses for the general step
  have h_tick_Wj : W_j.tick = t_j :=
    gSimWorld_tick groups actTick groupOrd withinOrd pos t_j
  have h_body : gSimWorld groups actTick groupOrd withinOrd pos (t_j + 1) =
      gSimBody actTick obsAll groupOrd withinOrd pos W_j t_j :=
    gSimWorld_succ_eq_body groups actTick groupOrd withinOrd pos t_j
  -- Rewrite due-filter hypotheses using h_tick_Wj
  have h_nodup_due' :
      (W_j.events.filter (fun e => e.targetTick == W_j.tick)).Nodup := by
    rw [h_tick_Wj]; exact h_nodup_due
  have hAD' : evBefore
      (W_j.events.filter (fun e => e.targetTick == W_j.tick))
      (stageEvent actTick groups g₁ c₁ j)
      (stageEvent actTick groups g₂ c₂ j) := by
    rw [h_tick_Wj]; exact hAD
  have h_stage' : StageMemAt groups actTick W_j W_j.tick := by
    rw [h_tick_Wj]; exact h_stage_mem
  have h_nd_post_j' :
      (gSimBody actTick obsAll groupOrd withinOrd pos W_j t_j).events.Nodup := by
    rw [← h_body]; exact h_nd_post_j
  -- Burst Nodup: unfold set definitions so types match
  have h_nd_burst' :
    let w_log := W_j.logOutput s!"tick {W_j.tick}"
    let active := groupOrd.filter (fun gi =>
      decide (gi < obsAll.length) && (actTick gi == W_j.tick))
    (gSimBurst W_j.tick obsAll withinOrd pos w_log
      active.zipIdx).events.Nodup := by
    dsimp only [obsAll, W_j, t_j]
    exact h_nd_burst
  -- Apply the general (survival-free) step
  have h_mb_step : MiddleBlockOk groups actTick T
      (gSimBody actTick obsAll groupOrd withinOrd pos W_j t_j).events
      g₁ c₁ g₂ c₂ (j + 1) :=
    MiddleBlockOk_gSimBody_step_general groups actTick T
      obsAll groupOrd withinOrd pos W_j t_j
      g₁ c₁ g₂ c₂ j
      h_g₁ h_c₁ h_g₂ h_c₂ h_layout h_j_ge h_j₁ h_j₂
      (by rw [h_tick_Wj]) h_tgt₂
      hA_mem_j hD_mem_j h_nodup_due' hAD' h_mb_due h_stage'
      h_sA_absent h_sD_absent h_nd_post_j' h_nd_burst'
  -- Step 3: rewrite as gSimWorld (t_j + 1)
  have h_mb_j₁ : MiddleBlockOk groups actTick T
      (gSimWorld groups actTick groupOrd withinOrd pos (t_j + 1)).events
      g₁ c₁ g₂ c₂ (j + 1) := by
    rw [h_body]
    exact h_mb_step
  -- Step 4: carry from t_j + 1 to t_j₁
  have h_stage_lt : t_j + 1 ≤ t_j₁ :=
    Nat.succ_le_of_lt (stageTarget_lt_succ actTick groups g₁ c₁ j (by omega))
  by_cases h_eq : t_j + 1 = t_j₁
  · rw [← h_eq]
    exact h_mb_j₁
  · have h_lt : t_j + 1 < t_j₁ := Nat.lt_of_le_of_ne h_stage_lt h_eq
    have h_carry : MiddleBlockOk groups actTick T
        (gSimWorld groups actTick groupOrd withinOrd pos t_j₁).events
        g₁ c₁ g₂ c₂ (j + 1) :=
      MiddleBlockOk_gSimWorld_carry_range groups actTick groupOrd
        withinOrd pos (t_j + 1) t_j₁ g₁ c₁ g₂ c₂ (j + 1) T
        (by omega) h_mb_j₁
        (by dsimp [t_j₁]; exact hA_mem_carry)
        (by dsimp [t_j₁]; exact hD_mem_carry)
        (fun k hk₁ hk₂ => by
          have h_lt_k : k < stageTarget actTick groups g₁ c₁ (j + 1) := by
            dsimp [t_j₁] at hk₂; exact hk₂
          intro h_eq'
          have h_tgt_eq : stageTarget actTick groups g₁ c₁ (j + 1) = k := by
            simpa [stageEvent] using h_eq'
          rw [← h_tgt_eq] at h_lt_k
          omega)
        (fun k hk₁ hk₂ => by
          have h_lt_k : k < stageTarget actTick groups g₁ c₁ (j + 1) := by
            dsimp [t_j₁] at hk₂; exact hk₂
          intro h_eq'
          have h_tgt_eq : stageTarget actTick groups g₂ c₂ (j + 1) = k := by
            simpa [stageEvent] using h_eq'
          rw [h_tgt₂_next] at h_tgt_eq
          rw [← h_tgt_eq] at h_lt_k
          omega)
        (by dsimp [t_j₁]; exact h_nd_post_carry)
    exact h_carry

/-- Per-stage side hypotheses for one survival-free middle-block stage
    step (`MiddleBlockOk_gSimFoldl_stage_succ_general`), excluding the
    inductive payload (MiddleBlockOk at stage `j`) and the global
    chain-index bounds. -/
structure MBStepSideGeneral (groups : List GroupSpec) (actTick : Nat → Nat)
    (groupOrd : List Nat) (withinOrd pos : Nat → List Nat)
    (g₁ c₁ g₂ c₂ j : Nat) : Prop where
  j_ge : 1 ≤ j
  j₁ : j + 1 ≤ (chainAt groups g₁ c₁).middleDelays.length
  j₂ : j + 1 ≤ (chainAt groups g₂ c₂).middleDelays.length
  tgt₂ : stageTarget actTick groups g₂ c₂ j =
    stageTarget actTick groups g₁ c₁ j
  tgt₂_next : stageTarget actTick groups g₂ c₂ (j + 1) =
    stageTarget actTick groups g₁ c₁ (j + 1)
  A_mem_j : stageEvent actTick groups g₁ c₁ j ∈
    (gSimWorld groups actTick groupOrd withinOrd pos
      (stageTarget actTick groups g₁ c₁ j)).events
  D_mem_j : stageEvent actTick groups g₂ c₂ j ∈
    (gSimWorld groups actTick groupOrd withinOrd pos
      (stageTarget actTick groups g₁ c₁ j)).events
  nodup_due :
    ((gSimWorld groups actTick groupOrd withinOrd pos
      (stageTarget actTick groups g₁ c₁ j)).events.filter
      (fun e => e.targetTick == stageTarget actTick groups g₁ c₁ j)).Nodup
  AD : evBefore
    ((gSimWorld groups actTick groupOrd withinOrd pos
      (stageTarget actTick groups g₁ c₁ j)).events.filter
      (fun e => e.targetTick == stageTarget actTick groups g₁ c₁ j))
    (stageEvent actTick groups g₁ c₁ j)
    (stageEvent actTick groups g₂ c₂ j)
  stage_mem : StageMemAt groups actTick
    (gSimWorld groups actTick groupOrd withinOrd pos
      (stageTarget actTick groups g₁ c₁ j))
    (stageTarget actTick groups g₁ c₁ j)
  layout : NodeLayoutOk groups
    (gSimWorld groups actTick groupOrd withinOrd pos
      (stageTarget actTick groups g₁ c₁ j))
  sA_absent : stageEvent actTick groups g₁ c₁ (j + 1) ∉
    (gSimWorld groups actTick groupOrd withinOrd pos
      (stageTarget actTick groups g₁ c₁ j)).events
  sD_absent : stageEvent actTick groups g₂ c₂ (j + 1) ∉
    (gSimWorld groups actTick groupOrd withinOrd pos
      (stageTarget actTick groups g₁ c₁ j)).events
  nd_post_j :
    (gSimWorld groups actTick groupOrd withinOrd pos
      (stageTarget actTick groups g₁ c₁ j + 1)).events.Nodup
  nd_burst :
    let w := gSimWorld groups actTick groupOrd withinOrd pos
      (stageTarget actTick groups g₁ c₁ j)
    let w_log := w.logOutput s!"tick {w.tick}"
    let active := groupOrd.filter (fun gi =>
      decide (gi < (buildGroups groups).2.length) && (actTick gi == w.tick))
    (gSimBurst w.tick (buildGroups groups).2 withinOrd pos w_log
      active.zipIdx).events.Nodup
  A_mem_carry : ∀ k,
    stageTarget actTick groups g₁ c₁ j + 1 ≤ k →
    k < stageTarget actTick groups g₁ c₁ (j + 1) →
    stageEvent actTick groups g₁ c₁ (j + 1) ∈
      (gSimWorld groups actTick groupOrd withinOrd pos k).events
  D_mem_carry : ∀ k,
    stageTarget actTick groups g₁ c₁ j + 1 ≤ k →
    k < stageTarget actTick groups g₁ c₁ (j + 1) →
    stageEvent actTick groups g₂ c₂ (j + 1) ∈
      (gSimWorld groups actTick groupOrd withinOrd pos k).events
  nd_post_carry : ∀ k,
    stageTarget actTick groups g₁ c₁ j + 1 ≤ k →
    k < stageTarget actTick groups g₁ c₁ (j + 1) →
    (gSimWorld groups actTick groupOrd withinOrd pos (k + 1)).events.Nodup

/-- The full middle-block stage induction, survival-free. From the base
    at stage 1 and per-stage side hypotheses, MiddleBlockOk holds at
    stage `m` on the tick-start queue at the pop tick of stage `m`. -/
theorem MiddleBlockOk_gSimFoldl_stage_general (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat)
    (g₁ c₁ g₂ c₂ m T : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_m_ge : 1 ≤ m)
    (h_base : MiddleBlockOk groups actTick T
      (gSimWorld groups actTick groupOrd withinOrd pos
        (stageTarget actTick groups g₁ c₁ 1)).events g₁ c₁ g₂ c₂ 1)
    (h_steps : ∀ j, 1 ≤ j → j < m →
      MBStepSideGeneral groups actTick groupOrd withinOrd pos g₁ c₁ g₂ c₂ j) :
    MiddleBlockOk groups actTick T
      (gSimWorld groups actTick groupOrd withinOrd pos
        (stageTarget actTick groups g₁ c₁ m)).events g₁ c₁ g₂ c₂ m := by
  suffices H : ∀ k, k ≤ m → 1 ≤ k → MiddleBlockOk groups actTick T
      (gSimWorld groups actTick groupOrd withinOrd pos
        (stageTarget actTick groups g₁ c₁ k)).events g₁ c₁ g₂ c₂ k by
    exact H m (le_refl m) h_m_ge
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ih hk_le hk_ge
  by_cases h_k1 : k = 1
  · subst h_k1
    exact h_base
  · have h_j_ge1 : 1 ≤ k - 1 := by omega
    have h_j_lt_m : k - 1 < m := by omega
    have h_j_lt_k : k - 1 < k := by omega
    have h_j_le_m : k - 1 ≤ m := by omega
    have h_side := h_steps (k - 1) h_j_ge1 h_j_lt_m
    have h_mb_pred := ih (k - 1) h_j_lt_k h_j_le_m h_j_ge1
    have h_step := MiddleBlockOk_gSimFoldl_stage_succ_general groups actTick
      groupOrd withinOrd pos g₁ c₁ g₂ c₂ (k - 1) T
      h_g₁ h_c₁ h_g₂ h_c₂
      h_side.j_ge h_side.j₁ h_side.j₂
      h_side.tgt₂ h_side.tgt₂_next
      h_mb_pred
      h_side.A_mem_j h_side.D_mem_j
      h_side.nodup_due h_side.AD
      h_side.stage_mem h_side.layout
      h_side.sA_absent h_side.sD_absent
      h_side.nd_post_j
      h_side.nd_burst
      h_side.A_mem_carry h_side.D_mem_carry h_side.nd_post_carry
    have h_k1' : k - 1 + 1 = k := by omega
    rw [h_k1'] at h_step
    exact h_step
