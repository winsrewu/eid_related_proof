import BasicProofs.GroupClustering.GSimBodyIteration
import BasicProofs.GroupClustering.OrderPreservationPremises

open BasicRedstoneSim List

/-! # Group clustering — MiddleBlockOk induction over gSimFoldl stages

This file proves the middle-block invariant across the full stage
sequence. It composes the unified step lemma (GSimBodyIteration) with the carry
lemma (GSimBodyIteration) and the cross-tick order transport (OrderPreservationPremises).

Main results:

* `MiddleBlockOk_gSimWorld_carry_tick` — one `gSimBody` tick carries
  the invariant when both reference events are non-due.

* `MiddleBlockOk_gSimWorld_carry_range` — iterating the carry across
  a range of non-pop ticks.

* `MiddleBlockOk_gSimFoldl_stage_succ` — one stage step from pop tick
  `j` to pop tick `j + 1` for `j ≥ 1`, combining the unified step
  with the multi-tick carry.
-/

/-! ## Private helpers -/

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

/-- `evBefore` on an appended list restricts to the left part when
    both reference events belong to the left part and the full list
    is duplicate-free. -/
private theorem evBefore_restrict_left''' {l r : List ScheduledEvent}
    {x y : ScheduledEvent}
    (h : evBefore (l ++ r) x y) (hx : x ∈ l) (hy : y ∈ l)
    (h_nd : (l ++ r).Nodup) :
    evBefore l x y := by
  revert x y h hx hy h_nd
  induction l with
  | nil => intro x y _ hx; cases hx
  | cons a l ih =>
    intro x y h hx hy h_nd
    have h_cons_app : (a :: l) ++ r = a :: (l ++ r) := by rw [List.cons_append]
    rw [h_cons_app] at h h_nd
    simp only [List.nodup_cons] at h_nd
    have h_a_not : a ∉ l ++ r := h_nd.1
    have h_nd_tail : (l ++ r).Nodup := h_nd.2
    rw [evBefore.cons_iff] at h
    rcases h with ⟨h_ax, h_y_lr⟩ | h_tail
    · cases hy with
      | head =>
        exact absurd h_y_lr h_a_not
      | tail _ hy_l =>
        rw [evBefore.cons_iff]
        exact Or.inl ⟨h_ax, hy_l⟩
    · cases hx with
      | head =>
        exact absurd (evBefore.mem_left h_tail) h_a_not
      | tail _ hx_l =>
        cases hy with
        | head =>
          exact absurd (evBefore.mem_right h_tail) h_a_not
        | tail _ hy_l =>
          exact evBefore.cons_extend (ih h_tail hx_l hy_l h_nd_tail)

/-! ## Restricting MiddleBlockOk from full events to due-filter -/

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

/-! ## One-tick carry for gSimWorld -/

/-- One `gSimBody` tick carries the middle-block invariant when both
    reference events target a future tick. This specializes the GSimBodyIteration
    carry lemma to the `gSimWorld` recurrence. -/
theorem MiddleBlockOk_gSimWorld_carry_tick (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (t : Nat)
    (g₁ c₁ g₂ c₂ j : Nat) (T : Nat)
    (h_mb : MiddleBlockOk groups actTick T
        (gSimWorld groups actTick groupOrd withinOrd pos t).events
        g₁ c₁ g₂ c₂ j)
    (hA_mem : stageEvent actTick groups g₁ c₁ j ∈
        (gSimWorld groups actTick groupOrd withinOrd pos t).events)
    (hD_mem : stageEvent actTick groups g₂ c₂ j ∈
        (gSimWorld groups actTick groupOrd withinOrd pos t).events)
    (hA_nd : (stageEvent actTick groups g₁ c₁ j).targetTick ≠ t)
    (hD_nd : (stageEvent actTick groups g₂ c₂ j).targetTick ≠ t)
    (h_nd_post :
        (gSimWorld groups actTick groupOrd withinOrd pos (t + 1)).events.Nodup) :
    MiddleBlockOk groups actTick T
      (gSimWorld groups actTick groupOrd withinOrd pos (t + 1)).events
      g₁ c₁ g₂ c₂ j := by
  set W := gSimWorld groups actTick groupOrd withinOrd pos t
  have h_tick_W : W.tick = t :=
    gSimWorld_tick groups actTick groupOrd withinOrd pos t
  have h_body : gSimWorld groups actTick groupOrd withinOrd pos (t + 1) =
      gSimBody actTick (buildGroups groups).2 groupOrd withinOrd pos W t :=
    gSimWorld_succ_eq_body groups actTick groupOrd withinOrd pos t
  rw [h_body] at h_nd_post
  rw [h_body]
  exact MiddleBlockOk_gSimBody_carry groups actTick T
    (buildGroups groups).2 groupOrd withinOrd pos W t g₁ c₁ g₂ c₂ j
    h_mb hA_mem hD_mem
    (by rwa [h_tick_W]) (by rwa [h_tick_W]) h_nd_post

/-! ## Multi-tick carry -/

/-- Iterating the one-tick carry across `n` ticks. -/
private theorem MiddleBlockOk_gSimWorld_carry_add (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (a n : Nat)
    (g₁ c₁ g₂ c₂ j : Nat) (T : Nat)
    (h_mb : MiddleBlockOk groups actTick T
        (gSimWorld groups actTick groupOrd withinOrd pos a).events
        g₁ c₁ g₂ c₂ j)
    (hA_mem : ∀ k, a ≤ k → k < a + n →
        stageEvent actTick groups g₁ c₁ j ∈
          (gSimWorld groups actTick groupOrd withinOrd pos k).events)
    (hD_mem : ∀ k, a ≤ k → k < a + n →
        stageEvent actTick groups g₂ c₂ j ∈
          (gSimWorld groups actTick groupOrd withinOrd pos k).events)
    (hA_nd : ∀ k, a ≤ k → k < a + n →
        (stageEvent actTick groups g₁ c₁ j).targetTick ≠ k)
    (hD_nd : ∀ k, a ≤ k → k < a + n →
        (stageEvent actTick groups g₂ c₂ j).targetTick ≠ k)
    (h_nd_post : ∀ k, a ≤ k → k < a + n →
        (gSimWorld groups actTick groupOrd withinOrd pos (k + 1)).events.Nodup) :
    MiddleBlockOk groups actTick T
      (gSimWorld groups actTick groupOrd withinOrd pos (a + n)).events
      g₁ c₁ g₂ c₂ j := by
  induction n with
  | zero =>
    simpa using h_mb
  | succ n ih =>
    have h_mb_n : MiddleBlockOk groups actTick T
        (gSimWorld groups actTick groupOrd withinOrd pos (a + n)).events
        g₁ c₁ g₂ c₂ j :=
      ih (fun k h₁ h₂ => hA_mem k h₁ (by omega))
         (fun k h₁ h₂ => hD_mem k h₁ (by omega))
         (fun k h₁ h₂ => hA_nd k h₁ (by omega))
         (fun k h₁ h₂ => hD_nd k h₁ (by omega))
         (fun k h₁ h₂ => h_nd_post k h₁ (by omega))
    exact MiddleBlockOk_gSimWorld_carry_tick groups actTick groupOrd
      withinOrd pos (a + n) g₁ c₁ g₂ c₂ j T h_mb_n
      (hA_mem (a + n) (by omega) (by omega))
      (hD_mem (a + n) (by omega) (by omega))
      (hA_nd (a + n) (by omega) (by omega))
      (hD_nd (a + n) (by omega) (by omega))
      (h_nd_post (a + n) (by omega) (by omega))

/-- Iterating the carry across a range `[a, b)` of non-pop ticks. -/
theorem MiddleBlockOk_gSimWorld_carry_range (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (a b : Nat)
    (g₁ c₁ g₂ c₂ j : Nat) (T : Nat)
    (h_le : a ≤ b)
    (h_mb : MiddleBlockOk groups actTick T
        (gSimWorld groups actTick groupOrd withinOrd pos a).events
        g₁ c₁ g₂ c₂ j)
    (hA_mem : ∀ k, a ≤ k → k < b →
        stageEvent actTick groups g₁ c₁ j ∈
          (gSimWorld groups actTick groupOrd withinOrd pos k).events)
    (hD_mem : ∀ k, a ≤ k → k < b →
        stageEvent actTick groups g₂ c₂ j ∈
          (gSimWorld groups actTick groupOrd withinOrd pos k).events)
    (hA_nd : ∀ k, a ≤ k → k < b →
        (stageEvent actTick groups g₁ c₁ j).targetTick ≠ k)
    (hD_nd : ∀ k, a ≤ k → k < b →
        (stageEvent actTick groups g₂ c₂ j).targetTick ≠ k)
    (h_nd_post : ∀ k, a ≤ k → k < b →
        (gSimWorld groups actTick groupOrd withinOrd pos (k + 1)).events.Nodup) :
    MiddleBlockOk groups actTick T
      (gSimWorld groups actTick groupOrd withinOrd pos b).events
      g₁ c₁ g₂ c₂ j := by
  have h : b = a + (b - a) := by omega
  rw [h]
  refine MiddleBlockOk_gSimWorld_carry_add groups actTick groupOrd withinOrd pos
    a (b - a) g₁ c₁ g₂ c₂ j T h_mb ?_ ?_ ?_ ?_ ?_
  · intro k h₁ h₂; exact hA_mem k h₁ (by omega)
  · intro k h₁ h₂; exact hD_mem k h₁ (by omega)
  · intro k h₁ h₂; exact hA_nd k h₁ (by omega)
  · intro k h₁ h₂; exact hD_nd k h₁ (by omega)
  · intro k h₁ h₂; exact h_nd_post k h₁ (by omega)

/-! ## One stage step: pop tick j → pop tick (j+1), for j ≥ 1 -/

/-- One stage step for middle stages: at the pop tick of stage `j`
    (with `j ≥ 1`), the unified step advances to stage `j + 1`, then
    the carry transports across non-pop ticks to the pop tick of
    stage `j + 1`. -/
theorem MiddleBlockOk_gSimFoldl_stage_succ (groups : List GroupSpec)
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
          (fun e => e.targetTick ==
            stageTarget actTick groups g₁ c₁ j)).Nodup)
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
    -- Survival of stage-(j+1) events through the burst
    (h_surv_A :
      let w := gSimWorld groups actTick groupOrd withinOrd pos
        (stageTarget actTick groups g₁ c₁ j)
      let w_log := w.logOutput s!"tick {w.tick}"
      let active := groupOrd.filter (fun gi =>
        decide (gi < (buildGroups groups).2.length) && (actTick gi == w.tick))
      stageEvent actTick groups g₁ c₁ (j + 1) ∈
        (gSimBurst w.tick (buildGroups groups).2 withinOrd pos w_log
          active.zipIdx).events)
    (h_surv_D :
      let w := gSimWorld groups actTick groupOrd withinOrd pos
        (stageTarget actTick groups g₁ c₁ j)
      let w_log := w.logOutput s!"tick {w.tick}"
      let active := groupOrd.filter (fun gi =>
        decide (gi < (buildGroups groups).2.length) && (actTick gi == w.tick))
      stageEvent actTick groups g₂ c₂ (j + 1) ∈
        (gSimBurst w.tick (buildGroups groups).2 withinOrd pos w_log
          active.zipIdx).events)
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
  -- Step 2: prepare hypotheses for the unified step
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
  -- Survival A
  have h_surv_A' :
    let w_log := W_j.logOutput s!"tick {W_j.tick}"
    let active := groupOrd.filter (fun gi =>
      decide (gi < obsAll.length) && (actTick gi == W_j.tick))
    stageEvent actTick groups g₁ c₁ (j + 1) ∈
      (gSimBurst W_j.tick obsAll withinOrd pos w_log
        active.zipIdx).events := by
    dsimp only [obsAll, W_j, t_j]
    exact h_surv_A
  -- Survival D
  have h_surv_D' :
    let w_log := W_j.logOutput s!"tick {W_j.tick}"
    let active := groupOrd.filter (fun gi =>
      decide (gi < obsAll.length) && (actTick gi == W_j.tick))
    stageEvent actTick groups g₂ c₂ (j + 1) ∈
      (gSimBurst W_j.tick obsAll withinOrd pos w_log
        active.zipIdx).events := by
    dsimp only [obsAll, W_j, t_j]
    exact h_surv_D
  -- Apply the unified step
  have h_mb_step : MiddleBlockOk groups actTick T
      (gSimBody actTick obsAll groupOrd withinOrd pos W_j t_j).events
      g₁ c₁ g₂ c₂ (j + 1) :=
    MiddleBlockOk_gSimBody_step groups actTick T
      obsAll groupOrd withinOrd pos W_j t_j
      g₁ c₁ g₂ c₂ j
      h_g₁ h_c₁ h_g₂ h_c₂ h_layout h_j_ge h_j₁ h_j₂
      (by rw [h_tick_Wj]) h_tgt₂
      hA_mem_j hD_mem_j h_nodup_due' hAD' h_mb_due h_stage'
      h_sA_absent h_sD_absent h_nd_post_j' h_nd_burst'
      h_surv_A' h_surv_D'
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

/-! ## The full stage induction -/

/-- Per-stage side hypotheses for one middle-block stage step
    (`MiddleBlockOk_gSimFoldl_stage_succ`), excluding the inductive
    payload (MiddleBlockOk at stage `j`) and the global chain-index
    bounds. -/
structure MBStepSide (groups : List GroupSpec) (actTick : Nat → Nat)
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
  surv_A :
    let w := gSimWorld groups actTick groupOrd withinOrd pos
      (stageTarget actTick groups g₁ c₁ j)
    let w_log := w.logOutput s!"tick {w.tick}"
    let active := groupOrd.filter (fun gi =>
      decide (gi < (buildGroups groups).2.length) && (actTick gi == w.tick))
    stageEvent actTick groups g₁ c₁ (j + 1) ∈
      (gSimBurst w.tick (buildGroups groups).2 withinOrd pos w_log
        active.zipIdx).events
  surv_D :
    let w := gSimWorld groups actTick groupOrd withinOrd pos
      (stageTarget actTick groups g₁ c₁ j)
    let w_log := w.logOutput s!"tick {w.tick}"
    let active := groupOrd.filter (fun gi =>
      decide (gi < (buildGroups groups).2.length) && (actTick gi == w.tick))
    stageEvent actTick groups g₂ c₂ (j + 1) ∈
      (gSimBurst w.tick (buildGroups groups).2 withinOrd pos w_log
        active.zipIdx).events
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

/-- The full middle-block stage induction. From the base at stage 1 and
    per-stage side hypotheses, MiddleBlockOk holds at stage `m` on the
    tick-start queue at the pop tick of stage `m`. The induction threads
    `MiddleBlockOk_gSimFoldl_stage_succ` from stage 1 up to stage `m`. -/
theorem MiddleBlockOk_gSimFoldl_stage (groups : List GroupSpec)
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
      MBStepSide groups actTick groupOrd withinOrd pos g₁ c₁ g₂ c₂ j) :
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
    have h_step := MiddleBlockOk_gSimFoldl_stage_succ groups actTick
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
      h_side.nd_burst h_side.surv_A h_side.surv_D
      h_side.A_mem_carry h_side.D_mem_carry h_side.nd_post_carry
    have h_k1' : k - 1 + 1 = k := by omega
    rw [h_k1'] at h_step
    exact h_step

/-!
## What remains toward the full stage induction

The theorem `MiddleBlockOk_gSimFoldl_stage` states: for every stage
`j ≤ m₁`, MiddleBlockOk holds at stage `j` on the tick-start queue
at the pop tick of stage `j`.

The proof proceeds by induction on `j`:

1. **Base case (j = 0)**: MiddleBlockOk at stage 0 on the tick-start
   queue at pop tick `actTick gi + 2`. This requires carrying the
   invariant from `activateGroup` (MiddleBlockOkTicks stage0) through the
   remaining burst steps and `stepUntilNextTick` at tick
   `actTick gi`, then through `gSimBody` at tick `actTick gi + 1`.
   The carry lemmas above handle the tick-to-tick transport. The
   remaining gap is proving that the queue between the two stage-0
   reference events contains only priority-0 observer events (no
   priority -3 middle repeater events).

2. **Step (j → j + 1) for j ≥ 1**: Proven by
   `MiddleBlockOk_gSimFoldl_stage_succ` above. This applies the
   unified step (GSimBodyIteration) at the pop tick, then carries across the
   non-pop ticks to the next pop tick.

3. **Step (j = 0 → j = 1)**: The unified step (GSimBodyIteration) requires
   `1 ≤ j`, so the base step needs a separate lemma for stage 0.
   At stage 0, the observer events have priority 0 instead of -3.
   A stage-0 step lemma must show that the observer lockstep at
   pop tick 0 spawns the stage-1 repeater events in the correct
   order.

4. **Side hypotheses**: Each step requires Nodup of the due-filter,
   StageMemAt preservation, NodeLayoutOk preservation, absence of
   stage-(j+1) events, survival of reference events through the
   burst, and Nodup of the post-body queue. QueueMembership gives
   NodeLayoutOk preservation. LockstepComposition gives due-filter Nodup. The
   remaining side hypotheses (survival, absence, StageMemAt
   preservation across gSimFoldl) need dedicated proofs.
-/
