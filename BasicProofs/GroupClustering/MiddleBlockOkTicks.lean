import BasicProofs.GroupClustering.MiddleBlockPopStep
import BasicProofs.GroupClustering.LockstepComposition

open BasicRedstoneSim List

/-! # Group clustering — MiddleBlockOk across gSimFoldl ticks

The middle-block invariant holds at stage `j` on the tick-start queue.
This file composes the step lemmas of MiddleBlockPopStep into preservation results
for one full `gSimBody` tick.

One `gSimBody` tick has two branches. The idle branch runs
`stepUntilNextTick` alone. The active branch runs `gSimBurst` then
`stepUntilNextTick`. MiddleBlockPopStep gives the stage step for each piece.
This file combines them.
-/

/-! ## Private helpers -/

/-- A list of length zero is empty. -/
private theorem list_nil_of_length_zero' {α : Type} (l : List α)
    (h : l.length = 0) : l = [] := by
  cases l with
  | nil => rfl
  | cons _ _ => simp at h

/-- Erasing an in-range element removes exactly one position. -/
private theorem length_eraseIdx_of_lt' {α : Type} (l : List α) (i : Nat)
    (h : i < l.length) : (l.eraseIdx i).length = l.length - 1 := by
  revert i h
  induction l with
  | nil => intro i h; cases h
  | cons x xs ih =>
    intro i h
    cases i with
    | zero => simp [List.eraseIdx]
    | succ i' =>
      have h_i' : i' < xs.length := Nat.lt_of_succ_lt_succ (by simpa using h)
      simp only [List.eraseIdx, List.length_cons]
      rw [ih i' h_i']
      omega

/-- A filter keeps a list unchanged when the predicate holds
    everywhere. -/
private theorem filter_eq_self_of_forall'' {α : Type} (p : α → Bool)
    (l : List α) (h : ∀ x ∈ l, p x = true) : l.filter p = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have h_x := h x (List.mem_cons.mpr (Or.inl rfl))
    simp [List.filter, h_x,
      ih (fun y hy => h y (List.mem_cons.mpr (Or.inr hy)))]

/-- One pop removes the popped event from the due filter. -/
private theorem due_tail_eq_eraseIdx' (w : World) (ev₀ : ScheduledEvent)
    (w_pop : World) (h_pop : w.popNextEvent = some (ev₀, w_pop)) :
    ∃ j, j < (w.events.filter (fun e => e.targetTick == w.tick)).length ∧
      (w_pop.onScheduledTick ev₀.nodeId).events.filter
          (fun e => e.targetTick == w.tick) =
        (w.events.filter (fun e => e.targetTick == w.tick)).eraseIdx j := by
  obtain ⟨idx, h_idx, h_erase, h_tick_ev, _, h_get⟩ :=
    World.popNextEvent_eraseIdx w ev₀ w_pop h_pop
  have h_due_ev₀ : (fun e => e.targetTick == w.tick)
      (w.events[idx]'h_idx) = true := by
    simp [h_get, h_tick_ev]
  obtain ⟨j, hj, h_filter_erase, _⟩ :=
    filter_eraseIdx_getElem (fun e => e.targetTick == w.tick) w.events idx
      h_idx h_due_ev₀
  refine ⟨j, hj, ?_⟩
  obtain ⟨new, h_app_new, h_fut_new⟩ :=
    World.onScheduledTick_appends_future w_pop ev₀.nodeId
  have h_tick_pop : w_pop.tick = w.tick :=
    World.popNextEvent_tick w ev₀ w_pop h_pop
  rw [h_app_new, List.filter_append]
  have h_new_nil : new.filter (fun e => e.targetTick == w.tick) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro e h_e
    have h_gt := h_fut_new e h_e
    rw [h_tick_pop] at h_gt
    simp
    omega
  rw [h_new_nil, List.append_nil, h_erase, h_filter_erase]

/-- A full drain of the due events leaves no event at the tick. -/
private theorem drain_due_filter' (w : World) :
    (processNEvents w
        ((w.events.filter (fun e => e.targetTick == w.tick)).length)).events.filter
      (fun e => e.targetTick == w.tick) = [] := by
  have h_gen : ∀ (w : World) (n : Nat),
      (w.events.filter (fun e => e.targetTick == w.tick)).length ≤ n →
      (processNEvents w n).events.filter
        (fun e => e.targetTick == w.tick) = [] := by
    intro w n
    induction n generalizing w with
    | zero =>
      intro h_len
      dsimp only [processNEvents]
      apply list_nil_of_length_zero'
      omega
    | succ n ih =>
      intro h_len
      dsimp only [processNEvents]
      cases h_step : w.step with
      | none =>
        dsimp
        dsimp [World.step] at h_step
        cases h_pop : w.popNextEvent with
        | none =>
          apply List.filter_eq_nil_iff.mpr
          intro ev h_ev
          by_cases h_be : ev.targetTick = w.tick
          · exact (popNextEvent_none_no_events w h_pop ev h_ev h_be).elim
          · simp [h_be]
        | some p => simp [h_pop] at h_step
      | some w' =>
        dsimp [World.step] at h_step
        cases h_pop : w.popNextEvent with
        | none => simp [h_pop] at h_step
        | some p =>
          rcases p with ⟨ev₀, w_pop⟩
          simp only [h_pop] at h_step
          injection h_step with h_w'
          have h_len' :
              (w'.events.filter
                (fun e => e.targetTick == w'.tick)).length ≤ n := by
            rw [← h_w']
            have h_tick :
                (w_pop.onScheduledTick ev₀.nodeId).tick = w.tick := by
              rw [World.onScheduledTick_tick,
                World.popNextEvent_tick w ev₀ w_pop h_pop]
            obtain ⟨j, hj, h_eq⟩ := due_tail_eq_eraseIdx' w ev₀ w_pop h_pop
            rw [h_tick, h_eq, length_eraseIdx_of_lt' _ _ hj]
            omega
          have h_tick_w' : w'.tick = w.tick := by
            rw [← h_w', World.onScheduledTick_tick,
              World.popNextEvent_tick w ev₀ w_pop h_pop]
          rw [← h_tick_w']
          exact ih w' h_len'
  exact h_gen w _ (by omega)

/-- `evBefore` on an appended list restricts to the left part when both
    reference events belong to the left part and the full list is
    duplicate-free. -/
private theorem evBefore_restrict_left' {l r : List ScheduledEvent}
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

/-- Carrying MiddleBlockOk through `stepUntilNextTick` when both
    reference events are non-due survivors. No spawn can sit between
    two survivors in the post-drain queue. -/
private theorem MiddleBlockOk_carry_stepUntilNextTick'
    (groups : List GroupSpec) (actTick : Nat → Nat) (T : Nat)
    (w : World) (g₁ c₁ g₂ c₂ j : Nat)
    (h_mb : MiddleBlockOk groups actTick T w.events g₁ c₁ g₂ c₂ j)
    (hA_mem : stageEvent actTick groups g₁ c₁ j ∈ w.events)
    (hD_mem : stageEvent actTick groups g₂ c₂ j ∈ w.events)
    (hA_nd : (stageEvent actTick groups g₁ c₁ j).targetTick ≠ w.tick)
    (hD_nd : (stageEvent actTick groups g₂ c₂ j).targetTick ≠ w.tick)
    (h_nd_post : w.stepUntilNextTick.events.Nodup) :
    MiddleBlockOk groups actTick T w.stepUntilNextTick.events
      g₁ c₁ g₂ c₂ j := by
  set sA := stageEvent actTick groups g₁ c₁ j
  set sD := stageEvent actTick groups g₂ c₂ j
  -- the filtered split: stepUntilNextTick.events = survivors ++ spawns
  set due := w.events.filter (fun e => e.targetTick == w.tick)
  set n := due.length
  set W := processNEvents w n
  have h_drain : W.events.filter (fun ev => ev.targetTick == w.tick) = [] :=
    drain_due_filter' w
  have h_no : ∀ ev ∈ W.events, ev.targetTick ≠ W.tick := by
    intro ev h_ev h_eq
    have h_mem : ev ∈ W.events.filter (fun e => e.targetTick == w.tick) := by
      rw [List.mem_filter]
      exact ⟨h_ev, by rw [processNEvents_tick] at h_eq; rw [h_eq]; simp⟩
    rw [h_drain] at h_mem
    cases h_mem
  have h_pop_none : W.popNextEvent = none :=
    World.popNextEvent_none_of_no_due W h_no
  have h_step_none : W.step = none := by simp only [World.step, h_pop_none]
  have h_sunt : w.stepUntilNextTick.events = W.events := by
    rw [← processNEvents_stepUntilNextTick_eq w n,
      stepUntilNextTick_of_step_none W h_step_none]
  have h_split : W.events =
      w.events.filter (fun ev => ev.targetTick ≠ w.tick) ++
        World.popSpawnAcc w n := by
    have h_f := (World.popSeqWorldFuel_filter_split w n).1
    rw [← processNEvents_eq_popSeqWorldFuel] at h_f
    have h_keep : W.events.filter (fun ev => ev.targetTick ≠ w.tick) =
        W.events := by
      apply filter_eq_self_of_forall''
      intro ev h_ev
      have h_ne : ev.targetTick ≠ w.tick := by
        have h := h_no ev h_ev; rwa [processNEvents_tick] at h
      rw [decide_eq_true_eq]; exact h_ne
    rw [← h_keep]; exact h_f
  set survivors := w.events.filter (fun ev => ev.targetTick ≠ w.tick)
  set spawns := World.popSpawnAcc w n
  -- sA and sD are survivors
  have h_sA_surv : sA ∈ survivors := by
    rw [List.mem_filter]
    exact ⟨hA_mem, decide_eq_true_eq.mpr hA_nd⟩
  have h_sD_surv : sD ∈ survivors := by
    rw [List.mem_filter]
    exact ⟨hD_mem, decide_eq_true_eq.mpr hD_nd⟩
  -- nodup of survivors ++ spawns
  have h_nd_app : (survivors ++ spawns).Nodup := by
    rw [← h_split, ← h_sunt]; exact h_nd_post
  -- transfer MiddleBlockOk to survivors via the filter
  intro e h_b1 h_b2 h_pri h_tgt
  rw [h_sunt, h_split] at h_b1 h_b2
  -- any e between sA and sD in survivors ++ spawns is a survivor
  have h_e_surv : e ∈ survivors := by
    have h_e_mem : e ∈ survivors ++ spawns := evBefore.mem_left h_b2
    rw [List.mem_append] at h_e_mem
    rcases h_e_mem with h_e_s | h_e_sp
    · exact h_e_s
    · exfalso
      -- sD is a survivor, e is a spawn: sD before e.
      have h_sD_before_e : evBefore (survivors ++ spawns) sD e :=
        evBefore.of_mem_append h_sD_surv h_e_sp
      -- but h_b2 says e before sD: contradiction
      exact evBefore.asymm h_nd_app h_b2 h_sD_before_e
  -- restrict evBefore to survivors
  have h_b1_s : evBefore survivors sA e :=
    evBefore_restrict_left' h_b1 h_sA_surv h_e_surv h_nd_app
  have h_b2_s : evBefore survivors e sD :=
    evBefore_restrict_left' h_b2 h_e_surv h_sD_surv h_nd_app
  -- transfer evBefore from survivors to w.events via filter
  set pTick : ScheduledEvent → Bool :=
    fun ev => decide (ev.targetTick ≠ w.tick)
  have h_b1_full : evBefore w.events sA e :=
    evBefore.of_filter pTick h_b1_s
  have h_b2_full : evBefore w.events e sD :=
    evBefore.of_filter pTick h_b2_s
  exact h_mb e h_b1_full h_b2_full h_pri h_tgt

/-! ## One gSimBody tick preserves MiddleBlockOk -/

/-- One `gSimBody` tick preserves the middle-block invariant when no
    groups activate. The body reduces to `stepUntilNextTick` after a
    log entry. The log entry does not change events or tick. -/
theorem MiddleBlockOk_gSimBody_step_idle (groups : List GroupSpec)
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
    (h_idle : groupOrd.filter (fun gi =>
        decide (gi < obsAll.length) && (actTick gi == w.tick)) = [])
    (h_nd_post :
        (gSimBody actTick obsAll groupOrd withinOrd pos w i).events.Nodup) :
    MiddleBlockOk groups actTick T
      (gSimBody actTick obsAll groupOrd withinOrd pos w i).events
      g₁ c₁ g₂ c₂ (j + 1) := by
  set w_log := w.logOutput s!"tick {w.tick}"
  have h_ev_log : w_log.events = w.events := by simp [w_log]
  have h_tick_log : w_log.tick = w.tick := by simp [w_log]
  have h_body : gSimBody actTick obsAll groupOrd withinOrd pos w i =
      w_log.stepUntilNextTick := by
    dsimp [gSimBody]; simp only [h_idle]; rfl
  rw [h_body] at h_nd_post
  rw [h_body]
  have h_layout_log : NodeLayoutOk groups w_log :=
    NodeLayoutOk_logOutput groups w _ h_layout
  have h_stage_log : StageMemAt groups actTick w_log w_log.tick := by
    intro ev h_ev
    exact h_stage ev (by rwa [h_ev_log] at h_ev)
  have hA_mem_log : stageEvent actTick groups g₁ c₁ j ∈ w_log.events := by
    rwa [h_ev_log]
  have hD_mem_log : stageEvent actTick groups g₂ c₂ j ∈ w_log.events := by
    rwa [h_ev_log]
  have h_nodup_log :
      (w_log.events.filter (fun e => e.targetTick == w_log.tick)).Nodup := by
    rw [h_ev_log, h_tick_log]; exact h_nodup
  have hAD_log : evBefore
      (w_log.events.filter (fun e => e.targetTick == w_log.tick))
      (stageEvent actTick groups g₁ c₁ j)
      (stageEvent actTick groups g₂ c₂ j) := by
    rw [h_ev_log, h_tick_log]; exact hAD
  have h_mb_log : MiddleBlockOk groups actTick T
      (w_log.events.filter (fun e => e.targetTick == w_log.tick))
      g₁ c₁ g₂ c₂ j := by
    rw [h_ev_log, h_tick_log]; exact h_mb
  have h_sA_absent_log :
      stageEvent actTick groups g₁ c₁ (j + 1) ∉ w_log.events := by
    rwa [h_ev_log]
  have h_sD_absent_log :
      stageEvent actTick groups g₂ c₂ (j + 1) ∉ w_log.events := by
    rwa [h_ev_log]
  exact MiddleBlockOk_step_stepUntilNextTick groups actTick T w_log
    g₁ c₁ g₂ c₂ j h_g₁ h_c₁ h_g₂ h_c₂ h_layout_log h_j_ge h_j₁ h_j₂
    (by rw [h_tick_log]; exact h_due)
    h_tgt₂ hA_mem_log hD_mem_log h_nodup_log hAD_log h_mb_log
    h_stage_log h_sA_absent_log h_sD_absent_log h_nd_post

/-- One `gSimBody` tick preserves the middle-block invariant when some
    groups activate. The body runs `gSimBurst` then `stepUntilNextTick`.
    The burst advances the stage to `j + 1`. The drain step preserves
    the stage-`(j + 1)` invariant because the stage-`(j + 1)` events
    are non-due survivors. -/
theorem MiddleBlockOk_gSimBody_step_burst (groups : List GroupSpec)
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
    (h_active : groupOrd.filter (fun gi =>
        decide (gi < obsAll.length) && (actTick gi == w.tick)) ≠ [])
    (h_nd_burst :
      let w_log := w.logOutput s!"tick {w.tick}"
      let active := groupOrd.filter (fun gi =>
        decide (gi < obsAll.length) && (actTick gi == w.tick))
      (gSimBurst w.tick obsAll withinOrd pos w_log
        active.zipIdx).events.Nodup)
    (h_surv_A :
      let w_log := w.logOutput s!"tick {w.tick}"
      let active := groupOrd.filter (fun gi =>
        decide (gi < obsAll.length) && (actTick gi == w.tick))
      stageEvent actTick groups g₁ c₁ (j + 1) ∈
        (gSimBurst w.tick obsAll withinOrd pos w_log
          active.zipIdx).events)
    (h_surv_D :
      let w_log := w.logOutput s!"tick {w.tick}"
      let active := groupOrd.filter (fun gi =>
        decide (gi < obsAll.length) && (actTick gi == w.tick))
      stageEvent actTick groups g₂ c₂ (j + 1) ∈
        (gSimBurst w.tick obsAll withinOrd pos w_log
          active.zipIdx).events)
    (h_nd_post :
        (gSimBody actTick obsAll groupOrd withinOrd pos w i).events.Nodup) :
    MiddleBlockOk groups actTick T
      (gSimBody actTick obsAll groupOrd withinOrd pos w i).events
      g₁ c₁ g₂ c₂ (j + 1) := by
  set w_log := w.logOutput s!"tick {w.tick}"
  set active := groupOrd.filter (fun gi =>
    decide (gi < obsAll.length) && (actTick gi == w.tick))
  set W_B := gSimBurst w.tick obsAll withinOrd pos w_log active.zipIdx
  have h_ev_log : w_log.events = w.events := by simp [w_log]
  have h_tick_log : w_log.tick = w.tick := by simp [w_log]
  -- gSimBody reduces to W_B.stepUntilNextTick
  have h_body : gSimBody actTick obsAll groupOrd withinOrd pos w i =
      W_B.stepUntilNextTick := by
    dsimp only [gSimBody]
    simp only [World.logOutput_tick]
    dsimp [W_B, w_log, active]
    split_ifs with h_cond
    · exfalso
      have h_eq : active = [] := by simpa [active] using h_cond
      exact h_active h_eq
    · rfl
  rw [h_body] at h_nd_post
  rw [h_body]
  -- transfer hypotheses to w_log
  have h_layout_log : NodeLayoutOk groups w_log :=
    NodeLayoutOk_logOutput groups w _ h_layout
  have h_stage_log : StageMemAt groups actTick w_log w_log.tick := by
    intro ev h_ev; exact h_stage ev (by rwa [h_ev_log] at h_ev)
  have hA_mem_log : stageEvent actTick groups g₁ c₁ j ∈ w_log.events := by
    rwa [h_ev_log]
  have hD_mem_log : stageEvent actTick groups g₂ c₂ j ∈ w_log.events := by
    rwa [h_ev_log]
  have h_nodup_log :
      (w_log.events.filter (fun e => e.targetTick == w_log.tick)).Nodup := by
    rw [h_ev_log, h_tick_log]; exact h_nodup
  have hAD_log : evBefore
      (w_log.events.filter (fun e => e.targetTick == w_log.tick))
      (stageEvent actTick groups g₁ c₁ j)
      (stageEvent actTick groups g₂ c₂ j) := by
    rw [h_ev_log, h_tick_log]; exact hAD
  have h_mb_log : MiddleBlockOk groups actTick T
      (w_log.events.filter (fun e => e.targetTick == w_log.tick))
      g₁ c₁ g₂ c₂ j := by
    rw [h_ev_log, h_tick_log]; exact h_mb
  have h_sA_absent_log :
      stageEvent actTick groups g₁ c₁ (j + 1) ∉ w_log.events := by
    rwa [h_ev_log]
  have h_sD_absent_log :
      stageEvent actTick groups g₂ c₂ (j + 1) ∉ w_log.events := by
    rwa [h_ev_log]
  -- tick of W_B
  have h_tick_WB : W_B.tick = w.tick := by
    dsimp [W_B]; rw [gSimBurst_tick, h_tick_log]
  -- apply MiddleBlockOk_step_gSimBurst on w_log
  have h_mb_burst : MiddleBlockOk groups actTick T W_B.events
      g₁ c₁ g₂ c₂ (j + 1) :=
    MiddleBlockOk_step_gSimBurst groups actTick T w.tick obsAll withinOrd pos
      w_log active.zipIdx g₁ c₁ g₂ c₂ j
      h_g₁ h_c₁ h_g₂ h_c₂ h_layout_log h_j_ge h_j₁ h_j₂
      (by rw [h_tick_log]; exact h_due)
      h_tgt₂ hA_mem_log hD_mem_log h_nodup_log hAD_log h_mb_log
      h_stage_log h_sA_absent_log h_sD_absent_log h_nd_burst
  -- stage-(j+1) events are non-due in W_B
  set sA₁ := stageEvent actTick groups g₁ c₁ (j + 1)
  set sD₁ := stageEvent actTick groups g₂ c₂ (j + 1)
  have h_j₁' : j ≤ (chainAt groups g₁ c₁).middleDelays.length := by omega
  have h_sA_nd : sA₁.targetTick ≠ W_B.tick := by
    rw [h_tick_WB, h_due]
    dsimp [sA₁, stageEvent]
    exact (stageTarget_lt_succ actTick groups g₁ c₁ j h_j₁').ne'
  have h_sD_nd : sD₁.targetTick ≠ W_B.tick := by
    rw [h_tick_WB, h_due, ← h_tgt₂]
    dsimp [sD₁, stageEvent]
    exact (stageTarget_lt_succ actTick groups g₂ c₂ j (by omega)).ne'
  -- carry through stepUntilNextTick
  exact MiddleBlockOk_carry_stepUntilNextTick' groups actTick T W_B
    g₁ c₁ g₂ c₂ (j + 1) h_mb_burst h_surv_A h_surv_D h_sA_nd h_sD_nd
    h_nd_post

/-! ## gSimFoldl base case -/

/-- At stage 0 right after group activation, the middle-block invariant
    holds vacuously. The observer events carry priority 0, so no event
    between two of them carries priority -3. -/
theorem MiddleBlockOk_gSimFoldl_stage0 (groups : List GroupSpec)
    (actTick : Nat → Nat) (T : Nat)
    (w : World) (observers : List Nat) (gi c₁ c₂ : Nat)
    (h_absent : stageEvent actTick groups gi c₁ 0 ∉ w.events) :
    MiddleBlockOk groups actTick T (activateGroup w observers).events
      gi c₁ gi c₂ 0 :=
  MiddleBlockOk_activateGroup groups actTick T w observers gi c₁ c₂ h_absent
