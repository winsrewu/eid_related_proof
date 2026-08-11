import BasicProofs.GroupClustering.MiddleBlockOkTicks

open BasicRedstoneSim List

/-! # Group clustering — unified gSimBody step and foldl iteration

This file unifies the idle and burst branches of MiddleBlockOkTicks into a single
`gSimBody` step lemma. It then iterates that step across pop ticks to
carry the middle-block invariant from stage 0 to any stage `j`.

Main results:

* `MiddleBlockOk_gSimBody_step`: one `gSimBody` tick advances the
  middle-block invariant from stage `j` to stage `j + 1`, regardless
  of whether groups activate.

* `MiddleBlockOk_gSimBody_carry`: at a non-pop tick, one `gSimBody`
  call preserves the middle-block invariant at the current stage.
-/

/-! ## Private helpers -/

/-- A list of length zero is empty. -/
private theorem list_nil_of_length_zero'' {α : Type} (l : List α)
    (h : l.length = 0) : l = [] := by
  cases l with
  | nil => rfl
  | cons _ _ => simp at h

/-- Erasing an in-range element removes exactly one position. -/
private theorem length_eraseIdx_of_lt'' {α : Type} (l : List α) (i : Nat)
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
private theorem filter_eq_self_of_forall''' {α : Type} (p : α → Bool)
    (l : List α) (h : ∀ x ∈ l, p x = true) : l.filter p = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have h_x := h x (List.mem_cons.mpr (Or.inl rfl))
    simp [List.filter, h_x,
      ih (fun y hy => h y (List.mem_cons.mpr (Or.inr hy)))]

/-- One pop removes the popped event from the due filter. -/
private theorem due_tail_eq_eraseIdx'' (w : World) (ev₀ : ScheduledEvent)
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
private theorem drain_due_filter'' (w : World) :
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
      apply list_nil_of_length_zero''
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
            obtain ⟨j, hj, h_eq⟩ := due_tail_eq_eraseIdx'' w ev₀ w_pop h_pop
            rw [h_tick, h_eq, length_eraseIdx_of_lt'' _ _ hj]
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
private theorem evBefore_restrict_left'' {l r : List ScheduledEvent}
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

/-! ## General carry lemma: survivors ++ new events

If the post-tick queue is the non-due survivors of the pre-tick queue
followed by new events, and the reference events are non-due survivors,
then MiddleBlockOk carries through. -/

/-- MiddleBlockOk carries from `w.events` to any queue of the form
    `survivors ++ new` where survivors are the non-due events of
    `w.events`. The reference events must be non-due. -/
private theorem MiddleBlockOk_carry_survivors_append
    (groups : List GroupSpec) (actTick : Nat → Nat) (T : Nat)
    (w : World) (new : List ScheduledEvent) (g₁ c₁ g₂ c₂ j : Nat)
    (h_mb : MiddleBlockOk groups actTick T w.events g₁ c₁ g₂ c₂ j)
    (hA_mem : stageEvent actTick groups g₁ c₁ j ∈ w.events)
    (hD_mem : stageEvent actTick groups g₂ c₂ j ∈ w.events)
    (hA_nd : (stageEvent actTick groups g₁ c₁ j).targetTick ≠ w.tick)
    (hD_nd : (stageEvent actTick groups g₂ c₂ j).targetTick ≠ w.tick)
    (q : List ScheduledEvent)
    (h_q : q = w.events.filter (fun ev => ev.targetTick ≠ w.tick) ++ new)
    (h_nd : q.Nodup) :
    MiddleBlockOk groups actTick T q g₁ c₁ g₂ c₂ j := by
  set sA := stageEvent actTick groups g₁ c₁ j
  set sD := stageEvent actTick groups g₂ c₂ j
  set survivors := w.events.filter (fun ev => ev.targetTick ≠ w.tick)
  have h_sA_surv : sA ∈ survivors := by
    rw [List.mem_filter]
    exact ⟨hA_mem, decide_eq_true_eq.mpr hA_nd⟩
  have h_sD_surv : sD ∈ survivors := by
    rw [List.mem_filter]
    exact ⟨hD_mem, decide_eq_true_eq.mpr hD_nd⟩
  have h_nd_app : (survivors ++ new).Nodup := by
    rw [← h_q]; exact h_nd
  intro e h_b1 h_b2 h_pri h_tgt
  rw [h_q] at h_b1 h_b2
  -- any e between sA and sD in survivors ++ new is a survivor
  have h_e_surv : e ∈ survivors := by
    have h_e_mem : e ∈ survivors ++ new := evBefore.mem_left h_b2
    rw [List.mem_append] at h_e_mem
    rcases h_e_mem with h_e_s | h_e_sp
    · exact h_e_s
    · exfalso
      have h_sD_before_e : evBefore (survivors ++ new) sD e :=
        evBefore.of_mem_append h_sD_surv h_e_sp
      exact evBefore.asymm h_nd_app h_b2 h_sD_before_e
  -- restrict evBefore to survivors
  have h_b1_s : evBefore survivors sA e :=
    evBefore_restrict_left'' h_b1 h_sA_surv h_e_surv h_nd_app
  have h_b2_s : evBefore survivors e sD :=
    evBefore_restrict_left'' h_b2 h_e_surv h_sD_surv h_nd_app
  -- transfer evBefore from survivors to w.events via filter
  set pTick : ScheduledEvent → Bool :=
    fun ev => decide (ev.targetTick ≠ w.tick)
  have h_b1_full : evBefore w.events sA e :=
    evBefore.of_filter pTick h_b1_s
  have h_b2_full : evBefore w.events e sD :=
    evBefore.of_filter pTick h_b2_s
  exact h_mb e h_b1_full h_b2_full h_pri h_tgt

/-! ## Non-due filter of gSimBurst -/

/-- The non-due filter of the post-burst queue is the original non-due
    events followed by some list of new events. -/
private theorem gSimBurst_filter_notDue_split
    (t : Nat) (obsAll : List (List Nat))
    (withinOrd pos : Nat → List Nat)
    (w : World) (pairs : List (Nat × Nat)) :
    ∃ newEvts : List ScheduledEvent,
      (gSimBurst t obsAll withinOrd pos w pairs).events.filter
        (fun ev => ev.targetTick ≠ w.tick) =
      w.events.filter (fun ev => ev.targetTick ≠ w.tick) ++ newEvts := by
  induction pairs generalizing w with
  | nil =>
    refine ⟨[], ?_⟩
    simp [gSimBurst]
  | cons p ps ih =>
    simp only [gSimBurst, List.foldl_cons]
    rcases p with ⟨gi, k⟩
    set m := (pos t)[k]?.getD 0
    set ordered : List Nat := (withinOrd gi).foldl (fun acc ci =>
      match (obsAll[gi]?.getD [])[ci]? with
      | some oid => acc ++ [oid]
      | none => acc) []
    set Wproc := processNEvents w m
    set W₁ := activateGroup Wproc ordered
    -- non-due filter of Wproc
    have h_proc_split :
        Wproc.events.filter (fun ev => ev.targetTick ≠ w.tick) =
        w.events.filter (fun ev => ev.targetTick ≠ w.tick) ++
          World.popSpawnAcc w m := by
      dsimp [Wproc]
      rw [processNEvents_eq_popSeqWorldFuel]
      exact (World.popSeqWorldFuel_filter_split w m).1
    -- tick of Wproc
    have h_tick_Wproc : Wproc.tick = w.tick := by
      dsimp [Wproc]; rw [processNEvents_tick]
    -- tick of W₁
    have h_tick_W₁ : W₁.tick = w.tick := by
      dsimp [W₁]; rw [activateGroup_tick, h_tick_Wproc]
    -- observer events are non-due
    set obsEvts := ordered.map (fun nid =>
      ({ targetTick := Wproc.tick + 2, priority := 0,
          nodeId := nid } : ScheduledEvent))
    have h_obs_nd : ∀ ev ∈ obsEvts, decide (ev.targetTick ≠ w.tick) = true := by
      intro ev h_ev
      dsimp [obsEvts] at h_ev
      rw [List.mem_map] at h_ev
      obtain ⟨nid, _, h_ev_eq⟩ := h_ev
      subst h_ev_eq
      rw [h_tick_Wproc]
      simp
    -- non-due filter of W₁
    have h_act_split :
        W₁.events.filter (fun ev => ev.targetTick ≠ w.tick) =
        Wproc.events.filter (fun ev => ev.targetTick ≠ w.tick) ++
          obsEvts := by
      dsimp [W₁]
      rw [activateGroup_events_map]
      rw [List.filter_append]
      have h_keep : obsEvts.filter (fun ev => ev.targetTick ≠ w.tick) =
          obsEvts := by
        apply filter_eq_self_of_forall'''
        exact h_obs_nd
      rw [h_keep]
    -- combine proc and activate splits
    have h_combined :
        W₁.events.filter (fun ev => ev.targetTick ≠ w.tick) =
        w.events.filter (fun ev => ev.targetTick ≠ w.tick) ++
          (World.popSpawnAcc w m ++ obsEvts) := by
      rw [h_act_split, h_proc_split]
      rw [List.append_assoc]
    -- apply IH to W₁
    obtain ⟨newRest, h_ih⟩ := ih W₁
    -- IH says: filter (≠ W₁.tick) ... = filter (≠ W₁.tick) ... ++ newRest
    -- rewrite W₁.tick = w.tick using simpa
    have h_ih' : (gSimBurst t obsAll withinOrd pos W₁ ps).events.filter
        (fun ev => ev.targetTick ≠ w.tick) =
        W₁.events.filter (fun ev => ev.targetTick ≠ w.tick) ++ newRest := by
      simpa [h_tick_W₁] using h_ih
    -- substitute h_combined into the RHS of h_ih'
    have h_full : (gSimBurst t obsAll withinOrd pos W₁ ps).events.filter
        (fun ev => ev.targetTick ≠ w.tick) =
        w.events.filter (fun ev => ev.targetTick ≠ w.tick) ++
          ((World.popSpawnAcc w m ++ obsEvts) ++ newRest) := by
      rw [h_ih', h_combined]
      rw [List.append_assoc]
    -- use h_full to provide the witness
    exact ⟨(World.popSpawnAcc w m ++ obsEvts) ++ newRest, h_full⟩

/-! ## Unified gSimBody step -/

/-- One `gSimBody` tick advances the middle-block invariant from stage
    `j` to stage `j + 1`, regardless of whether groups activate. This
    unifies the idle and burst branches of MiddleBlockOkTicks. -/
theorem MiddleBlockOk_gSimBody_step (groups : List GroupSpec)
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
          active.zipIdx).events) :
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
  · -- burst branch
    exact MiddleBlockOk_gSimBody_step_burst groups actTick T obsAll groupOrd
      withinOrd pos w i g₁ c₁ g₂ c₂ j
      h_g₁ h_c₁ h_g₂ h_c₂ h_layout h_j_ge h_j₁ h_j₂
      h_due h_tgt₂ hA_mem hD_mem h_nodup hAD h_mb h_stage
      h_sA_absent h_sD_absent h_active h_nd_burst h_surv_A h_surv_D
      h_nd_post

/-! ## Carry through gSimBody at a non-pop tick -/

/-- At a non-pop tick, one `gSimBody` call preserves the middle-block
    invariant at the current stage. Both reference events target a
    future tick and survive through the body. -/
theorem MiddleBlockOk_gSimBody_carry (groups : List GroupSpec)
    (actTick : Nat → Nat) (T : Nat)
    (obsAll : List (List Nat)) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat)
    (w : World) (i : Nat) (g₁ c₁ g₂ c₂ j : Nat)
    (h_mb : MiddleBlockOk groups actTick T w.events g₁ c₁ g₂ c₂ j)
    (hA_mem : stageEvent actTick groups g₁ c₁ j ∈ w.events)
    (hD_mem : stageEvent actTick groups g₂ c₂ j ∈ w.events)
    (hA_nd : (stageEvent actTick groups g₁ c₁ j).targetTick ≠ w.tick)
    (hD_nd : (stageEvent actTick groups g₂ c₂ j).targetTick ≠ w.tick)
    (h_nd_post :
        (gSimBody actTick obsAll groupOrd withinOrd pos w i).events.Nodup) :
    MiddleBlockOk groups actTick T
      (gSimBody actTick obsAll groupOrd withinOrd pos w i).events
      g₁ c₁ g₂ c₂ j := by
  set w_log := w.logOutput s!"tick {w.tick}"
  set active := groupOrd.filter (fun gi =>
    decide (gi < obsAll.length) && (actTick gi == w.tick))
  set sA := stageEvent actTick groups g₁ c₁ j
  set sD := stageEvent actTick groups g₂ c₂ j
  have h_ev_log : w_log.events = w.events := by simp [w_log]
  have h_tick_log : w_log.tick = w.tick := by simp [w_log]
  -- the active list in gSimBody matches our active
  have h_active_eq :
      groupOrd.filter (fun gi =>
        decide (gi < obsAll.length) && (actTick gi == w_log.tick)) =
      active := by
    rw [h_tick_log]
  set survivors := w.events.filter (fun ev => ev.targetTick ≠ w.tick)
  -- case split on active
  by_cases h_idle : active = []
  · -- idle branch: gSimBody = w_log.stepUntilNextTick
    have h_body : gSimBody actTick obsAll groupOrd withinOrd pos w i =
        w_log.stepUntilNextTick := by
      dsimp only [gSimBody, w_log, active]
      rw [World.logOutput_tick]
      have h_cond_true :
          (filter (fun gi => decide (gi < obsAll.length) && actTick gi == w.tick)
            groupOrd == []) = true := by
        change (active == []) = true
        rw [h_idle]
        rfl
      rw [h_cond_true]
      rfl
    rw [h_body] at h_nd_post
    rw [h_body]
    -- stepUntilNextTick.events = survivors ++ spawns
    set due := w_log.events.filter (fun e => e.targetTick == w_log.tick)
    set n := due.length
    set W := processNEvents w_log n
    have h_drain : W.events.filter (fun ev => ev.targetTick == w_log.tick) = [] :=
      drain_due_filter'' w_log
    have h_no : ∀ ev ∈ W.events, ev.targetTick ≠ W.tick := by
      intro ev h_ev h_eq
      have h_mem : ev ∈ W.events.filter (fun e => e.targetTick == w_log.tick) := by
        rw [List.mem_filter]
        exact ⟨h_ev, by
          rw [processNEvents_tick] at h_eq
          rw [h_eq]
          simp⟩
      rw [h_drain] at h_mem
      cases h_mem
    have h_pop_none : W.popNextEvent = none :=
      World.popNextEvent_none_of_no_due W h_no
    have h_step_none : W.step = none := by simp only [World.step, h_pop_none]
    have h_sunt : w_log.stepUntilNextTick.events = W.events := by
      rw [← processNEvents_stepUntilNextTick_eq w_log n,
        stepUntilNextTick_of_step_none W h_step_none]
    have h_split : W.events =
        w_log.events.filter (fun ev => ev.targetTick ≠ w_log.tick) ++
          World.popSpawnAcc w_log n := by
      have h_f := (World.popSeqWorldFuel_filter_split w_log n).1
      rw [← processNEvents_eq_popSeqWorldFuel] at h_f
      have h_keep : W.events.filter (fun ev => ev.targetTick ≠ w_log.tick) =
          W.events := by
        apply filter_eq_self_of_forall'''
        intro ev h_ev
        have h_ne : ev.targetTick ≠ w_log.tick := by
          have h := h_no ev h_ev
          rwa [processNEvents_tick] at h
        rw [decide_eq_true_eq]; exact h_ne
      rw [← h_keep]; exact h_f
    rw [h_ev_log, h_tick_log] at h_split
    -- apply the general carry lemma
    exact MiddleBlockOk_carry_survivors_append groups actTick T w
      (World.popSpawnAcc w_log n) g₁ c₁ g₂ c₂ j
      h_mb hA_mem hD_mem hA_nd hD_nd
      w_log.stepUntilNextTick.events
      (by rw [h_sunt, h_split])
      h_nd_post
  · -- burst branch: gSimBody = W_B.stepUntilNextTick
    set W_B := gSimBurst w.tick obsAll withinOrd pos w_log active.zipIdx
    have h_body : gSimBody actTick obsAll groupOrd withinOrd pos w i =
        W_B.stepUntilNextTick := by
      dsimp only [gSimBody, W_B, w_log, active]
      rw [World.logOutput_tick]
      split_ifs with h_cond
      · exfalso
        apply h_idle
        change (active == []) = true at h_cond
        have h_eq : active = [] := by simpa using h_cond
        exact h_eq
      · rfl
    rw [h_body] at h_nd_post
    rw [h_body]
    have h_tick_WB : W_B.tick = w.tick := by
      dsimp [W_B]; rw [gSimBurst_tick, h_tick_log]
    -- non-due filter of W_B
    obtain ⟨burstNew, h_filter_WB⟩ :=
      gSimBurst_filter_notDue_split w.tick obsAll withinOrd pos w_log
        active.zipIdx
    have h_filter_WB' : W_B.events.filter
        (fun ev => ev.targetTick ≠ w.tick) =
        w.events.filter (fun ev => ev.targetTick ≠ w.tick) ++ burstNew := by
      rw [h_ev_log, h_tick_log] at h_filter_WB
      exact h_filter_WB
    -- stepUntilNextTick of W_B drains all due events
    set due_B := W_B.events.filter (fun e => e.targetTick == W_B.tick)
    set n_B := due_B.length
    set W_final := processNEvents W_B n_B
    have h_drain_B :
        W_final.events.filter (fun ev => ev.targetTick == W_B.tick) = [] :=
      drain_due_filter'' W_B
    have h_no_B : ∀ ev ∈ W_final.events, ev.targetTick ≠ W_final.tick := by
      intro ev h_ev h_eq
      have h_mem : ev ∈ W_final.events.filter
          (fun e => e.targetTick == W_B.tick) := by
        rw [List.mem_filter]
        exact ⟨h_ev, by
          rw [processNEvents_tick] at h_eq
          rw [h_eq]
          simp⟩
      rw [h_drain_B] at h_mem
      cases h_mem
    have h_pop_none_B : W_final.popNextEvent = none :=
      World.popNextEvent_none_of_no_due W_final h_no_B
    have h_step_none_B : W_final.step = none := by
      simp only [World.step, h_pop_none_B]
    have h_sunt_B : W_B.stepUntilNextTick.events = W_final.events := by
      rw [← processNEvents_stepUntilNextTick_eq W_B n_B,
        stepUntilNextTick_of_step_none W_final h_step_none_B]
    have h_split_B : W_final.events =
        W_B.events.filter (fun ev => ev.targetTick ≠ w.tick) ++
          World.popSpawnAcc W_B n_B := by
      have h_f := (World.popSeqWorldFuel_filter_split W_B n_B).1
      rw [← processNEvents_eq_popSeqWorldFuel] at h_f
      rw [h_tick_WB] at h_f
      have h_keep :
          W_final.events.filter (fun ev => ev.targetTick ≠ w.tick) =
          W_final.events := by
        apply filter_eq_self_of_forall'''
        intro ev h_ev
        have h_ne₁ : ev.targetTick ≠ W_final.tick := h_no_B ev h_ev
        have h_ne₂ : ev.targetTick ≠ W_B.tick := by
          rwa [processNEvents_tick] at h_ne₁
        rw [h_tick_WB] at h_ne₂
        rw [decide_eq_true_eq]
        exact h_ne₂
      rw [← h_keep]; exact h_f
    -- combine: final queue = survivors ++ burstNew ++ stepUntilNextTick spawns
    have h_final : W_B.stepUntilNextTick.events =
        survivors ++ (burstNew ++ World.popSpawnAcc W_B n_B) := by
      rw [h_sunt_B, h_split_B, h_filter_WB']
      rw [List.append_assoc]
    -- apply the general carry lemma
    exact MiddleBlockOk_carry_survivors_append groups actTick T w
      (burstNew ++ World.popSpawnAcc W_B n_B) g₁ c₁ g₂ c₂ j
      h_mb hA_mem hD_mem hA_nd hD_nd
      W_B.stepUntilNextTick.events
      h_final h_nd_post
