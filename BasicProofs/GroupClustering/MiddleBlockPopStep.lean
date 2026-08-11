import BasicProofs.GroupClustering.ConverseSpawn


open BasicRedstoneSim List

/-! # Group clustering — the middle-block step at a pop tick

The middle-block invariant holds at stage `j` before the pop tick. This
file moves it to stage `j + 1` after the tick.

Take an event between the two spawned reference events in the next
queue. ConverseSpawn identifies it as the stage-`j + 1` event of some chain.
The stage-`j` event of that chain sits between the two reference events
in the due filter. The stage-`j` invariant classifies it. MiddleBlockInvariant lifts
the classification to stage `j + 1`.

The theorem takes one premise beyond the premises of the ConverseSpawn
converse fact: the next queue is duplicate-free. The converse fact
needs the classified event to be absent from `w.events`. A survivor of
the tick sits before every spawn of the tick. A survivor that also
appears in the spawn block sits on both sides of the first spawned
reference event. A duplicate-free next queue rules that out.
-/

/-! ## List and queue helpers -/

/-- A list of length zero is empty. -/
private theorem list_nil_of_length_zero {α : Type} (l : List α)
    (h : l.length = 0) : l = [] := by
  cases l with
  | nil => rfl
  | cons _ _ => simp at h

/-- Erasing an in-range element removes exactly one position. -/
private theorem length_eraseIdx_of_lt {α : Type} (l : List α) (i : Nat)
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
private theorem filter_eq_self_of_forall' {α : Type} (p : α → Bool)
    (l : List α) (h : ∀ x ∈ l, p x = true) : l.filter p = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have h_x := h x (List.mem_cons.mpr (Or.inl rfl))
    simp [List.filter, h_x,
      ih (fun y hy => h y (List.mem_cons.mpr (Or.inr hy)))]

/-- One pop removes the popped event from the due filter. -/
private theorem due_tail_eq_eraseIdx (w : World) (ev₀ : ScheduledEvent)
    (w_pop : World) (h_pop : w.popNextEvent = some (ev₀, w_pop)) :
    ∃ j, j < (w.events.filter (fun e => e.targetTick == w.tick)).length ∧
      (w_pop.onScheduledTick ev₀.nodeId).events.filter
          (fun e => e.targetTick == w.tick) =
        (w.events.filter (fun e => e.targetTick == w.tick)).eraseIdx j := by
  obtain ⟨idx, h_idx, h_erase, h_tick_ev, _, h_get⟩ :=
    World.popNextEvent_eraseIdx w ev₀ w_pop h_pop
  set due := w.events.filter (fun e => e.targetTick == w.tick)
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
      apply list_nil_of_length_zero
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
            obtain ⟨j, hj, h_eq⟩ := due_tail_eq_eraseIdx w ev₀ w_pop h_pop
            rw [h_tick, h_eq, length_eraseIdx_of_lt _ _ hj]
            omega
          have h_tick_w' : w'.tick = w.tick := by
            rw [← h_w', World.onScheduledTick_tick,
              World.popNextEvent_tick w ev₀ w_pop h_pop]
          rw [← h_tick_w']
          exact ih w' h_len'
  exact h_gen w _ (by omega)

/-! ## The middle-block induction step -/

/-- At the pop tick of middle stage `j`, the middle-block invariant
    steps from stage `j` to stage `j + 1`. Stage `j + 1` is a middle
    stage of both reference chains. The stage-`j` invariant acts on the
    due filter of `w.events`. The conclusion acts on
    `w.stepUntilNextTick.events`. The post-tick queue is
    duplicate-free. That premise keeps survivors out of the spawn
    block. A survivor sits before every spawn, and a second copy in
    the spawn block sits on both sides of the first spawned reference
    event. -/
theorem MiddleBlockOk_step_stepUntilNextTick (groups : List GroupSpec)
    (actTick : Nat → Nat) (T : Nat) (w : World) (g₁ c₁ g₂ c₂ j : Nat)
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
        (w.events.filter (fun e => e.targetTick == w.tick)) g₁ c₁ g₂ c₂ j)
    (h_stage : StageMemAt groups actTick w w.tick)
    (h_sA_absent : stageEvent actTick groups g₁ c₁ (j + 1) ∉ w.events)
    (h_sD_absent : stageEvent actTick groups g₂ c₂ (j + 1) ∉ w.events)
    (h_nd_post : (w.stepUntilNextTick.events).Nodup) :
    MiddleBlockOk groups actTick T w.stepUntilNextTick.events
      g₁ c₁ g₂ c₂ (j + 1) := by
  dsimp [MiddleBlockOk]
  set sA := stageEvent actTick groups g₁ c₁ (j + 1)
  set sD := stageEvent actTick groups g₂ c₂ (j + 1)
  set due := w.events.filter (fun ev => ev.targetTick == w.tick)
  intro e h_b1 h_b2 h_pri h_tgt
  have h_j₁' : j ≤ (chainAt groups g₁ c₁).middleDelays.length := by omega
  -- e targets a tick after the tick of w
  have h_e_nd : e.targetTick ≠ w.tick := by
    rw [h_tgt, h_due]
    exact (stageTarget_lt_succ actTick groups g₁ c₁ j h_j₁').ne'
  -- drain the tick and split the next queue into survivors and spawns
  set n := due.length
  set W := processNEvents w n
  have h_drain : W.events.filter (fun ev => ev.targetTick == w.tick) = [] :=
    drain_due_filter' w
  have h_no : ∀ ev ∈ W.events, ev.targetTick ≠ W.tick := by
    intro ev h_ev h_eq
    have h_mem : ev ∈ W.events.filter (fun e => e.targetTick == w.tick) := by
      rw [List.mem_filter]
      exact ⟨h_ev, by
        rw [processNEvents_tick] at h_eq
        rw [h_eq]
        simp⟩
    rw [h_drain] at h_mem
    cases h_mem
  have h_post_events : w.stepUntilNextTick.events = W.events := by
    have h_pop_none : W.popNextEvent = none :=
      World.popNextEvent_none_of_no_due W h_no
    have h_step_none : W.step = none := by
      simp only [World.step, h_pop_none]
    rw [← processNEvents_stepUntilNextTick_eq w n,
      stepUntilNextTick_of_step_none W h_step_none]
  have h_split : W.events =
      w.events.filter (fun ev => ev.targetTick ≠ w.tick) ++
        World.popSpawnAcc w n := by
    have h_f := (World.popSeqWorldFuel_filter_split w n).1
    rw [← processNEvents_eq_popSeqWorldFuel] at h_f
    have h_keep : W.events.filter (fun ev => ev.targetTick ≠ w.tick) =
        W.events := by
      apply filter_eq_self_of_forall'
      intro ev h_ev
      have h_ne : ev.targetTick ≠ w.tick := by
        have h := h_no ev h_ev
        rwa [processNEvents_tick] at h
      rw [decide_eq_true_eq]
      exact h_ne
    rw [← h_keep]
    exact h_f
  have h_nd_W : W.events.Nodup := by rwa [← h_post_events]
  -- e is not an old event: a survivor sits before sA, and h_b1 puts
  -- sA before e
  have h_e_absent : e ∉ w.events := by
    by_contra h_e_w
    have h_e_surv :
        e ∈ w.events.filter (fun ev => ev.targetTick ≠ w.tick) := by
      rw [List.mem_filter]
      exact ⟨h_e_w, by
        rw [decide_eq_true_eq]
        exact h_e_nd⟩
    have h_sA_W : sA ∈ W.events := by
      rw [← h_post_events]
      exact evBefore.mem_left h_b1
    have h_sA_sp : sA ∈ World.popSpawnAcc w n := by
      rw [h_split, List.mem_append] at h_sA_W
      rcases h_sA_W with h_sA_surv | h_sA_sp
      · exact absurd (List.mem_filter.mp h_sA_surv).1 h_sA_absent
      · exact h_sA_sp
    have h_b1_W : evBefore W.events sA e := by rwa [← h_post_events]
    have h_b_es : evBefore W.events e sA := by
      rw [h_split]
      exact evBefore.of_mem_append h_e_surv h_sA_sp
    exact evBefore.asymm h_nd_W h_b1_W h_b_es
  -- the converse spawn-origin fact identifies e and its stage-j parent
  obtain ⟨g, c, h_g, h_c, h_e_eq, hAC, hCD⟩ :=
    converse_spawn_stepUntilNextTick groups actTick T w g₁ c₁ g₂ c₂ j
      h_g₁ h_c₁ h_g₂ h_c₂ h_layout h_j₁' (by omega) h_j_ge h_due h_tgt₂
      hA_mem hD_mem h_nodup hAD h_mb h_stage h_sA_absent h_sD_absent
      e h_e_absent h_b1 h_b2 h_tgt
  set C := stageEvent actTick groups g c j
  -- the parent sits in the due filter, so it targets the tick of w
  have hC_due : C ∈ due := evBefore.mem_left hCD
  have hC_tick : C.targetTick = w.tick := by
    simpa [Nat.beq_eq] using (List.mem_filter.mp hC_due).2
  -- the parent is a middle-stage event
  have h_e_pri' : (stageEvent actTick groups g c (j + 1)).priority =
      (-3 : Int) := by
    rw [← h_e_eq]
    exact h_pri
  have h_j_gc : j < (chainAt groups g c).middleDelays.length := by
    dsimp [stageEvent, stagePri] at h_e_pri'
    split_ifs at h_e_pri' <;> omega
  have hC_pri : C.priority = (-3 : Int) := by
    dsimp [C, stageEvent]
    exact stagePri_middle groups g c j h_j_ge (by omega)
  -- the stage-j invariant classifies the parent
  have h_mb_C : MiddleBlock groups actTick T g₁ c₁ j C :=
    h_mb C hAC hCD hC_pri (by rw [hC_tick, h_due])
  -- lift the classification to stage j + 1
  have h_tgt_succ : stageTarget actTick groups g c (j + 1) =
      stageTarget actTick groups g₁ c₁ (j + 1) := by
    have h := congr_arg ScheduledEvent.targetTick h_e_eq
    dsimp [stageEvent] at h
    exact h.symm.trans h_tgt
  have h_lift : MiddleBlock groups actTick T g₁ c₁ (j + 1)
      (stageEvent actTick groups g c (j + 1)) :=
    MiddleBlock_step_middle groups actTick T g₁ c₁ g c j h_g h_c h_j_gc
      (by omega) h_mb_C h_tgt_succ
  rw [h_e_eq]
  exact h_lift

/-- The middle-block invariant steps from stage `j` to stage `j + 1`
    after processing `n` events. The post-tick queue is
    duplicate-free. This keeps survivors out of the spawn block. -/
theorem MiddleBlockOk_step_processNEvents (groups : List GroupSpec)
    (actTick : Nat → Nat) (T : Nat) (w : World) (n : Nat)
    (g₁ c₁ g₂ c₂ j : Nat)
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
        (w.events.filter (fun e => e.targetTick == w.tick)) g₁ c₁ g₂ c₂ j)
    (h_stage : StageMemAt groups actTick w w.tick)
    (h_sA_absent : stageEvent actTick groups g₁ c₁ (j + 1) ∉ w.events)
    (h_sD_absent : stageEvent actTick groups g₂ c₂ (j + 1) ∉ w.events)
    (h_nd_post : (processNEvents w n).events.Nodup) :
    MiddleBlockOk groups actTick T (processNEvents w n).events
      g₁ c₁ g₂ c₂ (j + 1) := by
  dsimp [MiddleBlockOk]
  set sA := stageEvent actTick groups g₁ c₁ (j + 1)
  set sD := stageEvent actTick groups g₂ c₂ (j + 1)
  set due := w.events.filter (fun ev => ev.targetTick == w.tick)
  set W := processNEvents w n
  intro e h_b1 h_b2 h_pri h_tgt
  have h_j₁' : j ≤ (chainAt groups g₁ c₁).middleDelays.length := by omega
  -- e targets a tick after the tick of w
  have h_e_nd : e.targetTick ≠ w.tick := by
    rw [h_tgt, h_due]
    exact (stageTarget_lt_succ actTick groups g₁ c₁ j h_j₁').ne'
  -- sA misses the tick of w
  have h_sA_nd : sA.targetTick ≠ w.tick := by
    dsimp [sA, stageEvent]
    rw [h_due]
    exact (stageTarget_lt_succ actTick groups g₁ c₁ j h_j₁').ne'
  -- filtered split: survivors ++ spawns
  have h_split : W.events.filter (fun ev => ev.targetTick ≠ w.tick) =
      w.events.filter (fun ev => ev.targetTick ≠ w.tick) ++
        World.popSpawnAcc w n := by
    have h_f := (World.popSeqWorldFuel_filter_split w n).1
    rw [← processNEvents_eq_popSeqWorldFuel] at h_f
    exact h_f
  -- the filtered queue is duplicate-free
  have h_nd_filt : (W.events.filter
      (fun ev => ev.targetTick ≠ w.tick)).Nodup :=
    List.Nodup.filter _ h_nd_post
  -- e is not an old event
  have h_e_absent : e ∉ w.events := by
    by_contra h_e_w
    have h_e_surv :
        e ∈ w.events.filter (fun ev => ev.targetTick ≠ w.tick) := by
      rw [List.mem_filter]
      exact ⟨h_e_w, by rw [decide_eq_true_eq]; exact h_e_nd⟩
    have h_sA_W : sA ∈ W.events := evBefore.mem_left h_b1
    have h_sA_filt : sA ∈ W.events.filter
        (fun ev => ev.targetTick ≠ w.tick) := by
      rw [List.mem_filter]
      exact ⟨h_sA_W, by rw [decide_eq_true_eq]; exact h_sA_nd⟩
    rw [h_split] at h_sA_filt
    have h_sA_sp : sA ∈ World.popSpawnAcc w n := by
      rw [List.mem_append] at h_sA_filt
      rcases h_sA_filt with h_sA_surv | h_sA_sp
      · exact absurd (List.mem_filter.mp h_sA_surv).1 h_sA_absent
      · exact h_sA_sp
    -- sA before e in the filtered queue (from h_b1)
    have h_b1_f : evBefore
        (W.events.filter (fun ev => ev.targetTick ≠ w.tick)) sA e :=
      evBefore.filter (fun ev => ev.targetTick ≠ w.tick)
        (by rw [decide_eq_true_eq]; exact h_sA_nd)
        (by rw [decide_eq_true_eq]; exact h_e_nd) h_b1
    rw [h_split] at h_b1_f
    -- e before sA in the filtered queue (survivor before spawn)
    have h_b_es : evBefore
        (w.events.filter (fun ev => ev.targetTick ≠ w.tick) ++
          World.popSpawnAcc w n) e sA :=
      evBefore.of_mem_append h_e_surv h_sA_sp
    -- contradiction: both orders on a duplicate-free list
    have h_nd_ss :
        (w.events.filter (fun ev => ev.targetTick ≠ w.tick) ++
          World.popSpawnAcc w n).Nodup := by
      rw [← h_split]
      exact h_nd_filt
    exact evBefore.asymm h_nd_ss h_b1_f h_b_es
  -- the converse spawn-origin fact identifies e and its stage-j parent
  obtain ⟨g, c, h_g, h_c, h_e_eq, hAC, hCD⟩ :=
    converse_spawn_processNEvents groups actTick T w n g₁ c₁ g₂ c₂ j
      h_g₁ h_c₁ h_g₂ h_c₂ h_layout h_j₁' (by omega) h_j_ge h_due h_tgt₂
      hA_mem hD_mem h_nodup hAD h_mb h_stage h_sA_absent h_sD_absent
      e h_e_absent h_b1 h_b2 h_pri h_tgt
  set C := stageEvent actTick groups g c j
  -- the parent sits in the due filter
  have hC_due : C ∈ due := evBefore.mem_left hCD
  have hC_tick : C.targetTick = w.tick := by
    simpa [Nat.beq_eq] using (List.mem_filter.mp hC_due).2
  -- the parent is a middle-stage event
  have h_e_pri' : (stageEvent actTick groups g c (j + 1)).priority =
      (-3 : Int) := by
    rw [← h_e_eq]
    exact h_pri
  have h_j_gc : j < (chainAt groups g c).middleDelays.length := by
    dsimp [stageEvent, stagePri] at h_e_pri'
    split_ifs at h_e_pri' <;> omega
  have hC_pri : C.priority = (-3 : Int) := by
    dsimp [C, stageEvent]
    exact stagePri_middle groups g c j h_j_ge (by omega)
  -- the stage-j invariant classifies the parent
  have h_mb_C : MiddleBlock groups actTick T g₁ c₁ j C :=
    h_mb C hAC hCD hC_pri (by rw [hC_tick, h_due])
  -- lift the classification to stage j + 1
  have h_tgt_succ : stageTarget actTick groups g c (j + 1) =
      stageTarget actTick groups g₁ c₁ (j + 1) := by
    have h := congr_arg ScheduledEvent.targetTick h_e_eq
    dsimp [stageEvent] at h
    exact h.symm.trans h_tgt
  have h_lift : MiddleBlock groups actTick T g₁ c₁ (j + 1)
      (stageEvent actTick groups g c (j + 1)) :=
    MiddleBlock_step_middle groups actTick T g₁ c₁ g c j h_g h_c h_j_gc
      (by omega) h_mb_C h_tgt_succ
  rw [h_e_eq]
  exact h_lift

/-! ## Helpers for the burst variant -/

/-- If e sits before sA in a world, the relation survives one step of
    processNEvents followed by activateGroup. -/
private theorem gSimBurst_one_step_evBefore
    (w : World) (m : Nat) (ordered : List Nat)
    (e sA : ScheduledEvent)
    (h_eb : evBefore w.events e sA)
    (h_e_nd : e.targetTick ≠ w.tick)
    (h_sA_nd : sA.targetTick ≠ w.tick) :
    evBefore (activateGroup (processNEvents w m) ordered).events e sA := by
  set wProc := processNEvents w m
  set w₁ := activateGroup wProc ordered
  set pTick : ScheduledEvent → Bool :=
    fun ev => decide (ev.targetTick ≠ w.tick)
  -- filtered split
  have h_split : wProc.events.filter pTick =
      w.events.filter pTick ++ World.popSpawnAcc w m := by
    have h_f := (World.popSeqWorldFuel_filter_split w m).1
    rw [← processNEvents_eq_popSeqWorldFuel] at h_f
    exact h_f
  -- evBefore in the filtered list
  have h_eb_f : evBefore (w.events.filter pTick) e sA :=
    evBefore.filter pTick
      (by rw [decide_eq_true_eq]; exact h_e_nd)
      (by rw [decide_eq_true_eq]; exact h_sA_nd) h_eb
  have h_eb_proc_f :
      evBefore (wProc.events.filter pTick) e sA := by
    rw [h_split]
    exact evBefore.append_right h_eb_f
  have h_eb_proc : evBefore wProc.events e sA :=
    evBefore.of_filter pTick h_eb_proc_f
  -- activateGroup appends observer events
  have h_w₁_ev : w₁.events = wProc.events ++
      ordered.map (fun nid =>
        (⟨wProc.tick + 2, 0, nid⟩ : ScheduledEvent)) := by
    dsimp [w₁]
    exact activateGroup_events_map wProc ordered
  rw [h_w₁_ev]
  exact evBefore.append_right h_eb_proc

/-- An evBefore relation in the starting world propagates through a
    full burst. -/
private theorem gSimBurst_evBefore_preserved
    (t : Nat) (obsAll : List (List Nat))
    (withinOrd pos : Nat → List Nat)
    (w : World) (pairs : List (Nat × Nat))
    (e sA : ScheduledEvent)
    (h_eb : evBefore w.events e sA)
    (h_e_nd : e.targetTick ≠ w.tick)
    (h_sA_nd : sA.targetTick ≠ w.tick) :
    evBefore (gSimBurst t obsAll withinOrd pos w pairs).events
      e sA := by
  revert w e sA h_eb h_e_nd h_sA_nd
  induction pairs with
  | nil =>
    intro w e sA h_eb h_e_nd h_sA_nd
    dsimp [gSimBurst]
    exact h_eb
  | cons p ps ih =>
    intro w e sA h_eb h_e_nd h_sA_nd
    rcases p with ⟨gi, k⟩
    dsimp only [gSimBurst, List.foldl_cons]
    set m := (pos t)[k]?.getD 0
    set obs : List Nat := obsAll[gi]?.getD []
    set ordered := (withinOrd gi).foldl (fun acc ci =>
      match obs[ci]? with
      | some oid => acc ++ [oid]
      | none => acc) []
    set wProc := processNEvents w m
    set w₁ := activateGroup wProc ordered
    have h_eb_w₁ : evBefore w₁.events e sA :=
      gSimBurst_one_step_evBefore w m ordered e sA
        h_eb h_e_nd h_sA_nd
    have h_tick_w₁ : w₁.tick = w.tick := by
      dsimp [w₁, wProc]
      rw [activateGroup_tick, processNEvents_tick]
    exact ih w₁ e sA h_eb_w₁
      (by rw [h_tick_w₁]; exact h_e_nd)
      (by rw [h_tick_w₁]; exact h_sA_nd)

/-- A survivor of the original world sits before any event that was not
    in the original world, after a full burst. -/
private theorem gSimBurst_survivor_before_nonmember
    (t : Nat) (obsAll : List (List Nat))
    (withinOrd pos : Nat → List Nat)
    (w : World) (pairs : List (Nat × Nat))
    (e sA : ScheduledEvent)
    (h_e_mem : e ∈ w.events)
    (h_e_nd : e.targetTick ≠ w.tick)
    (h_e_pri : e.priority ≠ (0 : Int))
    (h_sA_absent : sA ∉ w.events)
    (h_sA_mem : sA ∈
        (gSimBurst t obsAll withinOrd pos w pairs).events)
    (h_sA_nd : sA.targetTick ≠ w.tick)
    (h_sA_pri : sA.priority ≠ (0 : Int)) :
    evBefore (gSimBurst t obsAll withinOrd pos w pairs).events
      e sA := by
  revert w e sA h_e_mem h_e_nd h_e_pri h_sA_absent h_sA_mem
    h_sA_nd h_sA_pri
  induction pairs with
  | nil =>
    intro w e sA h_e_mem h_e_nd h_e_pri h_sA_absent h_sA_mem
      h_sA_nd h_sA_pri
    dsimp [gSimBurst] at h_sA_mem
    exact absurd h_sA_mem h_sA_absent
  | cons p ps ih =>
    intro w e sA h_e_mem h_e_nd h_e_pri h_sA_absent h_sA_mem
      h_sA_nd h_sA_pri
    rcases p with ⟨gi, k⟩
    dsimp only [gSimBurst, List.foldl_cons]
    set m := (pos t)[k]?.getD 0
    set obs : List Nat := obsAll[gi]?.getD []
    set ordered := (withinOrd gi).foldl (fun acc ci =>
      match obs[ci]? with
      | some oid => acc ++ [oid]
      | none => acc) []
    set wProc := processNEvents w m
    set w₁ := activateGroup wProc ordered
    set pTick : ScheduledEvent → Bool :=
      fun ev => decide (ev.targetTick ≠ w.tick)
    -- tick preservation
    have h_tick_wProc : wProc.tick = w.tick :=
      processNEvents_tick w m
    have h_tick_w₁ : w₁.tick = w.tick := by
      dsimp [w₁]
      rw [activateGroup_tick, h_tick_wProc]
    -- e survives the step
    have h_e_filt : e ∈ w.events.filter pTick := by
      rw [List.mem_filter]
      exact ⟨h_e_mem, by rw [decide_eq_true_eq]; exact h_e_nd⟩
    have h_split : wProc.events.filter pTick =
        w.events.filter pTick ++ World.popSpawnAcc w m := by
      have h_f := (World.popSeqWorldFuel_filter_split w m).1
      rw [← processNEvents_eq_popSeqWorldFuel] at h_f
      exact h_f
    have h_e_wProc_f : e ∈ wProc.events.filter pTick := by
      rw [h_split]
      exact List.mem_append_left _ h_e_filt
    have h_e_wProc : e ∈ wProc.events :=
      List.mem_of_mem_filter h_e_wProc_f
    have h_e_w₁ : e ∈ w₁.events := by
      have h_w₁_ev : w₁.events = wProc.events ++
          ordered.map (fun nid =>
            (⟨wProc.tick + 2, 0, nid⟩ : ScheduledEvent)) := by
        dsimp [w₁]
        exact activateGroup_events_map wProc ordered
      rw [h_w₁_ev]
      exact List.mem_append_left _ h_e_wProc
    -- case split: is sA in w₁?
    by_cases h_sA_w₁ : sA ∈ w₁.events
    · -- sA appeared in the first step.
      -- Show e before sA in w₁.
      have h_w₁_ev : w₁.events = wProc.events ++
          ordered.map (fun nid =>
            (⟨wProc.tick + 2, 0, nid⟩ : ScheduledEvent)) := by
        dsimp [w₁]
        exact activateGroup_events_map wProc ordered
      -- is sA in wProc or in the observer batch?
      have h_sA_proc : sA ∈ wProc.events := by
        rw [h_w₁_ev] at h_sA_w₁
        rw [List.mem_append] at h_sA_w₁
        rcases h_sA_w₁ with h_sA_p | h_sA_obs
        · exact h_sA_p
        · rcases List.mem_map.mp h_sA_obs with ⟨nid, _, h_eq⟩
          have h_pri₀ :
              (⟨wProc.tick + 2, 0, nid⟩ : ScheduledEvent).priority =
                (0 : Int) := by rfl
          rw [← h_eq] at h_sA_pri
          exact absurd h_pri₀ h_sA_pri
      -- sA is not in w (given), so sA is a spawn
      have h_sA_filt_proc : sA ∈ wProc.events.filter pTick := by
        rw [List.mem_filter]
        exact ⟨h_sA_proc, by
          rw [decide_eq_true_eq]
          dsimp [wProc] at *
          rw [processNEvents_tick] at *
          exact h_sA_nd⟩
      rw [h_split] at h_sA_filt_proc
      have h_sA_sp : sA ∈ World.popSpawnAcc w m := by
        rw [List.mem_append] at h_sA_filt_proc
        rcases h_sA_filt_proc with h_sA_surv | h_sA_sp
        · exact absurd
              (List.mem_filter.mp h_sA_surv).1 h_sA_absent
        · exact h_sA_sp
      -- e is a survivor, sA is a spawn: e before sA
      have h_eb_proc_f : evBefore
          (wProc.events.filter pTick) e sA := by
        rw [h_split]
        exact evBefore.of_mem_append h_e_filt h_sA_sp
      have h_eb_proc : evBefore wProc.events e sA :=
        evBefore.of_filter pTick h_eb_proc_f
      have h_eb_w₁ : evBefore w₁.events e sA := by
        rw [h_w₁_ev]
        exact evBefore.append_right h_eb_proc
      -- propagate through the remaining steps
      exact gSimBurst_evBefore_preserved t obsAll withinOrd pos
        w₁ ps e sA h_eb_w₁
        (by rw [h_tick_w₁]; exact h_e_nd)
        (by rw [h_tick_w₁]; exact h_sA_nd)
    · -- sA is not in w₁. Apply the IH.
      exact ih w₁ e sA h_e_w₁
        (by rw [h_tick_w₁]; exact h_e_nd) h_e_pri
        h_sA_w₁ h_sA_mem
        (by rw [h_tick_w₁]; exact h_sA_nd) h_sA_pri

/-- The middle-block invariant steps from stage `j` to stage `j + 1`
    after a burst phase. The burst appends observer events at
    priority 0. Those events do not enter the priority-(-3) block.
    The post-burst queue is duplicate-free. -/
theorem MiddleBlockOk_step_gSimBurst (groups : List GroupSpec)
    (actTick : Nat → Nat) (T : Nat) (t : Nat)
    (obsAll : List (List Nat)) (withinOrd pos : Nat → List Nat)
    (w : World) (pairs : List (Nat × Nat))
    (g₁ c₁ g₂ c₂ j : Nat)
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
        (w.events.filter (fun e => e.targetTick == w.tick)) g₁ c₁ g₂ c₂ j)
    (h_stage : StageMemAt groups actTick w w.tick)
    (h_sA_absent : stageEvent actTick groups g₁ c₁ (j + 1) ∉ w.events)
    (h_sD_absent : stageEvent actTick groups g₂ c₂ (j + 1) ∉ w.events)
    (h_nd_post : (gSimBurst t obsAll withinOrd pos w pairs).events.Nodup) :
    MiddleBlockOk groups actTick T
      (gSimBurst t obsAll withinOrd pos w pairs).events
      g₁ c₁ g₂ c₂ (j + 1) := by
  dsimp [MiddleBlockOk]
  set sA := stageEvent actTick groups g₁ c₁ (j + 1)
  set sD := stageEvent actTick groups g₂ c₂ (j + 1)
  set due := w.events.filter (fun ev => ev.targetTick == w.tick)
  set W_B := gSimBurst t obsAll withinOrd pos w pairs
  intro e h_b1 h_b2 h_pri h_tgt
  have h_j₁' : j ≤ (chainAt groups g₁ c₁).middleDelays.length := by omega
  -- e targets a tick after the tick of w
  have h_e_nd : e.targetTick ≠ w.tick := by
    rw [h_tgt, h_due]
    exact (stageTarget_lt_succ actTick groups g₁ c₁ j h_j₁').ne'
  -- sA and sD miss the tick of w
  have h_sA_nd : sA.targetTick ≠ w.tick := by
    dsimp [sA, stageEvent]
    rw [h_due]
    exact (stageTarget_lt_succ actTick groups g₁ c₁ j h_j₁').ne'
  -- sA has priority -3, not 0
  have h_sA_pri : sA.priority ≠ (0 : Int) := by
    dsimp [sA, stageEvent, stagePri]
    intro h_eq
    omega
  -- e is not an old event
  have h_e_absent : e ∉ w.events := by
    by_contra h_e_w
    have h_eb : evBefore W_B.events e sA :=
      gSimBurst_survivor_before_nonmember t obsAll withinOrd pos
        w pairs e sA h_e_w h_e_nd (by rw [h_pri]; intro h; omega)
        h_sA_absent (evBefore.mem_left h_b1) h_sA_nd h_sA_pri
    exact evBefore.asymm h_nd_post h_b1 h_eb
  -- the converse spawn-origin fact identifies e and its parent
  obtain ⟨g, c, h_g, h_c, h_e_eq, hAC, hCD⟩ :=
    converse_spawn_gSimBurst groups actTick T t obsAll withinOrd pos
      w pairs g₁ c₁ g₂ c₂ j
      h_g₁ h_c₁ h_g₂ h_c₂ h_layout h_j₁' (by omega) h_j_ge
      h_due h_tgt₂ hA_mem hD_mem h_nodup hAD h_mb h_stage
      h_sA_absent h_sD_absent
      e h_e_absent h_b1 h_b2 h_pri h_tgt
  set C := stageEvent actTick groups g c j
  -- the parent sits in the due filter
  have hC_due : C ∈ due := evBefore.mem_left hCD
  have hC_tick : C.targetTick = w.tick := by
    simpa [Nat.beq_eq] using (List.mem_filter.mp hC_due).2
  -- the parent is a middle-stage event
  have h_e_pri' : (stageEvent actTick groups g c (j + 1)).priority =
      (-3 : Int) := by
    rw [← h_e_eq]
    exact h_pri
  have h_j_gc : j < (chainAt groups g c).middleDelays.length := by
    dsimp [stageEvent, stagePri] at h_e_pri'
    split_ifs at h_e_pri' <;> omega
  have hC_pri : C.priority = (-3 : Int) := by
    dsimp [C, stageEvent]
    exact stagePri_middle groups g c j h_j_ge (by omega)
  -- the stage-j invariant classifies the parent
  have h_mb_C : MiddleBlock groups actTick T g₁ c₁ j C :=
    h_mb C hAC hCD hC_pri (by rw [hC_tick, h_due])
  -- lift the classification to stage j + 1
  have h_tgt_succ : stageTarget actTick groups g c (j + 1) =
      stageTarget actTick groups g₁ c₁ (j + 1) := by
    have h := congr_arg ScheduledEvent.targetTick h_e_eq
    dsimp [stageEvent] at h
    exact h.symm.trans h_tgt
  have h_lift : MiddleBlock groups actTick T g₁ c₁ (j + 1)
      (stageEvent actTick groups g c (j + 1)) :=
    MiddleBlock_step_middle groups actTick T g₁ c₁ g c j h_g h_c h_j_gc
      (by omega) h_mb_C h_tgt_succ
  rw [h_e_eq]
  exact h_lift
