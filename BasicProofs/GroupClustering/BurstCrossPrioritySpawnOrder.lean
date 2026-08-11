import BasicProofs.GroupClustering.CrossPriorityPopDiscipline

open BasicRedstoneSim List

/-! # Group clustering — cross-priority spawn order in the burst

Two due events popped by the same tick's burst spawn in priority
order: the strictly lower-priority event is popped first
(`popNextEvent` picks minimum priority), so its spawn is appended
first.

* `processNEvents_smaller_pri_spawn_before` — within one
  `processNEvents` run;
* `gSimBurst_smaller_pri_spawn_before` — across the whole burst phase.
  When the lower-priority event is popped in an earlier segment, its
  spawn is a present non-due event and LockstepComposition's
  `gSimBurst_present_before_spawn` finishes the argument.

This supplies the last ordering ingredient of the stage-`1` base case
of `MiddleBlockOk` (the subcase where both reference stage-`0` events
are popped by the burst). -/

/-- Within one `processNEvents` run, two due events that are both
    popped spawn in priority order: the spawn of the strictly
    lower-priority event precedes the spawn of the other. -/
theorem processNEvents_smaller_pri_spawn_before (groups : List GroupSpec)
    (w : World) (n : Nat) (P A sP sA : ScheduledEvent)
    (h_layout : NodeLayoutOk groups w)
    (hP_mem : P ∈ w.events) (hA_mem : A ∈ w.events)
    (hP_due : P.targetTick = w.tick) (hA_due : A.targetTick = w.tick)
    (h_pri : P.priority < A.priority)
    (hP_gone : P ∉ (processNEvents w n).events)
    (hA_gone : A ∉ (processNEvents w n).events)
    (h_sP_nd : sP.targetTick ≠ w.tick) (h_sA_nd : sA.targetTick ≠ w.tick)
    (h_spawnP : ∀ (v : World), v.tick = w.tick → NodeLayoutOk groups v →
        (v.onScheduledTick P.nodeId).events = v.events ++ [sP])
    (h_spawnA : ∀ (v : World), v.tick = w.tick → NodeLayoutOk groups v →
        (v.onScheduledTick A.nodeId).events = v.events ++ [sA]) :
    evBefore (processNEvents w n).events sP sA := by
  induction n generalizing w h_layout with
  | zero =>
    simp [processNEvents] at hP_gone
    exact (hP_gone hP_mem).elim
  | succ n ih =>
    dsimp only [processNEvents] at hP_gone hA_gone ⊢
    cases h_step : w.step with
    | none =>
      simp only [h_step] at hP_gone
      exact (hP_gone hP_mem).elim
    | some w' =>
      have h_layout_w' : NodeLayoutOk groups w' :=
        NodeLayoutOk_step groups w w' h_step h_layout
      simp only [h_step] at hP_gone hA_gone ⊢
      dsimp [World.step] at h_step
      cases h_pop : w.popNextEvent with
      | none => simp [h_pop] at h_step
      | some p =>
        rcases p with ⟨ev₀, w_pop⟩
        simp only [h_pop] at h_step
        injection h_step with h_w'
        obtain ⟨idx, h_idx, h_erase, h_tick_ev, _, h_get_idx⟩ :=
          World.popNextEvent_eraseIdx w ev₀ w_pop h_pop
        have h_tick_pop : w_pop.tick = w.tick :=
          World.popNextEvent_tick w ev₀ w_pop h_pop
        have h_tick_w' : w'.tick = w.tick := by
          rw [← h_w', World.onScheduledTick_tick, h_tick_pop]
        have h_layout_pop : NodeLayoutOk groups w_pop :=
          NodeLayoutOk_of_nodes_eq groups w w_pop
            (World.popNextEvent_nodes w ev₀ w_pop h_pop) h_layout
        -- the popped event is not A: the minimum due priority is at most
        -- P's priority, strictly below A's
        have h_ev_A : ev₀ ≠ A := by
          intro h_eq
          obtain ⟨_, h_min, _⟩ :=
            popNextEvent_first_min_priority w ev₀ w_pop h_pop
          have h_P_filter : P ∈
              w.events.filter (fun e => e.targetTick == w.tick) := by
            rw [List.mem_filter]
            exact ⟨hP_mem, by rw [hP_due]; simp⟩
          have h_le : ev₀.priority ≤ P.priority := h_min P h_P_filter
          rw [h_eq] at h_le
          omega
        by_cases h_ev_P : ev₀ = P
        · -- P is popped now: sP is appended; A stays due and is popped
          -- later in the run, so LockstepComposition's present-before-spawn applies
          have h_w'_events : w'.events = w_pop.events ++ [sP] := by
            rw [← h_w', h_ev_P]
            exact h_spawnP w_pop h_tick_pop h_layout_pop
          have h_sP_w' : sP ∈ w'.events := by
            rw [h_w'_events]
            exact List.mem_append_right _ (by simp)
          have hA_pop : A ∈ w_pop.events := by
            rw [h_erase]
            exact mem_eraseIdx_of_ne w.events idx h_idx ev₀ A h_get_idx
              hA_mem (Ne.symm h_ev_A)
          have hA_w' : A ∈ w'.events := by
            rw [h_w'_events]
            exact List.mem_append_left _ hA_pop
          exact processNEvents_present_before_spawn groups w' n sP A sA
            h_layout_w' h_sP_w' (by rw [h_tick_w']; exact h_sP_nd) hA_w'
            (by rw [h_tick_w']; exact hA_due) hA_gone
            (by rw [h_tick_w']; exact h_sA_nd)
            (fun v h_v => h_spawnA v (h_v.trans h_tick_w'))
        · -- another event is popped: P and A both survive
          have hP_pop : P ∈ w_pop.events := by
            rw [h_erase]
            exact mem_eraseIdx_of_ne w.events idx h_idx ev₀ P h_get_idx
              hP_mem (Ne.symm h_ev_P)
          have hA_pop : A ∈ w_pop.events := by
            rw [h_erase]
            exact mem_eraseIdx_of_ne w.events idx h_idx ev₀ A h_get_idx
              hA_mem (Ne.symm h_ev_A)
          obtain ⟨new₀, h_app_new, _⟩ :=
            World.onScheduledTick_appends_future w_pop ev₀.nodeId
          have hP_w' : P ∈ w'.events := by
            rw [← h_w', h_app_new]
            exact List.mem_append_left _ hP_pop
          have hA_w' : A ∈ w'.events := by
            rw [← h_w', h_app_new]
            exact List.mem_append_left _ hA_pop
          exact ih w' h_layout_w' hP_w' hA_w'
            (by rw [hP_due, h_tick_w']) (by rw [hA_due, h_tick_w'])
            hP_gone hA_gone
            (by rw [h_tick_w']; exact h_sP_nd)
            (by rw [h_tick_w']; exact h_sA_nd)
            (fun v h_v => h_spawnP v (h_v.trans h_tick_w'))
            (fun v h_v => h_spawnA v (h_v.trans h_tick_w'))

/-- Across a whole burst phase, two due events that are both popped
    spawn in priority order: the spawn of the strictly lower-priority
    event precedes the spawn of the other in the post-burst queue. -/
theorem gSimBurst_smaller_pri_spawn_before (groups : List GroupSpec)
    (t : Nat) (obsAll : List (List Nat))
    (withinOrd pos : Nat → List Nat) (w : World)
    (pairs : List (Nat × Nat)) (P A sP sA : ScheduledEvent)
    (h_layout : NodeLayoutOk groups w)
    (hP_mem : P ∈ w.events) (hA_mem : A ∈ w.events)
    (hP_due : P.targetTick = w.tick) (hA_due : A.targetTick = w.tick)
    (h_pri : P.priority < A.priority)
    (hP_gone : P ∉ (gSimBurst t obsAll withinOrd pos w pairs).events)
    (hA_gone : A ∉ (gSimBurst t obsAll withinOrd pos w pairs).events)
    (h_sP_nd : sP.targetTick ≠ w.tick) (h_sA_nd : sA.targetTick ≠ w.tick)
    (h_spawnP : ∀ (v : World), v.tick = w.tick → NodeLayoutOk groups v →
        (v.onScheduledTick P.nodeId).events = v.events ++ [sP])
    (h_spawnA : ∀ (v : World), v.tick = w.tick → NodeLayoutOk groups v →
        (v.onScheduledTick A.nodeId).events = v.events ++ [sA]) :
    evBefore (gSimBurst t obsAll withinOrd pos w pairs).events sP sA := by
  induction pairs generalizing w h_layout with
  | nil =>
    simp [gSimBurst] at hP_gone
    exact (hP_gone hP_mem).elim
  | cons p ps ih =>
    simp only [gSimBurst, List.foldl_cons] at hP_gone hA_gone ⊢
    rcases p with ⟨gi, k⟩
    set m := (pos t)[k]?.getD 0
    set ordered : List Nat := (withinOrd gi).foldl (fun acc ci =>
      match (obsAll[gi]?.getD [])[ci]? with
      | some oid => acc ++ [oid]
      | none => acc) []
    set Wproc := processNEvents w m
    set W₁ := activateGroup Wproc ordered
    change P ∉ (gSimBurst t obsAll withinOrd pos W₁ ps).events at hP_gone
    change A ∉ (gSimBurst t obsAll withinOrd pos W₁ ps).events at hA_gone
    change evBefore (gSimBurst t obsAll withinOrd pos W₁ ps).events sP sA
    have h_tick_W₁ : W₁.tick = w.tick := by
      dsimp [W₁, Wproc]
      rw [activateGroup_tick, processNEvents_tick]
    have h_layout_Wproc : NodeLayoutOk groups Wproc :=
      NodeLayoutOk_processNEvents groups w m h_layout
    have h_layout_W₁ : NodeLayoutOk groups W₁ :=
      NodeLayoutOk_activateGroup groups Wproc ordered h_layout_Wproc
    by_cases hP_proc : P ∈ Wproc.events
    · -- P survives this segment; by the cross-priority discipline
      -- (CrossPriorityPopDiscipline), A survives it too; continue inductively from W₁
      have hA_proc : A ∈ Wproc.events :=
        processNEvents_not_pop_larger_pri w m P A hP_due hA_due h_pri
          hA_mem hP_proc
      have hP_W₁ : P ∈ W₁.events := by
        dsimp [W₁]
        rw [activateGroup_events_map]
        exact List.mem_append_left _ hP_proc
      have hA_W₁ : A ∈ W₁.events := by
        dsimp [W₁]
        rw [activateGroup_events_map]
        exact List.mem_append_left _ hA_proc
      exact ih W₁ h_layout_W₁ hP_W₁ hA_W₁
        (by rw [hP_due, h_tick_W₁]) (by rw [hA_due, h_tick_W₁])
        hP_gone hA_gone
        (by rw [h_tick_W₁]; exact h_sP_nd) (by rw [h_tick_W₁]; exact h_sA_nd)
        (fun v h_v => h_spawnP v (h_v.trans h_tick_W₁))
        (fun v h_v => h_spawnA v (h_v.trans h_tick_W₁))
    · -- P is popped by this segment's processing
      have h_sP_proc : sP ∈ Wproc.events :=
        processNEvents_spawn_mem groups w m P sP h_layout hP_mem hP_due
          hP_proc h_sP_nd h_spawnP
      by_cases hA_proc : A ∈ Wproc.events
      · -- A survives this segment and is popped by a later segment:
        -- sP is a present non-due event, so LockstepComposition's
        -- gSimBurst_present_before_spawn finishes the argument
        have h_sP_W₁ : sP ∈ W₁.events := by
          dsimp [W₁]
          rw [activateGroup_events_map]
          exact List.mem_append_left _ h_sP_proc
        have hA_W₁ : A ∈ W₁.events := by
          dsimp [W₁]
          rw [activateGroup_events_map]
          exact List.mem_append_left _ hA_proc
        exact gSimBurst_present_before_spawn groups t obsAll withinOrd pos
          W₁ ps sP A sA h_layout_W₁ h_sP_W₁
          (by rw [h_tick_W₁]; exact h_sP_nd) hA_W₁
          (by rw [hA_due, h_tick_W₁]) hA_gone
          (by rw [h_tick_W₁]; exact h_sA_nd)
          (fun v h_v => h_spawnA v (h_v.trans h_tick_W₁))
      · -- A is popped in the same processing run: the spawn order
        -- inside the run carries through the appended activations and
        -- the remaining (non-due-preserving) segments
        have h_order : evBefore Wproc.events sP sA :=
          processNEvents_smaller_pri_spawn_before groups w m P A sP sA
            h_layout hP_mem hA_mem hP_due hA_due h_pri hP_proc hA_proc
            h_sP_nd h_sA_nd h_spawnP h_spawnA
        have h_order_W₁ : evBefore W₁.events sP sA := by
          dsimp [W₁]
          rw [activateGroup_events_map]
          exact evBefore.append_right h_order
        exact evBefore_gSimBurst_of_notDue t obsAll withinOrd pos W₁ ps
          sP sA (by rw [h_tick_W₁]; exact h_sP_nd)
          (by rw [h_tick_W₁]; exact h_sA_nd) h_order_W₁
