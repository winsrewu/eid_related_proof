import BasicProofs.GroupClustering.StageEventCompleteness
import BasicProofs.GroupClustering.LockstepComposition

open BasicRedstoneSim List

/-! # Group clustering — cross-priority pop discipline

`popNextEvent` always pops a due event of minimum priority. Two
consequences used by the stage-`1` base case of `MiddleBlockOk`:

* a burst phase cannot pop a due event while a strictly lower-priority
  due event is still queued: if the lower-priority event survives the
  burst, so does the higher-priority one
  (`gSimBurst_not_pop_larger_pri`);
* in a drain, the spawn of a lower-priority due event precedes the
  spawn of a higher-priority due event
  (`stepUNT_spawn_before_of_pri_lt`), the order-theoretic twin of
  StageEventCompleteness's `mem_stepUNT_of_due_spawn`.
-/

/-! ## processNEvents and the burst: cross-priority survival -/

/-- `processNEvents` cannot pop a due event while a strictly
    lower-priority due event survives: if the low-priority event is
    still queued after the processing, so is the high-priority one. -/
theorem processNEvents_not_pop_larger_pri (w : World) (n : Nat)
    (P A : ScheduledEvent)
    (hP_due : P.targetTick = w.tick) (hA_due : A.targetTick = w.tick)
    (h_pri : P.priority < A.priority)
    (hA_mem : A ∈ w.events)
    (hP_stays : P ∈ (processNEvents w n).events) :
    A ∈ (processNEvents w n).events := by
  induction n generalizing w with
  | zero =>
    simp [processNEvents]
    exact hA_mem
  | succ n ih =>
    dsimp only [processNEvents] at hP_stays ⊢
    cases h_step : w.step with
    | none =>
      simp only [h_step] at hP_stays ⊢
      exact hA_mem
    | some w' =>
      simp only [h_step] at hP_stays ⊢
      dsimp [World.step] at h_step
      cases h_pop : w.popNextEvent with
      | none => simp [h_pop] at h_step
      | some p =>
        rcases p with ⟨ev₀, w_pop⟩
        simp only [h_pop] at h_step
        injection h_step with h_w'
        obtain ⟨idx, h_idx, h_erase, _, _, h_get_idx⟩ :=
          World.popNextEvent_eraseIdx w ev₀ w_pop h_pop
        have h_tick_pop : w_pop.tick = w.tick :=
          World.popNextEvent_tick w ev₀ w_pop h_pop
        have h_tick_w' : w'.tick = w.tick := by
          rw [← h_w', World.onScheduledTick_tick, h_tick_pop]
        -- the popped event is not A: the minimum due priority is at most
        -- P's priority, and P is still queued at this step
        have h_ev_A : ev₀ ≠ A := by
          intro h_eq
          have hP_w' : P ∈ w'.events :=
            mem_processNEvents_due_back w' n P hP_stays (by
              rw [hP_due, h_tick_w'])
          obtain ⟨new₀, h_app_new, h_fut_new⟩ :=
            World.onScheduledTick_appends_future w_pop ev₀.nodeId
          have hP_pop : P ∈ w_pop.events := by
            rw [← h_w', h_app_new, List.mem_append] at hP_w'
            rcases hP_w' with h | h_new
            · exact h
            · have h_gt := h_fut_new P h_new
              rw [h_tick_pop, hP_due] at h_gt
              omega
          rw [h_erase] at hP_pop
          have hP_wev : P ∈ w.events :=
            List.eraseIdx_subset' w.events idx hP_pop
          obtain ⟨_, h_min, _⟩ :=
            popNextEvent_first_min_priority w ev₀ w_pop h_pop
          have h_P_filter : P ∈
              w.events.filter (fun e => e.targetTick == w.tick) := by
            rw [List.mem_filter]
            exact ⟨hP_wev, by rw [hP_due]; simp⟩
          have h_le : ev₀.priority ≤ P.priority := h_min P h_P_filter
          rw [h_eq] at h_le
          omega
        -- A survives this pop; the induction continues at w'
        have hA_pop : A ∈ w_pop.events := by
          rw [h_erase]
          exact mem_eraseIdx_of_ne w.events idx h_idx ev₀ A h_get_idx hA_mem
            (Ne.symm h_ev_A)
        obtain ⟨new₀, h_app_new, _⟩ :=
          World.onScheduledTick_appends_future w_pop ev₀.nodeId
        have hA_w' : A ∈ w'.events := by
          rw [← h_w', h_app_new]
          exact List.mem_append_left _ hA_pop
        exact ih w' (by rw [hP_due, h_tick_w'])
          (by rw [hA_due, h_tick_w']) hA_w' hP_stays

/-- A burst phase cannot pop a due event while a strictly lower-priority
    due event survives: if the low-priority event is still queued after
    the burst, so is the high-priority one. -/
theorem gSimBurst_not_pop_larger_pri (t : Nat) (obsAll : List (List Nat))
    (withinOrd pos : Nat → List Nat) (w : World)
    (pairs : List (Nat × Nat)) (P A : ScheduledEvent)
    (hP_due : P.targetTick = w.tick) (hA_due : A.targetTick = w.tick)
    (h_pri : P.priority < A.priority)
    (hA_mem : A ∈ w.events)
    (hP_stays : P ∈ (gSimBurst t obsAll withinOrd pos w pairs).events) :
    A ∈ (gSimBurst t obsAll withinOrd pos w pairs).events := by
  induction pairs generalizing w with
  | nil =>
    simp [gSimBurst] at hP_stays
    exact hA_mem
  | cons p ps ih =>
    simp only [gSimBurst, List.foldl_cons] at hP_stays ⊢
    rcases p with ⟨gi, k⟩
    set m := (pos t)[k]?.getD 0
    set ordered : List Nat := (withinOrd gi).foldl (fun acc ci =>
      match (obsAll[gi]?.getD [])[ci]? with
      | some oid => acc ++ [oid]
      | none => acc) []
    set Wproc := processNEvents w m
    set W₁ := activateGroup Wproc ordered
    change P ∈ (gSimBurst t obsAll withinOrd pos W₁ ps).events at hP_stays
    change A ∈ (gSimBurst t obsAll withinOrd pos W₁ ps).events
    have h_tick_W₁ : W₁.tick = w.tick := by
      dsimp [W₁, Wproc]
      rw [activateGroup_tick, processNEvents_tick]
    -- P, due and present in the final result, is already present at W₁
    have hP_W₁ : P ∈ W₁.events :=
      mem_gSimBurst_due_back t obsAll withinOrd pos W₁ ps P hP_stays (by
        rw [hP_due, h_tick_W₁])
    have hP_proc : P ∈ Wproc.events := by
      dsimp [W₁] at hP_W₁
      rw [activateGroup_events_map, List.mem_append] at hP_W₁
      rcases hP_W₁ with h | h_obs
      · exact h
      · rcases List.mem_map.mp h_obs with ⟨nid, _, h_ev_eq⟩
        have h_tgt : P.targetTick = Wproc.tick + 2 := by
          rw [← h_ev_eq]
        have h_tick_proc : Wproc.tick = w.tick := by
          dsimp [Wproc]
          exact processNEvents_tick w m
        rw [h_tgt, h_tick_proc] at hP_due
        omega
    -- A survives the processing steps of this segment
    have hA_proc : A ∈ Wproc.events :=
      processNEvents_not_pop_larger_pri w m P A hP_due hA_due h_pri
        hA_mem hP_proc
    have hA_W₁ : A ∈ W₁.events := by
      dsimp [W₁]
      rw [activateGroup_events_map]
      exact List.mem_append_left _ hA_proc
    exact ih W₁ (by rw [hP_due, h_tick_W₁])
      (by rw [hA_due, h_tick_W₁]) hA_W₁ hP_stays

/-! ## The drain: spawn order follows priority -/

/-- A non-due event present in the queue precedes the spawn of a due
    event through the whole drain: the due event is eventually popped
    (its spawn appended at the end of that step), while the non-due
    event is never popped. -/
private theorem present_before_drain_spawn (groups : List GroupSpec)
    (w : World) (A sP sA : ScheduledEvent)
    (h_layout : NodeLayoutOk groups w)
    (h_sP_mem : sP ∈ w.events) (h_sP_nd : sP.targetTick ≠ w.tick)
    (hA_mem : A ∈ w.events) (hA_due : A.targetTick = w.tick)
    (h_sA_nd : sA.targetTick ≠ w.tick)
    (h_spawnA : ∀ (v : World), v.tick = w.tick → NodeLayoutOk groups v →
        (v.onScheduledTick A.nodeId).events = v.events ++ [sA]) :
    evBefore w.stepUntilNextTick.events sP sA := by
  induction w using World.stepUntilNextTick.induct with
  | case1 x h_step =>
    -- no pop possible, but A is due and present
    dsimp [World.step] at h_step
    cases h_pop : x.popNextEvent with
    | none =>
      exact False.elim (popNextEvent_none_no_events x h_pop A hA_mem hA_due)
    | some p =>
      simp only [h_pop] at h_step
      cases h_step
  | case2 x w' h_step ih =>
    have h_layout_w' : NodeLayoutOk groups w' :=
      NodeLayoutOk_step groups x w' h_step h_layout
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
      obtain ⟨idx, h_idx, h_erase, _, _, h_get_idx⟩ :=
        World.popNextEvent_eraseIdx x ev₀ w_pop h_pop
      have h_tick_pop : w_pop.tick = x.tick :=
        World.popNextEvent_tick x ev₀ w_pop h_pop
      have h_tick_w' : w'.tick = x.tick := by
        rw [← h_w', World.onScheduledTick_tick, h_tick_pop]
      have h_layout_pop : NodeLayoutOk groups w_pop :=
        NodeLayoutOk_of_nodes_eq groups x w_pop
          (World.popNextEvent_nodes x ev₀ w_pop h_pop) h_layout
      by_cases h_ev_A : ev₀ = A
      · -- A is popped now: sA is appended at the end, sP is present
        have h_w'_events : w'.events = w_pop.events ++ [sA] := by
          rw [← h_w', h_ev_A]
          exact h_spawnA w_pop h_tick_pop h_layout_pop
        have h_sP_pop : sP ∈ w_pop.events := by
          rw [h_erase]
          exact mem_eraseIdx_of_ne x.events idx h_idx ev₀ sP h_get_idx h_sP_mem
            (fun h_eq => h_sP_nd (by
              rw [h_eq]
              exact (popNextEvent_first_min_priority x ev₀ w_pop h_pop).1))
        have h_sP_w' : sP ∈ w'.events := by
          rw [h_w'_events]
          exact List.mem_append_left _ h_sP_pop
        have h_sA_w' : sA ∈ w'.events := by
          rw [h_w'_events]
          exact List.mem_append_right _ (by simp)
        have h_before_w' : evBefore w'.events sP sA := by
          rw [h_w'_events]
          exact evBefore.of_mem_append h_sP_pop (by simp)
        have h_step_w' : evBefore w'.stepUntilNextTick.events sP sA :=
          evBefore_stepUNT_of_notDue w' sP sA h_sP_w' h_sA_w'
            (by rw [h_tick_w']; exact h_sP_nd)
            (by rw [h_tick_w']; exact h_sA_nd)
            h_before_w'
        rwa [h_sunt]
      · -- another event is popped: sP and A both survive
        have hA_pop : A ∈ w_pop.events := by
          rw [h_erase]
          exact mem_eraseIdx_of_ne x.events idx h_idx ev₀ A h_get_idx hA_mem
            (Ne.symm h_ev_A)
        have h_sP_pop : sP ∈ w_pop.events := by
          rw [h_erase]
          exact mem_eraseIdx_of_ne x.events idx h_idx ev₀ sP h_get_idx h_sP_mem
            (fun h_eq => h_sP_nd (by
              rw [h_eq]
              exact (popNextEvent_first_min_priority x ev₀ w_pop h_pop).1))
        obtain ⟨new₀, h_app_new, _⟩ :=
          World.onScheduledTick_appends_future w_pop ev₀.nodeId
        have hA_w' : A ∈ w'.events := by
          rw [← h_w', h_app_new]
          exact List.mem_append_left _ hA_pop
        have h_sP_w' : sP ∈ w'.events := by
          rw [← h_w', h_app_new]
          exact List.mem_append_left _ h_sP_pop
        have h_ih : evBefore w'.stepUntilNextTick.events sP sA :=
          ih h_layout_w' h_sP_w'
            (by rw [h_tick_w']; exact h_sP_nd) hA_w'
            (by rw [h_tick_w']; exact hA_due)
            (by rw [h_tick_w']; exact h_sA_nd)
            (fun v h_v => h_spawnA v (h_v.trans h_tick_w'))
        rwa [h_sunt]

/-- In a drain, the spawn of a strictly lower-priority due event
    precedes the spawn of a higher-priority due event. The low-priority
    event cannot be popped after the high-priority one
    (`popNextEvent` picks minimum priority), so it is popped first (or
    the high-priority event is never popped before it), and its spawn
    is appended earlier. -/
theorem stepUNT_spawn_before_of_pri_lt (groups : List GroupSpec)
    (w : World) (P A sP sA : ScheduledEvent)
    (h_layout : NodeLayoutOk groups w)
    (hP_mem : P ∈ w.events) (hA_mem : A ∈ w.events)
    (hP_due : P.targetTick = w.tick) (hA_due : A.targetTick = w.tick)
    (h_pri : P.priority < A.priority)
    (h_sP_nd : sP.targetTick ≠ w.tick) (h_sA_nd : sA.targetTick ≠ w.tick)
    (h_spawnP : ∀ (v : World), v.tick = w.tick → NodeLayoutOk groups v →
        (v.onScheduledTick P.nodeId).events = v.events ++ [sP])
    (h_spawnA : ∀ (v : World), v.tick = w.tick → NodeLayoutOk groups v →
        (v.onScheduledTick A.nodeId).events = v.events ++ [sA]) :
    evBefore w.stepUntilNextTick.events sP sA := by
  induction w using World.stepUntilNextTick.induct with
  | case1 x h_step =>
    dsimp [World.step] at h_step
    cases h_pop : x.popNextEvent with
    | none =>
      exact False.elim (popNextEvent_none_no_events x h_pop P hP_mem hP_due)
    | some p =>
      simp only [h_pop] at h_step
      cases h_step
  | case2 x w' h_step ih =>
    have h_layout_w' : NodeLayoutOk groups w' :=
      NodeLayoutOk_step groups x w' h_step h_layout
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
      obtain ⟨idx, h_idx, h_erase, _, _, h_get_idx⟩ :=
        World.popNextEvent_eraseIdx x ev₀ w_pop h_pop
      have h_tick_pop : w_pop.tick = x.tick :=
        World.popNextEvent_tick x ev₀ w_pop h_pop
      have h_tick_w' : w'.tick = x.tick := by
        rw [← h_w', World.onScheduledTick_tick, h_tick_pop]
      have h_layout_pop : NodeLayoutOk groups w_pop :=
        NodeLayoutOk_of_nodes_eq groups x w_pop
          (World.popNextEvent_nodes x ev₀ w_pop h_pop) h_layout
      -- the popped event is not A: the minimum due priority is at most
      -- P's priority, strictly below A's
      have h_ev_A : ev₀ ≠ A := by
        intro h_eq
        obtain ⟨_, h_min, _⟩ :=
          popNextEvent_first_min_priority x ev₀ w_pop h_pop
        have h_P_filter : P ∈
            x.events.filter (fun e => e.targetTick == x.tick) := by
          rw [List.mem_filter]
          exact ⟨hP_mem, by rw [hP_due]; simp⟩
        have h_le : ev₀.priority ≤ P.priority := h_min P h_P_filter
        rw [h_eq] at h_le
        omega
      by_cases h_ev_P : ev₀ = P
      · -- P is popped now: sP is appended, A survives; the auxiliary
        -- lemma carries the drain from w' onward
        have h_w'_events : w'.events = w_pop.events ++ [sP] := by
          rw [← h_w', h_ev_P]
          exact h_spawnP w_pop h_tick_pop h_layout_pop
        have h_sP_w' : sP ∈ w'.events := by
          rw [h_w'_events]
          exact List.mem_append_right _ (by simp)
        have hA_pop : A ∈ w_pop.events := by
          rw [h_erase]
          exact mem_eraseIdx_of_ne x.events idx h_idx ev₀ A h_get_idx hA_mem
            (Ne.symm h_ev_A)
        have hA_w' : A ∈ w'.events := by
          rw [h_w'_events]
          exact List.mem_append_left _ hA_pop
        have h_aux : evBefore w'.stepUntilNextTick.events sP sA :=
          present_before_drain_spawn groups w' A sP sA h_layout_w'
            h_sP_w' (by rw [h_tick_w']; exact h_sP_nd) hA_w'
            (by rw [h_tick_w']; exact hA_due)
            (by rw [h_tick_w']; exact h_sA_nd)
            (fun v h_v => h_spawnA v (h_v.trans h_tick_w'))
        rwa [h_sunt]
      · -- another event is popped: P and A both survive
        have hP_pop : P ∈ w_pop.events := by
          rw [h_erase]
          exact mem_eraseIdx_of_ne x.events idx h_idx ev₀ P h_get_idx hP_mem
            (Ne.symm h_ev_P)
        have hA_pop : A ∈ w_pop.events := by
          rw [h_erase]
          exact mem_eraseIdx_of_ne x.events idx h_idx ev₀ A h_get_idx hA_mem
            (Ne.symm h_ev_A)
        obtain ⟨new₀, h_app_new, _⟩ :=
          World.onScheduledTick_appends_future w_pop ev₀.nodeId
        have hP_w' : P ∈ w'.events := by
          rw [← h_w', h_app_new]
          exact List.mem_append_left _ hP_pop
        have hA_w' : A ∈ w'.events := by
          rw [← h_w', h_app_new]
          exact List.mem_append_left _ hA_pop
        have h_ih : evBefore w'.stepUntilNextTick.events sP sA :=
          ih h_layout_w' hP_w' hA_w'
            (by rw [hP_due, h_tick_w']) (by rw [hA_due, h_tick_w'])
            (by rw [h_tick_w']; exact h_sP_nd)
            (by rw [h_tick_w']; exact h_sA_nd)
            (fun v h_v => h_spawnP v (h_v.trans h_tick_w'))
            (fun v h_v => h_spawnA v (h_v.trans h_tick_w'))
        rwa [h_sunt]
