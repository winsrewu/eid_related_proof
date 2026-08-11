import BasicProofs.GroupClustering.BurstEventShape


open BasicRedstoneSim

/-! # Group clustering — event accounting for the burst phase

Two facts per burst phase:
1. events targeting strictly future ticks are never removed
   (`gSimBurst_future_mem`);
2. every event that appears without being there before targets a strictly
   future tick (`gSimBurst_new_events_future`, needs the delay ≥ 2 invariant).
-/

/-- An element different from the erased one stays in `eraseIdx`. -/
private theorem mem_eraseIdx_of_mem_ne {α : Type} {l : List α} {i : Nat} {x : α}
    (h_i : i < l.length) (h_mem : x ∈ l) (h_ne : x ≠ l[i]) : x ∈ l.eraseIdx i := by
  induction l generalizing i with
  | nil => exact absurd h_i (by simp)
  | cons hd tl ih =>
    cases i with
    | zero =>
      simp only [List.eraseIdx]
      have h_hd : (hd :: tl)[0] = hd := rfl
      rw [h_hd] at h_ne
      rw [List.mem_cons] at h_mem
      rcases h_mem with rfl | h_mem
      · exact absurd rfl h_ne
      · exact h_mem
    | succ i' =>
      simp only [List.eraseIdx, List.getElem_cons_succ] at h_ne ⊢
      rw [List.mem_cons] at h_mem ⊢
      rcases h_mem with rfl | h_mem
      · exact Or.inl rfl
      · exact Or.inr (ih (by simpa using h_i) h_mem h_ne)

/-- `processNEvents` preserves every event targeting a strictly future tick. -/
theorem processNEvents_future_mem (w : World) (n : Nat)
    (ev : ScheduledEvent) (h_ev : ev ∈ w.events) (h_fut : ev.targetTick > w.tick) :
    ev ∈ (processNEvents w n).events := by
  induction n generalizing w with
  | zero => simpa [processNEvents] using h_ev
  | succ n' ih =>
    simp only [processNEvents]
    cases h_step : w.step with
    | none => exact h_ev
    | some w' =>
      apply ih
      · cases h_pop : w.popNextEvent with
        | none => simp [World.step, h_pop] at h_step
        | some p =>
          cases p with | mk ev₀ w_pop =>
          simp only [World.step, h_pop] at h_step
          injection h_step with h_w'_eq
          obtain ⟨idx, h_idx, h_erase, h_tick₀, _, h_idx_eq⟩ :=
            World.popNextEvent_eraseIdx w ev₀ w_pop h_pop
          rw [← h_w'_eq]
          apply World.onScheduledTick_events_subset
          rw [h_erase]
          apply mem_eraseIdx_of_mem_ne h_idx h_ev
          intro h_eq
          have h_contra := h_fut
          rw [h_eq, h_idx_eq, h_tick₀] at h_contra
          omega
      · rw [World.step_tick w w' h_step]
        exact h_fut

/-- `activateGroup` only appends; old events stay. -/
theorem activateGroup_events_subset (w : World) (observers : List Nat) :
    w.events ⊆ (activateGroup w observers).events := by
  induction observers generalizing w with
  | nil => simp [activateGroup]
  | cons oid os ih =>
    simp only [activateGroup, List.foldl_cons]
    rw [← activateGroup]
    intro ev h_ev
    apply ih
    rw [World.scheduleEvent_events, List.mem_append]
    exact Or.inl h_ev

/-- The burst phase preserves every event targeting a strictly future tick. -/
theorem gSimBurst_future_mem (t : Nat) (obsAll : List (List Nat))
    (withinOrd : Nat → List Nat) (pos : Nat → List Nat) (w : World)
    (pairs : List (Nat × Nat)) :
    ∀ ev ∈ w.events, ev.targetTick > w.tick →
      ev ∈ (gSimBurst t obsAll withinOrd pos w pairs).events := by
  induction pairs generalizing w with
  | nil => simp [gSimBurst]; intro ev h_ev _; exact h_ev
  | cons p ps ih =>
    simp only [gSimBurst, List.foldl_cons]
    rcases p with ⟨gi, k⟩
    intro ev h_ev h_fut
    apply ih
    · apply activateGroup_events_subset
      exact processNEvents_future_mem w ((pos t)[k]?.getD 0) ev h_ev h_fut
    · rw [activateGroup_tick, processNEvents_tick]
      exact h_fut

/-! ## New events are future -/

/-- The delay ≥ 2 invariant survives one `step`. -/
theorem step_delay_preserved (w w' : World) (h_step : w.step = some w')
    (h_delay : ∀ nid nd, w.getNode nid = some nd → ∀ d p,
        nd.kind = .repeater d p → d ≥ 2) :
    ∀ nid nd, w'.getNode nid = some nd → ∀ d p,
      nd.kind = .repeater d p → d ≥ 2 := by
  cases h_pop : w.popNextEvent with
  | none => simp [World.step, h_pop] at h_step
  | some p =>
    cases p with | mk ev₀ w_pop =>
    simp only [World.step, h_pop] at h_step
    injection h_step with h_w'_eq
    intro nid nd h_nd d p h_kind
    rw [← h_w'_eq] at h_nd
    obtain ⟨nd₀, h_nd₀, h_kind₀⟩ :=
      World.onScheduledTick_kind_preserved w_pop ev₀.nodeId nid nd h_nd
    rw [h_kind₀] at h_kind
    have h_nodes_pop : w_pop.nodes = w.nodes := World.popNextEvent_nodes w ev₀ w_pop h_pop
    have h_nd_w : w.getNode nid = some nd₀ := by
      dsimp [World.getNode]; rw [← h_nodes_pop]; exact h_nd₀
    exact h_delay nid nd₀ h_nd_w d p h_kind

/-- The delay ≥ 2 invariant survives `processNEvents`. -/
theorem processNEvents_delay_preserved (w : World) (n : Nat)
    (h_delay : ∀ nid nd, w.getNode nid = some nd → ∀ d p,
        nd.kind = .repeater d p → d ≥ 2) :
    ∀ nid nd, (processNEvents w n).getNode nid = some nd → ∀ d p,
      nd.kind = .repeater d p → d ≥ 2 := by
  induction n generalizing w with
  | zero => simpa [processNEvents] using h_delay
  | succ n' ih =>
    simp only [processNEvents]
    cases h_step : w.step with
    | none => simpa [h_step] using h_delay
    | some w' =>
      exact ih w' (step_delay_preserved w w' h_step h_delay)

/-- `processNEvents` adds only events targeting strictly future ticks. -/
theorem processNEvents_new_events_future (w : World) (n : Nat)
    (h_delay : ∀ nid nd, w.getNode nid = some nd → ∀ d p,
        nd.kind = .repeater d p → d ≥ 2) :
    ∀ ev ∈ (processNEvents w n).events, ev ∉ w.events → ev.targetTick > w.tick := by
  induction n generalizing w with
  | zero =>
    intro ev h_ev h_notin
    simpa [processNEvents] using absurd h_ev h_notin
  | succ n' ih =>
    simp only [processNEvents]
    cases h_step : w.step with
    | none =>
      intro ev h_ev h_notin
      simpa [h_step] using absurd h_ev h_notin
    | some w' =>
      simp only
      intro ev h_ev h_notin
      cases h_pop : w.popNextEvent with
      | none => simp [World.step, h_pop] at h_step
      | some p =>
        cases p with | mk ev₀ w_pop =>
        have h_tick' : w'.tick = w.tick := World.step_tick w w' h_step
        have h_delay_w' := step_delay_preserved w w' h_step h_delay
        simp only [World.step, h_pop] at h_step
        injection h_step with h_w'_eq
        by_cases h_in_w' : ev ∈ w'.events
        · obtain ⟨new, h_app, h_new_fut⟩ := World.onScheduledTick_events_append w_pop ev₀.nodeId
            (by
              intro nid nd h_nd d p h_kind
              have h_nodes_pop : w_pop.nodes = w.nodes :=
                World.popNextEvent_nodes w ev₀ w_pop h_pop
              have h_nd_w : w.getNode nid = some nd := by
                dsimp [World.getNode]; rw [← h_nodes_pop]; exact h_nd
              exact h_delay nid nd h_nd_w d p h_kind)
          have h_app' : w'.events = w_pop.events ++ new := by rw [← h_w'_eq, h_app]
          rw [h_app'] at h_in_w'
          simp only [List.mem_append] at h_in_w'
          rcases h_in_w' with h_old | h_new
          · obtain ⟨idx, _, h_erase, _, _, _⟩ :=
              World.popNextEvent_eraseIdx w ev₀ w_pop h_pop
            rw [h_erase] at h_old
            exact absurd (List.mem_of_mem_eraseIdx h_old) h_notin
          · have h_tick_pop : w_pop.tick = w.tick :=
              World.popNextEvent_tick w ev₀ w_pop h_pop
            rw [h_tick_pop] at h_new_fut
            exact h_new_fut ev h_new
        · exact h_tick' ▸ ih w' h_delay_w' ev h_ev h_in_w'

/-- `activateGroup` does not touch the nodes. -/
theorem activateGroup_nodes (w : World) (observers : List Nat) :
    (activateGroup w observers).nodes = w.nodes := by
  induction observers generalizing w with
  | nil => simp [activateGroup]
  | cons oid os ih =>
    simp only [activateGroup, List.foldl_cons]
    rw [← activateGroup, ih, World.scheduleEvent_nodes]

/-- The delay ≥ 2 invariant survives `activateGroup` (which does not touch
    nodes at all). -/
theorem activateGroup_delay_preserved (w : World) (observers : List Nat)
    (h_delay : ∀ nid nd, w.getNode nid = some nd → ∀ d p,
        nd.kind = .repeater d p → d ≥ 2) :
    ∀ nid nd, (activateGroup w observers).getNode nid = some nd → ∀ d p,
      nd.kind = .repeater d p → d ≥ 2 := by
  intro nid nd h_nd d p h_kind
  dsimp [World.getNode] at h_nd
  rw [activateGroup_nodes] at h_nd
  exact h_delay nid nd h_nd d p h_kind

/-- One burst step (pos-insertion, then one atomic group firing) adds only
    events targeting strictly future ticks. -/
private theorem burstStep_new_events_future (w : World) (m : Nat) (observers : List Nat)
    (h_delay : ∀ nid nd, w.getNode nid = some nd → ∀ d p,
        nd.kind = .repeater d p → d ≥ 2) :
    ∀ ev ∈ (activateGroup (processNEvents w m) observers).events,
      ev ∉ w.events → ev.targetTick > w.tick := by
  intro ev h_ev h_notin
  by_cases h_in₁ : ev ∈ (processNEvents w m).events
  · by_cases h_in₀ : ev ∈ w.events
    · exact absurd h_in₀ h_notin
    · exact (processNEvents_tick w m) ▸
        processNEvents_new_events_future w m h_delay ev h_in₁ h_in₀
  · obtain ⟨new, h_app, h_new_fut⟩ := activateGroup_events_append
      (processNEvents w m) observers
    rw [h_app] at h_ev
    simp only [List.mem_append] at h_ev
    rcases h_ev with h_ev' | h_ev'
    · exact absurd h_ev' h_in₁
    · exact (processNEvents_tick w m) ▸ h_new_fut ev h_ev'

/-- The burst phase adds only events targeting strictly future ticks. -/
theorem gSimBurst_new_events_future (t : Nat) (obsAll : List (List Nat))
    (withinOrd : Nat → List Nat) (pos : Nat → List Nat) (w : World)
    (pairs : List (Nat × Nat))
    (h_delay : ∀ nid nd, w.getNode nid = some nd → ∀ d p,
        nd.kind = .repeater d p → d ≥ 2) :
    ∀ ev ∈ (gSimBurst t obsAll withinOrd pos w pairs).events,
      ev ∉ w.events → ev.targetTick > w.tick := by
  induction pairs generalizing w h_delay with
  | nil =>
    simp [gSimBurst]
    exact fun _ h_ev h_notin => absurd h_ev h_notin
  | cons p ps ih =>
    simp only [gSimBurst, List.foldl_cons]
    rcases p with ⟨gi, k⟩
    set w₁ : World := processNEvents w ((pos t)[k]?.getD 0)
    set ordered : List Nat := (withinOrd gi).foldl (fun acc ci =>
      match (obsAll[gi]?.getD [])[ci]? with
      | some oid => acc ++ [oid]
      | none => acc) []
    intro ev h_ev h_notin
    by_cases h_in₂ : ev ∈ (activateGroup w₁ ordered).events
    · exact burstStep_new_events_future w ((pos t)[k]?.getD 0) ordered h_delay ev
        h_in₂ h_notin
    · have h_gt := ih (activateGroup w₁ ordered)
        (activateGroup_delay_preserved w₁ ordered
          (processNEvents_delay_preserved w ((pos t)[k]?.getD 0) h_delay))
        ev h_ev h_in₂
      rw [activateGroup_tick] at h_gt
      dsimp [w₁] at h_gt
      rw [processNEvents_tick] at h_gt
      exact h_gt
