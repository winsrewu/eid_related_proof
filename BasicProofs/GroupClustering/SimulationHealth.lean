import BasicProofs.GroupClustering.BurstEventAccounting


open BasicRedstoneSim

/-! # Group clustering — whole-simulation health

After every completed tick, all queued events target strictly future ticks
(`gSimFoldl_events_ge`), and the delay ≥ 2 invariant persists through the
whole simulation (`gSimFoldl_delay_preserved`). These are the standing facts
the stage-event analysis builds on.
-/

/-- `stepUntilNextTick` leaves only strictly future events, provided the queue
    held no past-tick events and delays are ≥ 2. -/
theorem stepUntilNextTick_events_future :
    ∀ (w : World),
    (∀ ev ∈ w.events, ev.targetTick ≥ w.tick) →
    (∀ nid nd, w.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2) →
    ∀ ev ∈ (w.stepUntilNextTick).events, ev.targetTick > w.tick := by
  intro w
  induction w using World.stepUntilNextTick.induct with
  | case1 x h =>
    intro h_ge _ ev h_ev
    have h_step_eq : x.stepUntilNextTick = { x with tick := x.tick + 1 } :=
      stepUntilNextTick_of_step_none x h
    rw [h_step_eq] at h_ev
    have h_ge' := h_ge ev h_ev
    have h_ne : ev.targetTick ≠ x.tick := by
      intro h_tick
      dsimp [World.step] at h
      cases h_pop : x.popNextEvent with
      | some p => simp [h_pop] at h
      | none => exact popNextEvent_none_no_events x h_pop ev h_ev h_tick
    omega
  | case2 x w' h ih =>
    intro h_ge h_delay
    have h_delay_w' := step_delay_preserved x w' h h_delay
    have h_tick := World.step_tick x w' h
    have h_ih := ih (by
      dsimp [World.step] at h
      cases h_pop : x.popNextEvent with
      | none => simp [h_pop] at h
      | some p =>
        cases p with | mk ev₀ w_pop =>
        simp only [h_pop] at h
        injection h with h_w'_eq
        intro ev h_ev
        rw [← h_w'_eq] at h_ev
        obtain ⟨new, h_app, h_new_fut⟩ :=
          World.onScheduledTick_events_append w_pop ev₀.nodeId (by
            intro nid nd h_nd d p h_kind
            have h_nodes_pop : w_pop.nodes = x.nodes :=
              World.popNextEvent_nodes x ev₀ w_pop h_pop
            have h_nd_x : x.getNode nid = some nd := by
              dsimp [World.getNode]; rw [← h_nodes_pop]; exact h_nd
            exact h_delay nid nd h_nd_x d p h_kind)
        rw [h_app] at h_ev
        simp only [List.mem_append] at h_ev
        rcases h_ev with h_old | h_new
        · obtain ⟨idx, _, h_erase, _, _, _⟩ :=
            World.popNextEvent_eraseIdx x ev₀ w_pop h_pop
          rw [h_erase] at h_old
          have h_ge' := h_ge ev (List.mem_of_mem_eraseIdx h_old)
          rw [h_tick]
          exact h_ge'
        · have h_tick_pop : w_pop.tick = x.tick := World.popNextEvent_tick x ev₀ w_pop h_pop
          rw [h_tick, ← h_tick_pop]
          exact le_of_lt (h_new_fut ev h_new)) h_delay_w'
    rw [World.stepUntilNextTick, h]
    intro ev h_ev
    have h_gt := h_ih ev h_ev
    rw [← h_tick]
    exact h_gt

/-- The burst phase keeps all events at or beyond the current tick. -/
theorem gSimBurst_events_ge (t : Nat) (obsAll : List (List Nat))
    (withinOrd : Nat → List Nat) (pos : Nat → List Nat) (w : World)
    (pairs : List (Nat × Nat))
    (h_ge : ∀ ev ∈ w.events, ev.targetTick ≥ w.tick)
    (h_delay : ∀ nid nd, w.getNode nid = some nd → ∀ d p,
        nd.kind = .repeater d p → d ≥ 2) :
    ∀ ev ∈ (gSimBurst t obsAll withinOrd pos w pairs).events,
      ev.targetTick ≥ w.tick := by
  intro ev h_ev
  by_cases h_in : ev ∈ w.events
  · exact h_ge ev h_in
  · exact le_of_lt (gSimBurst_new_events_future t obsAll withinOrd pos w pairs
      h_delay ev h_ev h_in)

/-- `activateGroup` preserves node kinds (it does not touch nodes). -/
private theorem activateGroup_kind_preserved (w : World) (observers : List Nat) :
    ∀ nid nd, (activateGroup w observers).getNode nid = some nd →
    ∃ nd₀, w.getNode nid = some nd₀ ∧ nd.kind = nd₀.kind := by
  intro nid nd h
  dsimp [World.getNode] at h
  rw [activateGroup_nodes] at h
  exact ⟨nd, h, rfl⟩

/-- The burst phase preserves node kinds. -/
theorem gSimBurst_kind_preserved (t : Nat) (obsAll : List (List Nat))
    (withinOrd : Nat → List Nat) (pos : Nat → List Nat) (w : World)
    (pairs : List (Nat × Nat)) :
    ∀ nid nd, (gSimBurst t obsAll withinOrd pos w pairs).getNode nid = some nd →
    ∃ nd₀, w.getNode nid = some nd₀ ∧ nd.kind = nd₀.kind := by
  induction pairs generalizing w with
  | nil => intro nid nd h; simp [gSimBurst] at h; exact ⟨nd, h, rfl⟩
  | cons p ps ih =>
    simp only [gSimBurst, List.foldl_cons]
    rcases p with ⟨gi, k⟩
    intro nid nd h
    obtain ⟨nd₁, h_nd₁, h_kind₁⟩ := ih
      (activateGroup (processNEvents w ((pos t)[k]?.getD 0))
        ((withinOrd gi).foldl (fun acc ci =>
          match (obsAll[gi]?.getD [])[ci]? with
          | some oid => acc ++ [oid]
          | none => acc) [])) nid nd h
    obtain ⟨nd₂, h_nd₂, h_kind₂⟩ := activateGroup_kind_preserved
      (processNEvents w ((pos t)[k]?.getD 0))
      ((withinOrd gi).foldl (fun acc ci =>
        match (obsAll[gi]?.getD [])[ci]? with
        | some oid => acc ++ [oid]
        | none => acc) []) nid nd₁ h_nd₁
    obtain ⟨nd₀, h_nd₀, h_kind₀⟩ := processNEvents_kind_preserved w
      ((pos t)[k]?.getD 0) nid nd₂ h_nd₂
    exact ⟨nd₀, h_nd₀, by rw [h_kind₁, h_kind₂, h_kind₀]⟩

/-- The burst phase preserves the delay ≥ 2 invariant. -/
theorem gSimBurst_delay_preserved (t : Nat) (obsAll : List (List Nat))
    (withinOrd : Nat → List Nat) (pos : Nat → List Nat) (w : World)
    (pairs : List (Nat × Nat))
    (h_delay : ∀ nid nd, w.getNode nid = some nd → ∀ d p,
        nd.kind = .repeater d p → d ≥ 2) :
    ∀ nid nd, (gSimBurst t obsAll withinOrd pos w pairs).getNode nid = some nd →
    ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
  induction pairs generalizing w with
  | nil => simpa [gSimBurst] using h_delay
  | cons p ps ih =>
    simp only [gSimBurst, List.foldl_cons]
    rcases p with ⟨gi, k⟩
    apply ih
    apply activateGroup_delay_preserved
    exact processNEvents_delay_preserved w ((pos t)[k]?.getD 0) h_delay

/-- One `gSimBody` call preserves the delay ≥ 2 invariant. -/
theorem gSimBody_delay_preserved (actTick : Nat → Nat) (obsAll : List (List Nat))
    (groupOrd : List Nat) (withinOrd : Nat → List Nat) (pos : Nat → List Nat)
    (w : World) (i : Nat)
    (h_delay : ∀ nid nd, w.getNode nid = some nd → ∀ d p,
        nd.kind = .repeater d p → d ≥ 2) :
    ∀ nid nd, (gSimBody actTick obsAll groupOrd withinOrd pos w i).getNode nid = some nd →
    ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
  dsimp [gSimBody]
  split_ifs with h_active
  · intro nid nd h_nd d p h_kind
    obtain ⟨nd₁, h_nd₁, h_kind₁⟩ := World.stepUntilNextTick_kind_preserved
      (w.logOutput s!"tick {w.tick}") nid nd h_nd
    rw [h_kind₁] at h_kind
    obtain ⟨nd₀, h_nd₀, h_kind₀⟩ := World.logOutput_kind_preserved w
      s!"tick {w.tick}" nid nd₁ h_nd₁
    rw [h_kind₀] at h_kind
    exact h_delay nid nd₀ h_nd₀ d p h_kind
  · intro nid nd h_nd d p h_kind
    obtain ⟨nd₁, h_nd₁, h_kind₁⟩ := World.stepUntilNextTick_kind_preserved
      (gSimBurst w.tick obsAll withinOrd pos (w.logOutput s!"tick {w.tick}")
        (groupOrd.filter (fun gi =>
          decide (gi < obsAll.length) && (actTick gi == w.tick))).zipIdx) nid nd h_nd
    rw [h_kind₁] at h_kind
    obtain ⟨nd₂, h_nd₂, h_kind₂⟩ := gSimBurst_kind_preserved w.tick obsAll withinOrd pos
      (w.logOutput s!"tick {w.tick}")
      (groupOrd.filter (fun gi =>
        decide (gi < obsAll.length) && (actTick gi == w.tick))).zipIdx nid nd₁ h_nd₁
    rw [h_kind₂] at h_kind
    obtain ⟨nd₀, h_nd₀, h_kind₀⟩ := World.logOutput_kind_preserved w
      s!"tick {w.tick}" nid nd₂ h_nd₂
    rw [h_kind₀] at h_kind
    exact h_delay nid nd₀ h_nd₀ d p h_kind

/-- One `gSimBody` call leaves only strictly future events. -/
theorem gSimBody_events_future (actTick : Nat → Nat) (obsAll : List (List Nat))
    (groupOrd : List Nat) (withinOrd : Nat → List Nat) (pos : Nat → List Nat)
    (w : World) (i : Nat)
    (h_ge : ∀ ev ∈ w.events, ev.targetTick ≥ w.tick)
    (h_delay : ∀ nid nd, w.getNode nid = some nd → ∀ d p,
        nd.kind = .repeater d p → d ≥ 2) :
    ∀ ev ∈ (gSimBody actTick obsAll groupOrd withinOrd pos w i).events,
      ev.targetTick > w.tick := by
  dsimp [gSimBody]
  split_ifs with h_active
  · have h_step_fut := stepUntilNextTick_events_future (w.logOutput s!"tick {w.tick}")
      (by simpa using h_ge)
      (by
        intro nid nd h_nd d p h_kind
        obtain ⟨nd₀, h_nd₀, h_kind₀⟩ := World.logOutput_kind_preserved w
          s!"tick {w.tick}" nid nd h_nd
        rw [h_kind₀] at h_kind
        exact h_delay nid nd₀ h_nd₀ d p h_kind)
    intro ev h_ev
    have h_gt := h_step_fut ev h_ev
    simpa [World.logOutput_tick] using h_gt
  · have h_step_fut := stepUntilNextTick_events_future
      (gSimBurst w.tick obsAll withinOrd pos (w.logOutput s!"tick {w.tick}")
        (groupOrd.filter (fun gi =>
          decide (gi < obsAll.length) && (actTick gi == w.tick))).zipIdx)
      (by
        have h := gSimBurst_events_ge w.tick obsAll withinOrd pos (w.logOutput s!"tick {w.tick}")
          (groupOrd.filter (fun gi =>
            decide (gi < obsAll.length) && (actTick gi == w.tick))).zipIdx
          (by simpa using h_ge)
          (by
            intro nid nd h_nd d p h_kind
            obtain ⟨nd₀, h_nd₀, h_kind₀⟩ := World.logOutput_kind_preserved w
              s!"tick {w.tick}" nid nd h_nd
            rw [h_kind₀] at h_kind
            exact h_delay nid nd₀ h_nd₀ d p h_kind)
        intro ev h_ev
        rw [gSimBurst_tick]
        exact h ev h_ev)
      (gSimBurst_delay_preserved w.tick obsAll withinOrd pos (w.logOutput s!"tick {w.tick}")
        (groupOrd.filter (fun gi =>
          decide (gi < obsAll.length) && (actTick gi == w.tick))).zipIdx
        (by
          intro nid nd h_nd d p h_kind
          obtain ⟨nd₀, h_nd₀, h_kind₀⟩ := World.logOutput_kind_preserved w
            s!"tick {w.tick}" nid nd h_nd
          rw [h_kind₀] at h_kind
          exact h_delay nid nd₀ h_nd₀ d p h_kind))
    intro ev h_ev
    have h_gt := h_step_fut ev h_ev
    rw [gSimBurst_tick, World.logOutput_tick] at h_gt
    exact h_gt

/-- The delay ≥ 2 invariant survives `gSimFoldl`. -/
theorem gSimFoldl_delay_preserved (actTick : Nat → Nat) (obsAll : List (List Nat))
    (groupOrd : List Nat) (withinOrd : Nat → List Nat) (pos : Nat → List Nat)
    (w : World) (n : Nat)
    (h_delay : ∀ nid nd, w.getNode nid = some nd → ∀ d p,
        nd.kind = .repeater d p → d ≥ 2) :
    ∀ nid nd, (gSimFoldl actTick obsAll groupOrd withinOrd pos w n).getNode nid = some nd →
    ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
  induction n generalizing w with
  | zero => simpa [gSimFoldl] using h_delay
  | succ n' ih =>
    simp only [gSimFoldl, List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil]
    apply gSimBody_delay_preserved
    exact ih w h_delay

/-- After `n` ticks, every queued event targets at least `w.tick + n`. -/
theorem gSimFoldl_events_ge (actTick : Nat → Nat) (obsAll : List (List Nat))
    (groupOrd : List Nat) (withinOrd : Nat → List Nat) (pos : Nat → List Nat)
    (w : World) (n : Nat)
    (h_ge : ∀ ev ∈ w.events, ev.targetTick ≥ w.tick)
    (h_delay : ∀ nid nd, w.getNode nid = some nd → ∀ d p,
        nd.kind = .repeater d p → d ≥ 2) :
    ∀ ev ∈ (gSimFoldl actTick obsAll groupOrd withinOrd pos w n).events,
      ev.targetTick ≥ w.tick + n := by
  induction n generalizing w with
  | zero =>
    simpa [gSimFoldl] using h_ge
  | succ n' ih =>
    simp only [gSimFoldl, List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil]
    intro ev h_ev
    have h_ge' := ih w h_ge h_delay
    have h_ge'' : ∀ ev ∈ (gSimFoldl actTick obsAll groupOrd withinOrd pos w n').events,
        ev.targetTick ≥ (gSimFoldl actTick obsAll groupOrd withinOrd pos w n').tick := by
      intro ev' h_ev'
      rw [gSimFoldl_tick]
      exact h_ge' ev' h_ev'
    have h_body := gSimBody_events_future actTick obsAll groupOrd withinOrd pos
      (gSimFoldl actTick obsAll groupOrd withinOrd pos w n') n' h_ge''
      (gSimFoldl_delay_preserved actTick obsAll groupOrd withinOrd pos w n' h_delay)
    have h_gt := h_body ev h_ev
    rw [gSimFoldl_tick] at h_gt
    omega

/-! ## The initial world -/

/-- Building one group's chains adds no events. -/
private theorem buildGroupChains_no_events (gi start : Nat) (w : World)
    (g : List ChainSpec) (h : w.events = []) :
    (buildGroupChainsFrom gi start w g).1.events = [] := by
  induction g generalizing w start with
  | nil => simp [buildGroupChainsFrom, h]
  | cons c cs ih =>
    simp only [buildGroupChainsFrom]
    apply ih
    exact buildChain_no_events w (chainName gi start) c h

/-- Building groups adds no events. -/
theorem buildGroups_no_events (groups : List GroupSpec) :
    (buildGroups groups).1.events = [] := by
  suffices ∀ (start : Nat) (w : World), w.events = [] →
      (buildGroupsFrom start w groups).1.events = [] by
    exact this 0 World.empty (by simp [World.empty])
  intro start w h_empty
  induction groups generalizing w start with
  | nil => simpa [buildGroupsFrom] using h_empty
  | cons g gs ih =>
    simp only [buildGroupsFrom]
    apply ih
    exact buildGroupChains_no_events start 0 w g h_empty
