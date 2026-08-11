import BasicProofs.GroupClustering.TickBookkeeping


open BasicRedstoneSim

/-! # Group clustering — world invariants and burst event shape

The world built from valid groups satisfies the two standing invariants the
PrefixChain event lemmas need: all node ids stay below `nextId`, and all
repeaters have delay ≥ 2. On such worlds, firing observers directly appends
only future-tick events.
-/

/-! ## ids < nextId -/

/-- Bridge from the `(a, b)`-binder form of the ids invariant to the form
    `buildChain_ids_lt_nextId` expects. -/
private theorem ids_bridge (w : World)
    (h_ids : ∀ (a : Nat) (b : NodeData), (a, b) ∈ w.nodes → a < w.nextId) :
    ∀ p ∈ w.nodes, p.1 < w.nextId :=
  fun p hp => h_ids p.1 p.2 (by rw [Prod.eta p]; exact hp)

/-- `buildGroupChainsFrom` preserves "all ids below nextId". -/
theorem buildGroupChainsFrom_ids_lt_nextId (gi start : Nat) (w : World)
    (g : List ChainSpec)
    (h_ids : ∀ (a : Nat) (b : NodeData), (a, b) ∈ w.nodes → a < w.nextId) :
    ∀ (a : Nat) (b : NodeData), (a, b) ∈ (buildGroupChainsFrom gi start w g).1.nodes →
      a < (buildGroupChainsFrom gi start w g).1.nextId := by
  induction g generalizing w start with
  | nil => simp [buildGroupChainsFrom]; exact h_ids
  | cons c cs ih =>
    simp only [buildGroupChainsFrom]
    apply ih
    intro a b hab
    have h_chain := buildChain_ids_lt_nextId w (chainName gi start) c (ids_bridge w h_ids)
    simpa using h_chain (a, b) hab

/-- `buildGroupsFrom` preserves "all ids below nextId". -/
theorem buildGroupsFrom_ids_lt_nextId (start : Nat) (w : World)
    (groups : List GroupSpec)
    (h_ids : ∀ (a : Nat) (b : NodeData), (a, b) ∈ w.nodes → a < w.nextId) :
    ∀ (a : Nat) (b : NodeData), (a, b) ∈ (buildGroupsFrom start w groups).1.nodes →
      a < (buildGroupsFrom start w groups).1.nextId := by
  induction groups generalizing w start with
  | nil => simp [buildGroupsFrom]; exact h_ids
  | cons g gs ih =>
    simp only [buildGroupsFrom]
    apply ih
    exact buildGroupChainsFrom_ids_lt_nextId start 0 w g h_ids

/-- The world built by `buildGroups` has all ids below `nextId`. -/
theorem buildGroups_ids_lt_nextId (groups : List GroupSpec) :
    ∀ (a : Nat) (b : NodeData), (a, b) ∈ (buildGroups groups).1.nodes →
      a < (buildGroups groups).1.nextId := by
  simpa [buildGroups] using
    buildGroupsFrom_ids_lt_nextId 0 World.empty groups (by simp [World.empty])

/-! ## delay ≥ 2 -/

/-- `buildGroupChainsFrom` preserves "all repeater delays ≥ 2" when every
    added chain has delays ≥ 2. -/
theorem buildGroupChainsFrom_delay_ge2 (gi start : Nat) (w : World)
    (g : List ChainSpec)
    (h_w : ∀ nid nd, w.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2)
    (h_ids : ∀ (a : Nat) (b : NodeData), (a, b) ∈ w.nodes → a < w.nextId)
    (h_chains : ∀ (c : ChainSpec), c ∈ g →
        (∀ d ∈ c.middleDelays, (d : Nat) ≥ 2) ∧ (c.lastDelay : Nat) ≥ 2) :
    ∀ nid nd, (buildGroupChainsFrom gi start w g).1.getNode nid = some nd →
      ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
  induction g generalizing w start with
  | nil => simp [buildGroupChainsFrom]; exact h_w
  | cons c cs ih =>
    simp only [buildGroupChainsFrom]
    apply ih
    · exact buildChain_repeater_delay_ge2 w (chainName gi start) c
        (h_chains c (List.mem_cons.mpr (Or.inl rfl))).1
        (h_chains c (List.mem_cons.mpr (Or.inl rfl))).2
        h_w (ids_bridge w h_ids)
    · intro a b hab
      have h_chain := buildChain_ids_lt_nextId w (chainName gi start) c (ids_bridge w h_ids)
      simpa using h_chain (a, b) hab
    · intro c' hc'
      exact h_chains c' (List.mem_cons.mpr (Or.inr hc'))

/-- `buildGroupsFrom` preserves "all repeater delays ≥ 2": every group at
    index `gi` (offset by `start`) has delay-valid chains. -/
theorem buildGroupsFrom_delay_ge2 (start : Nat) (w : World)
    (groups : List GroupSpec)
    (h_w : ∀ nid nd, w.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2)
    (h_ids : ∀ (a : Nat) (b : NodeData), (a, b) ∈ w.nodes → a < w.nextId)
    (h_groups : ∀ gi, gi < groups.length → ∀ (c : ChainSpec), c ∈ groupAt groups gi →
        (∀ d ∈ c.middleDelays, (d : Nat) ≥ 2) ∧ (c.lastDelay : Nat) ≥ 2) :
    ∀ nid nd, (buildGroupsFrom start w groups).1.getNode nid = some nd →
      ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
  induction groups generalizing w start with
  | nil => simp [buildGroupsFrom]; exact h_w
  | cons g gs ih =>
    simp only [buildGroupsFrom]
    apply ih
    · apply buildGroupChainsFrom_delay_ge2 start 0 w g h_w h_ids
      intro c hc
      exact h_groups 0 (by simp) c (by simpa [groupAt] using hc)
    · exact buildGroupChainsFrom_ids_lt_nextId start 0 w g h_ids
    · intro gi' h_gi' c hc
      exact h_groups (gi' + 1) (by rw [List.length_cons]; omega) c
        (by simpa [groupAt] using hc)

/-- ValidDelay implies the ≥ 2 condition used by the event-append lemmas. -/
private theorem validDelay_ge2_pair (c : ChainSpec)
    (h : (∀ d ∈ c.middleDelays, ValidDelay d) ∧ ValidDelay c.lastDelay) :
    (∀ d ∈ c.middleDelays, (d : Nat) ≥ 2) ∧ (c.lastDelay : Nat) ≥ 2 :=
  ⟨fun d hd => ValidDelay.ge2 (h.1 d hd), ValidDelay.ge2 h.2⟩

/-- Under `h_valid`, every repeater in the built world has delay ≥ 2. -/
theorem buildGroups_delay_ge2 (groups : List GroupSpec)
    (h_valid : ∀ gi (c : ChainSpec), gi < groups.length → c ∈ groupAt groups gi →
        (∀ d ∈ c.middleDelays, ValidDelay d) ∧ ValidDelay c.lastDelay) :
    ∀ nid nd, (buildGroups groups).1.getNode nid = some nd →
      ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
  simpa [buildGroups] using
    buildGroupsFrom_delay_ge2 0 World.empty groups
      (fun nid nd h => by simp [World.empty, World.getNode] at h)
      (by simp [World.empty])
      (fun gi h_gi c hc => validDelay_ge2_pair c (h_valid gi c h_gi hc))

/-! ## Burst event shape -/

/-- Activating a group only appends events, all at strictly future ticks
    (the enqueued observer events target tick + 2). -/
theorem activateGroup_events_append (w : World) (observers : List Nat) :
    ∃ new_events, (activateGroup w observers).events = w.events ++ new_events ∧
      ∀ ev ∈ new_events, ev.targetTick > w.tick := by
  induction observers generalizing w with
  | nil => exact ⟨[], by simp [activateGroup], by simp⟩
  | cons oid os ih =>
    simp only [activateGroup, List.foldl_cons]
    obtain ⟨new, h_app, h_fut⟩ := ih
      (w.scheduleEvent { targetTick := w.tick + 2, priority := 0, nodeId := oid })
    refine ⟨{ targetTick := w.tick + 2, priority := 0, nodeId := oid } :: new, ?_, ?_⟩
    · rw [← activateGroup, h_app, World.scheduleEvent_events, List.append_assoc]
      rfl
    · intro ev h_ev
      rw [List.mem_cons] at h_ev
      rcases h_ev with rfl | h_ev
      · dsimp
        omega
      · rw [World.scheduleEvent_tick] at h_fut
        exact h_fut ev h_ev
