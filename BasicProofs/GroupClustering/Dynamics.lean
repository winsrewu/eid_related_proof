import BasicProofs.GroupClustering.NodeLayout


open BasicRedstoneSim

/-! # Group clustering — dynamics

How events are spawned and how node structure persists:

* `activateGroup_events_map`: activating a group appends exactly one observer
  event per observer, in list order, targeting `tick + 2` with priority 0.
* `World.onScheduledTick_fields_preserved` and its `step` variant: firing
  events never changes node kinds, inputs or outputs (only signal levels).
* firing an observer / middle repeater spawns the next stage event with the
  correct target tick, priority and node id;
* firing a last repeater appends the chain's output-log entry and spawns
  nothing.
-/

/-- Activating a group appends exactly the observer events, in list order. -/
theorem activateGroup_events_map (w : World) (observers : List Nat) :
    (activateGroup w observers).events =
    w.events ++ observers.map (fun nid =>
      ({ targetTick := w.tick + 2, priority := 0, nodeId := nid } : ScheduledEvent)) := by
  induction observers generalizing w with
  | nil => simp [activateGroup]
  | cons oid os ih =>
    show (activateGroup
        (w.scheduleEvent { targetTick := w.tick + 2, priority := 0, nodeId := oid }) os).events =
      w.events ++ List.map (fun nid =>
        ({ targetTick := w.tick + 2, priority := 0, nodeId := nid } : ScheduledEvent)) (oid :: os)
    rw [ih, World.scheduleEvent_tick, World.scheduleEvent_events, List.append_assoc]
    rfl

/-- Firing a node changes no node's kind, inputs or outputs. -/
theorem World.onScheduledTick_fields_preserved (w : World) (tickId nid : Nat)
    (nd : NodeData) (h : (w.onScheduledTick tickId).getNode nid = some nd) :
    ∃ nd₀, w.getNode nid = some nd₀ ∧ nd.kind = nd₀.kind ∧
      nd.inputs = nd₀.inputs ∧ nd.outputs = nd₀.outputs := by
  dsimp only [World.onScheduledTick] at h
  cases h_tick : w.getNode tickId with
  | none => simp [h_tick] at h; exact ⟨nd, h, rfl, rfl, rfl⟩
  | some nd_tick =>
    simp only [h_tick] at h
    cases h_kind : nd_tick.kind with
    | input => simp [h_kind] at h; exact ⟨nd, h, rfl, rfl, rfl⟩
    | output nm => simp [h_kind] at h; exact ⟨nd, h, rfl, rfl, rfl⟩
    | observer =>
      simp only [h_kind] at h
      rw [World.notifyOutputs_getNode] at h
      by_cases h_eq : tickId = nid
      · rw [← h_eq] at h
        have h_upd := World.updateNode_getNode_eq w tickId
          (fun nd' => ({ nd' with sigLevel := 15 } : NodeData)) nd_tick h_tick
        rw [h_upd] at h
        injection h with h_nd_eq
        have h_tick' : w.getNode nid = some nd_tick := by rw [← h_eq]; exact h_tick
        refine ⟨nd_tick, h_tick', ?_, ?_, ?_⟩ <;> rw [← h_nd_eq]
      · rw [World.updateNode_getNode_ne w tickId nid _ h_eq] at h
        exact ⟨nd, h, rfl, rfl, rfl⟩
    | repeater d p =>
      simp only [h_kind] at h
      rw [World.notifyOutputs_getNode] at h
      by_cases h_eq : tickId = nid
      · rw [← h_eq] at h
        have h_upd := World.updateNode_getNode_eq w tickId
          (fun nd' => ({ nd' with
              sigLevel := if w.getInputSignal tickId > 0 then 15 else 0 } : NodeData))
          nd_tick h_tick
        rw [h_upd] at h
        injection h with h_nd_eq
        have h_tick' : w.getNode nid = some nd_tick := by rw [← h_eq]; exact h_tick
        refine ⟨nd_tick, h_tick', ?_, ?_, ?_⟩ <;> rw [← h_nd_eq]
      · rw [World.updateNode_getNode_ne w tickId nid _ h_eq] at h
        exact ⟨nd, h, rfl, rfl, rfl⟩

/-- One `step` changes no node's kind, inputs or outputs. -/
theorem step_fields_preserved (w w' : World) (h_step : w.step = some w')
    (nid : Nat) (nd : NodeData) (h : w'.getNode nid = some nd) :
    ∃ nd₀, w.getNode nid = some nd₀ ∧ nd.kind = nd₀.kind ∧
      nd.inputs = nd₀.inputs ∧ nd.outputs = nd₀.outputs := by
  dsimp [World.step] at h_step
  cases h_pop : w.popNextEvent with
  | none => simp [h_pop] at h_step
  | some p =>
    cases p with | mk ev w_pop =>
    simp only [h_pop] at h_step
    injection h_step with h_w'_eq
    have h_nodes_pop : w_pop.nodes = w.nodes := World.popNextEvent_nodes w ev w_pop h_pop
    have h_gn : (w_pop.onScheduledTick ev.nodeId).getNode nid = some nd := by
      rw [h_w'_eq]
      exact h
    obtain ⟨nd₁, h_nd₁, h_kind, h_inputs, h_outputs⟩ :=
      World.onScheduledTick_fields_preserved w_pop ev.nodeId nid nd h_gn
    have h_nd_w : w.getNode nid = some nd₁ := by
      dsimp [World.getNode] at h_nd₁
      rw [h_nodes_pop] at h_nd₁
      exact h_nd₁
    exact ⟨nd₁, h_nd_w, h_kind, h_inputs, h_outputs⟩

/-- Firing an observer spawns exactly the event of its (single) output
    repeater. -/
theorem World.onScheduledTick_observer_spawns (w : World) (nid rep : Nat)
    (nd nd_rep : NodeData) (d : PNat) (p : Int)
    (h_obs : w.getNode nid = some nd) (h_kind : nd.kind = .observer)
    (h_outputs : nd.outputs = [rep])
    (h_rep : w.getNode rep = some nd_rep)
    (h_kind_rep : nd_rep.kind = .repeater d p) :
    (w.onScheduledTick nid).events =
    w.events ++ [{ targetTick := w.tick + (d : Nat), priority := p, nodeId := rep }] := by
  dsimp [World.onScheduledTick]
  rw [h_obs]
  simp only
  rw [h_kind]
  dsimp [World.notifyOutputs]
  have h_upd_gn : (w.updateNode nid
      (fun nd' => ({ nd' with sigLevel := 15 } : NodeData))).getNode nid =
      some ({ nd with sigLevel := 15 } : NodeData) :=
    World.updateNode_getNode_eq w nid _ nd h_obs
  rw [h_upd_gn]
  simp only
  rw [h_outputs]
  simp only [List.foldl_cons, List.foldl_nil]
  dsimp [World.onNeighborUpdate]
  have h_ne : nid ≠ rep := by
    intro h_eq
    have h_gn : w.getNode nid = w.getNode rep := congr_arg (fun i => w.getNode i) h_eq
    have h_nd_eq : nd = nd_rep := by rw [h_obs, h_rep] at h_gn; exact Option.some_inj.mp h_gn
    rw [← h_nd_eq, h_kind] at h_kind_rep
    injection h_kind_rep
  rw [World.updateNode_getNode_ne w nid rep _ h_ne, h_rep]
  simp only
  rw [h_kind_rep]
  simp [World.scheduleEvent_events, World.updateNode_events]

/-- Firing a repeater spawns exactly the event of its (single) output
    repeater. -/
theorem World.onScheduledTick_repeater_spawns (w : World) (nid nxt : Nat)
    (nd nd_next : NodeData) (d : PNat) (p p' : Int) (d' : PNat)
    (h_rep : w.getNode nid = some nd) (h_kind : nd.kind = .repeater d p)
    (h_outputs : nd.outputs = [nxt]) (h_ne : nid ≠ nxt)
    (h_next : w.getNode nxt = some nd_next)
    (h_kind_next : nd_next.kind = .repeater d' p') :
    (w.onScheduledTick nid).events =
    w.events ++ [{ targetTick := w.tick + (d' : Nat), priority := p', nodeId := nxt }] := by
  dsimp [World.onScheduledTick]
  rw [h_rep]
  simp only
  rw [h_kind]
  dsimp [World.notifyOutputs]
  have h_upd_gn : (w.updateNode nid
      (fun nd' => ({ nd' with
          sigLevel := if w.getInputSignal nid > 0 then 15 else 0 } : NodeData))).getNode nid =
      some ({ nd with
          sigLevel := if w.getInputSignal nid > 0 then 15 else 0 } : NodeData) :=
    World.updateNode_getNode_eq w nid _ nd h_rep
  rw [h_upd_gn]
  simp only
  rw [h_outputs]
  simp only [List.foldl_cons, List.foldl_nil]
  dsimp [World.onNeighborUpdate]
  rw [World.updateNode_getNode_ne w nid nxt _ h_ne, h_next]
  simp only
  rw [h_kind_next]
  simp [World.scheduleEvent_events, World.updateNode_events]

/-- Firing the last repeater of a chain appends the chain's output entry and
    spawns no events. -/
theorem World.onScheduledTick_lastRep_logs (w : World) (nid out : Nat)
    (nd nd_out : NodeData) (d : PNat) (nm : String)
    (h_rep : w.getNode nid = some nd) (h_kind : nd.kind = .repeater d (-1))
    (h_outputs : nd.outputs = [out])
    (h_out : w.getNode out = some nd_out)
    (h_kind_out : nd_out.kind = .output nm) :
    ∃ (v : Nat), (w.onScheduledTick nid).outputLog = w.outputLog ++ [s!"{nm}: {v}"] ∧
      (w.onScheduledTick nid).events = w.events := by
  set f := fun (nd' : NodeData) => ({ nd' with sigLevel := if w.getInputSignal nid > 0 then 15 else 0 } : NodeData)
  have h_ne : nid ≠ out := by
    intro h_eq
    have h_gn : w.getNode nid = w.getNode out := congr_arg (fun i => w.getNode i) h_eq
    have h_nd_eq : nd = nd_out := by rw [h_rep, h_out] at h_gn; exact Option.some_inj.mp h_gn
    rw [← h_nd_eq, h_kind] at h_kind_out
    injection h_kind_out
  have h_red : w.onScheduledTick nid =
      (w.updateNode nid f).logOutput s!"{nm}: {(w.updateNode nid f).getInputSignal out}" := by
    dsimp [World.onScheduledTick, f]
    rw [h_rep]
    simp only
    rw [h_kind]
    dsimp [World.notifyOutputs]
    rw [World.updateNode_getNode_eq w nid f nd h_rep]
    simp only
    rw [h_outputs]
    simp only [List.foldl_cons, List.foldl_nil]
    dsimp [World.onNeighborUpdate]
    rw [World.updateNode_getNode_ne w nid out _ h_ne, h_out]
    simp only
    rw [h_kind_out]
  refine ⟨(w.updateNode nid f).getInputSignal out, ?_, ?_⟩
  · rw [h_red]
    simp [World.logOutput, World.updateNode]
  · rw [h_red]
    simp [World.logOutput_events, World.updateNode_events]

/-! ## Lifting fields preservation through the simulation -/

/-- `processNEvents` preserves node kinds, inputs and outputs. -/
theorem processNEvents_fields_preserved (w : World) (n : Nat) :
    ∀ nid nd, (processNEvents w n).getNode nid = some nd →
    ∃ nd₀, w.getNode nid = some nd₀ ∧ nd.kind = nd₀.kind ∧
      nd.inputs = nd₀.inputs ∧ nd.outputs = nd₀.outputs := by
  induction n generalizing w with
  | zero => intro nid nd h; exact ⟨nd, h, rfl, rfl, rfl⟩
  | succ n' ih =>
    intro nid nd h
    dsimp [processNEvents] at h
    cases h_step : w.step with
    | none => simp [h_step] at h; exact ⟨nd, h, rfl, rfl, rfl⟩
    | some w' =>
      simp [h_step] at h
      obtain ⟨nd₁, h₁, hk₁, hin₁, hout₁⟩ := ih w' nid nd h
      obtain ⟨nd₀, h₀, hk₀, hin₀, hout₀⟩ := step_fields_preserved w w' h_step nid nd₁ h₁
      exact ⟨nd₀, h₀, hk₁.trans hk₀, hin₁.trans hin₀, hout₁.trans hout₀⟩

/-- `stepUntilNextTick` preserves node kinds, inputs and outputs. -/
theorem World.stepUntilNextTick_fields_preserved (w : World) :
    ∀ nid nd, (w.stepUntilNextTick).getNode nid = some nd →
    ∃ nd₀, w.getNode nid = some nd₀ ∧ nd.kind = nd₀.kind ∧
      nd.inputs = nd₀.inputs ∧ nd.outputs = nd₀.outputs := by
  induction w using World.stepUntilNextTick.induct with
  | case1 x h_step =>
    intro nid nd h
    rw [stepUntilNextTick_of_step_none x h_step] at h
    dsimp [World.getNode] at h ⊢
    exact ⟨nd, h, rfl, rfl, rfl⟩
  | case2 x w' h_step' ih =>
    intro nid nd h
    have h_sunt : x.stepUntilNextTick = w'.stepUntilNextTick := by
      rw [World.stepUntilNextTick, h_step']
    rw [h_sunt] at h
    obtain ⟨nd₁, h₁, hk₁, hin₁, hout₁⟩ := ih nid nd h
    obtain ⟨nd₀, h₀, hk₀, hin₀, hout₀⟩ := step_fields_preserved x w' h_step' nid nd₁ h₁
    exact ⟨nd₀, h₀, hk₁.trans hk₀, hin₁.trans hin₀, hout₁.trans hout₀⟩

/-- `activateGroup` preserves node kinds, inputs and outputs. -/
private theorem activateGroup_fields_preserved (w : World) (observers : List Nat) :
    ∀ nid nd, (activateGroup w observers).getNode nid = some nd →
    ∃ nd₀, w.getNode nid = some nd₀ ∧ nd.kind = nd₀.kind ∧
      nd.inputs = nd₀.inputs ∧ nd.outputs = nd₀.outputs := by
  intro nid nd h
  dsimp [World.getNode] at h
  rw [activateGroup_nodes] at h
  exact ⟨nd, h, rfl, rfl, rfl⟩

/-- `logOutput` preserves node kinds, inputs and outputs. -/
private theorem logOutput_fields_preserved (w : World) (msg : String) :
    ∀ nid nd, (w.logOutput msg).getNode nid = some nd →
    ∃ nd₀, w.getNode nid = some nd₀ ∧ nd.kind = nd₀.kind ∧
      nd.inputs = nd₀.inputs ∧ nd.outputs = nd₀.outputs := by
  intro nid nd h
  exact ⟨nd, by dsimp [World.getNode, World.logOutput] at h ⊢; exact h, rfl, rfl, rfl⟩

/-- The burst phase preserves node kinds, inputs and outputs. -/
theorem gSimBurst_fields_preserved (t : Nat) (obsAll : List (List Nat))
    (withinOrd : Nat → List Nat) (pos : Nat → List Nat) (w : World)
    (pairs : List (Nat × Nat)) :
    ∀ nid nd, (gSimBurst t obsAll withinOrd pos w pairs).getNode nid = some nd →
    ∃ nd₀, w.getNode nid = some nd₀ ∧ nd.kind = nd₀.kind ∧
      nd.inputs = nd₀.inputs ∧ nd.outputs = nd₀.outputs := by
  induction pairs generalizing w with
  | nil => intro nid nd h; simp [gSimBurst] at h; exact ⟨nd, h, rfl, rfl, rfl⟩
  | cons p ps ih =>
    simp only [gSimBurst, List.foldl_cons]
    rcases p with ⟨gi, k⟩
    intro nid nd h
    obtain ⟨nd₁, h_nd₁, hk₁, hin₁, hout₁⟩ := ih
      (activateGroup (processNEvents w ((pos t)[k]?.getD 0))
        ((withinOrd gi).foldl (fun acc ci =>
          match (obsAll[gi]?.getD [])[ci]? with
          | some oid => acc ++ [oid]
          | none => acc) [])) nid nd h
    obtain ⟨nd₂, h_nd₂, hk₂, hin₂, hout₂⟩ := activateGroup_fields_preserved
      (processNEvents w ((pos t)[k]?.getD 0))
      ((withinOrd gi).foldl (fun acc ci =>
        match (obsAll[gi]?.getD [])[ci]? with
        | some oid => acc ++ [oid]
        | none => acc) []) nid nd₁ h_nd₁
    obtain ⟨nd₀, h_nd₀, hk₀, hin₀, hout₀⟩ := processNEvents_fields_preserved w
      ((pos t)[k]?.getD 0) nid nd₂ h_nd₂
    exact ⟨nd₀, h_nd₀, by rw [hk₁, hk₂, hk₀], by rw [hin₁, hin₂, hin₀],
      by rw [hout₁, hout₂, hout₀]⟩

/-- One `gSimBody` call preserves node kinds, inputs and outputs. -/
theorem gSimBody_fields_preserved (actTick : Nat → Nat) (obsAll : List (List Nat))
    (groupOrd : List Nat) (withinOrd : Nat → List Nat) (pos : Nat → List Nat)
    (w : World) (i : Nat) :
    ∀ nid nd, (gSimBody actTick obsAll groupOrd withinOrd pos w i).getNode nid = some nd →
    ∃ nd₀, w.getNode nid = some nd₀ ∧ nd.kind = nd₀.kind ∧
      nd.inputs = nd₀.inputs ∧ nd.outputs = nd₀.outputs := by
  dsimp [gSimBody]
  split_ifs with h_active
  · intro nid nd h_nd
    obtain ⟨nd₁, h_nd₁, hk₁, hin₁, hout₁⟩ := World.stepUntilNextTick_fields_preserved
      (w.logOutput s!"tick {w.tick}") nid nd h_nd
    obtain ⟨nd₀, h_nd₀, hk₀, hin₀, hout₀⟩ := logOutput_fields_preserved w
      s!"tick {w.tick}" nid nd₁ h_nd₁
    exact ⟨nd₀, h_nd₀, by rw [hk₁, hk₀], by rw [hin₁, hin₀], by rw [hout₁, hout₀]⟩
  · intro nid nd h_nd
    obtain ⟨nd₁, h_nd₁, hk₁, hin₁, hout₁⟩ := World.stepUntilNextTick_fields_preserved
      (gSimBurst w.tick obsAll withinOrd pos (w.logOutput s!"tick {w.tick}")
        (groupOrd.filter (fun gi =>
          decide (gi < obsAll.length) && (actTick gi == w.tick))).zipIdx) nid nd h_nd
    obtain ⟨nd₂, h_nd₂, hk₂, hin₂, hout₂⟩ := gSimBurst_fields_preserved w.tick obsAll
      withinOrd pos (w.logOutput s!"tick {w.tick}")
      (groupOrd.filter (fun gi =>
        decide (gi < obsAll.length) && (actTick gi == w.tick))).zipIdx nid nd₁ h_nd₁
    obtain ⟨nd₀, h_nd₀, hk₀, hin₀, hout₀⟩ := logOutput_fields_preserved w
      s!"tick {w.tick}" nid nd₂ h_nd₂
    exact ⟨nd₀, h_nd₀, by rw [hk₁, hk₂, hk₀], by rw [hin₁, hin₂, hin₀],
      by rw [hout₁, hout₂, hout₀]⟩

/-- The whole `n`-tick simulation preserves node kinds, inputs and outputs. -/
theorem gSimFoldl_fields_preserved (actTick : Nat → Nat) (obsAll : List (List Nat))
    (groupOrd : List Nat) (withinOrd : Nat → List Nat) (pos : Nat → List Nat)
    (w : World) (n : Nat) :
    ∀ nid nd, (gSimFoldl actTick obsAll groupOrd withinOrd pos w n).getNode nid = some nd →
    ∃ nd₀, w.getNode nid = some nd₀ ∧ nd.kind = nd₀.kind ∧
      nd.inputs = nd₀.inputs ∧ nd.outputs = nd₀.outputs := by
  induction n generalizing w with
  | zero =>
    intro nid nd h
    exact ⟨nd, by simpa [gSimFoldl] using h, rfl, rfl, rfl⟩
  | succ n' ih =>
    simp only [gSimFoldl, List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil]
    intro nid nd h
    obtain ⟨nd₁, h_nd₁, hk₁, hin₁, hout₁⟩ := gSimBody_fields_preserved actTick obsAll
      groupOrd withinOrd pos (gSimFoldl actTick obsAll groupOrd withinOrd pos w n') n'
      nid nd h
    obtain ⟨nd₀, h_nd₀, hk₀, hin₀, hout₀⟩ := ih w nid nd₁ h_nd₁
    exact ⟨nd₀, h_nd₀, by rw [hk₁, hk₀], by rw [hin₁, hin₀], by rw [hout₁, hout₀]⟩
