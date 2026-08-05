import BasicProofs.PrefixChain.Part05


open BasicRedstoneSim

/-- `processNEvents` preserves "all events have priority < 100". -/
theorem processNEvents_events_pri (w : World) (n : Nat)
    (h_pri : ∀ ev ∈ w.events, ev.priority < 100)
    (h_np : ∀ nid nd, w.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 100)
    (h_delay : ∀ nid nd, w.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2) :
    ∀ ev ∈ (processNEvents w n).events, ev.priority < 100 := by
  induction n generalizing w with
  | zero => simpa [processNEvents] using h_pri
  | succ n' ih =>
    simp only [processNEvents]
    cases h_step : w.step with
    | none => simpa [h_step] using h_pri
    | some w' =>
      cases h_pop : w.popNextEvent with
      | none => simp [World.step, h_pop] at h_step
      | some p =>
        cases p with | mk ev_pop w_pop =>
        simp only [World.step, h_pop] at h_step
        injection h_step with h_w'_eq
        have h_nodes_pop : w_pop.nodes = w.nodes :=
          World.popNextEvent_nodes w ev_pop w_pop h_pop
        have h_np_pop : ∀ nid nd, w_pop.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 100 := by
          intro nid nd h_nd d p h_kind
          have h_nd_w : w.getNode nid = some nd := by dsimp [World.getNode]; rw [← h_nodes_pop]; exact h_nd
          exact h_np nid nd h_nd_w d p h_kind
        have h_delay_pop : ∀ nid nd, w_pop.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
          intro nid nd h_nd d p h_kind
          have h_nd_w : w.getNode nid = some nd := by dsimp [World.getNode]; rw [← h_nodes_pop]; exact h_nd
          exact h_delay nid nd h_nd_w d p h_kind
        have h_pri' : ∀ ev' ∈ w'.events, ev'.priority < 100 := by
          intro ev' h_ev'
          rw [← h_w'_eq] at h_ev'
          by_cases h_old : ev' ∈ w_pop.events
          · have h_erase := World.popNextEvent_eraseIdx w ev_pop w_pop h_pop
            obtain ⟨idx, _, h_erase_eq, _, _, _⟩ := h_erase
            have h_old_w : ev' ∈ w.events := by
              rw [h_erase_eq] at h_old
              exact List.mem_of_mem_eraseIdx h_old
            exact h_pri ev' h_old_w
          · have h_new := World.onScheduledTick_new_events w_pop ev_pop.nodeId h_np_pop h_delay_pop
            exact h_new.1 ev' h_ev' h_old
        have h_np' : ∀ nid nd, w'.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 100 := by
          intro nid nd h_nd d p h_kind
          have h_kind_orig := World.onScheduledTick_getNode_kind w_pop ev_pop.nodeId nid nd
            (by rwa [h_w'_eq])
          obtain ⟨nd_orig, h_orig, h_kind_eq⟩ := h_kind_orig
          have h_orig_w : w.getNode nid = some nd_orig := by
            dsimp [World.getNode]; rw [← h_nodes_pop]; exact h_orig
          rw [← h_kind_eq] at h_kind
          exact h_np nid nd_orig h_orig_w d p h_kind
        have h_delay' : ∀ nid nd, w'.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
          intro nid nd h_nd d p h_kind
          have h_kind_orig := World.onScheduledTick_getNode_kind w_pop ev_pop.nodeId nid nd
            (by rwa [h_w'_eq])
          obtain ⟨nd_orig, h_orig, h_kind_eq⟩ := h_kind_orig
          have h_orig_w : w.getNode nid = some nd_orig := by
            dsimp [World.getNode]; rw [← h_nodes_pop]; exact h_orig
          rw [← h_kind_eq] at h_kind
          exact h_delay nid nd_orig h_orig_w d p h_kind
        exact ih w' h_pri' h_np' h_delay'

/-- `stepUntilNextTick` preserves "all events have priority < 100". -/
theorem stepUntilNextTick_events_pri (w : World)
    (h_pri : ∀ ev ∈ w.events, ev.priority < 100)
    (h_np : ∀ nid nd, w.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 100)
    (h_delay : ∀ nid nd, w.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2) :
    ∀ ev ∈ (w.stepUntilNextTick).events, ev.priority < 100 := by
  suffices ∀ w : World, (∀ ev ∈ w.events, ev.priority < 100) →
      (∀ nid nd, w.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 100) →
      (∀ nid nd, w.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2) →
      ∀ ev ∈ (w.stepUntilNextTick).events, ev.priority < 100 from
    this w h_pri h_np h_delay
  intro w h_pri h_np h_delay
  induction w using World.stepUntilNextTick.induct with
  | case1 w h_step =>
    rw [stepUntilNextTick_of_step_none w h_step]; exact h_pri
  | case2 w w' h_step' ih =>
    have h_sunt : w.stepUntilNextTick = w'.stepUntilNextTick := by
      rw [World.stepUntilNextTick, h_step']
    rw [h_sunt]
    dsimp [World.step] at h_step'
    cases h_pop : w.popNextEvent with
    | none => simp [h_pop] at h_step'
    | some p =>
      cases p with | mk ev_pop w_pop =>
      simp only [h_pop] at h_step'
      injection h_step' with h_w'_eq
      have h_nodes_pop : w_pop.nodes = w.nodes :=
        World.popNextEvent_nodes w ev_pop w_pop h_pop
      have h_np_pop : ∀ nid nd, w_pop.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 100 := by
        intro nid nd h_nd d p h_kind
        have h_nd_w : w.getNode nid = some nd := by dsimp [World.getNode]; rw [← h_nodes_pop]; exact h_nd
        exact h_np nid nd h_nd_w d p h_kind
      have h_delay_pop : ∀ nid nd, w_pop.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
        intro nid nd h_nd d p h_kind
        have h_nd_w : w.getNode nid = some nd := by dsimp [World.getNode]; rw [← h_nodes_pop]; exact h_nd
        exact h_delay nid nd h_nd_w d p h_kind
      have h_pri' : ∀ ev' ∈ w'.events, ev'.priority < 100 := by
        intro ev' h_ev'
        rw [← h_w'_eq] at h_ev'
        by_cases h_old : ev' ∈ w_pop.events
        · have h_erase := World.popNextEvent_eraseIdx w ev_pop w_pop h_pop
          obtain ⟨idx, _, h_erase_eq, _, _, _⟩ := h_erase
          have h_old_w : ev' ∈ w.events := by
            rw [h_erase_eq] at h_old
            exact List.mem_of_mem_eraseIdx h_old
          exact h_pri ev' h_old_w
        · have h_new := World.onScheduledTick_new_events w_pop ev_pop.nodeId h_np_pop h_delay_pop
          exact h_new.1 ev' h_ev' h_old
      have h_np' : ∀ nid nd, w'.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 100 := by
        intro nid nd h_nd d p h_kind
        have h_kind_orig := World.onScheduledTick_getNode_kind w_pop ev_pop.nodeId nid nd
          (by rwa [h_w'_eq])
        obtain ⟨nd_orig, h_orig, h_kind_eq⟩ := h_kind_orig
        have h_orig_w : w.getNode nid = some nd_orig := by
          dsimp [World.getNode]; rw [← h_nodes_pop]; exact h_orig
        rw [← h_kind_eq] at h_kind
        exact h_np nid nd_orig h_orig_w d p h_kind
      have h_delay' : ∀ nid nd, w'.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
        intro nid nd h_nd d p h_kind
        have h_kind_orig := World.onScheduledTick_getNode_kind w_pop ev_pop.nodeId nid nd
          (by rwa [h_w'_eq])
        obtain ⟨nd_orig, h_orig, h_kind_eq⟩ := h_kind_orig
        have h_orig_w : w.getNode nid = some nd_orig := by
          dsimp [World.getNode]; rw [← h_nodes_pop]; exact h_orig
        rw [← h_kind_eq] at h_kind
        exact h_delay nid nd_orig h_orig_w d p h_kind
      exact ih h_pri' h_np' h_delay'

/-- `simBody` preserves "all events have priority < 100". -/
theorem simBody_events_pri (t1 t2 pos in1 in2 : Nat) (w : World) (i : Nat)
    (h_pri : ∀ ev ∈ w.events, ev.priority < 100)
    (h_np : ∀ nid nd, w.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 100)
    (h_delay : ∀ nid nd, w.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2) :
    ∀ ev ∈ (simBody t1 t2 pos in1 in2 w i).events, ev.priority < 100 := by
  dsimp (config := { zeta := true }) [simBody]
  -- After logOutput, events/nodes/kinds are preserved
  set w₀ := w.logOutput s!"tick {w.tick}"
  have h_pri₀ : ∀ ev ∈ w₀.events, ev.priority < 100 := by simpa [w₀] using h_pri
  have h_np₀ : ∀ nid nd, w₀.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 100 := by
    intro nid nd h_nd d p h_kind; simpa [w₀] using h_np nid nd h_nd d p h_kind
  have h_delay₀ : ∀ nid nd, w₀.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
    intro nid nd h_nd d p h_kind; simpa [w₀] using h_delay nid nd h_nd d p h_kind
  split_ifs with h_tick1 h_tick2
  · -- tick = t1 and tick = t2: setInput in1, processNEvents, setInput in2, stepUntilNextTick
    have h_pri₁ := setInput_events_pri w₀ in1 15 h_pri₀ h_np₀
    have h_np₁ : ∀ nid nd, (w₀.setInput in1 15).getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 100 := by
      intro nid nd h_nd d p h_kind
      obtain ⟨nd₀, h₀, hkeq⟩ := World.setInput_kind_preserved w₀ in1 15 nid nd h_nd
      rw [hkeq] at h_kind; exact h_np₀ nid nd₀ h₀ d p h_kind
    have h_delay₁ : ∀ nid nd, (w₀.setInput in1 15).getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
      intro nid nd h_nd d p h_kind
      obtain ⟨nd₀, h₀, hkeq⟩ := World.setInput_kind_preserved w₀ in1 15 nid nd h_nd
      rw [hkeq] at h_kind; exact h_delay₀ nid nd₀ h₀ d p h_kind
    have h_pri₂ := processNEvents_events_pri (w₀.setInput in1 15) pos h_pri₁ h_np₁ h_delay₁
    have h_np₂ : ∀ nid nd, (processNEvents (w₀.setInput in1 15) pos).getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 100 := by
      intro nid nd h_nd d p h_kind
      obtain ⟨nd₀, h₀, hkeq⟩ := processNEvents_kind_preserved (w₀.setInput in1 15) pos nid nd h_nd
      rw [hkeq] at h_kind; exact h_np₁ nid nd₀ h₀ d p h_kind
    have h_delay₂ : ∀ nid nd, (processNEvents (w₀.setInput in1 15) pos).getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
      intro nid nd h_nd d p h_kind
      obtain ⟨nd₀, h₀, hkeq⟩ := processNEvents_kind_preserved (w₀.setInput in1 15) pos nid nd h_nd
      rw [hkeq] at h_kind; exact h_delay₁ nid nd₀ h₀ d p h_kind
    have h_pri₃ := setInput_events_pri (processNEvents (w₀.setInput in1 15) pos) in2 15 h_pri₂ h_np₂
    have h_np₃ : ∀ nid nd, (processNEvents (w₀.setInput in1 15) pos |>.setInput in2 15).getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 100 := by
      intro nid nd h_nd d p h_kind
      obtain ⟨nd₀, h₀, hkeq⟩ := World.setInput_kind_preserved (processNEvents (w₀.setInput in1 15) pos) in2 15 nid nd h_nd
      rw [hkeq] at h_kind; exact h_np₂ nid nd₀ h₀ d p h_kind
    have h_delay₃ : ∀ nid nd, (processNEvents (w₀.setInput in1 15) pos |>.setInput in2 15).getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
      intro nid nd h_nd d p h_kind
      obtain ⟨nd₀, h₀, hkeq⟩ := World.setInput_kind_preserved (processNEvents (w₀.setInput in1 15) pos) in2 15 nid nd h_nd
      rw [hkeq] at h_kind; exact h_delay₂ nid nd₀ h₀ d p h_kind
    exact stepUntilNextTick_events_pri _ h_pri₃ h_np₃ h_delay₃
  · -- tick = t1, tick ≠ t2: setInput in1, stepUntilNextTick
    have h_pri₁ := setInput_events_pri w₀ in1 15 h_pri₀ h_np₀
    have h_np₁ : ∀ nid nd, (w₀.setInput in1 15).getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 100 := by
      intro nid nd h_nd d p h_kind
      obtain ⟨nd₀, h₀, hkeq⟩ := World.setInput_kind_preserved w₀ in1 15 nid nd h_nd
      rw [hkeq] at h_kind; exact h_np₀ nid nd₀ h₀ d p h_kind
    have h_delay₁ : ∀ nid nd, (w₀.setInput in1 15).getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
      intro nid nd h_nd d p h_kind
      obtain ⟨nd₀, h₀, hkeq⟩ := World.setInput_kind_preserved w₀ in1 15 nid nd h_nd
      rw [hkeq] at h_kind; exact h_delay₀ nid nd₀ h₀ d p h_kind
    exact stepUntilNextTick_events_pri _ h_pri₁ h_np₁ h_delay₁
  · -- tick ≠ t1, tick = t2: processNEvents, setInput in2, stepUntilNextTick
    have h_pri₁ := processNEvents_events_pri w₀ pos h_pri₀ h_np₀ h_delay₀
    have h_np₁ : ∀ nid nd, (processNEvents w₀ pos).getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 100 := by
      intro nid nd h_nd d p h_kind
      obtain ⟨nd₀, h₀, hkeq⟩ := processNEvents_kind_preserved w₀ pos nid nd h_nd
      rw [hkeq] at h_kind; exact h_np₀ nid nd₀ h₀ d p h_kind
    have h_delay₁ : ∀ nid nd, (processNEvents w₀ pos).getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
      intro nid nd h_nd d p h_kind
      obtain ⟨nd₀, h₀, hkeq⟩ := processNEvents_kind_preserved w₀ pos nid nd h_nd
      rw [hkeq] at h_kind; exact h_delay₀ nid nd₀ h₀ d p h_kind
    have h_pri₂ := setInput_events_pri (processNEvents w₀ pos) in2 15 h_pri₁ h_np₁
    have h_np₂ : ∀ nid nd, (processNEvents w₀ pos |>.setInput in2 15).getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 100 := by
      intro nid nd h_nd d p h_kind
      obtain ⟨nd₀, h₀, hkeq⟩ := World.setInput_kind_preserved (processNEvents w₀ pos) in2 15 nid nd h_nd
      rw [hkeq] at h_kind; exact h_np₁ nid nd₀ h₀ d p h_kind
    have h_delay₂ : ∀ nid nd, (processNEvents w₀ pos |>.setInput in2 15).getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
      intro nid nd h_nd d p h_kind
      obtain ⟨nd₀, h₀, hkeq⟩ := World.setInput_kind_preserved (processNEvents w₀ pos) in2 15 nid nd h_nd
      rw [hkeq] at h_kind; exact h_delay₁ nid nd₀ h₀ d p h_kind
    exact stepUntilNextTick_events_pri _ h_pri₂ h_np₂ h_delay₂
  · -- tick ≠ t1, tick ≠ t2: stepUntilNextTick
    exact stepUntilNextTick_events_pri w₀ h_pri₀ h_np₀ h_delay₀

/-- `simFoldl` preserves "all events have priority < 100". -/
theorem simFoldl_events_pri (w : World) (t1 t2 pos in1 in2 : Nat) (n : Nat)
    (h_pri : ∀ ev ∈ w.events, ev.priority < 100)
    (h_np : ∀ nid nd, w.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 100)
    (h_delay : ∀ nid nd, w.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2) :
    ∀ ev ∈ ((List.range n).foldl (simBody t1 t2 pos in1 in2) w).events, ev.priority < 100 := by
  induction n generalizing w with
  | zero => intro ev h_ev; simpa using h_pri ev h_ev
  | succ n' ih =>
    intro ev h_ev
    rw [List.range_succ, List.foldl_append] at h_ev
    simp only [List.foldl_cons, List.foldl_nil] at h_ev
    set w_mid := (List.range n').foldl (simBody t1 t2 pos in1 in2) w
    have h_pri_mid : ∀ ev ∈ w_mid.events, ev.priority < 100 :=
      ih w h_pri h_np h_delay
    have h_np_mid : ∀ nid nd, w_mid.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 100 := by
      intro nid nd h_nd d p h_kind
      obtain ⟨nd₀, h₀, hkeq⟩ := simFoldl_kind_preserved w t1 t2 pos in1 in2 n' nid nd h_nd
      rw [hkeq] at h_kind; exact h_np nid nd₀ h₀ d p h_kind
    have h_delay_mid : ∀ nid nd, w_mid.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
      intro nid nd h_nd d p h_kind
      obtain ⟨nd₀, h₀, hkeq⟩ := simFoldl_kind_preserved w t1 t2 pos in1 in2 n' nid nd h_nd
      rw [hkeq] at h_kind; exact h_delay nid nd₀ h₀ d p h_kind
    exact simBody_events_pri t1 t2 pos in1 in2 w_mid n' h_pri_mid h_np_mid h_delay_mid ev h_ev

/-! ### Layer 7: buildChain structural properties -/

/-- `addNode` returns `w.nextId` as the new node's ID. -/
theorem World.addNode_fst (w : World) (nd : NodeData) :
    (w.addNode nd).1 = w.nextId := rfl

/-- `addNode` increments `nextId` by 1. -/
theorem World.addNode_nextId (w : World) (nd : NodeData) :
    (w.addNode nd).2.nextId = w.nextId + 1 := rfl

/-- The foldl in `buildChain` increments `nextId` by `delays.length`. -/
theorem buildChain_foldl_nextId (delays : List PNat) :
    ∀ (ids : List Nat) (w₀ : World),
    (delays.foldl (fun (acc : List Nat × World) delay =>
      let (repId, w₂) := acc.2.addNode
        { kind := .repeater delay (-3), sigLevel := 0, inputs := [], outputs := [] }
      (acc.1 ++ [repId], w₂)
    ) (ids, w₀)).2.nextId = w₀.nextId + delays.length := by
  induction delays with
  | nil => intro ids w₀; rfl
  | cons d rest ih =>
    intro ids w₀
    simp only [List.foldl_cons, List.length]
    set nd : NodeData := { kind := NodeKind.repeater d (-3), sigLevel := 0, inputs := [], outputs := [] }
    have h₁ := World.addNode_nextId w₀ nd
    have h₂ := ih (ids ++ [(w₀.addNode nd).1]) (w₀.addNode nd).2
    rw [h₂, h₁]; omega

/-- The foldl in `buildChain` produces `repIds` of length `delays.length`. -/
theorem buildChain_foldl_repIds_length (delays : List PNat) :
    ∀ (ids : List Nat) (w₀ : World),
    (delays.foldl (fun (acc : List Nat × World) delay =>
      let (repId, w₂) := acc.2.addNode
        { kind := .repeater delay (-3), sigLevel := 0, inputs := [], outputs := [] }
      (acc.1 ++ [repId], w₂)
    ) (ids, w₀)).1.length = ids.length + delays.length := by
  induction delays with
  | nil => intro ids w₀; rfl
  | cons d rest ih =>
    intro ids w₀
    simp only [List.foldl_cons, List.length]
    set nd : NodeData := { kind := NodeKind.repeater d (-3), sigLevel := 0, inputs := [], outputs := [] }
    have h₁ := ih (ids ++ [(w₀.addNode nd).1]) (w₀.addNode nd).2
    simp [List.length_append] at h₁ ⊢; omega

/-- `connectChain` preserves `nextId`. -/
theorem connectChain_nextId (w : World) (ids : List Nat) :
    (connectChain w ids).nextId = w.nextId := by
  dsimp [connectChain]
  set f := fun (w' : World) (p : Nat × Nat) =>
    (w'.updateNode p.2 (fun nd => { nd with inputs := nd.inputs ++ [p.1] })).updateNode p.1
      (fun nd => { nd with outputs := nd.outputs ++ [p.2] })
  have h : ∀ (l : List (Nat × Nat)) (w : World), (l.foldl f w).nextId = w.nextId := by
    intro l; induction l with
    | nil => intro w; rfl
    | cons hd tl ih =>
      intro w
      simp only [List.foldl_cons]
      have h₁ : (f w hd).nextId = w.nextId := by dsimp [f, World.updateNode]
      rw [ih (f w hd), h₁]
  exact h (ids.zip (ids.drop 1)) w

/-- [a] ++ (range n).map (· + a + 1) = (range n).map (· + a) ++ [a + n] -/
theorem list_range_shift (a n : Nat) :
    [a] ++ (List.range n).map (fun i => a + 1 + i) =
    (List.range n).map (fun i => a + i) ++ [a + n] := by
  induction n with
  | zero => simp
  | succ k ih =>
    simp only [List.range_succ, List.map_append, List.map_singleton]
    rw [← List.append_assoc, ih]
    have : a + 1 + k = a + (k + 1) := by omega
    simp [this]

/-- The foldl in `buildChain` produces `repIds = (range n).map (fun i => w₀.nextId + i)`.
    Proof sketch: induction on delays, using `h_init` to rewrite the foldl initial state.
    Key issue: after `simp only [List.foldl_cons]`, need to rewrite `(w₀.addNode nd).1` to
    `w₀.nextId` and `(w₀.addNode nd).2` to `w₁` in the foldl initial state, then apply IH.
    The final list equality `[a] ++ (range k).map (· + a + 1) = (range (k+1)).map (· + a)`
    needs `List.ext` + `omega` for element-wise proof. -/
theorem buildChain_foldl_repIds_eq (delays : List PNat) :
    ∀ (ids : List Nat) (w₀ : World),
    (delays.foldl (fun (acc : List Nat × World) delay =>
      let (repId, w₂) := acc.2.addNode
        { kind := .repeater delay (-3), sigLevel := 0, inputs := [], outputs := [] }
      (acc.1 ++ [repId], w₂)
    ) (ids, w₀)).1 = ids ++ (List.range delays.length).map (fun i => w₀.nextId + i) := by
  induction delays with
  | nil => intro ids w₀; simp
  | cons d rest ih =>
    intro ids w₀
    simp only [List.foldl_cons]
    set nd : NodeData := { kind := NodeKind.repeater d (-3), sigLevel := 0, inputs := [], outputs := [] }
    set w₁ := (w₀.addNode nd).2
    have h_repId : (w₀.addNode nd).1 = w₀.nextId := World.addNode_fst w₀ nd
    have h_nextId : w₁.nextId = w₀.nextId + 1 := World.addNode_nextId w₀ nd
    have h_init : (ids ++ [(w₀.addNode nd).1], (w₀.addNode nd).2) = (ids ++ [w₀.nextId], w₁) := by
      ext <;> simp [h_repId, w₁]
    rw [h_init]
    have h_ih := ih (ids ++ [w₀.nextId]) w₁
    rw [h_ih, h_nextId]
    rw [List.append_assoc]
    congr 1
    exact (list_range_shift w₀.nextId rest.length).trans (by
      simp [List.range_succ, List.map_append])

/-- Unfolded version of `buildChain_foldl_repIds_eq` for use with `simp (config := { zeta := true })`. -/
theorem buildChain_foldl_repIds_eq' (delays : List PNat)
    (ids : List Nat) (w₀ : World) :
    (delays.foldl (fun (acc : List Nat × World) delay =>
      (acc.1 ++ [acc.2.nextId],
       (acc.2.addNode { kind := .repeater delay (-3), sigLevel := 0, inputs := [], outputs := [] }).2)
    ) (ids, w₀)).1 = ids ++ (List.range delays.length).map (fun i => w₀.nextId + i) := by
  simpa [World.addNode] using buildChain_foldl_repIds_eq delays ids w₀

/-- Unfolded version of `buildChain_foldl_nextId` for use with `simp (config := { zeta := true })`. -/
theorem buildChain_foldl_nextId' (delays : List PNat)
    (ids : List Nat) (w₀ : World) :
    (delays.foldl (fun (acc : List Nat × World) delay =>
      (acc.1 ++ [acc.2.nextId],
       (acc.2.addNode { kind := .repeater delay (-3), sigLevel := 0, inputs := [], outputs := [] }).2)
    ) (ids, w₀)).2.nextId = w₀.nextId + delays.length := by
  simpa [World.addNode] using buildChain_foldl_nextId delays ids w₀

/-- The chain IDs produced by `buildChain` are Nodup.

Proof approach: The chain IDs are w.nextId, w.nextId+1, ..., w.nextId+n+3 (consecutive).
Use `buildChain_foldl_repIds_eq` to show repIds = (range n).map (· + w.nextId + 2),
then show the full list equals (range (n+4)).map (· + w.nextId), which is Nodup.

Key challenge: The `let` bindings in the theorem statement prevent `simp` from matching
`buildChain_foldl_repIds_eq`. Need to either:
(a) Use `conv` to target specific subexpressions, or
(b) Prove a version with unfolded `let` bindings, or
(c) Prove inline in the event bound proof where `dsimp [buildChain]` is available.
-/
theorem buildChain_chainIds_nodup (w : World) (c : ChainSpec) :
    let (inputId, w₁) := w.addNode
      { kind := .input, sigLevel := 0, inputs := [], outputs := [] }
    let (obsId, w₂) := w₁.addNode
      { kind := .observer, sigLevel := 0, inputs := [], outputs := [] }
    let (repIds, w₃) := c.middleDelays.foldl (fun (acc : List Nat × World) delay =>
      let (repId, w') := acc.2.addNode
        { kind := .repeater delay (-3), sigLevel := 0, inputs := [], outputs := [] }
      (acc.1 ++ [repId], w')
    ) ([], w₂)
    let (lastRepId, w₄) := w₃.addNode
      { kind := .repeater c.lastDelay (-1), sigLevel := 0, inputs := [], outputs := [] }
    let (outId, _) := w₄.addNode
      { kind := .output "", sigLevel := 0, inputs := [], outputs := [] }
    ([inputId, obsId] ++ repIds ++ [lastRepId, outId]).Nodup := by
  -- Unfold let bindings and simplify with helper lemmas
  simp (config := { zeta := true }) only [World.addNode_fst, World.addNode_nextId,
    buildChain_foldl_nextId', buildChain_foldl_repIds_eq', List.nil_append]
  suffices h : ∀ (a n : Nat),
      ([a, a + 1] ++ (List.range n).map (fun i => a + 2 + i) ++ [a + 2 + n, a + 3 + n]).Nodup by
    simpa [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm] using h w.nextId c.middleDelays.length
  intro a n
  suffices h_eq : [a, a + 1] ++ (List.range n).map (fun i => a + 2 + i) ++ [a + 2 + n, a + 3 + n] =
      (List.range (n + 4)).map (fun i => a + i) by
    rw [h_eq]
    have h_inj : Function.Injective (fun i => a + i) := fun i j hij => Nat.add_left_cancel hij
    have h_nodup : (List.range (n + 4)).Nodup := @List.nodup_range (n + 4)
    exact List.Nodup.map h_inj h_nodup
  induction n with
  | zero => simp [List.range, List.range.loop]
  | succ k ih =>
    -- RHS: (range (k+5)).map (· + a) = (range (k+4)).map (· + a) ++ [a + (k+4)]
    have h_rhs : (List.range (k + 5)).map (fun i => a + i) =
        (List.range (k + 4)).map (fun i => a + i) ++ [a + (k + 4)] := by
      rw [show k + 5 = (k + 4) + 1 from by omega, List.range_succ, List.map_append, List.map_singleton]
    rw [h_rhs]
    -- LHS: simplify range (k+1) and regroup to match IH
    have h_lhs : [a, a + 1] ++ (List.range (k + 1)).map (fun i => a + 2 + i) ++
        [a + 2 + (k + 1), a + 3 + (k + 1)] =
        ([a, a + 1] ++ (List.range k).map (fun i => a + 2 + i) ++ [a + 2 + k, a + 3 + k]) ++
        [a + 4 + k] := by
      simp [List.range_succ, List.map_append, List.append_assoc]
      omega
    rw [h_lhs, ih]
    have : a + 4 + k = a + (k + 4) := by omega
    simp [this]
/-- The foldl with `repFoldlStep` increments `nextId` by the number of delays. -/
@[simp] theorem foldl_repFoldlStep_nextId (delays : List PNat)
    (initIds : List Nat) (w₀ : World) :
    (delays.foldl repFoldlStep (initIds, w₀)).2.nextId = w₀.nextId + delays.length := by
  induction delays generalizing initIds w₀ with
  | nil => simp
  | cons d rest ih =>
    simp only [List.foldl_cons, repFoldlStep]
    rw [ih, World.addNode_nextId, List.length_cons]
    omega

/-- The first component of the `repFoldlStep` foldl gives the repeater IDs. -/
theorem foldl_repFoldlStep_repIds_eq (delays : List PNat)
    (ids : List Nat) (w₀ : World) :
    (delays.foldl repFoldlStep (ids, w₀)).1 =
    ids ++ (List.range delays.length).map (fun i => w₀.nextId + i) := by
  induction delays generalizing ids w₀ with
  | nil => simp
  | cons d rest ih =>
    simp only [List.foldl_cons, repFoldlStep]
    rw [ih (ids ++ [w₀.nextId]) ((w₀.addNode (mkRepNode d)).2), World.addNode_nextId,
      List.length_cons]
    rw [List.append_assoc, List.range_succ, List.map_append, List.map_singleton]
    congr 1
    simpa [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm] using
      list_range_shift w₀.nextId rest.length

theorem buildChain_nextId (w : World) (name : String) (c : ChainSpec) :
    (buildChain w name c).2.nextId = w.nextId + c.middleDelays.length + 4 := by
  unfold buildChain buildChainPre
  simp only [foldl_repFoldlStep_nextId, World.addNode_nextId, connectChain_nextId]
  omega

/-! ### Layer 7b: Fuel independence for stepUntilNextTick -/

/-- Removing an element whose targetTick = t decreases `filter (·.targetTick == t)` length by 1. -/
theorem filter_length_eraseIdx (l : List ScheduledEvent) (idx : Nat)
    (h_idx : idx < l.length) (t : Nat) (h_ev : l[idx].targetTick = t) :
    ((l.eraseIdx idx).filter (fun e => e.targetTick == t)).length =
    (l.filter (fun e => e.targetTick == t)).length - 1 := by
  induction l generalizing idx with
  | nil => exfalso; exact Nat.not_lt_zero idx h_idx
  | cons a l' ih =>
    cases idx with
    | zero =>
      have h_a : a.targetTick = t := by simpa using h_ev
      simp [List.eraseIdx, h_a]
    | succ idx' =>
      have h_idx' : idx' < l'.length := by
        simp at h_idx; omega
      have h_ev' : l'[idx'].targetTick = t := by
        convert h_ev using 1; simp
      have h_ih := ih idx' h_idx' h_ev'
      by_cases h_a : (a.targetTick == t) = true
      · simp [List.eraseIdx, List.filter, h_a, h_ih]
        have h_ge : (List.filter (fun e => e.targetTick == t) l').length ≥ 1 := by
          have h_mem : l'[idx'] ∈ List.filter (fun e => e.targetTick == t) l' := by
            rw [List.mem_filter]; exact ⟨List.getElem_mem h_idx', by simp [h_ev']⟩
          exact Nat.succ_le_of_lt (List.length_pos_of_mem h_mem)
        omega
      · simp [List.eraseIdx, List.filter, h_a, h_ih]

/-- If no events target the current tick, `popNextEvent = none`. -/
theorem popNextEvent_none_of_no_events_at_tick (w : World)
    (h : ∀ ev ∈ w.events, ev.targetTick ≠ w.tick) :
    w.popNextEvent = none := by
  dsimp [World.popNextEvent]
  suffices h_empty : (List.zip (List.range w.events.length) w.events).filter
      (fun (_, e) => e.targetTick == w.tick) = [] by
    simp [h_empty]
  apply List.filter_eq_nil_iff.mpr
  intro p hp
  dsimp
  -- Need: ¬(p.2.targetTick == w.tick) = true
  -- i.e., p.2.targetTick ≠ w.tick
  -- From h: ∀ ev ∈ w.events, ev.targetTick ≠ w.tick
  -- Need: p.2 ∈ w.events
  have h_mem : p.2 ∈ w.events := by
    -- p ∈ zip (range n) events → p.2 ∈ events
    -- Prove by induction on the zip structure
    have : ∀ (xs : List Nat) (ys : List ScheduledEvent) (q : Nat × ScheduledEvent),
        q ∈ List.zip xs ys → q.2 ∈ ys := by
      intro xs ys q hq
      induction xs generalizing ys with
      | nil => cases ys <;> simp_all [List.zip]
      | cons x xs' ih =>
        cases ys with
        | nil => simp_all [List.zip]
        | cons y ys' =>
          simp [List.zip, List.zipWith] at hq ⊢
          rcases hq with rfl | hq
          · simp
          · exact Or.inr (ih ys' hq)
    exact this (List.range w.events.length) w.events p hp
  have h_ne := h p.2 h_mem
  intro h_beq
  apply h_ne
  exact Nat.eq_of_beq_eq_true (by simpa using h_beq)

/-- If no events target the current tick, `step = none`. -/
theorem step_none_of_no_events_at_tick (w : World)
    (h : ∀ ev ∈ w.events, ev.targetTick ≠ w.tick) :
    w.step = none := by
  dsimp [World.step]
  rw [popNextEvent_none_of_no_events_at_tick w h]

/-- If no events target the current tick, `stepUntilNextTick` just increments tick. -/
theorem stepUntilNextTick_no_events (w : World)
    (h : ∀ ev ∈ w.events, ev.targetTick ≠ w.tick) :
    w.stepUntilNextTick = {w with tick := w.tick + 1} := by
  have h_step : w.step = none := step_none_of_no_events_at_tick w h
  rw [World.stepUntilNextTick, h_step]

/-- `stepUntilNextTick` preserves events when no events target the current tick. -/
theorem stepUntilNextTick_events_eq_of_no_events (w : World)
    (h : ∀ ev ∈ w.events, ev.targetTick ≠ w.tick) :
    (w.stepUntilNextTick).events = w.events := by
  rw [stepUntilNextTick_no_events w h]

/-- After one `step`, the number of events at the current tick decreases by 1.
Requires: all priorities < 100, repeater delays ≥ 2, repeater priorities < 100. -/
theorem step_events_at_tick_decrease (w : World) (w' : World)
    (h_step : w.step = some w')
    (_ : ∀ ev ∈ w.events, ev.priority < 100)
    (h_np : ∀ nid nd, w.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 100)
    (h_delay : ∀ nid nd, w.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2) :
    (w'.events.filter (fun e => e.targetTick == w'.tick)).length =
    (w.events.filter (fun e => e.targetTick == w.tick)).length - 1 := by
  -- step w = some w' → ∃ ev w_pop, popNextEvent w = some (ev, w_pop) ∧ w' = w_pop.onScheduledTick ev.nodeId
  dsimp [World.step] at h_step
  cases h_pop : w.popNextEvent with
  | none => simp [h_pop] at h_step
  | some p =>
    cases p with
    | mk ev w_pop =>
      simp only [h_pop] at h_step
      injection h_step with h_w'
      -- w' = w_pop.onScheduledTick ev.nodeId
      have h_tick_pop : w_pop.tick = w.tick := World.popNextEvent_tick w ev w_pop h_pop
      have h_tick' : w'.tick = w.tick := by
        rw [← h_w', World.onScheduledTick_tick]; exact h_tick_pop
      rw [h_tick']
      -- popNextEvent preserves nodes → h_np, h_delay transfer to w_pop
      have h_nodes_pop : w_pop.nodes = w.nodes := World.popNextEvent_nodes w ev w_pop h_pop
      have h_np_pop : ∀ nid nd, w_pop.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 100 := by
        intro nid nd h_get d p h_kind
        have h_get_w : w.getNode nid = some nd := by
          dsimp [World.getNode]; rw [← h_nodes_pop]; exact h_get
        exact h_np nid nd h_get_w d p h_kind
      have h_delay_pop : ∀ nid nd, w_pop.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
        intro nid nd h_get d p h_kind
        have h_get_w : w.getNode nid = some nd := by
          dsimp [World.getNode]; rw [← h_nodes_pop]; exact h_get
        exact h_delay nid nd h_get_w d p h_kind
      -- New events from onScheduledTick are at future ticks
      have h_new := World.onScheduledTick_new_events w_pop ev.nodeId h_np_pop h_delay_pop
      have h_future := h_new.2
      -- Events at tick w.tick in w' have the same LENGTH as in w_pop
      -- (new events have targetTick > w_pop.tick = w.tick, by h_future)
      have h_filter_len : (w'.events.filter (fun e => e.targetTick == w.tick)).length =
          (w_pop.events.filter (fun e => e.targetTick == w.tick)).length := by
        rw [← h_w']
        obtain ⟨new_events, h_append, h_new_future⟩ :=
          World.onScheduledTick_events_append w_pop ev.nodeId h_delay_pop
        rw [h_append, List.filter_append]
        have h_new_empty : (new_events.filter (fun e => e.targetTick == w.tick)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro ev' h_mem
          have h_gt := h_new_future ev' h_mem
          have h_ne : ev'.targetTick ≠ w.tick := by omega
          intro h_true
          apply h_ne
          exact Nat.eq_of_beq_eq_true (by simpa using h_true)
        simp [h_new_empty]
      rw [h_filter_len]
      -- w_pop.events = w.events.eraseIdx idx
      have h_erase := World.popNextEvent_eraseIdx w ev w_pop h_pop
      obtain ⟨idx, h_idx, h_erase_eq, h_ev_tick, h_ev_mem, h_ev_idx⟩ := h_erase
      rw [h_erase_eq]
      -- filter (eraseIdx l idx) p has length = filter l p length - 1
      have h_get : w.events[idx].targetTick = w.tick := by rw [h_ev_idx]; exact h_ev_tick
      exact filter_length_eraseIdx w.events idx h_idx w.tick h_get

/-- `addNode` preserves `getNode` for IDs other than the newly assigned one. -/
theorem World.addNode_getNode_old (w : World) (nd : NodeData) (id : Nat)
    (h : id ≠ w.nextId) :
    (w.addNode nd).2.getNode id = w.getNode id := by
  dsimp [World.addNode, World.getNode]
  rw [List.find?_append]
  have h_none : [(w.nextId, nd)].find? (fun (nid, _) => nid == id) = none := by
    apply List.find?_eq_none.mpr
    intro p hp
    cases hp
    case head =>
      dsimp
      have : w.nextId ≠ id := Ne.symm h
      simpa
    case tail h_mem =>
      cases h_mem
  rw [h_none]
  cases w.nodes.find? (fun (nid, _) => nid == id) <;> rfl

/-- `addNode` on a fresh ID makes `getNode` return the new node data. -/
theorem World.addNode_getNode_fresh (w : World) (nd : NodeData)
    (h : w.getNode w.nextId = none) :
    (w.addNode nd).2.getNode w.nextId = some nd := by
  have h_none : w.nodes.find? (fun (nid, _) => nid == w.nextId) = none := by
    dsimp [World.getNode] at h
    cases h_find : w.nodes.find? (fun (nid, _) => nid == w.nextId) with
    | none => rfl
    | some p => rcases p with ⟨nid', nd'⟩; simp [h_find] at h
  dsimp [World.addNode, World.getNode]
  rw [List.find?_append, h_none]
  simp [List.find?]

/-- `addNode` preserves the invariant that all node IDs are < `nextId`. -/
theorem World.addNode_ids_lt_nextId (w : World) (nd : NodeData)
    (h : ∀ p ∈ w.nodes, p.1 < w.nextId) :
    ∀ p ∈ (w.addNode nd).2.nodes, p.1 < (w.addNode nd).2.nextId := by
  dsimp [World.addNode]
  intro p hp
  simp [List.mem_append] at hp
  cases hp with
  | inl hp' => exact Nat.lt_succ_of_lt (h p hp')
  | inr hp' =>
    cases hp'
    omega

/-- In a world where all node IDs are < `nextId`, `getNode nextId = none`. -/
theorem World.getNode_nextId_none (w : World)
    (h : ∀ p ∈ w.nodes, p.1 < w.nextId) :
    w.getNode w.nextId = none := by
  dsimp [World.getNode]
  have : w.nodes.find? (fun (nid, _) => nid == w.nextId) = none := by
    apply List.find?_eq_none.mpr
    intro p hp
    have := h p hp
    simp; omega
  simp [this]

/-- The foldl in `buildChain` creates nodes with `outputs = []` and preserves
`outputs = []` for previously created nodes.

**Human proof:** By induction on the delay list. Each `addNode` creates a node
with `outputs = []` and doesn't modify existing nodes (`addNode_getNode_old`). -/
theorem buildChain_foldl_outputs_nil (delays : List PNat) :
    ∀ (ids : List Nat) (w₀ : World),
    (∀ id ∈ ids, ∀ nd, w₀.getNode id = some nd → nd.outputs = []) →
    (∀ id ∈ ids, id < w₀.nextId) →
    (∀ p ∈ w₀.nodes, p.1 < w₀.nextId) →
    let (ids', w') := delays.foldl (fun (acc : List Nat × World) delay =>
      let (repId, w₂) := acc.2.addNode
        { kind := .repeater delay (-3), sigLevel := 0, inputs := [], outputs := [] }
      (acc.1 ++ [repId], w₂)
    ) (ids, w₀)
    ∀ id ∈ ids', ∀ nd, w'.getNode id = some nd → nd.outputs = [] := by
  induction delays with
  | nil => intro ids w₀ h_outputs _ _; exact h_outputs
  | cons d rest ih =>
    intro ids w₀ h_outputs h_lt h_ids
    simp only [List.foldl_cons]
    set nd : NodeData := { kind := NodeKind.repeater d (-3), sigLevel := 0, inputs := [], outputs := [] }
    set w₁ := (w₀.addNode nd).2
    have h_repId : (w₀.addNode nd).1 = w₀.nextId := rfl
    have h_fresh : w₀.getNode w₀.nextId = none := World.getNode_nextId_none w₀ h_ids
    have h_new : w₁.getNode w₀.nextId = some nd := World.addNode_getNode_fresh w₀ nd h_fresh
    have h_old : ∀ id ∈ ids, ∀ nd', w₁.getNode id = some nd' → nd'.outputs = [] := by
      intro id hid nd' h_getNode
      have h_ne : id ≠ w₀.nextId := by
        intro heq; have := h_lt id hid; omega
      have h_getNode' : w₀.getNode id = some nd' := by
        rw [← World.addNode_getNode_old w₀ nd id h_ne]; exact h_getNode
      exact h_outputs id hid nd' h_getNode'
    have h_lt' : ∀ id ∈ ids ++ [w₀.nextId], id < w₁.nextId := by
      intro id hid
      rw [List.mem_append] at hid
      cases hid with
      | inl hid' => exact Nat.lt_succ_of_lt (h_lt id hid')
      | inr hid' =>
        obtain rfl : id = w₀.nextId := by simpa using hid'
        dsimp [w₁, World.addNode]; omega
    have h_ids' : ∀ p ∈ w₁.nodes, p.1 < w₁.nextId :=
      World.addNode_ids_lt_nextId w₀ nd h_ids
    have h_init : (ids ++ [(w₀.addNode nd).1], (w₀.addNode nd).2) = (ids ++ [w₀.nextId], w₁) := by
      ext <;> simp [h_repId, w₁]
    rw [h_init]
    have h_outputs' : ∀ id ∈ ids ++ [w₀.nextId], ∀ nd', w₁.getNode id = some nd' → nd'.outputs = [] := by
      intro id hid nd' h_getNode
      rw [List.mem_append] at hid
      cases hid with
      | inl hid' => exact h_old id hid' nd' h_getNode
      | inr hid' =>
        obtain rfl : id = w₀.nextId := by simpa using hid'
        injection h_new.symm.trans h_getNode with h_nd
        cases h_nd; rfl
    exact ih (ids ++ [w₀.nextId]) w₁ h_outputs' h_lt' h_ids'

/-- `addNode` with `outputs = []` preserves "all nodes have `outputs = []`". -/
theorem World.addNode_all_outputs_nil (w : World) (nd : NodeData) (nid : Nat)
    (h_nd : nd.outputs = [])
    (h_w : ∀ nd', w.getNode nid = some nd' → nd'.outputs = [])
    (h_fresh : w.getNode w.nextId = none) :
    ∀ nd', (w.addNode nd).2.getNode nid = some nd' → nd'.outputs = [] := by
  intro nd' h_getNode
  by_cases h_eq : nid = w.nextId
  · subst h_eq
    have h_new := World.addNode_getNode_fresh w nd h_fresh
    injection h_new.symm.trans h_getNode with h_nd'
    cases h_nd'; exact h_nd
  · have h_old := World.addNode_getNode_old w nd nid h_eq
    rw [h_old] at h_getNode
    exact h_w nd' h_getNode

/-- `updateNode` preserves `getNode nid = none` (updating one node doesn't create another). -/
theorem World.updateNode_preserves_getNode_none (w : World) (nid cid : Nat)
    (f : NodeData → NodeData) (h : w.getNode nid = none) :
    (w.updateNode cid f).getNode nid = none := by
  -- Derive find? = none from h : getNode nid = none
  have h_find : w.nodes.find? (fun (nid', _) => nid' == nid) = none := by
    dsimp [World.getNode] at h
    cases h_find : w.nodes.find? (fun (nid', _) => nid' == nid) with
    | none => rfl
    | some p => cases p; simp [h_find] at h
  -- Show the mapped list also has find? = none (map preserves first components)
  have h_find' : (w.nodes.map (fun (nid', nd') =>
      if (nid' == cid) = true then (nid', f nd') else (nid', nd'))).find?
      (fun (nid', _) => nid' == nid) = none := by
    apply List.find?_eq_none.mpr
    intro p hp
    obtain ⟨⟨nid', nd'⟩, h_mem, h_p⟩ := List.mem_map.mp hp
    subst h_p
    dsimp
    split
    · exact List.find?_eq_none.mp h_find (nid', nd') h_mem
    · exact List.find?_eq_none.mp h_find (nid', nd') h_mem
  -- Now show getNode nid = none on the updated world
  dsimp [World.getNode]
  -- Goal: Option.map Prod.snd ((w.updateNode cid f).nodes.find? ...) = none
  -- Suffices: (w.updateNode cid f).nodes.find? ... = none
  suffices h_goal : (w.updateNode cid f).nodes.find? (fun (nid', _) => nid' == nid) = none by
    simp [h_goal]
  dsimp [World.updateNode]
  exact h_find'

/-- A foldl of `updateNode` calls preserves `getNode nid = none`. -/
theorem foldl_updateNode_preserves_getNode_none :
    ∀ (pairs : List (Nat × Nat)) (w : World) (nid : Nat),
    w.getNode nid = none →
    (pairs.foldl (fun w' (prev, curr) =>
      (w'.updateNode curr (fun nd => { nd with inputs := nd.inputs ++ [prev] })).updateNode prev
        (fun nd => { nd with outputs := nd.outputs ++ [curr] })
    ) w).getNode nid = none := by
  intro pairs
  induction pairs with
  | nil => intro w nid h; simp; exact h
  | cons p rest ih =>
    intro w nid h
    simp only [List.foldl_cons]
    cases p with
    | mk prev curr =>
      apply ih
      apply World.updateNode_preserves_getNode_none
      apply World.updateNode_preserves_getNode_none
      exact h

/-- `connectChain` preserves `getNode nid = none`. -/
theorem connectChain_preserves_getNode_none' (ids : List Nat) (w : World)
    (nid : Nat) (h : w.getNode nid = none) :
    (connectChain w ids).getNode nid = none := by
  dsimp [connectChain]
  exact foldl_updateNode_preserves_getNode_none (ids.zip (ids.drop 1)) w nid h

/-- `connectChain` with Nodup IDs: if a node has `outputs = []` before,
then after connectChain it has `outputs.length ≤ 1`. -/
theorem connectChain_all_outputs_le_one (chainIds : List Nat) (h_nodup : chainIds.Nodup)
    (w : World) (nid : Nat) (h_w : ∀ nd, w.getNode nid = some nd → nd.outputs = []) :
    ∀ nd, (connectChain w chainIds).getNode nid = some nd → nd.outputs.length ≤ 1 := by
  intro nd' h_getNode
  by_cases h_get : ∃ nd₀, w.getNode nid = some nd₀
  · obtain ⟨nd₀, h_nd₀⟩ := h_get
    have h_outputs := h_w nd₀ h_nd₀
    have h_len := connectChain_outputs_length_le chainIds h_nodup w nid nd₀ nd' h_nd₀ h_getNode
    simp [h_outputs] at h_len
    exact h_len
  · have h_none : w.getNode nid = none := by
      cases h : w.getNode nid with
      | none => rfl
      | some nd₀ => exfalso; exact h_get ⟨nd₀, h⟩
    have h_pres := connectChain_preserves_getNode_none' chainIds w nid h_none
    rw [h_pres] at h_getNode
    contradiction

/-- The foldl in `buildChain` preserves "all nodes have `outputs = []`". -/
theorem buildChain_addNode_foldl_all_outputs_nil (delays : List PNat)
    (initIds : List Nat) (w₀ : World) (nid : Nat)
    (h_w₀ : ∀ nd, w₀.getNode nid = some nd → nd.outputs = [])
    (h_ids : ∀ p ∈ w₀.nodes, p.1 < w₀.nextId) :
    ∀ nd, (delays.foldl repFoldlStep (initIds, w₀)).2.getNode nid = some nd →
    nd.outputs = [] := by
  induction delays generalizing initIds w₀ with
  | nil => simp; exact h_w₀
  | cons d rest ih =>
    simp only [List.foldl_cons]
    have h_fresh : w₀.getNode w₀.nextId = none := World.getNode_nextId_none w₀ h_ids
    have h_w₁ : ∀ nd', (w₀.addNode (mkRepNode d)).2.getNode nid = some nd' → nd'.outputs = [] :=
      World.addNode_all_outputs_nil w₀ (mkRepNode d) nid rfl h_w₀ h_fresh
    have h_ids₁ : ∀ p ∈ (w₀.addNode (mkRepNode d)).2.nodes,
        p.1 < (w₀.addNode (mkRepNode d)).2.nextId :=
      World.addNode_ids_lt_nextId w₀ (mkRepNode d) h_ids
    exact ih (initIds ++ [w₀.nextId]) (w₀.addNode (mkRepNode d)).2 h_w₁ h_ids₁

/-- The foldl preserves the invariant that all node IDs are < nextId. -/
theorem foldl_repFoldlStep_ids_lt_nextId (delays : List PNat)
    (initIds : List Nat) (w₀ : World)
    (h_ids : ∀ p ∈ w₀.nodes, p.1 < w₀.nextId) :
    ∀ p ∈ (delays.foldl repFoldlStep (initIds, w₀)).2.nodes,
    p.1 < (delays.foldl repFoldlStep (initIds, w₀)).2.nextId := by
  induction delays generalizing initIds w₀ with
  | nil => simpa using h_ids
  | cons d rest ih =>
    simp only [List.foldl_cons]
    exact ih (initIds ++ [w₀.nextId]) ((w₀.addNode (mkRepNode d)).2)
      (World.addNode_ids_lt_nextId w₀ (mkRepNode d) h_ids)
