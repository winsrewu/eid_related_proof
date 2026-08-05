import BasicProofs.PrefixChain.Part12


open BasicRedstoneSim

/-- Before tick t₁ (when t₁ ≤ t₂), no events have been scheduled. -/
theorem simFoldl_no_events_until_t1 (c1 c2 : ChainSpec) (t1 t2 pos' : Nat)
    (h_le : t1 ≤ t2) :
    ∀ k, k ≤ t1 → ((List.range k).foldl (simBody t1 t2 pos'
      (buildChain World.empty "A" c1).1
      (buildChain (buildChain World.empty "A" c1).2 "B" c2).1)
      (buildChain (buildChain World.empty "A" c1).2 "B" c2).2).events = [] := by
  intro k hk
  induction k with
  | zero => simp [List.range_zero, List.foldl_nil]; exact w0_events_empty c1 c2
  | succ k' ih =>
    have hk' : k' ≤ t1 := by omega
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    have h_ih := ih hk'
    have h_tick : ((List.range k').foldl (simBody t1 t2 pos'
        (buildChain World.empty "A" c1).1
        (buildChain (buildChain World.empty "A" c1).2 "B" c2).1)
        (buildChain (buildChain World.empty "A" c1).2 "B" c2).2).tick = k' := by
      have := simFoldl_tick (buildChain (buildChain World.empty "A" c1).2 "B" c2).2 t1 t2 pos'
        (buildChain World.empty "A" c1).1
        (buildChain (buildChain World.empty "A" c1).2 "B" c2).1 k'
      rw [w0_tick c1 c2] at this; omega
    have h_ne_t1 : k' ≠ t1 := by omega
    have h_ne_t2 : k' ≠ t2 := by omega
    dsimp (config := { zeta := true }) [simBody]
    simp only [h_tick]
    have h_beq1 : (k' == t1) = false := by
      cases h : k' == t1 <;> simp_all
    have h_beq2 : (k' == t2) = false := by
      cases h : k' == t2 <;> simp_all
    simp only [h_beq1, Bool.false_eq_true, ite_false]
    set w_log := ((List.range k').foldl (simBody t1 t2 pos'
        (buildChain World.empty "A" c1).1
        (buildChain (buildChain World.empty "A" c1).2 "B" c2).1)
        (buildChain (buildChain World.empty "A" c1).2 "B" c2).2).logOutput s!"tick {k'}"
    have h_no_at_tick : ∀ ev ∈ w_log.events, ev.targetTick ≠ w_log.tick := by
      dsimp [w_log]; simp [h_ih]
    dsimp [w_log]
    simp only [h_tick, h_beq2, Bool.false_eq_true, ite_false]
    rw [stepUntilNextTick_events_eq_of_no_events _ h_no_at_tick]
    rw [World.logOutput_events, h_ih]

/-- Through ticks 0..t₂ (when t₁ < t₂), the event list never exceeds one element. -/
theorem simFoldl_events_length_le_one (c1 c2 : ChainSpec) (t1 t2 pos' : Nat)
    (h_lt : t1 < t2) :
    ((List.range t2).foldl (simBody t1 t2 pos'
      (buildChain World.empty "A" c1).1
      (buildChain (buildChain World.empty "A" c1).2 "B" c2).1)
      (buildChain (buildChain World.empty "A" c1).2 "B" c2).2).events.length ≤ 1 ∧
    ∀ nid nd, ((List.range t2).foldl (simBody t1 t2 pos'
      (buildChain World.empty "A" c1).1
      (buildChain (buildChain World.empty "A" c1).2 "B" c2).1)
      (buildChain (buildChain World.empty "A" c1).2 "B" c2).2).getNode nid = some nd →
      nd.outputs.length ≤ 1 := by
  set w₀ := (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
  set in1 := (buildChain World.empty "A" c1).1
  set in2 := (buildChain (buildChain World.empty "A" c1).2 "B" c2).1
  have h_out_w0 : ∀ nid nd, w₀.getNode nid = some nd → nd.outputs.length ≤ 1 := by
    dsimp [w₀]
    intro nid nd h_nd
    set wA := (buildChain World.empty "A" c1).2
    have h_idsA : ∀ p ∈ wA.nodes, p.1 < wA.nextId :=
      buildChain_ids_lt_nextId World.empty "A" c1 (fun p hp => by simp [World.empty] at hp)
    by_cases h_old : nid < wA.nextId
    · have h_old' := buildChain_getNode_old wA "B" c2 nid h_old
      have h_ndA : wA.getNode nid = some nd := by rwa [h_old'] at h_nd
      exact buildChain_outputs_le_one World.empty "A" c1
        (fun p hp => by simp [World.empty] at hp) nid nd h_ndA
        (by simp [World.empty, World.getNode])
    · have h_fresh : wA.getNode nid = none := by
        dsimp [wA, World.getNode]
        cases h_find : wA.nodes.find? (fun (nid', _) => nid' == nid) with
        | none => rfl
        | some q =>
          rcases q with ⟨nid', nd'⟩
          have h_mem := List.mem_of_find?_eq_some h_find
          have h_lt' : nid' < wA.nextId := h_idsA (nid', nd') h_mem
          have h_eq : nid' = nid := by
            have := find?_eq_some_imp_pred (fun (x : Nat × NodeData) => x.1 == nid)
              wA.nodes (nid', nd') h_find
            simpa using this
          omega
      exact buildChain_outputs_le_one wA "B" c2 h_idsA nid nd h_nd h_fresh
  suffices h_main : ∀ k ≤ t2,
      ((List.range k).foldl (simBody t1 t2 pos' in1 in2) w₀).events.length ≤ 1 ∧
      ∀ nid nd, ((List.range k).foldl (simBody t1 t2 pos' in1 in2) w₀).getNode nid = some nd →
        nd.outputs.length ≤ 1 by
    exact h_main t2 (le_refl t2)
  intro k hk
  induction k with
  | zero =>
    constructor
    · simp [List.range_zero, List.foldl_nil]; rw [w0_events_empty c1 c2]; simp
    · dsimp [w₀]; exact h_out_w0
  | succ k' ih =>
    have hk' : k' ≤ t2 := by omega
    have h_ih := ih hk'
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    set W := (List.range k').foldl (simBody t1 t2 pos' in1 in2) w₀
    have h_tick_W : W.tick = k' := by
      dsimp [W, w₀]
      rw [simFoldl_tick _ t1 t2 pos' in1 in2 k', w0_tick c1 c2]
      omega
    have h_k'_ne_t2 : k' ≠ t2 := by omega
    by_cases h_t1 : k' = t1
    · -- tick = t₁: simBody = (logOutput + setInput in1).stepUntilNextTick
      have h_body : simBody t1 t2 pos' in1 in2 W k' =
          ((W.logOutput s!"tick {W.tick}").setInput in1 15).stepUntilNextTick := by
        unfold simBody
        dsimp (config := { zeta := true })
        split_ifs <;> simp_all [World.logOutput_tick, World.setInput_tick, beq_iff_eq]
      rw [h_body]
      set V := W.logOutput s!"tick {W.tick}"
      set X := V.setInput in1 15
      have h_W_empty : W.events = [] := by
        dsimp [W, w₀, in1, in2]
        exact simFoldl_no_events_until_t1 c1 c2 t1 t2 pos' h_lt.le k' (by omega)
      have h_V_events : V.events = W.events := by dsimp [V, World.logOutput]
      have h_out_V : ∀ nid nd, V.getNode nid = some nd → nd.outputs.length ≤ 1 := by
        intro nid nd h_nd; apply h_ih.2; rwa [World.logOutput_getNode] at h_nd
      have h_out_X : ∀ nid nd, X.getNode nid = some nd → nd.outputs.length ≤ 1 := by
        dsimp [X]; exact setInput_outputs_le_one V in1 15 h_out_V
      constructor
      · have h_len_set : X.events.length ≤ 1 := by
          dsimp [X, World.setInput]
          have h_le := World.notifyOutputs_events_length_le
            (V.updateNode in1 (fun nd => { nd with sigLevel := 15 })) in1
          rw [World.updateNode_events, h_V_events, h_W_empty] at h_le
          apply le_trans h_le
          simp
          have h_le_out : ((V.updateNode in1
              (fun nd => { nd with sigLevel := 15 })).getNode in1).elim 0
              (fun nd => nd.outputs.length) ≤ 1 := by
            cases h_gn : V.getNode in1 with
            | none =>
              rw [World.updateNode_getNode_none _ _ _ h_gn]
              simp
            | some nd =>
              rw [World.updateNode_getNode_eq _ _ _ nd h_gn]
              simp
              exact h_ih.2 in1 nd (by rwa [World.logOutput_getNode] at h_gn)
          omega
        have := stepUntilNextTick_events_length_le X h_out_X
        omega
      · dsimp [X]
        exact stepUntilNextTick_outputs_le_one (V.setInput in1 15) h_out_X
    · -- tick ≠ t₁: simBody = logOutput.stepUntilNextTick
      have h_body : simBody t1 t2 pos' in1 in2 W k' =
          (W.logOutput s!"tick {W.tick}").stepUntilNextTick := by
        unfold simBody
        dsimp (config := { zeta := true })
        split_ifs <;> simp_all [World.logOutput_tick, beq_iff_eq]
      rw [h_body]
      set V := W.logOutput s!"tick {W.tick}"
      have h_out_V : ∀ nid nd, V.getNode nid = some nd → nd.outputs.length ≤ 1 := by
        intro nid nd h_nd; apply h_ih.2; rwa [World.logOutput_getNode] at h_nd
      constructor
      · have h_le := stepUntilNextTick_events_length_le V h_out_V
        have h_Vev : V.events = W.events := by dsimp [V, World.logOutput]
        rw [h_Vev] at h_le
        exact le_trans h_le (by omega)
      · exact stepUntilNextTick_outputs_le_one V h_out_V

/-- `popNextEvent` on a world whose only event is at the current tick. -/
theorem popNextEvent_singleton (w : World) (e : ScheduledEvent)
    (h_ev : w.events = [e]) (h_tick : e.targetTick = w.tick) :
    w.popNextEvent = some (e, { w with events := [] }) := by
  unfold World.popNextEvent
  rw [h_ev]
  simp [h_tick]

/-- If `id`'s only output is an observer node, `setInput id 15` appends exactly one event. -/
theorem setInput_append_observer (w : World) (id obs : Nat)
    (h_in : ∃ nd, w.getNode id = some nd ∧ nd.outputs = [obs])
    (h_obs : ∃ nd, w.getNode obs = some nd ∧ nd.kind = .observer)
    (h_ne : obs ≠ id) :
    (w.setInput id 15).events =
    w.events ++ [{ targetTick := w.tick + 2, priority := 0, nodeId := obs }] := by
  rcases h_in with ⟨nd_in, h_gn_in, h_outs⟩
  rcases h_obs with ⟨nd_obs, h_gn_obs, h_kind_obs⟩
  dsimp [World.setInput, World.notifyOutputs]
  have h_gn_in' : (w.updateNode id (fun nd => { nd with sigLevel := 15 })).getNode id =
      some ({ nd_in with sigLevel := 15 } : NodeData) :=
    World.updateNode_getNode_eq w id (fun nd => { nd with sigLevel := 15 }) nd_in h_gn_in
  rw [h_gn_in']
  have h_outs' : ({ nd_in with sigLevel := 15 } : NodeData).outputs = [obs] := by rw [h_outs]
  rw [h_outs']
  simp only [List.foldl_cons, List.foldl_nil]
  have h_gn_obs' : (w.updateNode id (fun nd => { nd with sigLevel := 15 })).getNode obs =
      some nd_obs := by
    rw [World.updateNode_getNode_ne w id obs _ (Ne.symm h_ne)]
    exact h_gn_obs
  dsimp [World.onNeighborUpdate]
  simp only [h_gn_obs']
  rw [h_kind_obs]
  simp [World.scheduleEvent_events, World.updateNode_events]

/-- `addNode` preserves "all repeaters have negative priority". -/
theorem addNode_preserves_priority_neg (w : World) (nd : NodeData)
    (h_w : ∀ nid nd, w.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 0)
    (h_nd : ∀ d p, nd.kind = .repeater d p → p < 0)
    (h_none : w.getNode w.nextId = none) :
    ∀ nid nd', (w.addNode nd).2.getNode nid = some nd' →
    ∀ d p, nd'.kind = .repeater d p → p < 0 := by
  intro nid nd' h_get d p h_kind
  by_cases h_eq : nid = w.nextId
  · subst h_eq
    have h_fresh := World.addNode_getNode_fresh w nd h_none
    rw [h_fresh] at h_get
    injection h_get with h_eq'
    subst h_eq'
    exact h_nd d p h_kind
  · have h_old := World.addNode_getNode_old w nd nid h_eq
    rw [h_old] at h_get
    exact h_w nid nd' h_get d p h_kind

/-- `repFoldlStep` preserves "all repeaters have negative priority". -/
theorem repFoldl_preserves_priority_neg (delays : List PNat)
    (acc : List Nat × World)
    (h_acc : ∀ nid nd, acc.2.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 0)
    (h_ids : ∀ p ∈ acc.2.nodes, p.1 < acc.2.nextId) :
    ∀ nid nd, (delays.foldl repFoldlStep acc).2.getNode nid = some nd →
    ∀ d p, nd.kind = .repeater d p → p < 0 := by
  induction delays generalizing acc with
  | nil => intro nid nd h_get d p h_kind; simpa [List.foldl] using h_acc nid nd h_get d p h_kind
  | cons d ds ih =>
    intro nid nd h_get d' p h_kind
    dsimp [List.foldl, repFoldlStep] at h_get
    have h_ids' : ∀ p ∈ ((acc.2.addNode (mkRepNode d)).2).nodes,
        p.1 < (acc.2.addNode (mkRepNode d)).2.nextId :=
      World.addNode_ids_lt_nextId acc.2 (mkRepNode d) h_ids
    have h_acc' : ∀ nid nd, (acc.2.addNode (mkRepNode d)).2.getNode nid = some nd →
        ∀ d' p, nd.kind = .repeater d' p → p < 0 :=
      addNode_preserves_priority_neg acc.2 (mkRepNode d) h_acc
        (by intro d' p h; dsimp [mkRepNode] at h; injection h with h_d h_p; subst h_d; subst h_p; omega)
        (World.getNode_nextId_none acc.2 h_ids)
    exact ih (acc.1 ++ [acc.2.nextId], (acc.2.addNode (mkRepNode d)).2) h_acc' h_ids'
      nid nd h_get d' p h_kind

/-- `buildChain` preserves "all repeaters have negative priority". -/
theorem buildChain_repeater_priority_neg (w : World) (name : String) (c : ChainSpec)
    (h_w : ∀ nid nd, w.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 0)
    (h_ids : ∀ p ∈ w.nodes, p.1 < w.nextId) :
    ∀ nid nd, (buildChain w name c).2.getNode nid = some nd →
    ∀ d p, nd.kind = .repeater d p → p < 0 := by
  intro nid nd h_get d p h_kind
  dsimp [buildChain] at h_get
  obtain ⟨nd₀, h_nd₀, h_kind₀⟩ := connectChain_kind_preserved
    (buildChainPre w name c).2.1 (buildChainPre w name c).2.2 nid nd h_get
  rw [← h_kind₀] at h_kind
  dsimp [buildChainPre] at h_nd₀
  set w₁ := (w.addNode { kind := .input, sigLevel := 0, inputs := [], outputs := [] }).2
  set w₂ := (w₁.addNode { kind := .observer, sigLevel := 0, inputs := [], outputs := [] }).2
  set w₃ := (c.middleDelays.foldl repFoldlStep ([], w₂)).2
  set w₄ := (w₃.addNode { kind := .repeater c.lastDelay (-1), sigLevel := 0, inputs := [], outputs := [] }).2
  set w₅ := (w₄.addNode { kind := .output name, sigLevel := 0, inputs := [], outputs := [] }).2
  have h₁ : ∀ nid nd, w₁.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 0 :=
    addNode_preserves_priority_neg w { kind := .input, sigLevel := 0, inputs := [], outputs := [] }
      h_w (by intro d p h; cases h) (World.getNode_nextId_none w h_ids)
  have h_ids₁ : ∀ p ∈ w₁.nodes, p.1 < w₁.nextId :=
    World.addNode_ids_lt_nextId w { kind := .input, sigLevel := 0, inputs := [], outputs := [] } h_ids
  have h₂ : ∀ nid nd, w₂.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 0 :=
    addNode_preserves_priority_neg w₁ { kind := .observer, sigLevel := 0, inputs := [], outputs := [] }
      h₁ (by intro d p h; cases h) (World.getNode_nextId_none w₁ h_ids₁)
  have h_ids₂ : ∀ p ∈ w₂.nodes, p.1 < w₂.nextId :=
    World.addNode_ids_lt_nextId w₁ { kind := .observer, sigLevel := 0, inputs := [], outputs := [] } h_ids₁
  have h₃ : ∀ nid nd, w₃.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 0 :=
    repFoldl_preserves_priority_neg c.middleDelays ([], w₂) h₂ h_ids₂
  have h_ids₃ : ∀ p ∈ w₃.nodes, p.1 < w₃.nextId := by
    dsimp [w₃]
    suffices ∀ (ds : List PNat) (acc : List Nat × World),
        (∀ p ∈ acc.2.nodes, p.1 < acc.2.nextId) →
        ∀ p ∈ (ds.foldl repFoldlStep acc).2.nodes, p.1 < (ds.foldl repFoldlStep acc).2.nextId from
      this c.middleDelays ([], w₂) h_ids₂
    intro ds; induction ds with
    | nil => intro acc h_ids p hp; dsimp [List.foldl] at hp; exact h_ids p hp
    | cons d ds ih =>
      intro acc h_ids p hp
      dsimp [List.foldl, repFoldlStep] at hp
      exact ih (acc.1 ++ [acc.2.nextId], (acc.2.addNode (mkRepNode d)).2)
        (World.addNode_ids_lt_nextId acc.2 (mkRepNode d) h_ids) p hp
  have h₄ : ∀ nid nd, w₄.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 0 :=
    addNode_preserves_priority_neg w₃
      { kind := .repeater c.lastDelay (-1), sigLevel := 0, inputs := [], outputs := [] }
      h₃ (by intro d' p' h; injection h with h_d h_p; subst h_d; subst h_p; omega)
      (World.getNode_nextId_none w₃ h_ids₃)
  have h_ids₄ : ∀ p ∈ w₄.nodes, p.1 < w₄.nextId :=
    World.addNode_ids_lt_nextId w₃
      { kind := .repeater c.lastDelay (-1), sigLevel := 0, inputs := [], outputs := [] } h_ids₃
  have h₅ : ∀ nid nd, w₅.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 0 :=
    addNode_preserves_priority_neg w₄ { kind := .output name, sigLevel := 0, inputs := [], outputs := [] }
      h₄ (by intro d p h; cases h) (World.getNode_nextId_none w₄ h_ids₄)
  exact h₅ nid nd₀ h_nd₀ d p h_kind

/-- A foldl of `onNeighborUpdate` only appends events with negative priority when
every listed node is a negative-priority repeater (and no observer is listed). -/
theorem foldl_onNeighborUpdate_events_neg (l : List Nat) (w : World)
    (h_np : ∀ nid ∈ l, ∀ nd, w.getNode nid = some nd →
        (∀ d p, nd.kind = .repeater d p → p < 0) ∧ nd.kind ≠ .observer) :
    ∀ ev ∈ (l.foldl (fun w' outId => w'.onNeighborUpdate outId) w).events,
    ev ∉ w.events → ev.priority < 0 := by
  induction l generalizing w with
  | nil => intro ev h_ev h_notin; simp at h_ev; contradiction
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    intro ev h_ev h_notin
    have h_same : ∀ nid, (w.onNeighborUpdate hd).getNode nid = w.getNode nid := by
      intro nid
      dsimp [World.onNeighborUpdate]
      cases h_gn : w.getNode hd with
      | none => rfl
      | some nd =>
        cases h_kind : nd.kind <;> dsimp [World.getNode] <;>
          simp [h_kind, World.scheduleEvent_nodes, World.logOutput_nodes]
    by_cases h_ev_hd : ev ∈ (w.onNeighborUpdate hd).events
    · by_cases h_ev_w : ev ∈ w.events
      · contradiction
      · dsimp [World.onNeighborUpdate] at h_ev_hd
        cases h_gn : w.getNode hd with
        | none =>
          simp [h_gn] at h_ev_hd
          contradiction
        | some nd =>
          cases h_kind : nd.kind with
          | repeater d p =>
            simp only [h_gn, h_kind, World.scheduleEvent_events] at h_ev_hd
            have h_spec := h_np hd (by simp) nd h_gn
            have h_new : ev = { targetTick := w.tick + (d : Nat), priority := p, nodeId := hd } := by
              simp [List.mem_append] at h_ev_hd
              cases h_ev_hd with
              | inl h => contradiction
              | inr h => simpa using h
            subst h_new
            exact h_spec.1 d p h_kind
          | observer =>
            have h_spec := h_np hd (by simp) nd h_gn
            exact absurd h_kind h_spec.2
          | output name =>
            simp only [h_gn, h_kind, World.logOutput_events] at h_ev_hd
            contradiction
          | input =>
            simp only [h_gn, h_kind] at h_ev_hd
            contradiction
    · have h_tl : ∀ nid ∈ tl, ∀ nd, (w.onNeighborUpdate hd).getNode nid = some nd →
          (∀ d p, nd.kind = .repeater d p → p < 0) ∧ nd.kind ≠ .observer := by
        intro nid h_nid nd h_nd
        apply h_np nid (by simp [h_nid]) nd
        rwa [h_same nid] at h_nd
      exact ih (w.onNeighborUpdate hd) h_tl ev h_ev h_ev_hd

/-- New events from `onScheduledTick` have negative priority when all of the node's
outputs are negative-priority repeaters (and no observer is among them). -/
theorem World.onScheduledTick_new_events_neg (w : World) (id : Nat)
    (h_out : ∀ nd, w.getNode id = some nd → ∀ out_id ∈ nd.outputs,
        ∀ nd_out, w.getNode out_id = some nd_out →
        (∀ d p, nd_out.kind = .repeater d p → p < 0) ∧ nd_out.kind ≠ .observer) :
    ∀ ev ∈ (w.onScheduledTick id).events, ev ∉ w.events → ev.priority < 0 := by
  intro ev h_ev h_notin
  dsimp [World.onScheduledTick] at h_ev
  cases h_gn : w.getNode id with
  | none =>
    rw [h_gn] at h_ev
    dsimp at h_ev
    contradiction
  | some nd₀ =>
    rw [h_gn] at h_ev
    dsimp at h_ev
    cases h_kind : nd₀.kind with
    | repeater delay priority =>
      rw [h_kind] at h_ev
      dsimp (config := { zeta := true }) at h_ev
      set w' := w.updateNode id
        (fun nd' => { nd' with sigLevel := if w.getInputSignal id > 0 then 15 else 0 })
      dsimp [World.notifyOutputs] at h_ev
      have h_go : w'.getNode id =
          some ({ nd₀ with sigLevel := if w.getInputSignal id > 0 then 15 else 0 } : NodeData) :=
        World.updateNode_getNode_eq w id _ nd₀ h_gn
      rw [h_go] at h_ev
      dsimp at h_ev
      have h_prem : ∀ nid ∈ nd₀.outputs, ∀ nd, w'.getNode nid = some nd →
          (∀ d p, nd.kind = .repeater d p → p < 0) ∧ nd.kind ≠ .observer := by
        intro out_id h_mem_out nd_out' h_nd_out'
        by_cases h_eq : out_id = id
        · have h_nd_id : w'.getNode id = some nd_out' := by rwa [h_eq] at h_nd_out'
          rw [h_go] at h_nd_id
          injection h_nd_id with h_nd_eq
          subst h_nd_eq
          have h_gn_out : w.getNode out_id = some nd₀ := by rw [h_eq]; exact h_gn
          have h_spec := h_out nd₀ h_gn out_id h_mem_out nd₀ h_gn_out
          constructor
          · intro d p h_kind'; dsimp at h_kind'; exact h_spec.1 d p h_kind'
          · intro h_obs; dsimp at h_obs; exact h_spec.2 h_obs
        · have h_same : w'.getNode out_id = w.getNode out_id :=
            World.updateNode_getNode_ne w id out_id _ (Ne.symm h_eq)
          rw [h_same] at h_nd_out'
          exact h_out nd₀ h_gn out_id h_mem_out nd_out' h_nd_out'
      have := foldl_onNeighborUpdate_events_neg nd₀.outputs w' h_prem
      have h_ev' : w'.events = w.events := World.updateNode_events w id _
      rw [h_ev'] at this
      exact this ev h_ev h_notin
    | observer =>
      rw [h_kind] at h_ev
      dsimp (config := { zeta := true }) at h_ev
      set w' := w.updateNode id (fun nd' => { nd' with sigLevel := 15 })
      dsimp [World.notifyOutputs] at h_ev
      have h_go : w'.getNode id = some ({ nd₀ with sigLevel := 15 } : NodeData) :=
        World.updateNode_getNode_eq w id _ nd₀ h_gn
      rw [h_go] at h_ev
      dsimp at h_ev
      have h_prem : ∀ nid ∈ nd₀.outputs, ∀ nd, w'.getNode nid = some nd →
          (∀ d p, nd.kind = .repeater d p → p < 0) ∧ nd.kind ≠ .observer := by
        intro out_id h_mem_out nd_out' h_nd_out'
        by_cases h_eq : out_id = id
        · have h_nd_id : w'.getNode id = some nd_out' := by rwa [h_eq] at h_nd_out'
          rw [h_go] at h_nd_id
          injection h_nd_id with h_nd_eq
          subst h_nd_eq
          have h_gn_out : w.getNode out_id = some nd₀ := by rw [h_eq]; exact h_gn
          have h_spec := h_out nd₀ h_gn out_id h_mem_out nd₀ h_gn_out
          constructor
          · intro d p h_kind'; dsimp at h_kind'; exact h_spec.1 d p h_kind'
          · intro h_obs; dsimp at h_obs; exact h_spec.2 h_obs
        · have h_same : w'.getNode out_id = w.getNode out_id :=
            World.updateNode_getNode_ne w id out_id _ (Ne.symm h_eq)
          rw [h_same] at h_nd_out'
          exact h_out nd₀ h_gn out_id h_mem_out nd_out' h_nd_out'
      have := foldl_onNeighborUpdate_events_neg nd₀.outputs w' h_prem
      have h_ev' : w'.events = w.events := World.updateNode_events w id _
      rw [h_ev'] at this
      exact this ev h_ev h_notin
    | output name =>
      rw [h_kind] at h_ev
      dsimp at h_ev
      contradiction
    | input =>
      rw [h_kind] at h_ev
      dsimp at h_ev
      contradiction

/-- `buildChainPre` preserves "all nodes have empty outputs" for any base world. -/
theorem buildChainPre_outputs_empty (w : World) (name : String) (c : ChainSpec)
    (h_w : ∀ nid nd, w.getNode nid = some nd → nd.outputs = [])
    (h_ids : ∀ p ∈ w.nodes, p.1 < w.nextId) :
    ∀ nid nd, (buildChainPre w name c).2.1.getNode nid = some nd → nd.outputs = [] := by
  intro nid nd h_get
  dsimp [buildChainPre] at h_get
  have h₁ := addNode_preserves_outputs_empty w
    { kind := .input, sigLevel := 0, inputs := [], outputs := [] } h_ids h_w (by rfl)
  have h_ids₁ := World.addNode_ids_lt_nextId w
    { kind := .input, sigLevel := 0, inputs := [], outputs := [] } h_ids
  have h₂ := addNode_preserves_outputs_empty _
    { kind := .observer, sigLevel := 0, inputs := [], outputs := [] } h_ids₁ h₁ (by rfl)
  have h_ids₂ := World.addNode_ids_lt_nextId _
    { kind := .observer, sigLevel := 0, inputs := [], outputs := [] } h_ids₁
  have h₃ := foldl_repFoldlStep_preserves_outputs_empty c.middleDelays [] _ h_ids₂ h₂
  have h_ids₃ : ∀ p ∈ (c.middleDelays.foldl repFoldlStep ([],
      (w.addNode { kind := .input, sigLevel := 0, inputs := [], outputs := [] }).2.addNode
      { kind := .observer, sigLevel := 0, inputs := [], outputs := [] } |>.2)).2.nodes,
      p.1 < (c.middleDelays.foldl repFoldlStep ([],
      (w.addNode { kind := .input, sigLevel := 0, inputs := [], outputs := [] }).2.addNode
      { kind := .observer, sigLevel := 0, inputs := [], outputs := [] } |>.2)).2.nextId :=
    foldl_repFoldlStep_ids_lt_nextId c.middleDelays [] _ h_ids₂
  have h₄ := addNode_preserves_outputs_empty _
    { kind := .repeater c.lastDelay (-1), sigLevel := 0, inputs := [], outputs := [] } h_ids₃ h₃ (by rfl)
  have h_ids₄ := World.addNode_ids_lt_nextId _
    { kind := .repeater c.lastDelay (-1), sigLevel := 0, inputs := [], outputs := [] } h_ids₃
  have h₅ := addNode_preserves_outputs_empty _
    { kind := .output name, sigLevel := 0, inputs := [], outputs := [] } h_ids₄ h₄ (by rfl)
  exact h₅ nid nd h_get

/-- A list-arithmetic helper: `[N, N+1] ++ [N+2, ..., N+m+1] ++ [N+m+2, N+m+3]`
is the consecutive range `[N, ..., N+m+3]`. -/
theorem range_map_split (N m : Nat) :
    [N, N + 1] ++ (List.range m).map (fun i => N + 2 + i) ++ [N + 2 + m, N + 3 + m] =
    (List.range (m + 4)).map (N + ·) := by
  induction m with
  | zero =>
    rw [show (4 : Nat) = 3 + 1 from rfl, show (3 : Nat) = 2 + 1 from rfl,
        show (2 : Nat) = 1 + 1 from rfl, show (1 : Nat) = 0 + 1 from rfl]
    simp [List.range_succ, List.range_zero]
  | succ m' ih =>
    rw [show N + 2 + (m' + 1) = N + 3 + m' from by omega,
        show N + 3 + (m' + 1) = N + (m' + 4) from by omega]
    have h_rhs : (List.range (Nat.succ m' + 4)).map (N + ·) =
        (List.range (m' + 4)).map (N + ·) ++ [N + (m' + 4)] := by
      rw [show Nat.succ m' + 4 = m' + 4 + 1 from by omega,
          List.range_succ, List.map_append, List.map_singleton]
    rw [h_rhs, ← ih]
    rw [List.range_succ, List.map_append, List.map_singleton]
    simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- The chain IDs from `buildChainPre` are consecutive starting at `w.nextId`. -/
theorem buildChain_chainIds_range (w : World) (name : String) (c : ChainSpec) :
    (buildChainPre w name c).2.2 =
    (List.range (c.middleDelays.length + 4)).map (w.nextId + ·) := by
  dsimp (config := { zeta := true }) [buildChainPre]
  simp only [World.addNode_fst, World.addNode_nextId, foldl_repFoldlStep_repIds_eq,
    foldl_repFoldlStep_nextId, List.nil_append]
  rw [show w.nextId + 1 + 1 = w.nextId + 2 from by omega,
      show w.nextId + 2 + c.middleDelays.length + 1 =
        w.nextId + 3 + c.middleDelays.length from by omega]
  exact range_map_split w.nextId c.middleDelays.length

/-- For consecutive ids `[N, ..., N+n-1]` whose nodes have no outputs in `w`,
`connectChain` gives node `N+i` the single output `[N+i+1]` (empty for the last node). -/
theorem connectChain_consecutive_outputs (N n : Nat) (w : World)
    (h_empty : ∀ i < n, (w.getNode (N + i)).map NodeData.outputs = some []) :
    ∀ i < n, ((connectChain w ((List.range n).map (N + ·))).getNode (N + i)).map
      NodeData.outputs = some (if i + 1 < n then [N + i + 1] else []) := by
  revert N h_empty
  revert w
  induction n with
  | zero => intro w N h_empty i h_i; omega
  | succ n' ih =>
    intro w N h_empty i h_i
    cases n' with
    | zero =>
      have h_ids : (List.range 1).map (N + ·) = [N] := by simp
      rw [h_ids]
      dsimp [connectChain]
      have h_i0 : i = 0 := by omega
      subst h_i0
      simpa using h_empty 0 (by omega)
    | succ m =>
      set tl_ids := (List.range m).map (N + 2 + ·)
      have h_ids : (List.range (m + 2)).map (N + ·) = N :: (N + 1) :: tl_ids := by
        dsimp [tl_ids]
        suffices h_aux : ∀ M, (List.range (M + 2)).map (N + ·) =
            N :: (N + 1) :: (List.range M).map (N + 2 + ·) from h_aux m
        intro M
        induction M with
        | zero =>
          rw [show (2 : Nat) = 1 + 1 from rfl, show (1 : Nat) = 0 + 1 from rfl]
          simp [List.range_succ, List.range_zero]
        | succ M' ihM =>
          simp only [List.range_succ, List.map_append, List.map_singleton] at ihM ⊢
          rw [ihM]
          simp [List.cons_append]
          ; omega
      rw [h_ids]
      set w₁ := (w.updateNode (N + 1) (fun nd => { nd with inputs := nd.inputs ++ [N] })).updateNode N
        (fun nd => { nd with outputs := nd.outputs ++ [N + 1] })
      have h_decomp : connectChain w (N :: (N + 1) :: tl_ids) = connectChain w₁ ((N + 1) :: tl_ids) := by
        dsimp [connectChain, w₁]
      rw [h_decomp]
      by_cases h_i0 : i = 0
      · subst h_i0
        have h_if : (if 0 + 1 < m + 2 then [N + 0 + 1] else []) = [N + 1] := by simp
        rw [h_if]
        have h_not_mem : N ∉ (N + 1) :: tl_ids := by
          intro h
          have : N = N + 1 ∨ N ∈ tl_ids := by simpa using h
          rcases this with h₁ | h₁
          · omega
          · dsimp [tl_ids] at h₁
            rw [List.mem_map] at h₁
            rcases h₁ with ⟨j, _, h_eq⟩
            omega
        rw [show N + 0 = N from by omega]
        rw [connectChain_getNode_of_not_mem ((N + 1) :: tl_ids) N h_not_mem w₁]
        have h_gn_N : ∃ nd_N, w.getNode N = some nd_N ∧ nd_N.outputs = [] := by
          have := h_empty 0 (by omega)
          cases h_gn : w.getNode N with
          | none => simp [h_gn] at this
          | some nd =>
            refine ⟨nd, ?_, ?_⟩
            · rfl
            · simpa [h_gn] using this
        rcases h_gn_N with ⟨nd_N, h_gn_N, h_out_N⟩
        have h₁ : (w.updateNode (N + 1)
            (fun nd => { nd with inputs := nd.inputs ++ [N] })).getNode N = some nd_N := by
          rw [World.updateNode_getNode_ne w (N + 1) N _ (by omega)]
          exact h_gn_N
        have h₂ : w₁.getNode N =
            some ({ nd_N with outputs := nd_N.outputs ++ [N + 1] } : NodeData) := by
          dsimp [w₁]
          exact World.updateNode_getNode_eq _ N _ nd_N h₁
        rw [h₂, h_out_N]
        simp
      · have h_i_pos : i ≥ 1 := by omega
        set i' := i - 1
        have h_i_eq : i = i' + 1 := by omega
        have h_i'_lt : i' < m + 1 := by omega
        have h_empty' : ∀ j < m + 1, (w₁.getNode (N + 1 + j)).map NodeData.outputs = some [] := by
          intro j h_j
          by_cases h_j0 : j = 0
          · subst h_j0
            have := h_empty 1 (by omega)
            cases h_gn : w.getNode (N + 1) with
            | none => simp [h_gn] at this
            | some nd =>
              have h₁ : (w.updateNode (N + 1)
                  (fun nd => { nd with inputs := nd.inputs ++ [N] })).getNode (N + 1) =
                  some ({ nd with inputs := nd.inputs ++ [N] } : NodeData) :=
                World.updateNode_getNode_eq w (N + 1) _ nd h_gn
              have h₂ : w₁.getNode (N + 1) =
                  some ({ nd with inputs := nd.inputs ++ [N] } : NodeData) := by
                dsimp [w₁]
                rw [World.updateNode_getNode_ne _ N (N + 1) _ (by omega)]
                exact h₁
              rw [h₂]
              dsimp
              rw [h_gn] at this
              simpa using this
          · have h₁ : w₁.getNode (N + 1 + j) = w.getNode (N + 1 + j) := by
              dsimp [w₁]
              rw [World.updateNode_getNode_ne _ N (N + 1 + j) _ (by omega),
                  World.updateNode_getNode_ne _ (N + 1) (N + 1 + j) _ (by omega)]
            rw [h₁, show N + 1 + j = N + (j + 1) from by omega]
            exact h_empty (j + 1) (by omega)
        have h_ih := ih w₁ (N + 1) h_empty' i' h_i'_lt
        have h_tail : (N + 1) :: tl_ids = (List.range (m + 1)).map (N + 1 + ·) := by
          dsimp [tl_ids]
          suffices h_aux : ∀ M, (List.range (M + 1)).map (N + 1 + ·) =
              (N + 1) :: (List.range M).map (N + 2 + ·) from (h_aux m).symm
          intro M
          induction M with
          | zero => simp [List.range_succ, List.range_zero]
          | succ M' ihM =>
            simp only [List.range_succ, List.map_append, List.map_singleton] at ihM ⊢
            rw [ihM]
            simp [List.cons_append]
            ; omega
        rw [h_tail]
        rw [show N + i = N + 1 + i' from by omega, h_ih]
        congr 1
        split_ifs <;> simp at * <;> omega

/-- The world component of `foldl repFoldlStep` does not depend on the accumulated ids. -/
theorem foldl_repFoldlStep_snd_indep (delays : List PNat) (ids₁ ids₂ : List Nat)
    (w : World) :
    (delays.foldl repFoldlStep (ids₁, w)).2 = (delays.foldl repFoldlStep (ids₂, w)).2 := by
  induction delays generalizing ids₁ ids₂ w with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.foldl_cons, repFoldlStep]
    apply ih

/-- The j-th repeater added by `repFoldlStep` sits at `w₀.nextId + j`. -/
theorem foldl_repFoldlStep_getNode_rep (delays : List PNat) (w₀ : World)
    (h_ids : ∀ p ∈ w₀.nodes, p.1 < w₀.nextId) (j : Nat) (h_j : j < delays.length) :
    (delays.foldl repFoldlStep ([], w₀)).2.getNode (w₀.nextId + j) =
    some (mkRepNode delays[j]) := by
  revert w₀ h_ids j h_j
  induction delays with
  | nil => intro w₀ h_ids j h_j; dsimp at h_j; omega
  | cons d ds ih =>
    intro w₀ h_ids j h_j
    simp only [List.foldl_cons, List.length_cons] at h_j ⊢
    set w₁ := (w₀.addNode (mkRepNode d)).2
    have h_step : repFoldlStep ([], w₀) d = ([w₀.nextId], w₁) := by
      dsimp [repFoldlStep, w₁]
    rw [h_step]
    by_cases h_j0 : j = 0
    · subst h_j0
      rw [Nat.add_zero]
      have h_fresh : w₁.getNode w₀.nextId = some (mkRepNode d) :=
        World.addNode_getNode_fresh w₀ (mkRepNode d) (World.getNode_nextId_none w₀ h_ids)
      have h_old := foldl_repFoldlStep_getNode_old ds [w₀.nextId] w₁ w₀.nextId (by
        dsimp [w₁, World.addNode]; omega)
      rw [h_old, h_fresh]
      simp
    · set j' := j - 1
      have h_j_eq : j = j' + 1 := by omega
      have h_j'_lt : j' < ds.length := by omega
      have h_ids₁ : ∀ p ∈ w₁.nodes, p.1 < w₁.nextId :=
        World.addNode_ids_lt_nextId w₀ (mkRepNode d) h_ids
      have h_nextId : w₁.nextId = w₀.nextId + 1 := by dsimp [w₁, World.addNode]
      have h_ih := ih w₁ h_ids₁ j' h_j'_lt
      have h_foldl_snd : (ds.foldl repFoldlStep ([w₀.nextId], w₁)).2 =
          (ds.foldl repFoldlStep ([], w₁)).2 :=
        foldl_repFoldlStep_snd_indep ds [w₀.nextId] [] w₁
      rw [h_foldl_snd]
      rw [show w₀.nextId + j = w₁.nextId + j' from by rw [h_nextId]; omega]
      rw [h_ih]
      simp [h_j_eq, List.getElem_cons_succ]

/-- `foldl repFoldlStep` increases `nextId` by the number of delays. -/
theorem foldl_repFoldlStep_nextId_eq (delays : List PNat) (ids : List Nat) (w : World) :
    (delays.foldl repFoldlStep (ids, w)).2.nextId = w.nextId + delays.length := by
  induction delays generalizing ids w with
  | nil => simp [List.foldl]
  | cons d ds ih =>
    simp only [List.foldl_cons, repFoldlStep, List.length_cons]
    rw [ih]
    dsimp [World.addNode]
    omega

/-- The j-th chain node created by `buildChainPre` exists and has empty outputs. -/
theorem buildChainPre_getNode_chainId (w : World) (name : String) (c : ChainSpec)
    (h_ids : ∀ p ∈ w.nodes, p.1 < w.nextId) (j : Nat)
    (h_j : j < c.middleDelays.length + 4) :
    ∃ nd, (buildChainPre w name c).2.1.getNode (w.nextId + j) = some nd ∧ nd.outputs = [] := by
  set m := c.middleDelays.length
  set N := w.nextId
  have h_cases : j = 0 ∨ j = 1 ∨ (∃ k, k < m ∧ j = k + 2) ∨ j = m + 2 ∨ j = m + 3 := by
    dsimp [m]
    by_cases h_j0 : j = 0
    · exact Or.inl h_j0
    · by_cases h_j1 : j = 1
      · exact Or.inr (Or.inl h_j1)
      · by_cases h_jm2 : j = m + 2
        · exact Or.inr (Or.inr (Or.inr (Or.inl h_jm2)))
        · by_cases h_jm3 : j = m + 3
          · exact Or.inr (Or.inr (Or.inr (Or.inr h_jm3)))
          · exact Or.inr (Or.inr (Or.inl ⟨j - 2, by omega, by omega⟩))
  rcases h_cases with rfl | rfl | ⟨k, h_k_lt, rfl⟩ | rfl | rfl
  · refine ⟨{ kind := .input, sigLevel := 0, inputs := [], outputs := [] }, ?_, ?_⟩
    · exact buildChainPre_getNode_input w name c h_ids
    · rfl
  · refine ⟨{ kind := .observer, sigLevel := 0, inputs := [], outputs := [] }, ?_, ?_⟩
    · exact buildChainPre_getNode_observer w name c h_ids
    · rfl
  · -- the k-th middle repeater
    dsimp (config := { zeta := true }) [buildChainPre]
    set w₁ := (w.addNode { kind := .input, sigLevel := 0, inputs := [], outputs := [] }).2
    set w₂ := (w₁.addNode { kind := .observer, sigLevel := 0, inputs := [], outputs := [] }).2
    set w₃ := (c.middleDelays.foldl repFoldlStep ([], w₂)).2
    set w₄ := (w₃.addNode { kind := .repeater c.lastDelay (-1), sigLevel := 0, inputs := [], outputs := [] }).2
    set w₅ := (w₄.addNode { kind := .output name, sigLevel := 0, inputs := [], outputs := [] }).2
    have h_ids₂ : ∀ p ∈ w₂.nodes, p.1 < w₂.nextId :=
      World.addNode_ids_lt_nextId w₁ _ (World.addNode_ids_lt_nextId w _ h_ids)
    have h_nextId₂ : w₂.nextId = N + 2 := by
      dsimp [w₂, w₁, N]
      rw [World.addNode_nextId, World.addNode_nextId]
    have h_nextId₃ : w₃.nextId = N + 2 + m := by
      dsimp [w₃, m]
      rw [foldl_repFoldlStep_nextId_eq, h_nextId₂]
    refine ⟨mkRepNode c.middleDelays[k], ?_, ?_⟩
    · have h_rep : w₃.getNode (N + 2 + k) = some (mkRepNode c.middleDelays[k]) := by
        have := foldl_repFoldlStep_getNode_rep c.middleDelays w₂ h_ids₂ k h_k_lt
        rwa [h_nextId₂] at this
      have h_old₄ : w₄.getNode (N + 2 + k) = w₃.getNode (N + 2 + k) :=
        World.addNode_getNode_old w₃ _ (N + 2 + k) (by rw [h_nextId₃]; omega)
      have h_old₅ : w₅.getNode (N + 2 + k) = w₄.getNode (N + 2 + k) :=
        World.addNode_getNode_old w₄ _ (N + 2 + k) (by
          dsimp [w₄, World.addNode]; rw [h_nextId₃]; omega)
      rw [show w.nextId + (k + 2) = N + 2 + k from by dsimp [N]; omega]
      rw [h_old₅, h_old₄]
      exact h_rep
    · dsimp [mkRepNode]
  · -- the lastDelay repeater
    dsimp (config := { zeta := true }) [buildChainPre]
    set w₁ := (w.addNode { kind := .input, sigLevel := 0, inputs := [], outputs := [] }).2
    set w₂ := (w₁.addNode { kind := .observer, sigLevel := 0, inputs := [], outputs := [] }).2
    set w₃ := (c.middleDelays.foldl repFoldlStep ([], w₂)).2
    set w₄ := (w₃.addNode { kind := .repeater c.lastDelay (-1), sigLevel := 0, inputs := [], outputs := [] }).2
    set w₅ := (w₄.addNode { kind := .output name, sigLevel := 0, inputs := [], outputs := [] }).2
    have h_ids₂ : ∀ p ∈ w₂.nodes, p.1 < w₂.nextId :=
      World.addNode_ids_lt_nextId w₁ _ (World.addNode_ids_lt_nextId w _ h_ids)
    have h_ids₃ : ∀ p ∈ w₃.nodes, p.1 < w₃.nextId :=
      foldl_repFoldlStep_ids_lt_nextId c.middleDelays [] w₂ h_ids₂
    have h_nextId₂ : w₂.nextId = N + 2 := by
      dsimp [w₂, w₁, N]
      rw [World.addNode_nextId, World.addNode_nextId]
    have h_nextId₃ : w₃.nextId = N + 2 + m := by
      dsimp [w₃, m]
      rw [foldl_repFoldlStep_nextId_eq, h_nextId₂]
    refine ⟨{ kind := .repeater c.lastDelay (-1), sigLevel := 0, inputs := [], outputs := [] },
      ?_, ?_⟩
    · have h_fresh := World.addNode_getNode_fresh w₃
        { kind := .repeater c.lastDelay (-1), sigLevel := 0, inputs := [], outputs := [] }
        (World.getNode_nextId_none w₃ h_ids₃)
      have h_old₅ : w₅.getNode (N + (m + 2)) = w₄.getNode (N + (m + 2)) :=
        World.addNode_getNode_old w₄ _ (N + (m + 2)) (by
          dsimp [w₄, World.addNode]; rw [h_nextId₃]; omega)
      rw [h_old₅, show N + (m + 2) = w₃.nextId from by rw [h_nextId₃]; omega]
      exact h_fresh
    · rfl
  · -- the output node
    dsimp (config := { zeta := true }) [buildChainPre]
    set w₁ := (w.addNode { kind := .input, sigLevel := 0, inputs := [], outputs := [] }).2
    set w₂ := (w₁.addNode { kind := .observer, sigLevel := 0, inputs := [], outputs := [] }).2
    set w₃ := (c.middleDelays.foldl repFoldlStep ([], w₂)).2
    set w₄ := (w₃.addNode { kind := .repeater c.lastDelay (-1), sigLevel := 0, inputs := [], outputs := [] }).2
    set w₅ := (w₄.addNode { kind := .output name, sigLevel := 0, inputs := [], outputs := [] }).2
    have h_ids₂ : ∀ p ∈ w₂.nodes, p.1 < w₂.nextId :=
      World.addNode_ids_lt_nextId w₁ _ (World.addNode_ids_lt_nextId w _ h_ids)
    have h_ids₃ : ∀ p ∈ w₃.nodes, p.1 < w₃.nextId :=
      foldl_repFoldlStep_ids_lt_nextId c.middleDelays [] w₂ h_ids₂
    have h_ids₄ : ∀ p ∈ w₄.nodes, p.1 < w₄.nextId :=
      World.addNode_ids_lt_nextId w₃ _ h_ids₃
    have h_nextId₂ : w₂.nextId = N + 2 := by
      dsimp [w₂, w₁, N]
      rw [World.addNode_nextId, World.addNode_nextId]
    have h_nextId₄ : w₄.nextId = N + (m + 3) := by
      dsimp [w₄, m]
      rw [World.addNode_nextId, foldl_repFoldlStep_nextId_eq, h_nextId₂]
      omega
    refine ⟨{ kind := .output name, sigLevel := 0, inputs := [], outputs := [] }, ?_, ?_⟩
    · have h_fresh := World.addNode_getNode_fresh w₄
        { kind := .output name, sigLevel := 0, inputs := [], outputs := [] }
        (World.getNode_nextId_none w₄ h_ids₄)
      rw [show N + (m + 3) = w₄.nextId from h_nextId₄.symm]
      exact h_fresh
    · rfl

/-- In a freshly built chain, node `w.nextId + i` has output `[w.nextId + i + 1]`
(empty for the last node). -/
theorem buildChain_outputs_consecutive (w : World) (name : String) (c : ChainSpec)
    (_ : ∀ nid nd, w.getNode nid = some nd → nd.outputs = [])
    (h_ids : ∀ p ∈ w.nodes, p.1 < w.nextId) :
    ∀ i < c.middleDelays.length + 4,
      ((buildChain w name c).2.getNode (w.nextId + i)).map NodeData.outputs =
      some (if i + 1 < c.middleDelays.length + 4 then [w.nextId + i + 1] else []) := by
  intro i h_i
  dsimp [buildChain]
  set chainIds := (buildChainPre w name c).2.2
  have h_chainIds : chainIds =
      (List.range (c.middleDelays.length + 4)).map (w.nextId + ·) :=
    buildChain_chainIds_range w name c
  rw [h_chainIds]
  apply connectChain_consecutive_outputs
  · intro j h_j
    rcases buildChainPre_getNode_chainId w name c h_ids j h_j with ⟨nd, h_gn, h_out⟩
    rw [h_gn]
    simp [h_out]
  · exact h_i

/-- `updateNode` preserves existence of a node. -/
theorem World.updateNode_getNode_some (w : World) (updId nid : Nat)
    (f : NodeData → NodeData) :
    (∃ nd, w.getNode nid = some nd) → ∃ nd', (w.updateNode updId f).getNode nid = some nd' := by
  intro ⟨nd, hnd⟩
  by_cases h : nid = updId
  · rw [h.symm]; exact ⟨f nd, World.updateNode_getNode_eq w nid f nd hnd⟩
  · exact ⟨nd, by rw [World.updateNode_getNode_ne w updId nid f (Ne.symm h)]; exact hnd⟩

/-- `setInput` preserves existence of a node. -/
theorem World.setInput_getNode_some (w : World) (updId nid level : Nat) :
    (∃ nd, w.getNode nid = some nd) → ∃ nd', (w.setInput updId level).getNode nid = some nd' := by
  intro h
  dsimp [World.setInput]
  obtain ⟨nd₁, h₁⟩ := World.updateNode_getNode_some w updId nid (fun nd => { nd with sigLevel := level }) h
  rw [World.notifyOutputs_getNode]
  exact ⟨nd₁, h₁⟩

/-- `onScheduledTick` preserves existence of a node. -/
theorem World.onScheduledTick_getNode_some (w : World) (tickId nid : Nat) :
    (∃ nd, w.getNode nid = some nd) → ∃ nd', (w.onScheduledTick tickId).getNode nid = some nd' := by
  intro h
  dsimp [World.onScheduledTick]
  cases h_gn : w.getNode tickId with
  | none =>
    simp []; exact h
  | some nd =>
    cases hk : nd.kind with
    | input => simp [hk]; exact h
    | output name => simp [hk]; exact h
    | observer =>
      simp [hk]
      obtain ⟨nd₁, h₁⟩ := World.updateNode_getNode_some w tickId nid
        (fun nd' => { nd' with sigLevel := 15 }) h
      rw [World.notifyOutputs_getNode]; exact ⟨nd₁, h₁⟩
    | repeater d p =>
      simp [hk]
      obtain ⟨nd₁, h₁⟩ := World.updateNode_getNode_some w tickId nid
        (fun nd' => { nd' with sigLevel := if w.getInputSignal tickId > 0 then 15 else 0 }) h
      rw [World.notifyOutputs_getNode]; exact ⟨nd₁, h₁⟩

/-- `step` preserves existence of a node. -/
theorem World.step_getNode_some (w : World) (nid : Nat) :
    (∃ nd, w.getNode nid = some nd) → ∀ w', w.step = some w' → ∃ nd', w'.getNode nid = some nd' := by
  intro h w' h_step
  dsimp [World.step] at h_step
  cases h_pop : w.popNextEvent with
  | none => simp [h_pop] at h_step
  | some p =>
    rcases p with ⟨ev, w_pop⟩
    rw [h_pop] at h_step
    dsimp at h_step
    injection h_step with h_eq
    subst h_eq
    -- w_pop.getNode nid = w.getNode nid (popNextEvent preserves nodes)
    have h_nodes : w_pop.nodes = w.nodes := World.popNextEvent_nodes w ev w_pop h_pop
    have h_gn : w_pop.getNode nid = w.getNode nid := by dsimp [World.getNode]; rw [h_nodes]
    have h_pop_some : ∃ nd, w_pop.getNode nid = some nd := by
      rcases h with ⟨nd, hnd⟩; exact ⟨nd, by rw [h_gn]; exact hnd⟩
    exact World.onScheduledTick_getNode_some w_pop ev.nodeId nid h_pop_some
