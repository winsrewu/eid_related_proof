import BasicProofs.PrefixChain.Part10


open BasicRedstoneSim

/-- If two worlds share nodes/tick/outputLog/nextId and have the same events at
the current tick, then `stepUntilNextTick` produces the same outputLog. -/
theorem stepUntilNextTick_outputLog_congr (w₁ w₂ : World)
    (h_nodes : w₁.nodes = w₂.nodes)
    (h_tick : w₁.tick = w₂.tick)
    (h_log : w₁.outputLog = w₂.outputLog)
    (h_nextId : w₁.nextId = w₂.nextId)
    (h_filter : w₁.events.filter (fun e => e.targetTick == w₁.tick) =
        w₂.events.filter (fun e => e.targetTick == w₂.tick))
    (h_delay : ∀ nid nd, w₁.getNode nid = some nd → ∀ d p,
        nd.kind = .repeater d p → d ≥ 2) :
    w₁.stepUntilNextTick.outputLog = w₂.stepUntilNextTick.outputLog := by
  revert h_delay h_filter h_nextId h_log h_tick h_nodes w₂
  induction w₁ using World.stepUntilNextTick.induct with
  | case1 w₁ h_step₁ =>
    intro w₂ h_nodes h_tick h_log h_nextId h_filter h_delay
    have h_pop₁ : w₁.popNextEvent = none := by
      dsimp [World.step] at h_step₁
      cases h_pop : w₁.popNextEvent with
      | none => rfl
      | some p => simp [h_pop] at h_step₁
    have h_no₁ : ∀ ev ∈ w₁.events, ev.targetTick ≠ w₁.tick :=
      popNextEvent_none_no_events w₁ h_pop₁
    have h_no₂ : ∀ ev ∈ w₂.events, ev.targetTick ≠ w₂.tick := by
      intro ev h_ev h_eq
      have h_in : ev ∈ w₂.events.filter (fun e => e.targetTick == w₂.tick) := by
        simp [List.mem_filter, h_ev, h_eq]
      rw [← h_filter] at h_in
      have h_eq' : ev.targetTick = w₁.tick := by rwa [h_tick]
      exact h_no₁ ev (List.mem_of_mem_filter h_in) h_eq'
    have h_step₂ : w₂.step = none := by
      dsimp [World.step]
      cases h_pop : w₂.popNextEvent with
      | none => rfl
      | some p =>
        rcases p with ⟨ev, w'⟩
        have := popNextEvent_at_tick w₂ ev w' h_pop
        obtain ⟨_, _, _, _, h_mem, _⟩ := World.popNextEvent_eraseIdx w₂ ev w' h_pop
        exfalso; exact h_no₂ ev h_mem this
    rw [stepUntilNextTick_of_step_none w₁ h_step₁, stepUntilNextTick_of_step_none w₂ h_step₂]
    exact h_log
  | case2 w₁ w₁' h_step₁ ih =>
    intro w₂ h_nodes h_tick h_log h_nextId h_filter h_delay
    have h_sunt₁ : w₁.stepUntilNextTick = w₁'.stepUntilNextTick := by
      rw [World.stepUntilNextTick, h_step₁]
    rw [h_sunt₁]
    dsimp [World.step] at h_step₁
    cases h_pop₁ : w₁.popNextEvent with
    | none => simp [h_pop₁] at h_step₁
    | some p =>
      rcases p with ⟨ev, w₁_pop⟩
      simp [h_pop₁] at h_step₁
      subst h_step₁
      obtain ⟨w₂_pop, h_pop₂⟩ := popNextEvent_same_of_same_filter w₁ w₂ h_tick h_filter ev w₁_pop h_pop₁
      have h_step₂ : w₂.step = some (w₂_pop.onScheduledTick ev.nodeId) := by
        dsimp [World.step]; rw [h_pop₂]
      have h_sunt₂ : w₂.stepUntilNextTick = (w₂_pop.onScheduledTick ev.nodeId).stepUntilNextTick := by
        rw [World.stepUntilNextTick, h_step₂]
      rw [h_sunt₂]
      have h_pop_nodes₁ : w₁_pop.nodes = w₁.nodes := World.popNextEvent_nodes w₁ ev w₁_pop h_pop₁
      have h_pop_nodes₂ : w₂_pop.nodes = w₂.nodes := World.popNextEvent_nodes w₂ ev w₂_pop h_pop₂
      have h_nodes_pop : w₁_pop.nodes = w₂_pop.nodes := by rw [h_pop_nodes₁, h_pop_nodes₂, h_nodes]
      have h_tick_pop : w₁_pop.tick = w₂_pop.tick := by
        rw [World.popNextEvent_tick w₁ ev w₁_pop h_pop₁,
            World.popNextEvent_tick w₂ ev w₂_pop h_pop₂, h_tick]
      have h_log_pop : w₁_pop.outputLog = w₂_pop.outputLog := by
        rw [World.popNextEvent_outputLog w₁ ev w₁_pop h_pop₁,
            World.popNextEvent_outputLog w₂ ev w₂_pop h_pop₂, h_log]
      have h_nextId_pop : w₁_pop.nextId = w₂_pop.nextId := by
        rw [World.popNextEvent_nextId w₁ ev w₁_pop h_pop₁,
            World.popNextEvent_nextId w₂ ev w₂_pop h_pop₂, h_nextId]
      have h_congr := World.onScheduledTick_congr_fields w₁_pop w₂_pop ev.nodeId
        h_nodes_pop h_tick_pop h_log_pop h_nextId_pop
      have h_log' : (w₁_pop.onScheduledTick ev.nodeId).outputLog =
          (w₂_pop.onScheduledTick ev.nodeId).outputLog := h_congr.2.2.1
      have h_nodes' : (w₁_pop.onScheduledTick ev.nodeId).nodes =
          (w₂_pop.onScheduledTick ev.nodeId).nodes := h_congr.1
      have h_tick' : (w₁_pop.onScheduledTick ev.nodeId).tick =
          (w₂_pop.onScheduledTick ev.nodeId).tick := h_congr.2.1
      have h_nextId' : (w₁_pop.onScheduledTick ev.nodeId).nextId =
          (w₂_pop.onScheduledTick ev.nodeId).nextId := h_congr.2.2.2.1
      -- Filter equality after onScheduledTick (same as in nodes_congr)
      have h_filter' : (w₁_pop.onScheduledTick ev.nodeId).events.filter
          (fun e => e.targetTick == (w₁_pop.onScheduledTick ev.nodeId).tick) =
          (w₂_pop.onScheduledTick ev.nodeId).events.filter
          (fun e => e.targetTick == (w₂_pop.onScheduledTick ev.nodeId).tick) := by
        simp only [World.onScheduledTick_tick, ← h_tick_pop]
        have h_pop_filter := popNextEvent_filter_eq w₁ w₂
          h_tick h_filter ev w₁_pop w₂_pop h_pop₁ h_pop₂
        have h_delay₁ : ∀ nid nd, w₁_pop.getNode nid = some nd → ∀ d p,
            nd.kind = .repeater d p → d ≥ 2 := by
          intro nid nd h_nd
          have : w₁.getNode nid = some nd := by
            dsimp [World.getNode]; rw [← h_pop_nodes₁]; exact h_nd
          exact h_delay nid nd this
        obtain ⟨new₁, h_app₁, h_fut₁⟩ := World.onScheduledTick_events_append w₁_pop ev.nodeId h_delay₁
        rw [h_app₁, List.filter_append]
        have h_e₁ : new₁.filter (fun e => e.targetTick == w₁_pop.tick) = [] := by
          apply List.filter_eq_nil_iff.mpr; intro e he
          have := h_fut₁ e he; simp; omega
        rw [h_e₁, List.append_nil]
        have h_delay₂ : ∀ nid nd, w₂_pop.getNode nid = some nd → ∀ d p,
            nd.kind = .repeater d p → d ≥ 2 := by
          intro nid nd h_nd
          have : w₁_pop.getNode nid = some nd := by
            dsimp [World.getNode] at h_nd ⊢; rw [← h_nodes_pop] at h_nd; exact h_nd
          exact h_delay₁ nid nd this
        obtain ⟨new₂, h_app₂, h_fut₂⟩ := World.onScheduledTick_events_append w₂_pop ev.nodeId h_delay₂
        rw [h_app₂, List.filter_append]
        have h_e₂ : new₂.filter (fun e => e.targetTick == w₁_pop.tick) = [] := by
          apply List.filter_eq_nil_iff.mpr; intro e he
          have := h_fut₂ e he
          rw [← h_tick_pop] at this; simp; omega
        rw [h_e₂, List.append_nil]
        rw [← h_tick_pop] at h_pop_filter
        exact h_pop_filter
      have h_delay' : ∀ nid nd, (w₁_pop.onScheduledTick ev.nodeId).getNode nid = some nd →
          ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
        intro nid nd h_nd d p h_kind
        obtain ⟨nd₀, h_nd₀, h_kind_eq⟩ := World.onScheduledTick_kind_preserved w₁_pop ev.nodeId nid nd h_nd
        rw [h_kind_eq] at h_kind
        have : w₁.getNode nid = some nd₀ := by
          dsimp [World.getNode]; rw [← h_pop_nodes₁]; exact h_nd₀
        exact h_delay nid nd₀ this d p h_kind
      exact ih (w₂_pop.onScheduledTick ev.nodeId) h_nodes' h_tick' h_log' h_nextId' h_filter' h_delay'

/-- Folding `onNeighborUpdate` over a list preserves outputLog when none of the
target nodes are `.output` nodes. -/
theorem foldl_onNeighborUpdate_outputLog_eq (l : List Nat) (w : World)
    (h_no_output : ∀ out_id ∈ l, ∀ nd, w.getNode out_id = some nd → ∀ name, nd.kind ≠ .output name) :
    (l.foldl (fun w' outId => w'.onNeighborUpdate outId) w).outputLog = w.outputLog := by
  induction l generalizing w with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    have h_log : (w.onNeighborUpdate hd).outputLog = w.outputLog := by
      dsimp [World.onNeighborUpdate]
      cases h_gn : w.getNode hd with
      | none => rfl
      | some nd =>
        dsimp
        cases h_kind : nd.kind with
        | input => rfl
        | output name => exfalso; exact h_no_output hd (by simp) nd h_gn name (by rw [h_kind])
        | repeater _ _ => simp [World.scheduleEvent_outputLog]
        | observer => simp [World.scheduleEvent_outputLog]
    rw [ih (w.onNeighborUpdate hd) (by
      intro out_id h_mem nd_out h_nd_out name hk
      exact h_no_output out_id (by simp [h_mem]) nd_out
        (by rwa [← World.onNeighborUpdate_getNode w hd out_id]) name hk), h_log]

/-- `setInput in2 15` preserves outputLog when none of in2's outputs are `.output` nodes. -/
theorem setInput_outputLog_eq (w : World) (in2 : Nat)
    (h_no_output : ∀ nd, w.getNode in2 = some nd → ∀ out_id ∈ nd.outputs,
        ∀ nd_out, w.getNode out_id = some nd_out → ∀ name, nd_out.kind ≠ .output name) :
    (w.setInput in2 15).outputLog = w.outputLog := by
  dsimp [World.setInput, World.notifyOutputs]
  cases h_gn : w.getNode in2 with
  | none =>
    have h_none := World.updateNode_getNode_none w in2 (fun nd => { nd with sigLevel := 15 }) h_gn
    simp [h_none]; rfl
  | some nd₀ =>
    have h_gn' : (w.updateNode in2 (fun nd => { nd with sigLevel := 15 })).getNode in2 =
        some { nd₀ with sigLevel := 15 } :=
      World.updateNode_getNode_eq w in2 (fun nd => { nd with sigLevel := 15 }) nd₀ h_gn
    simp only [h_gn']
    apply foldl_onNeighborUpdate_outputLog_eq
    intro out_id h_mem nd_out h_nd_out name
    obtain ⟨nd₀', h_nd₀', h_kind_eq⟩ := World.updateNode_getNode_kind w in2 out_id
      (fun nd => { nd with sigLevel := 15 }) (fun nd => rfl) nd_out h_nd_out
    rw [← h_kind_eq]
    exact h_no_output nd₀ h_gn out_id (by simpa using h_mem) nd₀' h_nd₀' name

/-- `setInput in2 15` commutes with `stepUntilNextTick` for nodes, provided
no event at the current tick targets `in2` and `in2` is not in the inputs
of any node that has an event at the current tick. -/
theorem setInput_stepUntilNextTick_comm_nodes (w : World) (in2 : Nat)
    (h_no_target : ∀ ev ∈ w.events, ev.targetTick = w.tick → ev.nodeId ≠ in2)
    (h_sep : ∀ nid nd, w.getNode nid = some nd →
        (∃ ev ∈ w.events, ev.targetTick = w.tick ∧ ev.nodeId = nid) → in2 ∉ nd.inputs)
    (h_delay : ∀ nid nd, w.getNode nid = some nd → ∀ d p,
        nd.kind = .repeater d p → d ≥ 2) :
    ((w.setInput in2 15).stepUntilNextTick).nodes =
    ((w.stepUntilNextTick).setInput in2 15).nodes := by
  revert in2 h_no_target h_sep h_delay
  induction w using World.stepUntilNextTick.induct with
  | case1 w h_step =>
    intro in2 h_no_target h_sep h_delay
    rw [stepUntilNextTick_of_step_none w h_step]
    have h_pop : w.popNextEvent = none := by
      dsimp [World.step] at h_step
      cases h_pop : w.popNextEvent with
      | none => rfl
      | some p => simp [h_pop] at h_step
    have h_no_ev : ∀ ev ∈ w.events, ev.targetTick ≠ w.tick :=
      fun ev h_ev h_tick => (popNextEvent_none_no_events w h_pop ev h_ev h_tick).elim
    have h_step' : (w.setInput in2 15).step = none := by
      dsimp [World.step]
      cases h_pop' : (w.setInput in2 15).popNextEvent with
      | none => rfl
      | some p' =>
        rcases p' with ⟨ev, w'⟩
        have h_ev_tick := popNextEvent_at_tick (w.setInput in2 15) ev w' h_pop'
        obtain ⟨_, _, _, _, h_mem, _⟩ := World.popNextEvent_eraseIdx (w.setInput in2 15) ev w' h_pop'
        rw [World.setInput_tick] at h_ev_tick
        by_cases h_old : ev ∈ w.events
        · exfalso; exact h_no_ev ev h_old h_ev_tick
        · have := setInput_events_future_ge2 w in2 15 h_delay ev h_mem h_old
          omega
    rw [stepUntilNextTick_of_step_none (w.setInput in2 15) h_step']
    dsimp [World.setInput]
    rw [World.notifyOutputs_nodes, World.notifyOutputs_nodes]
    dsimp [World.updateNode]
  | case2 w w' h_step ih =>
    intro in2 h_no_target h_sep h_delay
    have h_sunt : w.stepUntilNextTick = w'.stepUntilNextTick := by
      rw [World.stepUntilNextTick, h_step]
    rw [h_sunt]
    dsimp [World.step] at h_step
    cases h_pop : w.popNextEvent with
    | none => simp [h_pop] at h_step
    | some p =>
      rcases p with ⟨ev, w_pop⟩
      simp [h_pop] at h_step
      subst h_step
      -- w' = w_pop.onScheduledTick ev.nodeId
      -- Goal: ((w.setInput in2 15).stepUntilNextTick).nodes =
      --        ((w_pop.onScheduledTick ev.nodeId).stepUntilNextTick.setInput in2 15).nodes
      -- Step 1: Show (w.setInput in2 15) has same filter at current tick as w
      have h_ev_tick : ev.targetTick = w.tick := popNextEvent_at_tick w ev w_pop h_pop
      have h_filter_set : (w.setInput in2 15).events.filter
          (fun e => e.targetTick == (w.setInput in2 15).tick) =
          w.events.filter (fun e => e.targetTick == w.tick) := by
        rw [World.setInput_tick]
        dsimp [World.setInput, World.notifyOutputs]
        set w' := w.updateNode in2 (fun nd => { nd with sigLevel := 15 })
        have h_ev' : w'.events = w.events := World.updateNode_events w in2 _
        have h_tick' : w'.tick = w.tick := World.updateNode_tick w in2 _
        cases h_gn : w'.getNode in2 with
        | none => simp [h_ev']
        | some nd =>
          simp only []
          have h_delay' : ∀ nid nd, w'.getNode nid = some nd → ∀ d p,
              nd.kind = .repeater d p → d ≥ 2 := by
            intro nid nd' h_nd' d p h_kind
            obtain ⟨nd₀, h_nd₀, h_kind_eq⟩ := World.updateNode_getNode_kind w in2 nid
              (fun nd => { nd with sigLevel := 15 }) (fun nd => rfl) nd' h_nd'
            rw [← h_kind_eq] at h_kind
            exact h_delay nid nd₀ h_nd₀ d p h_kind
          obtain ⟨new_ev, h_app, h_fut⟩ := foldl_onNeighborUpdate_events_append nd.outputs w' h_delay'
          rw [h_app, h_ev', List.filter_append]
          have h_empty : new_ev.filter (fun e => e.targetTick == w.tick) = [] := by
            apply List.filter_eq_nil_iff.mpr
            intro e he; have h_gt := h_fut e he; rw [h_tick'] at h_gt; simp; omega
          simp [h_empty]
      -- Step 2: Pop same event from (w.setInput in2 15)
      obtain ⟨w_pop', h_pop'⟩ := popNextEvent_same_of_same_filter w (w.setInput in2 15)
        (by rw [World.setInput_tick]) h_filter_set.symm ev w_pop h_pop
      -- Step 3: (w.setInput in2 15).stepUntilNextTick = (w_pop'.onScheduledTick ev.nodeId).stepUntilNextTick
      have h_sunt' : (w.setInput in2 15).stepUntilNextTick =
          (w_pop'.onScheduledTick ev.nodeId).stepUntilNextTick := by
        rw [World.stepUntilNextTick]
        dsimp [World.step]
        rw [h_pop']
      rw [h_sunt']
      -- Step 4: Show w_pop'.nodes = (w_pop.setInput in2 15).nodes (and tick, log, nextId)
      have h_pop'_nodes : w_pop'.nodes = (w.setInput in2 15).nodes :=
        World.popNextEvent_nodes (w.setInput in2 15) ev w_pop' h_pop'
      have h_pop_nodes : w_pop.nodes = w.nodes := World.popNextEvent_nodes w ev w_pop h_pop
      have h_pop'_eq_nodes : w_pop'.nodes = (w_pop.setInput in2 15).nodes := by
        rw [h_pop'_nodes]
        dsimp [World.setInput]
        rw [World.notifyOutputs_nodes, World.notifyOutputs_nodes]
        dsimp [World.updateNode]
        rw [h_pop_nodes]
      have h_pop'_eq_tick : w_pop'.tick = (w_pop.setInput in2 15).tick := by
        rw [World.popNextEvent_tick (w.setInput in2 15) ev w_pop' h_pop',
            World.setInput_tick, ← World.popNextEvent_tick w ev w_pop h_pop,
            World.setInput_tick]
      have h_pop'_eq_log : w_pop'.outputLog = (w_pop.setInput in2 15).outputLog := by
        rw [World.popNextEvent_outputLog (w.setInput in2 15) ev w_pop' h_pop']
        dsimp [World.setInput]
        apply World.notifyOutputs_outputLog_congr
        · dsimp [World.updateNode]; rw [h_pop_nodes]
        · dsimp [World.updateNode]
          rw [World.popNextEvent_outputLog w ev w_pop h_pop]
      have h_pop'_eq_nextId : w_pop'.nextId = (w_pop.setInput in2 15).nextId := by
        rw [World.popNextEvent_nextId (w.setInput in2 15) ev w_pop' h_pop',
            World.setInput_nextId, ← World.popNextEvent_nextId w ev w_pop h_pop,
            World.setInput_nextId]
      -- Step 5: By onScheduledTick_congr_fields + setInput_onScheduledTick_comm_nodes
      have h_congr := World.onScheduledTick_congr_fields w_pop' (w_pop.setInput in2 15) ev.nodeId
        h_pop'_eq_nodes h_pop'_eq_tick h_pop'_eq_log h_pop'_eq_nextId
      have h_sep' : ∀ nd, w_pop.getNode ev.nodeId = some nd → in2 ∉ nd.inputs := by
        intro nd h_nd
        apply h_sep ev.nodeId nd _ ⟨ev, by
          obtain ⟨_, _, _, _, h_mem, _⟩ := World.popNextEvent_eraseIdx w ev w_pop h_pop
          exact h_mem, h_ev_tick, rfl⟩
        have h_getNode_eq : w.getNode ev.nodeId = w_pop.getNode ev.nodeId := by
          rw [World.getNode, World.getNode, h_pop_nodes]
        rwa [h_getNode_eq]
      have h_id_ne : ev.nodeId ≠ in2 := by
        intro h_eq
        obtain ⟨_, _, _, _, h_mem, _⟩ := World.popNextEvent_eraseIdx w ev w_pop h_pop
        exact h_no_target ev h_mem h_ev_tick h_eq
      have h_comm := setInput_onScheduledTick_comm_nodes w_pop in2 ev.nodeId h_id_ne h_sep'
      have h_nodes'' : (w_pop'.onScheduledTick ev.nodeId).nodes =
          (w_pop.onScheduledTick ev.nodeId |>.setInput in2 15).nodes := by
        rw [h_congr.1, h_comm]
      have h_tick'' : (w_pop'.onScheduledTick ev.nodeId).tick =
          (w_pop.onScheduledTick ev.nodeId |>.setInput in2 15).tick := by
        rw [h_congr.2.1, World.onScheduledTick_tick, World.setInput_tick,
            World.setInput_tick, ← World.onScheduledTick_tick]
      -- Step 6: Filter equality (depends on h_k_eq being proved)
      have h_filter'' : (w_pop'.onScheduledTick ev.nodeId).events.filter
          (fun e => e.targetTick == (w_pop'.onScheduledTick ev.nodeId).tick) =
          (w_pop.onScheduledTick ev.nodeId |>.setInput in2 15).events.filter
          (fun e => e.targetTick == (w_pop.onScheduledTick ev.nodeId |>.setInput in2 15).tick) := by
        rw [h_tick'']
        -- Step A: popNextEvent preserves filter equality
        have h_pop_filter := popNextEvent_filter_eq w (w.setInput in2 15)
          (by rw [World.setInput_tick]) h_filter_set.symm ev w_pop w_pop' h_pop h_pop'
        -- Step B: LHS reduces to w_pop'.events.filter via onScheduledTick_events_append
        have h_delay_pop' : ∀ nid nd, w_pop'.getNode nid = some nd → ∀ d p,
            nd.kind = .repeater d p → d ≥ 2 := by
          intro nid nd h_nd d p h_kind
          have h_nd' : (w_pop.setInput in2 15).getNode nid = some nd := by
            dsimp [World.getNode] at h_nd ⊢; rw [← h_pop'_eq_nodes]; exact h_nd
          obtain ⟨nd₀, h_nd₀, h_kind_eq⟩ := World.setInput_kind_preserved w_pop in2 15 nid nd h_nd'
          have h_getNode_eq : w_pop.getNode nid = w.getNode nid := by
            rw [World.getNode, World.getNode, h_pop_nodes]
          rw [h_getNode_eq] at h_nd₀
          have h_kind₀ : nd₀.kind = .repeater d p := by rw [← h_kind_eq]; exact h_kind
          exact h_delay nid nd₀ h_nd₀ d p h_kind₀
        obtain ⟨new₁, h_app₁, h_fut₁⟩ := World.onScheduledTick_events_append w_pop' ev.nodeId h_delay_pop'
        rw [h_app₁, List.filter_append]
        have h_tick_rhs : (w_pop.onScheduledTick ev.nodeId |>.setInput in2 15).tick = w_pop.tick := by
          rw [World.setInput_tick, World.onScheduledTick_tick]
        simp only [h_tick_rhs]
        have h_e₁ : new₁.filter (fun e => e.targetTick == w_pop.tick) = [] := by
          apply List.filter_eq_nil_iff.mpr; intro e he
          have h_fut := h_fut₁ e he
          have h_tick_pop'_eq : w_pop'.tick = w_pop.tick := by
            rw [World.popNextEvent_tick (w.setInput in2 15) ev w_pop' h_pop',
                World.setInput_tick, ← World.popNextEvent_tick w ev w_pop h_pop]
          rw [h_tick_pop'_eq] at h_fut; simp; omega
        rw [h_e₁, List.append_nil]
        -- Step C: RHS reduces to w_pop.events.filter via onScheduledTick + setInput
        have h_delay_pop : ∀ nid nd, w_pop.getNode nid = some nd → ∀ d p,
            nd.kind = .repeater d p → d ≥ 2 := by
          intro nid nd h_nd
          have : w.getNode nid = some nd := by
            dsimp [World.getNode] at h_nd ⊢; rw [← h_pop_nodes]; exact h_nd
          exact h_delay nid nd this
        obtain ⟨new₂, h_app₂, h_fut₂⟩ := World.onScheduledTick_events_append w_pop ev.nodeId h_delay_pop
        -- Now handle setInput on (w_pop.onScheduledTick ev.nodeId)
        dsimp [World.setInput, World.notifyOutputs]
        set w_st := w_pop.onScheduledTick ev.nodeId
        set w_st' := w_st.updateNode in2 (fun nd => { nd with sigLevel := 15 })
        have h_st_ev : w_st'.events = w_st.events := by simp [w_st']
        have h_st_tick : w_st'.tick = w_st.tick := by simp [w_st']
        rw [h_app₂] at h_st_ev
        cases h_gn : w_st'.getNode in2 with
        | none =>
          have h_e₂ : new₂.filter (fun e => e.targetTick == w_pop.tick) = [] := by
            apply List.filter_eq_nil_iff.mpr; intro e he; have := h_fut₂ e he; simp; omega
          have h_tick_pop'_eq : w_pop'.tick = w_pop.tick := by
            rw [World.popNextEvent_tick (w.setInput in2 15) ev w_pop' h_pop',
                World.setInput_tick, ← World.popNextEvent_tick w ev w_pop h_pop]
          rw [h_st_ev, List.filter_append, h_e₂, List.append_nil]
          rw [h_tick_pop'_eq] at h_pop_filter
          exact h_pop_filter.symm
        | some nd =>
          simp only []
          have h_delay_st : ∀ nid nd, w_st'.getNode nid = some nd → ∀ d p,
              nd.kind = .repeater d p → d ≥ 2 := by
            intro nid nd' h_nd' d p h_kind'
            obtain ⟨nd₀, h_nd₀, h_kind_eq⟩ := World.updateNode_getNode_kind w_st in2 nid
              (fun nd => { nd with sigLevel := 15 }) (fun nd => rfl) nd' h_nd'
            rw [← h_kind_eq] at h_kind'
            obtain ⟨nd₁, h_nd₁, h_kind_eq'⟩ := World.onScheduledTick_kind_preserved w_pop ev.nodeId nid nd₀ h_nd₀
            rw [h_kind_eq'] at h_kind'
            exact h_delay_pop nid nd₁ h_nd₁ d p h_kind'
          obtain ⟨new₃, h_app₃, h_fut₃⟩ := foldl_onNeighborUpdate_events_append nd.outputs w_st' h_delay_st
          rw [h_app₃, h_st_ev, List.filter_append, List.filter_append]
          have h_tick_st : w_st.tick = w_pop.tick := World.onScheduledTick_tick _ _
          have h_e₂ : new₂.filter (fun e => e.targetTick == w_pop.tick) = [] := by
            apply List.filter_eq_nil_iff.mpr; intro e he; have := h_fut₂ e he; simp; omega
          have h_e₃ : new₃.filter (fun e => e.targetTick == w_pop.tick) = [] := by
            apply List.filter_eq_nil_iff.mpr; intro e he; have := h_fut₃ e he
            rw [h_st_tick, h_tick_st] at this; simp; omega
          rw [h_e₂, h_e₃, List.append_nil, List.append_nil]
          have h_tick_pop'_eq : w_pop'.tick = w_pop.tick := by
            rw [World.popNextEvent_tick (w.setInput in2 15) ev w_pop' h_pop',
                World.setInput_tick, ← World.popNextEvent_tick w ev w_pop h_pop]
          rw [h_tick_pop'_eq] at h_pop_filter
          exact h_pop_filter.symm
      -- Step 7: Delay property
      have h_delay'' : ∀ nid nd, (w_pop'.onScheduledTick ev.nodeId).getNode nid = some nd →
          ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
        intro nid nd h_nd d p h_kind
        obtain ⟨nd₀, h_nd₀, h_kind_eq⟩ := World.onScheduledTick_kind_preserved w_pop' ev.nodeId nid nd h_nd
        rw [h_kind_eq] at h_kind
        have h_getNode_eq₁ : w_pop'.getNode nid = (w_pop.setInput in2 15).getNode nid := by
          rw [World.getNode, World.getNode, h_pop'_eq_nodes]
        rw [h_getNode_eq₁] at h_nd₀
        obtain ⟨nd₁, h_nd₁, h_kind_eq'⟩ := World.setInput_kind_preserved w_pop in2 15 nid nd₀ h_nd₀
        have h_getNode_eq₂ : w_pop.getNode nid = w.getNode nid := by
          rw [World.getNode, World.getNode, h_pop_nodes]
        rw [h_getNode_eq₂] at h_nd₁
        have h_kind₁ : nd₁.kind = .repeater d p := by
          rw [← h_kind_eq']
          exact h_kind
        exact h_delay nid nd₁ h_nd₁ d p h_kind₁
      -- Step 8: Use stepUntilNextTick_nodes_congr
      have h_congr_nodes := stepUntilNextTick_nodes_congr (w_pop'.onScheduledTick ev.nodeId)
        (w_pop.onScheduledTick ev.nodeId |>.setInput in2 15)
        h_nodes'' h_tick'' h_filter'' h_delay''
      -- Step 9: Use IH
      have h_ih := ih in2
        (by -- h_no_target for w'
          intro ev' h_ev' h_tick'
          obtain ⟨new_ev, h_app, h_fut⟩ := World.onScheduledTick_events_append w_pop ev.nodeId
            (by intro nid nd h_nd
                have h_getNode_eq : w_pop.getNode nid = w.getNode nid := by
                  rw [World.getNode, World.getNode, h_pop_nodes]
                have : w.getNode nid = some nd := by rwa [← h_getNode_eq]
                exact h_delay nid nd this)
          rw [h_app] at h_ev'
          simp [List.mem_append] at h_ev'
          cases h_ev' with
          | inl h_old =>
            obtain ⟨idx, h_idx, h_erase, h_tick_ev, h_mem, h_get⟩ := World.popNextEvent_eraseIdx w ev w_pop h_pop
            rw [h_erase] at h_old
            have h_ev'_in_w : ev' ∈ w.events :=
              List.mem_of_mem_eraseIdx h_old
            have h_ev'_tick : ev'.targetTick = w.tick := by
              rw [World.onScheduledTick_tick, World.popNextEvent_tick w ev w_pop h_pop] at h_tick'
              exact h_tick'
            exact h_no_target ev' h_ev'_in_w h_ev'_tick
          | inr h_new =>
            have h_gt := h_fut ev' h_new
            rw [World.onScheduledTick_tick, World.popNextEvent_tick w ev w_pop h_pop] at h_tick'
            rw [World.popNextEvent_tick w ev w_pop h_pop] at h_gt
            omega)
        (by -- h_sep for w'
          intro nid nd h_nd h_exists
          obtain ⟨ev', h_ev', h_tick', h_node⟩ := h_exists
          obtain ⟨new_ev, h_app, h_fut⟩ := World.onScheduledTick_events_append w_pop ev.nodeId
            (by intro nid nd h_nd
                have h_getNode_eq : w_pop.getNode nid = w.getNode nid := by
                  rw [World.getNode, World.getNode, h_pop_nodes]
                have : w.getNode nid = some nd := by rwa [← h_getNode_eq]
                exact h_delay nid nd this)
          rw [h_app] at h_ev'
          simp [List.mem_append] at h_ev'
          cases h_ev' with
          | inl h_old =>
            obtain ⟨idx, h_idx, h_erase, h_tick_ev, h_mem, h_get⟩ := World.popNextEvent_eraseIdx w ev w_pop h_pop
            rw [h_erase] at h_old
            have h_ev'_in_w : ev' ∈ w.events :=
              List.mem_of_mem_eraseIdx h_old
            have h_ev'_tick : ev'.targetTick = w.tick := by
              rw [World.onScheduledTick_tick, World.popNextEvent_tick w ev w_pop h_pop] at h_tick'
              exact h_tick'
            obtain ⟨nd₀, h_nd₀, h_kind_eq⟩ := World.onScheduledTick_kind_preserved w_pop ev.nodeId nid nd h_nd
            have h_nd₀' : w.getNode nid = some nd₀ := by
              have h_getNode_eq : w_pop.getNode nid = w.getNode nid := by
                rw [World.getNode, World.getNode, h_pop_nodes]
              rwa [← h_getNode_eq]
            have h_inputs : nd.inputs = nd₀.inputs := by
              obtain ⟨nd₀', h_nd₀', h_inputs_eq, _⟩ := World.onScheduledTick_inputs_preserved w_pop ev.nodeId nid nd h_nd
              have h_nd₀_eq : nd₀' = nd₀ := by
                apply Option.some_inj.mp
                rw [← h_nd₀', h_nd₀]
              rw [← h_nd₀_eq]
              exact h_inputs_eq
            rw [h_inputs]
            exact h_sep nid nd₀ h_nd₀' ⟨ev', h_ev'_in_w, h_ev'_tick, h_node⟩
          | inr h_new =>
            have h_gt := h_fut ev' h_new
            rw [World.onScheduledTick_tick, World.popNextEvent_tick w ev w_pop h_pop] at h_tick'
            rw [World.popNextEvent_tick w ev w_pop h_pop] at h_gt
            omega)
        (by -- h_delay for w'
          intro nid nd h_nd d p h_kind
          obtain ⟨nd₀, h_nd₀, h_kind_eq⟩ := World.onScheduledTick_kind_preserved w_pop ev.nodeId nid nd h_nd
          rw [h_kind_eq] at h_kind
          have h_nd₀' : w.getNode nid = some nd₀ := by
            have h_getNode_eq : w_pop.getNode nid = w.getNode nid := by
              rw [World.getNode, World.getNode, h_pop_nodes]
            rwa [← h_getNode_eq]
          exact h_delay nid nd₀ h_nd₀' d p h_kind)
      rw [h_congr_nodes, h_ih]

/-- Folding `onNeighborUpdate` gives the same outputLog for worlds differing only
at `excluded`'s node data, when `excluded` is not in the inputs of any listed node
and all listed nodes have the same kind in both worlds. -/
theorem foldl_onNeighborUpdate_outputLog_congr_except (l : List Nat) (w₁ w₂ : World)
    (excluded : Nat)
    (h_nodes_except : ∀ nid, nid ≠ excluded → w₁.getNode nid = w₂.getNode nid)
    (h_mem_ne : ∀ nid ∈ l, nid ≠ excluded)
    (h_log : w₁.outputLog = w₂.outputLog)
    (h_not_input : ∀ nid ∈ l, ∀ nd, w₁.getNode nid = some nd → excluded ∉ nd.inputs) :
    (l.foldl (fun w' outId => w'.onNeighborUpdate outId) w₁).outputLog =
    (l.foldl (fun w' outId => w'.onNeighborUpdate outId) w₂).outputLog := by
  induction l generalizing w₁ w₂ with
  | nil => exact h_log
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    have h_hd_ne : hd ≠ excluded := h_mem_ne hd (by simp)
    have h_gn : w₁.getNode hd = w₂.getNode hd := h_nodes_except hd h_hd_ne
    have h_log' : (w₁.onNeighborUpdate hd).outputLog = (w₂.onNeighborUpdate hd).outputLog := by
      dsimp [World.onNeighborUpdate]
      rw [h_gn]
      split
      · exact h_log
      · rename_i nd; split
        · simp [World.scheduleEvent_outputLog, h_log]
        · simp [World.scheduleEvent_outputLog, h_log]
        · rename_i name
          have h_gis : w₁.getInputSignal hd = w₂.getInputSignal hd :=
            getInputSignal_congr_except w₁ w₂ hd excluded h_hd_ne
              (fun nid h_ne => h_nodes_except nid h_ne)
              (fun nd' h_nd' => h_not_input hd (by simp) nd' h_nd')
          simp [World.logOutput, h_log, h_gis]
        · exact h_log
    apply ih
    · intro nid h_ne; rw [World.onNeighborUpdate_getNode, World.onNeighborUpdate_getNode]
      exact h_nodes_except nid h_ne
    · intro nid h_mem; exact h_mem_ne nid (by simp [h_mem])
    · exact h_log'
    · intro nid h_mem nd h_nd
      exact h_not_input nid (by simp [h_mem]) nd (by
        rw [← World.onNeighborUpdate_getNode w₁ hd nid]; exact h_nd)

/-- Helper: `notifyOutputs id` gives the same outputLog for worlds differing
only at `excluded`'s sigLevel, when outputs of `id` avoid `excluded` and
`excluded` is not in their inputs. -/
theorem notifyOutputs_outputLog_congr_except' (w₁ w₂ : World) (id excluded : Nat)
    (h_id_ne : id ≠ excluded)
    (h_nodes_except : ∀ nid, nid ≠ excluded → w₁.getNode nid = w₂.getNode nid)
    (h_log : w₁.outputLog = w₂.outputLog)
    (h_outputs_ne : ∀ nd, w₁.getNode id = some nd → ∀ out_id ∈ nd.outputs, out_id ≠ excluded)
    (h_not_input : ∀ nd, w₁.getNode id = some nd → ∀ out_id ∈ nd.outputs,
        ∀ nd_out, w₁.getNode out_id = some nd_out → excluded ∉ nd_out.inputs) :
    (w₁.notifyOutputs id).outputLog = (w₂.notifyOutputs id).outputLog := by
  dsimp [World.notifyOutputs]
  have h_gn : w₁.getNode id = w₂.getNode id := h_nodes_except id h_id_ne
  rw [h_gn]
  cases h_nd : w₂.getNode id with
  | none => exact h_log
  | some nd =>
    have h_nd₁ : w₁.getNode id = some nd := by rw [h_gn, h_nd]
    simp only []
    apply foldl_onNeighborUpdate_outputLog_congr_except nd.outputs w₁ w₂ excluded
      h_nodes_except
      (fun nid h_mem => h_outputs_ne nd h_nd₁ nid h_mem)
      h_log
      (fun nid h_mem nd' h_nd' => h_not_input nd h_nd₁ nid h_mem nd' h_nd')

/-- `setInput in2 level` preserves `getNode nid` when `nid ≠ in2`. -/
theorem setInput_getNode_ne' (w : World) (in2 nid : Nat) (h : nid ≠ in2) :
    (w.setInput in2 15).getNode nid = w.getNode nid := by
  change ((w.updateNode in2 (fun nd => { nd with sigLevel := 15 })).notifyOutputs in2).getNode nid = w.getNode nid
  rw [World.notifyOutputs_getNode]
  exact World.updateNode_getNode_ne w in2 nid _ (Ne.symm h)

/-- After `updateNode nodeId f`, getNode agrees for nid ≠ in2 when setInput's getNode agrees. -/
theorem updateNode_getNode_congr_except (w : World) (in2 nodeId : Nat)
    (h_getNode : (w.setInput in2 15).getNode nodeId = w.getNode nodeId) :
    ∀ f : NodeData → NodeData, ∀ nid, nid ≠ in2 →
        ((w.setInput in2 15).updateNode nodeId f).getNode nid = (w.updateNode nodeId f).getNode nid := by
  intro f nid h_ne
  by_cases h_eq : nid = nodeId
  · rw [h_eq]
    by_cases h_none : w.getNode nodeId = none
    · have h₁ : (w.setInput in2 15).getNode nodeId = none := by rwa [h_getNode]
      rw [World.updateNode_getNode_none _ _ _ h₁, World.updateNode_getNode_none _ _ _ h_none]
    · obtain ⟨nd, h_nd⟩ := Option.ne_none_iff_exists'.mp h_none
      have h_nd' : (w.setInput in2 15).getNode nodeId = some nd := by rwa [h_getNode]
      rw [World.updateNode_getNode_eq _ _ _ _ h_nd', World.updateNode_getNode_eq _ _ _ _ h_nd]
  · rw [World.updateNode_getNode_ne _ _ _ _ (Ne.symm h_eq),
      setInput_getNode_ne' w in2 nid h_ne,
      ← World.updateNode_getNode_ne w nodeId nid f (Ne.symm h_eq)]

/-- `onScheduledTick` gives the same outputLog when `getNode` and `getInputSignal`
agree and `notifyOutputs` gives the same outputLog after `updateNode`. -/
theorem onScheduledTick_outputLog_congr_except (w₁ w₂ : World) (nodeId : Nat)
    (h_getNode : w₁.getNode nodeId = w₂.getNode nodeId)
    (h_gis : w₁.getInputSignal nodeId = w₂.getInputSignal nodeId)
    (h_log : w₁.outputLog = w₂.outputLog)
    (h_notify_rep : (w₁.updateNode nodeId
        (fun nd' => { nd' with sigLevel := if w₁.getInputSignal nodeId > 0 then 15 else 0 })
        |>.notifyOutputs nodeId).outputLog =
        (w₂.updateNode nodeId
        (fun nd' => { nd' with sigLevel := if w₂.getInputSignal nodeId > 0 then 15 else 0 })
        |>.notifyOutputs nodeId).outputLog)
    (h_notify_obs : (w₁.updateNode nodeId
        (fun nd' => { nd' with sigLevel := 15 })
        |>.notifyOutputs nodeId).outputLog =
        (w₂.updateNode nodeId
        (fun nd' => { nd' with sigLevel := 15 })
        |>.notifyOutputs nodeId).outputLog) :
    (w₁.onScheduledTick nodeId).outputLog = (w₂.onScheduledTick nodeId).outputLog := by
  dsimp [World.onScheduledTick]
  rw [h_getNode]
  cases h : w₂.getNode nodeId with
  | none => dsimp; exact h_log
  | some nd =>
    dsimp
    cases nd.kind with
    | repeater d p => simpa [h_gis] using h_notify_rep
    | observer => exact h_notify_obs
    | _ => exact h_log

/-- `setInput in2 15` and `onScheduledTick id` commute for outputLog. -/
theorem setInput_onScheduledTick_comm_outputLog (w : World) (in2 nodeId : Nat)
    (h_id_ne : nodeId ≠ in2)
    (h_sep : ∀ nd, w.getNode nodeId = some nd → in2 ∉ nd.inputs)
    (h_sep_out : ∀ nd, w.getNode nodeId = some nd →
        ∀ out_id ∈ nd.outputs, ∀ nd_out, w.getNode out_id = some nd_out → in2 ∉ nd_out.inputs)
    (h_outputs_ne : ∀ nd, w.getNode nodeId = some nd → ∀ out_id ∈ nd.outputs, out_id ≠ in2)
    (h_no_output : ∀ nd, w.getNode in2 = some nd → ∀ out_id ∈ nd.outputs,
        ∀ nd_out, w.getNode out_id = some nd_out → ∀ name, nd_out.kind ≠ .output name) :
    ((w.setInput in2 15).onScheduledTick nodeId).outputLog =
    ((w.onScheduledTick nodeId).setInput in2 15).outputLog := by
  -- RHS: setInput doesn't add to outputLog after onScheduledTick
  have h_rhs : ((w.onScheduledTick nodeId).setInput in2 15).outputLog = (w.onScheduledTick nodeId).outputLog := by
    apply setInput_outputLog_eq
    intro nd' h_nd' out_id h_mem nd_out h_nd_out name hk
    obtain ⟨nd₀, h_nd₀, hk'⟩ := World.onScheduledTick_kind_preserved w nodeId in2 nd' h_nd'
    have h_outs : nd'.outputs = nd₀.outputs := by
      obtain ⟨nd₀', h_nd₀', _, ho⟩ := World.onScheduledTick_inputs_preserved w nodeId in2 nd' h_nd'
      have : nd₀' = nd₀ := by apply Option.some_inj.mp; rw [← h_nd₀', h_nd₀]
      rwa [← this]
    rw [h_outs] at h_mem
    obtain ⟨nd₁, h_nd₁, hk''⟩ := World.onScheduledTick_kind_preserved w nodeId out_id nd_out h_nd_out
    rw [hk''] at hk
    exact h_no_output nd₀ h_nd₀ out_id h_mem nd₁ h_nd₁ name hk
  -- LHS: onScheduledTick gives same outputLog in w.setInput in2 15 and w
  have h_lhs : ((w.setInput in2 15).onScheduledTick nodeId).outputLog = (w.onScheduledTick nodeId).outputLog := by
    have h_gis : (w.setInput in2 15).getInputSignal nodeId = w.getInputSignal nodeId :=
      setInput_getInputSignal_ne w in2 nodeId 15 h_sep
    have h_getNode : (w.setInput in2 15).getNode nodeId = w.getNode nodeId := by
      have h₁ : (w.setInput in2 15) = (w.updateNode in2 (fun nd => { nd with sigLevel := 15 })).notifyOutputs in2 := rfl
      rw [h₁, World.notifyOutputs_getNode]
      exact World.updateNode_getNode_ne w in2 nodeId _ (Ne.symm h_id_ne)
    have h_log₀ : (w.setInput in2 15).outputLog = w.outputLog := setInput_outputLog_eq w in2 h_no_output
    have h_nodes_except_update := updateNode_getNode_congr_except w in2 nodeId h_getNode
    apply onScheduledTick_outputLog_congr_except _ _ nodeId h_getNode h_gis h_log₀
    · -- h_notify_rep
      rw [h_gis]
      apply notifyOutputs_outputLog_congr_except' _ _ nodeId in2 h_id_ne
        (h_nodes_except_update _)
        (by exact h_log₀)
      · intro nd h_nd out_id h_mem
        have h_ne_none : (w.setInput in2 15).getNode nodeId ≠ none := by
          intro h
          have h₁ : ((w.setInput in2 15).updateNode nodeId
            (fun nd' => { nd' with sigLevel := if w.getInputSignal nodeId > 0 then 15 else 0 })).getNode nodeId = none :=
            World.updateNode_getNode_none _ _ _ h
          rw [h₁] at h_nd; injection h_nd
        obtain ⟨nd₀, h_nd₀⟩ := Option.ne_none_iff_exists'.mp h_ne_none
        have h_nd₀' : w.getNode nodeId = some nd₀ := Eq.trans h_getNode.symm h_nd₀
        have h₁ := World.updateNode_getNode_eq (w.setInput in2 15) nodeId
          (fun nd' => { nd' with sigLevel := if w.getInputSignal nodeId > 0 then 15 else 0 })
          nd₀ h_nd₀
        rw [h₁] at h_nd; injection h_nd with h; subst h
        simp at h_mem
        exact h_outputs_ne nd₀ h_nd₀' out_id h_mem
      · intro nd h_nd out_id h_mem nd_out h_nd_out
        have h_ne_none : (w.setInput in2 15).getNode nodeId ≠ none := by
          intro h
          have h₁ : ((w.setInput in2 15).updateNode nodeId
            (fun nd' => { nd' with sigLevel := if w.getInputSignal nodeId > 0 then 15 else 0 })).getNode nodeId = none :=
            World.updateNode_getNode_none _ _ _ h
          rw [h₁] at h_nd; injection h_nd
        obtain ⟨nd₀, h_nd₀⟩ := Option.ne_none_iff_exists'.mp h_ne_none
        have h_nd₀' : w.getNode nodeId = some nd₀ := Eq.trans h_getNode.symm h_nd₀
        have h₁ := World.updateNode_getNode_eq (w.setInput in2 15) nodeId
          (fun nd' => { nd' with sigLevel := if w.getInputSignal nodeId > 0 then 15 else 0 })
          nd₀ h_nd₀
        rw [h₁] at h_nd; injection h_nd with h; subst h
        simp at h_mem
        by_cases h_eq : out_id = nodeId
        · have h_nd₀'' : w.getNode out_id = some nd₀ := by rwa [h_eq]
          have h_nd_out_eq : nd_out = { nd₀ with sigLevel := if w.getInputSignal nodeId > 0 then 15 else 0 } := by
            have h₂ := World.updateNode_getNode_eq (w.setInput in2 15) nodeId
              (fun nd' => { nd' with sigLevel := if w.getInputSignal nodeId > 0 then 15 else 0 }) nd₀ h_nd₀
            rw [h_eq] at h_nd_out
            injection Eq.trans h₂.symm h_nd_out with h
            exact Eq.symm h
          rw [h_nd_out_eq]; simp
          exact h_sep_out nd₀ h_nd₀' out_id h_mem nd₀ h_nd₀''
        · exact h_sep_out nd₀ h_nd₀' out_id h_mem nd_out (by
            have h₂ := World.updateNode_getNode_ne (w.setInput in2 15) nodeId out_id
              (fun nd' => { nd' with sigLevel := if w.getInputSignal nodeId > 0 then 15 else 0 }) (Ne.symm h_eq)
            rw [h₂] at h_nd_out
            rwa [setInput_getNode_ne' w in2 out_id (h_outputs_ne nd₀ h_nd₀' out_id h_mem)] at h_nd_out)
    · -- h_notify_obs
      apply notifyOutputs_outputLog_congr_except' _ _ nodeId in2 h_id_ne
        (h_nodes_except_update _)
        (by exact h_log₀)
      · intro nd h_nd out_id h_mem
        have h_ne_none : (w.setInput in2 15).getNode nodeId ≠ none := by
          intro h
          have h₁ : ((w.setInput in2 15).updateNode nodeId
            (fun nd' => { nd' with sigLevel := 15 })).getNode nodeId = none :=
            World.updateNode_getNode_none _ _ _ h
          rw [h₁] at h_nd; injection h_nd
        obtain ⟨nd₀, h_nd₀⟩ := Option.ne_none_iff_exists'.mp h_ne_none
        have h_nd₀' : w.getNode nodeId = some nd₀ := Eq.trans h_getNode.symm h_nd₀
        have h₁ := World.updateNode_getNode_eq (w.setInput in2 15) nodeId
          (fun nd' => { nd' with sigLevel := 15 }) nd₀ h_nd₀
        rw [h₁] at h_nd; injection h_nd with h; subst h
        simp at h_mem
        exact h_outputs_ne nd₀ h_nd₀' out_id h_mem
      · intro nd h_nd out_id h_mem nd_out h_nd_out
        have h_ne_none : (w.setInput in2 15).getNode nodeId ≠ none := by
          intro h
          have h₁ : ((w.setInput in2 15).updateNode nodeId
            (fun nd' => { nd' with sigLevel := 15 })).getNode nodeId = none :=
            World.updateNode_getNode_none _ _ _ h
          rw [h₁] at h_nd; injection h_nd
        obtain ⟨nd₀, h_nd₀⟩ := Option.ne_none_iff_exists'.mp h_ne_none
        have h_nd₀' : w.getNode nodeId = some nd₀ := Eq.trans h_getNode.symm h_nd₀
        have h₁ := World.updateNode_getNode_eq (w.setInput in2 15) nodeId
          (fun nd' => { nd' with sigLevel := 15 }) nd₀ h_nd₀
        rw [h₁] at h_nd; injection h_nd with h; subst h
        simp at h_mem
        by_cases h_eq : out_id = nodeId
        · have h_nd₀'' : w.getNode out_id = some nd₀ := by rwa [h_eq]
          have h_nd_out_eq : nd_out = { nd₀ with sigLevel := 15 } := by
            have h₂ := World.updateNode_getNode_eq (w.setInput in2 15) nodeId
              (fun nd' => { nd' with sigLevel := 15 }) nd₀ h_nd₀
            rw [h_eq] at h_nd_out
            injection Eq.trans h₂.symm h_nd_out with h
            exact Eq.symm h
          rw [h_nd_out_eq]; simp
          exact h_sep_out nd₀ h_nd₀' out_id h_mem nd₀ h_nd₀''
        · exact h_sep_out nd₀ h_nd₀' out_id h_mem nd_out (by
            have h₂ := World.updateNode_getNode_ne (w.setInput in2 15) nodeId out_id
              (fun nd' => { nd' with sigLevel := 15 }) (Ne.symm h_eq)
            rw [h₂] at h_nd_out
            rwa [setInput_getNode_ne' w in2 out_id (h_outputs_ne nd₀ h_nd₀' out_id h_mem)] at h_nd_out)
  rw [h_lhs, h_rhs]
