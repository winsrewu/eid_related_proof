import BasicProofs.PrefixChain.Part11


open BasicRedstoneSim

/-- `setInput in2 15` commutes with `stepUntilNextTick` for outputLog. -/
theorem setInput_stepUntilNextTick_comm_outputLog (w : World) (in2 : Nat)
    (h_no_target : ∀ ev ∈ w.events, ev.targetTick = w.tick → ev.nodeId ≠ in2)
    (h_sep : ∀ nid nd, w.getNode nid = some nd →
        (∃ ev ∈ w.events, ev.targetTick = w.tick ∧ ev.nodeId = nid) → in2 ∉ nd.inputs)
    (h_sep_out : ∀ nid nd, w.getNode nid = some nd →
        (∃ ev ∈ w.events, ev.targetTick = w.tick ∧ ev.nodeId = nid) →
        ∀ out_id ∈ nd.outputs, ∀ nd_out, w.getNode out_id = some nd_out → in2 ∉ nd_out.inputs)
    (h_outputs_ne : ∀ nid nd, w.getNode nid = some nd →
        (∃ ev ∈ w.events, ev.targetTick = w.tick ∧ ev.nodeId = nid) →
        ∀ out_id ∈ nd.outputs, out_id ≠ in2)
    (h_no_output : ∀ nd, w.getNode in2 = some nd → ∀ out_id ∈ nd.outputs,
        ∀ nd_out, w.getNode out_id = some nd_out → ∀ name, nd_out.kind ≠ .output name)
    (h_delay : ∀ nid nd, w.getNode nid = some nd → ∀ d p,
        nd.kind = .repeater d p → d ≥ 2) :
    ((w.setInput in2 15).stepUntilNextTick).outputLog =
    ((w.stepUntilNextTick).setInput in2 15).outputLog := by
  induction w using World.stepUntilNextTick.induct with
  | case1 w h_step =>
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
    have h₁ : (w.setInput in2 15).outputLog = w.outputLog := setInput_outputLog_eq w in2 h_no_output
    have h₂ : ({ w with tick := w.tick + 1 }.setInput in2 15).outputLog = w.outputLog := by
      have h₃ : ({ w with tick := w.tick + 1 }.setInput in2 15).outputLog =
          { w with tick := w.tick + 1 }.outputLog := by
        apply setInput_outputLog_eq
        intro nd h_nd out_id h_mem nd_out h_nd_out name hk
        have h_nd' : w.getNode in2 = some nd := by dsimp [World.getNode] at h_nd ⊢; exact h_nd
        have h_nd_out' : w.getNode out_id = some nd_out := by dsimp [World.getNode] at h_nd_out ⊢; exact h_nd_out
        exact h_no_output nd h_nd' out_id h_mem nd_out h_nd_out' name hk
      rw [h₃]
    rw [h₁, h₂]
  | case2 w w' h_step ih =>
    have h_sunt : w.stepUntilNextTick = w'.stepUntilNextTick := by
      rw [World.stepUntilNextTick, h_step]
    rw [h_sunt]
    dsimp [World.step] at h_step
    cases h_pop : w.popNextEvent with
    | none => simp [h_pop] at h_step
    | some p =>
      rcases p with ⟨ev, w_pop⟩
      -- Save w' and h_step before simp/subst modify them
      have h_w'_save : World := w'
      have h_step_save : w.step = some w' := h_step
      simp [h_pop] at h_step
      subst h_step
      have h_ev_tick : ev.targetTick = w.tick := popNextEvent_at_tick w ev w_pop h_pop
      have h_filter_set : (w.setInput in2 15).events.filter
          (fun e => e.targetTick == (w.setInput in2 15).tick) =
          w.events.filter (fun e => e.targetTick == w.tick) := by
        rw [World.setInput_tick]
        dsimp [World.setInput, World.notifyOutputs]
        set w_upd := w.updateNode in2 (fun nd => { nd with sigLevel := 15 })
        have h_ev' : w_upd.events = w.events := by simp [w_upd]
        have h_tick' : w_upd.tick = w.tick := by simp [w_upd]
        cases h_gn : w_upd.getNode in2 with
        | none => simp [h_ev']
        | some nd =>
          simp only []
          have h_delay' : ∀ nid nd, w_upd.getNode nid = some nd → ∀ d p,
              nd.kind = .repeater d p → d ≥ 2 := by
            intro nid nd' h_nd' d p h_kind
            obtain ⟨nd₀, h_nd₀, h_kind_eq⟩ := World.updateNode_getNode_kind w in2 nid
              (fun nd => { nd with sigLevel := 15 }) (fun nd => rfl) nd' h_nd'
            rw [← h_kind_eq] at h_kind
            exact h_delay nid nd₀ h_nd₀ d p h_kind
          obtain ⟨new_ev, h_app, h_fut⟩ := foldl_onNeighborUpdate_events_append nd.outputs w_upd h_delay'
          rw [h_app, h_ev', List.filter_append]
          have h_empty : new_ev.filter (fun e => e.targetTick == w.tick) = [] := by
            apply List.filter_eq_nil_iff.mpr
            intro e he; have h_gt := h_fut e he; rw [h_tick'] at h_gt; simp; omega
          simp [h_empty]
      obtain ⟨w_pop', h_pop'⟩ := popNextEvent_same_of_same_filter w (w.setInput in2 15)
        (by rw [World.setInput_tick]) h_filter_set.symm ev w_pop h_pop
      have h_sunt' : (w.setInput in2 15).stepUntilNextTick =
          (w_pop'.onScheduledTick ev.nodeId).stepUntilNextTick := by
        rw [World.stepUntilNextTick]
        dsimp [World.step]
        rw [h_pop']
      rw [h_sunt']
      have h_pop'_nodes : w_pop'.nodes = (w_pop.setInput in2 15).nodes := by
        have h₁ : w_pop'.nodes = (w.setInput in2 15).nodes :=
          World.popNextEvent_nodes (w.setInput in2 15) ev w_pop' h_pop'
        have h₂ : w_pop.nodes = w.nodes := World.popNextEvent_nodes w ev w_pop h_pop
        rw [h₁]; dsimp [World.setInput]
        rw [World.notifyOutputs_nodes, World.notifyOutputs_nodes]
        dsimp [World.updateNode]; rw [h₂]
      have h_pop'_tick : w_pop'.tick = (w_pop.setInput in2 15).tick := by
        rw [World.popNextEvent_tick (w.setInput in2 15) ev w_pop' h_pop',
            World.setInput_tick, ← World.popNextEvent_tick w ev w_pop h_pop,
            World.setInput_tick]
      have h_pop'_log : w_pop'.outputLog = (w_pop.setInput in2 15).outputLog := by
        rw [World.popNextEvent_outputLog (w.setInput in2 15) ev w_pop' h_pop']
        dsimp [World.setInput]
        apply World.notifyOutputs_outputLog_congr
        · dsimp [World.updateNode]; rw [World.popNextEvent_nodes w ev w_pop h_pop]
        · dsimp [World.updateNode]
          rw [World.popNextEvent_outputLog w ev w_pop h_pop]
      have h_pop'_nextId : w_pop'.nextId = (w_pop.setInput in2 15).nextId := by
        rw [World.popNextEvent_nextId (w.setInput in2 15) ev w_pop' h_pop',
            World.setInput_nextId, ← World.popNextEvent_nextId w ev w_pop h_pop,
            World.setInput_nextId]
      have h_congr := World.onScheduledTick_congr_fields w_pop' (w_pop.setInput in2 15) ev.nodeId
        h_pop'_nodes h_pop'_tick h_pop'_log h_pop'_nextId
      have h_pop_nodes : w_pop.nodes = w.nodes := World.popNextEvent_nodes w ev w_pop h_pop
      have h_id_ne : ev.nodeId ≠ in2 := by
        intro h_eq
        obtain ⟨_, _, _, _, h_mem, _⟩ := World.popNextEvent_eraseIdx w ev w_pop h_pop
        exact h_no_target ev h_mem h_ev_tick h_eq
      have h_sep' : ∀ nd, w_pop.getNode ev.nodeId = some nd → in2 ∉ nd.inputs := by
        intro nd h_nd
        apply h_sep ev.nodeId nd _ ⟨ev, by
          obtain ⟨_, _, _, _, h_mem, _⟩ := World.popNextEvent_eraseIdx w ev w_pop h_pop
          exact h_mem, h_ev_tick, rfl⟩
        have h_getNode_eq : w.getNode ev.nodeId = w_pop.getNode ev.nodeId := by
          rw [World.getNode, World.getNode, h_pop_nodes]
        rwa [h_getNode_eq]
      have h_sep_out' : ∀ nd, w_pop.getNode ev.nodeId = some nd →
          ∀ out_id ∈ nd.outputs, ∀ nd_out, w_pop.getNode out_id = some nd_out → in2 ∉ nd_out.inputs := by
        intro nd h_nd out_id h_mem nd_out h_nd_out
        exact h_sep_out ev.nodeId nd (by
          have h_getNode_eq : w.getNode ev.nodeId = w_pop.getNode ev.nodeId := by
            rw [World.getNode, World.getNode, h_pop_nodes]
          rwa [h_getNode_eq]) ⟨ev, by
          obtain ⟨_, _, _, _, h_mem, _⟩ := World.popNextEvent_eraseIdx w ev w_pop h_pop
          exact h_mem, h_ev_tick, rfl⟩ out_id h_mem nd_out (by
          have h_getNode_eq : w.getNode out_id = w_pop.getNode out_id := by
            rw [World.getNode, World.getNode, h_pop_nodes]
          rwa [h_getNode_eq])
      have h_outputs_ne' : ∀ nd, w_pop.getNode ev.nodeId = some nd →
          ∀ out_id ∈ nd.outputs, out_id ≠ in2 := by
        intro nd h_nd out_id h_mem
        exact h_outputs_ne ev.nodeId nd (by
          have h_getNode_eq : w.getNode ev.nodeId = w_pop.getNode ev.nodeId := by
            rw [World.getNode, World.getNode, h_pop_nodes]
          rwa [h_getNode_eq]) ⟨ev, by
          obtain ⟨_, _, _, _, h_mem, _⟩ := World.popNextEvent_eraseIdx w ev w_pop h_pop
          exact h_mem, h_ev_tick, rfl⟩ out_id h_mem
      have h_no_output' : ∀ nd, w_pop.getNode in2 = some nd → ∀ out_id ∈ nd.outputs,
          ∀ nd_out, w_pop.getNode out_id = some nd_out → ∀ name, nd_out.kind ≠ .output name := by
        intro nd h_nd out_id h_mem nd_out h_nd_out name hk
        have h_nd' : w.getNode in2 = some nd := by
          have h_getNode_eq : w.getNode in2 = w_pop.getNode in2 := by
            rw [World.getNode, World.getNode, h_pop_nodes]
          rwa [h_getNode_eq]
        have h_nd_out' : w.getNode out_id = some nd_out := by
          have h_getNode_eq : w.getNode out_id = w_pop.getNode out_id := by
            rw [World.getNode, World.getNode, h_pop_nodes]
          rwa [h_getNode_eq]
        exact h_no_output nd h_nd' out_id h_mem nd_out h_nd_out' name hk
      have h_comm := setInput_onScheduledTick_comm_outputLog w_pop in2 ev.nodeId
        h_id_ne h_sep' h_sep_out' h_outputs_ne' h_no_output'
      have h_log'' : (w_pop'.onScheduledTick ev.nodeId).outputLog =
          (w_pop.onScheduledTick ev.nodeId |>.setInput in2 15).outputLog := by
        rw [h_congr.2.2.1, h_comm]
      have h_tick'' : (w_pop'.onScheduledTick ev.nodeId).tick =
          (w_pop.onScheduledTick ev.nodeId |>.setInput in2 15).tick := by
        rw [h_congr.2.1, World.onScheduledTick_tick, World.setInput_tick,
            World.setInput_tick, ← World.onScheduledTick_tick]
      have h_nodes'' : (w_pop'.onScheduledTick ev.nodeId).nodes =
          (w_pop.onScheduledTick ev.nodeId |>.setInput in2 15).nodes := by
        rw [h_congr.1, setInput_onScheduledTick_comm_nodes w_pop in2 ev.nodeId h_id_ne h_sep']
      have h_nextId'' : (w_pop'.onScheduledTick ev.nodeId).nextId =
          (w_pop.onScheduledTick ev.nodeId |>.setInput in2 15).nextId := by
        rw [h_congr.2.2.2.1, World.onScheduledTick_nextId, World.setInput_nextId,
            World.setInput_nextId, ← World.onScheduledTick_nextId]
      have h_filter'' : (w_pop'.onScheduledTick ev.nodeId).events.filter
          (fun e => e.targetTick == (w_pop'.onScheduledTick ev.nodeId).tick) =
          (w_pop.onScheduledTick ev.nodeId |>.setInput in2 15).events.filter
          (fun e => e.targetTick == (w_pop.onScheduledTick ev.nodeId |>.setInput in2 15).tick) := by
        rw [h_tick'']
        have h_pop_filter := popNextEvent_filter_eq w (w.setInput in2 15)
          (by rw [World.setInput_tick]) h_filter_set.symm ev w_pop w_pop' h_pop h_pop'
        have h_delay_pop' : ∀ nid nd, w_pop'.getNode nid = some nd → ∀ d p,
            nd.kind = .repeater d p → d ≥ 2 := by
          intro nid nd h_nd d p h_kind
          have h_nd' : (w_pop.setInput in2 15).getNode nid = some nd := by
            dsimp [World.getNode] at h_nd ⊢; rw [← h_pop'_nodes]; exact h_nd
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
        have h_delay_pop : ∀ nid nd, w_pop.getNode nid = some nd → ∀ d p,
            nd.kind = .repeater d p → d ≥ 2 := by
          intro nid nd h_nd
          have : w.getNode nid = some nd := by
            dsimp [World.getNode] at h_nd ⊢; rw [← h_pop_nodes]; exact h_nd
          exact h_delay nid nd this
        obtain ⟨new₂, h_app₂, h_fut₂⟩ := World.onScheduledTick_events_append w_pop ev.nodeId h_delay_pop
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
            intro nid nd' h_nd' d p h_kind
            obtain ⟨nd₀, h_nd₀, h_kind_eq⟩ := World.updateNode_getNode_kind w_st in2 nid
              (fun nd => { nd with sigLevel := 15 }) (fun nd => rfl) nd' h_nd'
            rw [← h_kind_eq] at h_kind
            obtain ⟨nd₁, h_nd₁, h_kind_eq'⟩ := World.onScheduledTick_kind_preserved w_pop ev.nodeId nid nd₀ h_nd₀
            rw [h_kind_eq'] at h_kind
            exact h_delay_pop nid nd₁ h_nd₁ d p h_kind
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
      have h_delay_sunt : ∀ nid nd, (w_pop'.onScheduledTick ev.nodeId).getNode nid = some nd → ∀ d p,
          nd.kind = .repeater d p → d ≥ 2 := by
        intro nid nd h_nd d p h_kind
        obtain ⟨nd₀, h_nd₀, h_kind_eq⟩ := World.onScheduledTick_kind_preserved w_pop' ev.nodeId nid nd h_nd
        have h_kind₀ : nd₀.kind = .repeater d p := Eq.trans h_kind_eq.symm h_kind
        have h_nd₀' : w_pop'.getNode nid = some nd₀ := h_nd₀
        have h_delay_pop' : ∀ nid nd, w_pop'.getNode nid = some nd → ∀ d p,
            nd.kind = .repeater d p → d ≥ 2 := by
          intro nid nd h_nd d p h_kind
          have h_nd' : (w_pop.setInput in2 15).getNode nid = some nd := by
            dsimp [World.getNode] at h_nd ⊢; rw [← h_pop'_nodes]; exact h_nd
          obtain ⟨nd₀, h_nd₀, h_kind_eq⟩ := World.setInput_kind_preserved w_pop in2 15 nid nd h_nd'
          have h_getNode_eq : w_pop.getNode nid = w.getNode nid := by
            rw [World.getNode, World.getNode, h_pop_nodes]
          rw [h_getNode_eq] at h_nd₀
          have h_kind₀ : nd₀.kind = .repeater d p := by rw [← h_kind_eq]; exact h_kind
          exact h_delay nid nd₀ h_nd₀ d p h_kind₀
        exact h_delay_pop' nid nd₀ h_nd₀' d p h_kind₀
      have h_sunt_eq := stepUntilNextTick_outputLog_congr
        (w_pop'.onScheduledTick ev.nodeId)
        (w_pop.onScheduledTick ev.nodeId |>.setInput in2 15)
        h_nodes'' h_tick'' h_log'' h_nextId'' h_filter'' h_delay_sunt
      have h_ih := ih
        (by -- h_no_target for w'
          intro ev' h_ev' h_tick'
          obtain ⟨new_ev, h_app, h_fut⟩ := World.onScheduledTick_events_append w_pop ev.nodeId
            (by intro nid nd h_nd d p h_kind
                have : w.getNode nid = some nd := by
                  have h_getNode_eq : w_pop.getNode nid = w.getNode nid := by
                    rw [World.getNode, World.getNode, h_pop_nodes]
                  have : w_pop.getNode nid = some nd := h_nd
                  rwa [← h_getNode_eq]
                exact h_delay nid nd this d p h_kind)
          rw [h_app] at h_ev'
          simp [List.mem_append] at h_ev'
          cases h_ev' with
          | inl h_old =>
            obtain ⟨idx, h_idx, h_erase, h_tick_ev, h_mem, h_get⟩ := World.popNextEvent_eraseIdx w ev w_pop h_pop
            rw [h_erase] at h_old
            have h_ev'_in_w : ev' ∈ w.events := List.mem_of_mem_eraseIdx h_old
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
            (by intro nid nd h_nd d p h_kind
                have : w.getNode nid = some nd := by
                  have h_getNode_eq : w_pop.getNode nid = w.getNode nid := by
                    rw [World.getNode, World.getNode, h_pop_nodes]
                  have : w_pop.getNode nid = some nd := h_nd
                  rwa [← h_getNode_eq]
                exact h_delay nid nd this d p h_kind)
          rw [h_app] at h_ev'
          simp [List.mem_append] at h_ev'
          cases h_ev' with
          | inl h_old =>
            obtain ⟨idx, h_idx, h_erase, h_tick_ev, h_mem, h_get⟩ := World.popNextEvent_eraseIdx w ev w_pop h_pop
            rw [h_erase] at h_old
            have h_ev'_in_w : ev' ∈ w.events := List.mem_of_mem_eraseIdx h_old
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
              have h_nd₀_eq : nd₀' = nd₀ := by apply Option.some_inj.mp; rw [← h_nd₀', h_nd₀]
              rw [← h_nd₀_eq]; exact h_inputs_eq
            rw [h_inputs]
            exact h_sep nid nd₀ h_nd₀' ⟨ev', h_ev'_in_w, h_ev'_tick, h_node⟩
          | inr h_new =>
            have h_gt := h_fut ev' h_new
            rw [World.onScheduledTick_tick, World.popNextEvent_tick w ev w_pop h_pop] at h_tick'
            rw [World.popNextEvent_tick w ev w_pop h_pop] at h_gt
            omega)
        (by -- h_sep_out for w'
          intro nid nd h_nd h_exists out_id h_mem_out nd_out h_nd_out
          obtain ⟨ev', h_ev', h_tick', h_node⟩ := h_exists
          obtain ⟨new_ev, h_app, h_fut⟩ := World.onScheduledTick_events_append w_pop ev.nodeId
            (by intro nid nd h_nd d p h_kind
                have : w.getNode nid = some nd := by
                  have h_ge : w_pop.getNode nid = w.getNode nid := by rw [World.getNode, World.getNode, h_pop_nodes]
                  rwa [← h_ge]
                exact h_delay nid nd this d p h_kind)
          rw [h_app] at h_ev'; simp [List.mem_append] at h_ev'
          cases h_ev' with
          | inl h_old =>
            obtain ⟨idx, h_idx, h_erase, h_tick_ev, h_mem, h_get⟩ := World.popNextEvent_eraseIdx w ev w_pop h_pop
            rw [h_erase] at h_old
            have h_ev'_in_w : ev' ∈ w.events := List.mem_of_mem_eraseIdx h_old
            have h_ev'_tick : ev'.targetTick = w.tick := by
              rw [World.onScheduledTick_tick, World.popNextEvent_tick w ev w_pop h_pop] at h_tick'; exact h_tick'
            obtain ⟨nd₀, h_nd₀, _⟩ := World.onScheduledTick_kind_preserved w_pop ev.nodeId nid nd h_nd
            have h_nd₀' : w.getNode nid = some nd₀ := by
              have h_ge : w_pop.getNode nid = w.getNode nid := by rw [World.getNode, World.getNode, h_pop_nodes]
              rwa [← h_ge]
            have h_outputs : nd.outputs = nd₀.outputs := by
              obtain ⟨nd₀', h_nd₀', _, ho⟩ := World.onScheduledTick_inputs_preserved w_pop ev.nodeId nid nd h_nd
              have : nd₀' = nd₀ := by apply Option.some_inj.mp; rw [← h_nd₀', h_nd₀]
              rw [← this]; exact ho
            rw [h_outputs] at h_mem_out
            obtain ⟨nd_out₀, h_nd_out₀, _⟩ := World.onScheduledTick_kind_preserved w_pop ev.nodeId out_id nd_out h_nd_out
            have h_nd_out₀' : w.getNode out_id = some nd_out₀ := by
              have h_ge : w_pop.getNode out_id = w.getNode out_id := by rw [World.getNode, World.getNode, h_pop_nodes]
              rwa [← h_ge]
            have h_inputs_out : nd_out.inputs = nd_out₀.inputs := by
              obtain ⟨nd₀'', h_nd₀'', hi, _⟩ := World.onScheduledTick_inputs_preserved w_pop ev.nodeId out_id nd_out h_nd_out
              have : nd₀'' = nd_out₀ := by apply Option.some_inj.mp; rw [← h_nd₀'', h_nd_out₀]
              rw [← this]; exact hi
            rw [h_inputs_out]
            exact h_sep_out nid nd₀ h_nd₀' ⟨ev', h_ev'_in_w, h_ev'_tick, h_node⟩ out_id h_mem_out nd_out₀ h_nd_out₀'
          | inr h_new =>
            have h_gt := h_fut ev' h_new
            rw [World.onScheduledTick_tick, World.popNextEvent_tick w ev w_pop h_pop] at h_tick'
            rw [World.popNextEvent_tick w ev w_pop h_pop] at h_gt; omega)
        (by -- h_outputs_ne for w'
          intro nid nd h_nd h_exists out_id h_mem_out
          obtain ⟨ev', h_ev', h_tick', h_node⟩ := h_exists
          obtain ⟨new_ev, h_app, h_fut⟩ := World.onScheduledTick_events_append w_pop ev.nodeId
            (by intro nid nd h_nd d p h_kind
                have : w.getNode nid = some nd := by
                  have h_ge : w_pop.getNode nid = w.getNode nid := by rw [World.getNode, World.getNode, h_pop_nodes]
                  rwa [← h_ge]
                exact h_delay nid nd this d p h_kind)
          rw [h_app] at h_ev'; simp [List.mem_append] at h_ev'
          cases h_ev' with
          | inl h_old =>
            obtain ⟨idx, h_idx, h_erase, h_tick_ev, h_mem, h_get⟩ := World.popNextEvent_eraseIdx w ev w_pop h_pop
            rw [h_erase] at h_old
            have h_ev'_in_w : ev' ∈ w.events := List.mem_of_mem_eraseIdx h_old
            have h_ev'_tick : ev'.targetTick = w.tick := by
              rw [World.onScheduledTick_tick, World.popNextEvent_tick w ev w_pop h_pop] at h_tick'; exact h_tick'
            obtain ⟨nd₀, h_nd₀, _⟩ := World.onScheduledTick_kind_preserved w_pop ev.nodeId nid nd h_nd
            have h_nd₀' : w.getNode nid = some nd₀ := by
              have h_ge : w_pop.getNode nid = w.getNode nid := by rw [World.getNode, World.getNode, h_pop_nodes]
              rwa [← h_ge]
            have h_outputs : nd.outputs = nd₀.outputs := by
              obtain ⟨nd₀', h_nd₀', _, ho⟩ := World.onScheduledTick_inputs_preserved w_pop ev.nodeId nid nd h_nd
              have : nd₀' = nd₀ := by apply Option.some_inj.mp; rw [← h_nd₀', h_nd₀]
              rw [← this]; exact ho
            rw [h_outputs] at h_mem_out
            exact h_outputs_ne nid nd₀ h_nd₀' ⟨ev', h_ev'_in_w, h_ev'_tick, h_node⟩ out_id h_mem_out
          | inr h_new =>
            have h_gt := h_fut ev' h_new
            rw [World.onScheduledTick_tick, World.popNextEvent_tick w ev w_pop h_pop] at h_tick'
            rw [World.popNextEvent_tick w ev w_pop h_pop] at h_gt; omega)
        (by -- h_no_output for w'
          intro nd h_nd out_id h_mem_out nd_out h_nd_out name hk
          obtain ⟨nd₀, h_nd₀, _⟩ := World.onScheduledTick_kind_preserved w_pop ev.nodeId in2 nd h_nd
          have h_nd₀' : w.getNode in2 = some nd₀ := by
            have h_ge : w_pop.getNode in2 = w.getNode in2 := by rw [World.getNode, World.getNode, h_pop_nodes]
            rwa [← h_ge]
          have h_outputs : nd.outputs = nd₀.outputs := by
            obtain ⟨nd₀', h_nd₀', _, ho⟩ := World.onScheduledTick_inputs_preserved w_pop ev.nodeId in2 nd h_nd
            have : nd₀' = nd₀ := by apply Option.some_inj.mp; rw [← h_nd₀', h_nd₀]
            rw [← this]; exact ho
          rw [h_outputs] at h_mem_out
          obtain ⟨nd_out₀, h_nd_out₀, hk_out⟩ := World.onScheduledTick_kind_preserved w_pop ev.nodeId out_id nd_out h_nd_out
          have h_nd_out₀' : w.getNode out_id = some nd_out₀ := by
            have h_ge : w_pop.getNode out_id = w.getNode out_id := by rw [World.getNode, World.getNode, h_pop_nodes]
            rwa [← h_ge]
          have h₁ := h_no_output nd₀ h_nd₀' out_id h_mem_out nd_out₀ h_nd_out₀' name
          apply h₁; rw [hk] at hk_out; exact hk_out.symm)
        (by -- h_delay for w'
          intro nid nd h_nd d p h_kind
          obtain ⟨nd₀, h_nd₀, hk_eq⟩ := World.onScheduledTick_kind_preserved w_pop ev.nodeId nid nd h_nd
          rw [hk_eq] at h_kind
          have h_nd₀' : w.getNode nid = some nd₀ := by
            have h_ge : w_pop.getNode nid = w.getNode nid := by rw [World.getNode, World.getNode, h_pop_nodes]
            rwa [← h_ge]
          exact h_delay nid nd₀ h_nd₀' d p h_kind)
      exact Eq.trans h_sunt_eq h_ih

/-- `onNeighborUpdate` appends an event list determined only by the tick and the node's kind:
    two worlds with the same tick and the same kind at `id` append the same list. -/
theorem onNeighborUpdate_events_congr (w₁ w₂ : World) (id : Nat)
    (h_tick : w₁.tick = w₂.tick)
    (h_kind : (w₁.getNode id).map (·.kind) = (w₂.getNode id).map (·.kind)) :
    ∃ X, (w₁.onNeighborUpdate id).events = w₁.events ++ X ∧
         (w₂.onNeighborUpdate id).events = w₂.events ++ X := by
  cases h₁ : w₁.getNode id with
  | none =>
    have h₂ : w₂.getNode id = none := by
      dsimp [Option.map] at h_kind
      rw [h₁] at h_kind
      cases h : w₂.getNode id <;> simp_all []
    refine ⟨[], ?_, ?_⟩ <;> simp [World.onNeighborUpdate, h₁, h₂]
  | some nd₁ =>
    have h_map : (w₂.getNode id).map (·.kind) = some nd₁.kind := by
      dsimp [Option.map] at h_kind
      rw [h₁] at h_kind
      exact h_kind.symm
    have h₂some : ∃ nd₂, w₂.getNode id = some nd₂ := by
      by_contra h_contra
      push Not at h_contra
      have h_none : (w₂.getNode id).map (·.kind) = none := by
        cases h : w₂.getNode id with
        | none => rfl
        | some nd₂ => exfalso; exact h_contra nd₂ h
      rw [h_none] at h_map
      cases h_map
    obtain ⟨nd₂, h₂⟩ := h₂some
    have h_kind_eq : nd₁.kind = nd₂.kind := by
      have := h_map
      rw [h₂] at this
      dsimp [Option.map] at this
      exact (Option.some.inj this).symm
    cases hk₁ : nd₁.kind with
    | input =>
      have hk₂ : nd₂.kind = .input := by rw [← h_kind_eq]; exact hk₁
      refine ⟨[], ?_, ?_⟩ <;> simp [World.onNeighborUpdate, h₁, h₂, hk₁, hk₂]
    | output name =>
      have hk₂ : nd₂.kind = .output name := by rw [← h_kind_eq]; exact hk₁
      refine ⟨[], ?_, ?_⟩ <;> simp [World.onNeighborUpdate, h₁, h₂, hk₁, hk₂, World.logOutput_events]
    | observer =>
      have hk₂ : nd₂.kind = .observer := by rw [← h_kind_eq]; exact hk₁
      refine ⟨[{ targetTick := w₁.tick + 2, priority := 0, nodeId := id }], ?_, ?_⟩
      · simp [World.onNeighborUpdate, h₁, hk₁, World.scheduleEvent_events]
      · simp [World.onNeighborUpdate, h₂, hk₂, World.scheduleEvent_events]; rw [← h_tick]
    | repeater d p =>
      have hk₂ : nd₂.kind = .repeater d p := by rw [← h_kind_eq]; exact hk₁
      refine ⟨[{ targetTick := w₁.tick + d, priority := p, nodeId := id }], ?_, ?_⟩
      · simp [World.onNeighborUpdate, h₁, hk₁, World.scheduleEvent_events]
      · simp [World.onNeighborUpdate, h₂, hk₂, World.scheduleEvent_events]; rw [← h_tick]

/-- A foldl of `onNeighborUpdate` appends an event list determined only by the tick and the
    kinds of the nodes in the list: two worlds with the same tick and same kinds along `l`
    append the same list. -/
theorem foldl_onNeighborUpdate_events_congr (l : List Nat) (w₁ w₂ : World)
    (h_tick : w₁.tick = w₂.tick)
    (h_kind : ∀ nid ∈ l, (w₁.getNode nid).map (·.kind) = (w₂.getNode nid).map (·.kind)) :
    ∃ X, (l.foldl (fun w' outId => w'.onNeighborUpdate outId) w₁).events = w₁.events ++ X ∧
         (l.foldl (fun w' outId => w'.onNeighborUpdate outId) w₂).events = w₂.events ++ X := by
  induction l generalizing w₁ w₂ with
  | nil => exact ⟨[], by simp, by simp⟩
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    obtain ⟨X₀, h₁₀, h₂₀⟩ := onNeighborUpdate_events_congr w₁ w₂ hd h_tick
      (h_kind hd (List.mem_cons.mpr (Or.inl rfl)))
    set w₁' := w₁.onNeighborUpdate hd
    set w₂' := w₂.onNeighborUpdate hd
    have h_tick' : w₁'.tick = w₂'.tick := by
      dsimp [w₁', w₂']; rw [World.onNeighborUpdate_tick, World.onNeighborUpdate_tick, h_tick]
    have h_kind' : ∀ nid ∈ tl, (w₁'.getNode nid).map (·.kind) = (w₂'.getNode nid).map (·.kind) := by
      intro nid h_mem
      dsimp [w₁', w₂']
      rw [World.onNeighborUpdate_getNode, World.onNeighborUpdate_getNode]
      exact h_kind nid (List.mem_cons.mpr (Or.inr h_mem))
    obtain ⟨Xtl, h₁tl, h₂tl⟩ := ih w₁' w₂' h_tick' h_kind'
    refine ⟨X₀ ++ Xtl, ?_, ?_⟩
    · rw [h₁tl, h₁₀]; simp [List.append_assoc]
    · rw [h₂tl, h₂₀]; simp [List.append_assoc]

/-- `onScheduledTick id` appends the same event list in two worlds with the same tick,
    the same node at `id`, and the same node kinds everywhere. -/
theorem onScheduledTick_events_congr (w₁ w₂ : World) (id : Nat)
    (h_tick : w₁.tick = w₂.tick)
    (h_node : w₁.getNode id = w₂.getNode id)
    (h_kinds : ∀ nid, (w₁.getNode nid).map (·.kind) = (w₂.getNode nid).map (·.kind)) :
    ∃ new, (w₁.onScheduledTick id).events = w₁.events ++ new ∧
           (w₂.onScheduledTick id).events = w₂.events ++ new := by
  cases h_nd : w₁.getNode id with
  | none =>
    have h_nd₂ : w₂.getNode id = none := by rw [← h_node]; exact h_nd
    refine ⟨[], ?_, ?_⟩ <;> simp [World.onScheduledTick, h_nd, h_nd₂]
  | some nd =>
    have h_nd₂ : w₂.getNode id = some nd := by rw [← h_node]; exact h_nd
    cases hk : nd.kind with
    | input =>
      refine ⟨[], ?_, ?_⟩ <;> simp [World.onScheduledTick, h_nd, h_nd₂, hk]
    | output name =>
      refine ⟨[], ?_, ?_⟩ <;> simp [World.onScheduledTick, h_nd, h_nd₂, hk]
    | observer =>
      set w₁' := w₁.updateNode id (fun nd' => { nd' with sigLevel := 15 })
      set w₂' := w₂.updateNode id (fun nd' => { nd' with sigLevel := 15 })
      have h_gn₁ : w₁'.getNode id = some { nd with sigLevel := 15 } := by
        dsimp [w₁']; exact World.updateNode_getNode_eq w₁ id _ nd h_nd
      have h_gn₂ : w₂'.getNode id = some { nd with sigLevel := 15 } := by
        dsimp [w₂']; exact World.updateNode_getNode_eq w₂ id _ nd h_nd₂
      have h_ev₁ : (w₁.onScheduledTick id).events =
          (nd.outputs.foldl (fun w' outId => w'.onNeighborUpdate outId) w₁').events := by
        simp [World.onScheduledTick, World.notifyOutputs, w₁', h_nd, hk, h_gn₁]
      have h_ev₂ : (w₂.onScheduledTick id).events =
          (nd.outputs.foldl (fun w' outId => w'.onNeighborUpdate outId) w₂').events := by
        simp [World.onScheduledTick, World.notifyOutputs, w₂', h_nd₂, hk, h_gn₂]
      have h_tick' : w₁'.tick = w₂'.tick := by
        dsimp [w₁', w₂', World.updateNode]; rw [h_tick]
      have h_kinds' : ∀ nid ∈ nd.outputs,
          (w₁'.getNode nid).map (·.kind) = (w₂'.getNode nid).map (·.kind) := by
        intro nid h_mem
        by_cases h_eq : nid = id
        · subst h_eq; rw [h_gn₁, h_gn₂]
        · have hn₁ : w₁'.getNode nid = w₁.getNode nid := by
            dsimp [w₁']; exact World.updateNode_getNode_ne w₁ id nid _ (Ne.symm h_eq)
          have hn₂ : w₂'.getNode nid = w₂.getNode nid := by
            dsimp [w₂']; exact World.updateNode_getNode_ne w₂ id nid _ (Ne.symm h_eq)
          rw [hn₁, hn₂]; exact h_kinds nid
      obtain ⟨X, h_X₁, h_X₂⟩ := foldl_onNeighborUpdate_events_congr nd.outputs w₁' w₂' h_tick' h_kinds'
      refine ⟨X, ?_, ?_⟩
      · rw [h_ev₁, h_X₁]; simp [w₁', World.updateNode]
      · rw [h_ev₂, h_X₂]; simp [w₂', World.updateNode]
    | repeater d p =>
      set w₁' := w₁.updateNode id
        (fun nd' => { nd' with sigLevel := if w₁.getInputSignal id > 0 then 15 else 0 })
      set w₂' := w₂.updateNode id
        (fun nd' => { nd' with sigLevel := if w₂.getInputSignal id > 0 then 15 else 0 })
      have h_gn₁ : w₁'.getNode id =
          some { nd with sigLevel := if w₁.getInputSignal id > 0 then 15 else 0 } := by
        dsimp [w₁']; exact World.updateNode_getNode_eq w₁ id _ nd h_nd
      have h_gn₂ : w₂'.getNode id =
          some { nd with sigLevel := if w₂.getInputSignal id > 0 then 15 else 0 } := by
        dsimp [w₂']; exact World.updateNode_getNode_eq w₂ id _ nd h_nd₂
      have h_ev₁ : (w₁.onScheduledTick id).events =
          (nd.outputs.foldl (fun w' outId => w'.onNeighborUpdate outId) w₁').events := by
        simp [World.onScheduledTick, World.notifyOutputs, w₁', h_nd, hk, h_gn₁]
      have h_ev₂ : (w₂.onScheduledTick id).events =
          (nd.outputs.foldl (fun w' outId => w'.onNeighborUpdate outId) w₂').events := by
        simp [World.onScheduledTick, World.notifyOutputs, w₂', h_nd₂, hk, h_gn₂]
      have h_tick' : w₁'.tick = w₂'.tick := by
        dsimp [w₁', w₂', World.updateNode]; rw [h_tick]
      have h_kinds' : ∀ nid ∈ nd.outputs,
          (w₁'.getNode nid).map (·.kind) = (w₂'.getNode nid).map (·.kind) := by
        intro nid h_mem
        by_cases h_eq : nid = id
        · subst h_eq; rw [h_gn₁, h_gn₂]; rfl
        · have hn₁ : w₁'.getNode nid = w₁.getNode nid := by
            dsimp [w₁']; exact World.updateNode_getNode_ne w₁ id nid _ (Ne.symm h_eq)
          have hn₂ : w₂'.getNode nid = w₂.getNode nid := by
            dsimp [w₂']; exact World.updateNode_getNode_ne w₂ id nid _ (Ne.symm h_eq)
          rw [hn₁, hn₂]; exact h_kinds nid
      obtain ⟨X, h_X₁, h_X₂⟩ := foldl_onNeighborUpdate_events_congr nd.outputs w₁' w₂' h_tick' h_kinds'
      refine ⟨X, ?_, ?_⟩
      · rw [h_ev₁, h_X₁]; simp [w₁', World.updateNode]
      · rw [h_ev₂, h_X₂]; simp [w₂', World.updateNode]

/-- At tick t₂, chain c2's input node `in2` has exactly one output (chain c2's
    observer node), so none of `in2`'s outputs is an output node. -/
theorem w_t2_in2_outputs_not_output (c1 c2 : ChainSpec) (t1 t2 pos' : Nat) :
    let in2 := (buildChain (buildChain World.empty "A" c1).2 "B" c2).1
    let w_t₂ := (List.range t2).foldl
      (simBody t1 t2 pos' (buildChain World.empty "A" c1).1
        (buildChain (buildChain World.empty "A" c1).2 "B" c2).1)
      (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
    ∀ nd, w_t₂.getNode in2 = some nd →
    ∀ out_id ∈ nd.outputs, ∀ nd_out, w_t₂.getNode out_id = some nd_out →
    ∀ name, nd_out.kind ≠ .output name := by
  intro in2 w_t₂ nd h_nd out_id h_mem nd_out h_nd_out name hk
  obtain ⟨nd₁, h_nd₁, _, h_outp₁⟩ := simFoldl_inputs_preserved
    (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
    t1 t2 pos' (buildChain World.empty "A" c1).1
    (buildChain (buildChain World.empty "A" c1).2 "B" c2).1 t2 in2 nd h_nd
  obtain ⟨nd_out₁, h_nd_out₁, h_kind₁⟩ := simFoldl_kind_preserved
    (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
    t1 t2 pos' (buildChain World.empty "A" c1).1
    (buildChain (buildChain World.empty "A" c1).2 "B" c2).1 t2 out_id nd_out h_nd_out
  rw [h_outp₁] at h_mem
  have h_in2_eq : in2 = (buildChain World.empty "A" c1).2.nextId := by
    dsimp [in2]; simp [buildChain, buildChainPre, World.addNode]
  -- chain c2's chainIds start with [in2, in2 + 1]
  obtain ⟨rest, h_chainIds⟩ : ∃ rest,
      (buildChainPre (buildChain World.empty "A" c1).2 "B" c2).2.2 =
      in2 :: (in2 + 1) :: rest := by
    dsimp (config := { zeta := true }) [buildChainPre, in2, buildChain]
    refine ⟨_, rfl⟩
  have h_nd₁' : (connectChain (buildChainPre (buildChain World.empty "A" c1).2 "B" c2).2.1
      (in2 :: (in2 + 1) :: rest)).getNode in2 = some nd₁ := by
    rw [← h_chainIds]; exact h_nd₁
  have h_ids_c1 : ∀ p ∈ (buildChain World.empty "A" c1).2.nodes,
      p.1 < (buildChain World.empty "A" c1).2.nextId :=
    buildChain_ids_lt_nextId World.empty "A" c1 (fun p hp => by simp [World.empty] at hp)
  have h_pre_in2 : (buildChainPre (buildChain World.empty "A" c1).2 "B" c2).2.1.getNode in2 =
      some { kind := .input, sigLevel := 0, inputs := [], outputs := [] } := by
    rw [h_in2_eq]
    exact buildChainPre_getNode_input (buildChain World.empty "A" c1).2 "B" c2 h_ids_c1
  have h_not_mem : in2 ∉ (in2 + 1) :: rest := by
    have h_nodup : (in2 :: (in2 + 1) :: rest).Nodup := by
      have h := buildChain_chainIds_nodup (buildChain World.empty "A" c1).2 c2
      rwa [← h_chainIds]
    exact h_nodup.notMem
  -- in2's outputs in the initial world are exactly [in2 + 1]
  set nd_pre : NodeData := { kind := .input, sigLevel := 0, inputs := [], outputs := [] }
  have h_head := connectChain_head_outputs
    (buildChainPre (buildChain World.empty "A" c1).2 "B" c2).2.1
    in2 (in2 + 1) rest nd_pre h_pre_in2 h_not_mem
  have h_nd₁_eq : nd₁ = { nd_pre with outputs := nd_pre.outputs ++ [in2 + 1] } :=
    Option.some.inj (h_nd₁'.symm.trans h_head)
  have h_out_nd₁ : nd₁.outputs = [in2 + 1] := by
    rw [h_nd₁_eq]; dsimp [nd_pre]
  rw [h_out_nd₁] at h_mem
  simp at h_mem
  subst h_mem
  -- out_id = in2 + 1 is chain c2's observer node
  obtain ⟨nd_pre₂, h_nd_pre₂, h_kind_pre⟩ := connectChain_kind_preserved
    (buildChainPre (buildChain World.empty "A" c1).2 "B" c2).2.1
    (buildChainPre (buildChain World.empty "A" c1).2 "B" c2).2.2
    (in2 + 1) nd_out₁ (by exact h_nd_out₁)
  have h_pre_obs : (buildChainPre (buildChain World.empty "A" c1).2 "B" c2).2.1.getNode (in2 + 1) =
      some { kind := .observer, sigLevel := 0, inputs := [], outputs := [] } := by
    rw [h_in2_eq]
    exact buildChainPre_getNode_observer (buildChain World.empty "A" c1).2 "B" c2 h_ids_c1
  injection h_pre_obs.symm.trans h_nd_pre₂ with h_nd_pre_eq
  rw [← h_nd_pre_eq] at h_kind_pre
  -- h_kind_pre : NodeKind.observer = nd_out₁.kind; h_kind₁ : nd_out.kind = nd_out₁.kind
  have h_contra : NodeKind.observer = NodeKind.output name :=
    h_kind_pre.trans (h_kind₁.symm.trans hk)
  cases h_contra

/-! ### Structural lemmas for the 3-iteration convergence proof -/

/-- `onScheduledTick` preserves the output count of every node. -/
theorem World.onScheduledTick_outputs_length (w : World) (id nid : Nat) :
    ((w.onScheduledTick id).getNode nid).map (fun nd => nd.outputs.length) =
    (w.getNode nid).map (fun nd => nd.outputs.length) := by
  dsimp [World.onScheduledTick]
  split
  · rfl
  · rename_i nd₀
    split
    · -- repeater
      set w' := w.updateNode id
        (fun nd' => { nd' with sigLevel := if w.getInputSignal id > 0 then 15 else 0 })
      rw [World.notifyOutputs_getNode]
      by_cases h_eq : nid = id
      · rw [h_eq]
        cases h_gn : w.getNode id with
        | none =>
          have := World.updateNode_getNode_none w id
            (fun nd' => { nd' with sigLevel := if w.getInputSignal id > 0 then 15 else 0 }) h_gn
          simp [w', this]
        | some nd₀' =>
          have h_gn' : w'.getNode id =
              some ({ nd₀' with sigLevel := if w.getInputSignal id > 0 then 15 else 0 } : NodeData) :=
            World.updateNode_getNode_eq w id _ nd₀' h_gn
          rw [h_gn']; rfl
      · exact congrArg (Option.map (fun nd => nd.outputs.length))
          (World.updateNode_getNode_ne w id nid _ (Ne.symm h_eq))
    · -- observer
      set w' := w.updateNode id (fun nd' => { nd' with sigLevel := 15 })
      rw [World.notifyOutputs_getNode]
      by_cases h_eq : nid = id
      · rw [h_eq]
        cases h_gn : w.getNode id with
        | none =>
          have := World.updateNode_getNode_none w id (fun nd' => { nd' with sigLevel := 15 }) h_gn
          simp [w', this]
        | some nd₀' =>
          have h_gn' : w'.getNode id = some ({ nd₀' with sigLevel := 15 } : NodeData) :=
            World.updateNode_getNode_eq w id _ nd₀' h_gn
          rw [h_gn']; rfl
      · exact congrArg (Option.map (fun nd => nd.outputs.length))
          (World.updateNode_getNode_ne w id nid _ (Ne.symm h_eq))
    · -- output/input
      rfl

/-- `stepUntilNextTick` cannot grow the event list beyond `max n 1` when every node
has at most one output. -/
theorem stepUntilNextTick_events_length_le (w : World)
    (h_out : ∀ nid nd, w.getNode nid = some nd → nd.outputs.length ≤ 1) :
    w.stepUntilNextTick.events.length ≤ max w.events.length 1 := by
  revert h_out
  induction w using World.stepUntilNextTick.induct with
  | case1 w h_step =>
    intro h_out
    rw [stepUntilNextTick_of_step_none w h_step]
    exact le_max_left _ _
  | case2 w w' h_step ih =>
    intro h_out
    dsimp [World.step] at h_step
    cases h_pop : w.popNextEvent with
    | none => simp [h_pop] at h_step
    | some p =>
      rcases p with ⟨ev, w_pop⟩
      have h_w'_eq : w' = w_pop.onScheduledTick ev.nodeId := by
        simp only [h_pop] at h_step
        injection h_step with h_eq
        exact h_eq.symm
      subst h_w'_eq
      have h_step' : w.step = some (w_pop.onScheduledTick ev.nodeId) := by
        dsimp [World.step]; rw [h_pop]
      have h_sunt_rw : w.stepUntilNextTick =
          (w_pop.onScheduledTick ev.nodeId).stepUntilNextTick := by
        rw [World.stepUntilNextTick, h_step']
      rw [h_sunt_rw]
      have h_out' : ∀ nid nd, (w_pop.onScheduledTick ev.nodeId).getNode nid = some nd →
          nd.outputs.length ≤ 1 := by
        intro nid nd h_nd
        have h_map := World.onScheduledTick_outputs_length w_pop ev.nodeId nid
        rw [h_nd] at h_map
        have h_nodes : w_pop.nodes = w.nodes := World.popNextEvent_nodes w ev w_pop h_pop
        have h_getNode : w_pop.getNode nid = w.getNode nid := by
          dsimp [World.getNode]; rw [h_nodes]
        cases h_gn : w.getNode nid with
        | none =>
          have h_map' : (w_pop.getNode nid).map (fun nd => nd.outputs.length) = none := by
            rw [h_getNode, h_gn]; rfl
          rw [h_map'] at h_map; cases h_map
        | some nd₀ =>
          have h_map' : (w_pop.getNode nid).map (fun nd => nd.outputs.length) =
              some (nd₀.outputs.length) := by rw [h_getNode, h_gn]; rfl
          rw [h_map'] at h_map
          injection h_map with h_len
          dsimp at h_len
          rw [h_len]
          exact h_out nid nd₀ h_gn
      apply le_trans (ih h_out')
      apply max_le_max ?_ (le_refl 1)
      have h_len_pop : w_pop.events.length + 1 = w.events.length := by
        obtain ⟨idx, h_idx, h_erase, _, _, _⟩ := World.popNextEvent_eraseIdx w ev w_pop h_pop
        rw [h_erase, List.length_eraseIdx]
        split <;> omega
      have h_out_ev : (w_pop.getNode ev.nodeId).elim 0 (fun nd => nd.outputs.length) ≤ 1 := by
        have h_nodes : w_pop.nodes = w.nodes := World.popNextEvent_nodes w ev w_pop h_pop
        have h_gn_eq : w_pop.getNode ev.nodeId = w.getNode ev.nodeId := by
          dsimp [World.getNode]; rw [h_nodes]
        rw [h_gn_eq]
        cases h_gn : w.getNode ev.nodeId with
        | none => simp
        | some nd => exact h_out ev.nodeId nd h_gn
      have h_len_step : (w_pop.onScheduledTick ev.nodeId).events.length ≤
          w_pop.events.length + 1 :=
        World.onScheduledTick_events_le_one w_pop ev.nodeId h_out_ev
      omega

/-- `stepUntilNextTick` preserves "all nodes have ≤ 1 output". -/
theorem stepUntilNextTick_outputs_le_one (w : World)
    (h_out : ∀ nid nd, w.getNode nid = some nd → nd.outputs.length ≤ 1) :
    ∀ nid nd, w.stepUntilNextTick.getNode nid = some nd → nd.outputs.length ≤ 1 := by
  revert h_out
  induction w using World.stepUntilNextTick.induct with
  | case1 w h_step =>
    intro h_out nid nd h_nd
    rw [stepUntilNextTick_of_step_none w h_step] at h_nd
    have h_nd' : w.getNode nid = some nd := by
      dsimp [World.getNode] at h_nd ⊢
      exact h_nd
    exact h_out nid nd h_nd'
  | case2 w w' h_step ih =>
    intro h_out nid nd h_nd
    dsimp [World.step] at h_step
    cases h_pop : w.popNextEvent with
    | none => simp [h_pop] at h_step
    | some p =>
      rcases p with ⟨ev, w_pop⟩
      have h_w'_eq : w' = w_pop.onScheduledTick ev.nodeId := by
        simp only [h_pop] at h_step
        injection h_step with h_eq
        exact h_eq.symm
      subst h_w'_eq
      have h_step' : w.step = some (w_pop.onScheduledTick ev.nodeId) := by
        dsimp [World.step]; rw [h_pop]
      have h_rw : w.stepUntilNextTick = (w_pop.onScheduledTick ev.nodeId).stepUntilNextTick := by
        rw [World.stepUntilNextTick, h_step']
      rw [h_rw] at h_nd
      apply ih ?_ nid nd h_nd
      intro nid' nd' h_nd'
      have h_map := World.onScheduledTick_outputs_length w_pop ev.nodeId nid'
      rw [h_nd'] at h_map
      have h_nodes : w_pop.nodes = w.nodes := World.popNextEvent_nodes w ev w_pop h_pop
      have h_getNode : w_pop.getNode nid' = w.getNode nid' := by
        dsimp [World.getNode]; rw [h_nodes]
      cases h_gn : w.getNode nid' with
      | none =>
        have h_map' : (w_pop.getNode nid').map (fun nd => nd.outputs.length) = none := by
          rw [h_getNode, h_gn]; rfl
        rw [h_map'] at h_map; cases h_map
      | some nd₀ =>
        have h_map' : (w_pop.getNode nid').map (fun nd => nd.outputs.length) =
            some (nd₀.outputs.length) := by rw [h_getNode, h_gn]; rfl
        rw [h_map'] at h_map
        injection h_map with h_len
        dsimp at h_len
        rw [h_len]
        exact h_out nid' nd₀ h_gn

/-- `setInput` preserves "all nodes have ≤ 1 output". -/
theorem setInput_outputs_le_one (w : World) (id level : Nat)
    (h_out : ∀ nid nd, w.getNode nid = some nd → nd.outputs.length ≤ 1) :
    ∀ nid nd, (w.setInput id level).getNode nid = some nd → nd.outputs.length ≤ 1 := by
  intro nid nd h_nd
  dsimp [World.setInput] at h_nd
  rw [World.notifyOutputs_getNode] at h_nd
  by_cases h_eq : nid = id
  · cases h_gn : w.getNode id with
    | none =>
      have h_none : (w.updateNode id (fun nd => { nd with sigLevel := level })).getNode id =
          none :=
        World.updateNode_getNode_none w id (fun nd => { nd with sigLevel := level }) h_gn
      rw [h_eq] at h_nd
      rw [h_none] at h_nd
      cases h_nd
    | some nd₀ =>
      have h_gn' : (w.updateNode id (fun nd => { nd with sigLevel := level })).getNode id =
          some ({ nd₀ with sigLevel := level } : NodeData) :=
        World.updateNode_getNode_eq w id (fun nd => { nd with sigLevel := level }) nd₀ h_gn
      rw [h_eq] at h_nd
      rw [h_gn'] at h_nd
      injection h_nd with h_nd_eq
      subst h_nd_eq
      dsimp
      exact h_out id nd₀ h_gn
  · rw [World.updateNode_getNode_ne w id nid _ (Ne.symm h_eq)] at h_nd
    exact h_out nid nd h_nd
