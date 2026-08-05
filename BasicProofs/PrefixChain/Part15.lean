import BasicProofs.PrefixChain.Part14


open BasicRedstoneSim

/-- After one simBody step at tick t₂, the node lists agree for insertion
    positions `pos` and `pos'`. -/
theorem pos_indep_w1_nodes_eq (c1 c2 : ChainSpec) (t1 t2 pos pos' : Nat)
    (_ : ∀ d ∈ c1.middleDelays, ValidDelay d)
    (_ : ValidDelay c1.lastDelay)
    (_ : ∀ d ∈ c2.middleDelays, ValidDelay d)
    (_ : ValidDelay c2.lastDelay) :
    let in1 := (buildChain World.empty "A" c1).1
    let in2 := (buildChain (buildChain World.empty "A" c1).2 "B" c2).1
    let w_t₂ := (List.range t2).foldl (simBody t1 t2 pos' in1 in2)
        (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
    let w₁_pos := simBody t1 t2 pos in1 in2 w_t₂ 0
    let w₁_pos' := simBody t1 t2 pos' in1 in2 w_t₂ 0
    (h_t1_lt_t2 : t1 < t2) →
    (h_t₂_tick : w_t₂.tick = t2) →
    (h_delay_w : ∀ nid nd, w_t₂.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2) →
    (h_wt2_nodeId_lt : ∀ ev ∈ w_t₂.events, ev.nodeId < in2) →
    w₁_pos.nodes = w₁_pos'.nodes := by
        intro in1 in2 w_t₂ w₁_pos w₁_pos' h_t1_lt_t2 h_t₂_tick h_delay_w h_wt2_nodeId_lt
        dsimp (config := { zeta := true }) [w₁_pos, w₁_pos', simBody]
        split_ifs <;> simp [World.setInput_tick, World.logOutput_tick, h_t₂_tick] at * <;> try omega
        set w_log := w_t₂.logOutput (toString "tick " ++ t2.repr)
        -- Goal: ((processNEvents w_log pos).setInput in2 15).stepUntilNextTick.nodes =
        --        ((processNEvents w_log pos').setInput in2 15).stepUntilNextTick.nodes
        -- Use: processNEvents_stepUntilNextTick_eq + stepUntilNextTick_fuel_indep + setInput commutation
        -- Step 1: Commute setInput with stepUntilNextTick for nodes
        -- ((w.setInput in2 15).stepUntilNextTick 1000).nodes = ((w.stepUntilNextTick 1000).setInput in2 15).nodes
        -- This holds because:
        -- - setInput only changes in2.sigLevel (notifyOutputs preserves nodes)
        -- - stepUntilNextTick doesn't modify in2.sigLevel (no event targets in2, new events don't target in2)
        -- - stepUntilNextTick gives same non-in2 nodes regardless of in2.sigLevel (chain separation)
        -- Chain separation: events at tick t₂ target chain c1 nodes (nodeId < in2),
        -- and chain c1 nodes don't have in2 in their inputs.
        -- Key fact: all events in w_t₂ have nodeId < in2 (proved above as h_wt2_nodeId_lt)
        have h_comm_pos : ((processNEvents w_log pos).setInput in2 15).stepUntilNextTick.nodes =
            ((processNEvents w_log pos).stepUntilNextTick.setInput in2 15).nodes := by
          apply setInput_stepUntilNextTick_comm_nodes
          · -- h_no_target: events at tick t₂ don't target in2
            intro ev h_ev h_tick
            have h_all : ∀ ev ∈ (processNEvents w_log pos).events, ev.nodeId < in2 :=
              processNEvents_nodeId_lt w_log pos in2
                (by -- events in w_log have nodeId < in2
                  intro ev' h_ev'
                  dsimp [w_log, World.logOutput] at h_ev'
                  exact h_wt2_nodeId_lt ev' h_ev')
                (by -- outputs of nodes < in2 in w_log are < in2
                  intro nid nd h_nd h_lt out h_out
                  dsimp [w_log, World.logOutput] at h_nd
                  obtain ⟨nd₀, h_nd₀, h_inp, h_outp⟩ := simFoldl_inputs_preserved
                    (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
                    t1 t2 pos' in1 in2 t2 nid nd h_nd
                  rw [h_outp] at h_out
                  have h_in2_eq : in2 = (buildChain World.empty "A" c1).2.nextId := by
                    dsimp [in2]; simp [buildChain, buildChainPre, World.addNode]
                  have h_lt' : nid < (buildChain World.empty "A" c1).2.nextId := by
                    rw [← h_in2_eq]; exact h_lt
                  have h_old := buildChain_getNode_old (buildChain World.empty "A" c1).2 "B" c2 nid h_lt'
                  have h_nd₀' : (buildChain World.empty "A" c1).2.getNode nid = some nd₀ := by rwa [← h_old]
                  dsimp [buildChain] at h_nd₀'
                  have h_out₀ := connectChain_outputs_subset
                    (buildChainPre World.empty "A" c1).2.2
                    (buildChainPre World.empty "A" c1).2.1
                    nid nd₀ h_nd₀' out h_out
                  cases h_out₀ with
                  | inl h_mem =>
                    have h_lt_out := buildChainPre_chainIds_lt_nextId World.empty "A" c1 out h_mem
                    have h_nextId : (buildChainPre World.empty "A" c1).2.1.nextId =
                        (buildChain World.empty "A" c1).2.nextId := by
                      dsimp [buildChain]; simp [connectChain_nextId]
                    rwa [h_in2_eq, ← h_nextId]
                  | inr h_mem =>
                    obtain ⟨nd₁, h_nd₁, h_out₁⟩ := h_mem
                    have h_empty := buildChainPre_empty_outputs "A" c1 nid nd₁ h_nd₁
                    rw [h_empty] at h_out₁; cases h_out₁)
                (by -- delay ≥ 2
                  intro nid nd h_nd d p h_kind
                  dsimp [w_log, World.logOutput] at h_nd
                  exact h_delay_w nid nd h_nd d p h_kind)
            have h_nodeId_lt := h_all ev h_ev
            omega
          · -- h_sep: in2 not in inputs of nodes with events at tick t₂
            intro nid nd h_nd ⟨ev, h_ev, h_ev_tick, h_node⟩
            -- nid < in2 from the event
            have h_all : ∀ ev ∈ (processNEvents w_log pos).events, ev.nodeId < in2 :=
              processNEvents_nodeId_lt w_log pos in2
                (by intro ev' h_ev'; dsimp [w_log, World.logOutput] at h_ev'; exact h_wt2_nodeId_lt ev' h_ev')
                (by intro nid nd h_nd h_lt out h_out
                    dsimp [w_log, World.logOutput] at h_nd
                    obtain ⟨nd₀, h_nd₀, h_inp, h_outp⟩ := simFoldl_inputs_preserved
                      (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
                      t1 t2 pos' in1 in2 t2 nid nd h_nd
                    rw [h_outp] at h_out
                    have h_in2_eq : in2 = (buildChain World.empty "A" c1).2.nextId := by
                      dsimp [in2]; simp [buildChain, buildChainPre, World.addNode]
                    have h_lt' : nid < (buildChain World.empty "A" c1).2.nextId := by rw [← h_in2_eq]; exact h_lt
                    have h_old := buildChain_getNode_old (buildChain World.empty "A" c1).2 "B" c2 nid h_lt'
                    have h_nd₀' : (buildChain World.empty "A" c1).2.getNode nid = some nd₀ := by rwa [← h_old]
                    dsimp [buildChain] at h_nd₀'
                    have h_out₀ := connectChain_outputs_subset
                      (buildChainPre World.empty "A" c1).2.2 (buildChainPre World.empty "A" c1).2.1
                      nid nd₀ h_nd₀' out h_out
                    cases h_out₀ with
                    | inl h_mem =>
                      have h_lt_out := buildChainPre_chainIds_lt_nextId World.empty "A" c1 out h_mem
                      have h_nextId : (buildChainPre World.empty "A" c1).2.1.nextId =
                          (buildChain World.empty "A" c1).2.nextId := by dsimp [buildChain]; simp [connectChain_nextId]
                      rwa [h_in2_eq, ← h_nextId]
                    | inr h_mem =>
                      obtain ⟨nd₁, h_nd₁, h_out₁⟩ := h_mem
                      have h_empty := buildChainPre_empty_outputs "A" c1 nid nd₁ h_nd₁
                      rw [h_empty] at h_out₁; cases h_out₁)
                (by intro nid nd h_nd d p h_kind
                    dsimp [w_log, World.logOutput] at h_nd
                    exact h_delay_w nid nd h_nd d p h_kind)
            have h_nid_lt : nid < in2 := by rw [← h_node]; exact h_all ev h_ev
            -- processNEvents preserves nodes
            obtain ⟨nd₀, h_nd₀, h_inp_eq, h_out_eq⟩ := processNEvents_inputs_preserved w_log pos nid nd h_nd
            -- w_log has same nodes as w_t₂
            dsimp [w_log, World.logOutput] at h_nd₀
            -- simFoldl preserves inputs from initial world
            obtain ⟨nd₁, h_nd₁, h_inp₁, h_out₁⟩ := simFoldl_inputs_preserved
              (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
              t1 t2 pos' in1 in2 t2 nid nd₀ h_nd₀
            -- nd₁ is in the initial world, nid < in2
            have h_in2_eq : in2 = (buildChain World.empty "A" c1).2.nextId := by
              dsimp [in2]; simp [buildChain, buildChainPre, World.addNode]
            have h_lt' : nid < (buildChain World.empty "A" c1).2.nextId := by rw [← h_in2_eq]; exact h_nid_lt
            have h_old := buildChain_getNode_old (buildChain World.empty "A" c1).2 "B" c2 nid h_lt'
            have h_nd₁' : (buildChain World.empty "A" c1).2.getNode nid = some nd₁ := by rwa [← h_old]
            -- Inputs in (buildChain World.empty "A" c1).2 are from connectChain
            dsimp [buildChain] at h_nd₁'
            -- Show in2 ∉ nd.inputs by showing all inputs are < in2
            intro h_in2_in
            rw [h_inp_eq, h_inp₁] at h_in2_in
            -- in2 ∈ nd₁.inputs where nd₁ is in connectChain w_pre chainIds
            have h_inp₂ := connectChain_inputs_mem
              (buildChainPre World.empty "A" c1).2.2 (buildChainPre World.empty "A" c1).2.1
              nid nd₁ h_nd₁' in2 h_in2_in
            cases h_inp₂ with
            | inl h_mem =>
              -- in2 ∈ chainIds, but all chainIds < nextId = in2
              have h_lt_in2 := buildChainPre_chainIds_lt_nextId World.empty "A" c1 in2 h_mem
              have h_nextId : (buildChainPre World.empty "A" c1).2.1.nextId =
                  (buildChain World.empty "A" c1).2.nextId := by dsimp [buildChain]; simp [connectChain_nextId]
              rw [h_in2_eq, ← h_nextId] at h_lt_in2
              omega
            | inr h_mem =>
              -- in2 was already an input in buildChainPre World.empty, but inputs are empty
              obtain ⟨nd₂, h_nd₂, h_inp₂⟩ := h_mem
              have h_empty := buildChainPre_empty_inputs "A" c1 nid nd₂ h_nd₂
              rw [h_empty] at h_inp₂
              cases h_inp₂
          · intro nid nd h_nd d p h_kind
            obtain ⟨nd₀, h_nd₀, h_kind_eq⟩ := processNEvents_kind_preserved w_log pos nid nd h_nd
            rw [h_kind_eq] at h_kind
            have h_nd₀'' : w_t₂.getNode nid = some nd₀ := by
              have h_nodes : w_log.nodes = w_t₂.nodes := by dsimp [w_log]
              dsimp [World.getNode] at h_nd₀ ⊢
              rw [h_nodes] at h_nd₀
              exact h_nd₀
            exact h_delay_w nid nd₀ h_nd₀'' d p h_kind
        have h_comm_pos' : ((processNEvents w_log pos').setInput in2 15).stepUntilNextTick.nodes =
            ((processNEvents w_log pos').stepUntilNextTick.setInput in2 15).nodes := by
          apply setInput_stepUntilNextTick_comm_nodes
          · -- h_no_target for pos'
            intro ev h_ev h_tick
            have h_all : ∀ ev ∈ (processNEvents w_log pos').events, ev.nodeId < in2 :=
              processNEvents_nodeId_lt w_log pos' in2
                (by intro ev' h_ev'; dsimp [w_log, World.logOutput] at h_ev'; exact h_wt2_nodeId_lt ev' h_ev')
                (by intro nid nd h_nd h_lt out h_out
                    dsimp [w_log, World.logOutput] at h_nd
                    obtain ⟨nd₀, h_nd₀, h_inp, h_outp⟩ := simFoldl_inputs_preserved
                      (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
                      t1 t2 pos' in1 in2 t2 nid nd h_nd
                    rw [h_outp] at h_out
                    have h_in2_eq : in2 = (buildChain World.empty "A" c1).2.nextId := by
                      dsimp [in2]; simp [buildChain, buildChainPre, World.addNode]
                    have h_lt' : nid < (buildChain World.empty "A" c1).2.nextId := by rw [← h_in2_eq]; exact h_lt
                    have h_old := buildChain_getNode_old (buildChain World.empty "A" c1).2 "B" c2 nid h_lt'
                    have h_nd₀' : (buildChain World.empty "A" c1).2.getNode nid = some nd₀ := by rwa [← h_old]
                    dsimp [buildChain] at h_nd₀'
                    have h_out₀ := connectChain_outputs_subset
                      (buildChainPre World.empty "A" c1).2.2 (buildChainPre World.empty "A" c1).2.1
                      nid nd₀ h_nd₀' out h_out
                    cases h_out₀ with
                    | inl h_mem =>
                      have h_lt_out := buildChainPre_chainIds_lt_nextId World.empty "A" c1 out h_mem
                      have h_nextId : (buildChainPre World.empty "A" c1).2.1.nextId =
                          (buildChain World.empty "A" c1).2.nextId := by dsimp [buildChain]; simp [connectChain_nextId]
                      rwa [h_in2_eq, ← h_nextId]
                    | inr h_mem =>
                      obtain ⟨nd₁, h_nd₁, h_out₁⟩ := h_mem
                      have h_empty := buildChainPre_empty_outputs "A" c1 nid nd₁ h_nd₁
                      rw [h_empty] at h_out₁; cases h_out₁)
                (by intro nid nd h_nd d p h_kind
                    dsimp [w_log, World.logOutput] at h_nd
                    exact h_delay_w nid nd h_nd d p h_kind)
            have h_nodeId_lt := h_all ev h_ev
            omega
          · -- h_sep for pos'
            intro nid nd h_nd ⟨ev, h_ev, h_ev_tick, h_node⟩
            have h_all : ∀ ev ∈ (processNEvents w_log pos').events, ev.nodeId < in2 :=
              processNEvents_nodeId_lt w_log pos' in2
                (by intro ev' h_ev'; dsimp [w_log, World.logOutput] at h_ev'; exact h_wt2_nodeId_lt ev' h_ev')
                (by intro nid nd h_nd h_lt out h_out
                    dsimp [w_log, World.logOutput] at h_nd
                    obtain ⟨nd₀, h_nd₀, h_inp, h_outp⟩ := simFoldl_inputs_preserved
                      (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
                      t1 t2 pos' in1 in2 t2 nid nd h_nd
                    rw [h_outp] at h_out
                    have h_in2_eq : in2 = (buildChain World.empty "A" c1).2.nextId := by
                      dsimp [in2]; simp [buildChain, buildChainPre, World.addNode]
                    have h_lt' : nid < (buildChain World.empty "A" c1).2.nextId := by rw [← h_in2_eq]; exact h_lt
                    have h_old := buildChain_getNode_old (buildChain World.empty "A" c1).2 "B" c2 nid h_lt'
                    have h_nd₀' : (buildChain World.empty "A" c1).2.getNode nid = some nd₀ := by rwa [← h_old]
                    dsimp [buildChain] at h_nd₀'
                    have h_out₀ := connectChain_outputs_subset
                      (buildChainPre World.empty "A" c1).2.2 (buildChainPre World.empty "A" c1).2.1
                      nid nd₀ h_nd₀' out h_out
                    cases h_out₀ with
                    | inl h_mem =>
                      have h_lt_out := buildChainPre_chainIds_lt_nextId World.empty "A" c1 out h_mem
                      have h_nextId : (buildChainPre World.empty "A" c1).2.1.nextId =
                          (buildChain World.empty "A" c1).2.nextId := by dsimp [buildChain]; simp [connectChain_nextId]
                      rwa [h_in2_eq, ← h_nextId]
                    | inr h_mem =>
                      obtain ⟨nd₁, h_nd₁, h_out₁⟩ := h_mem
                      have h_empty := buildChainPre_empty_outputs "A" c1 nid nd₁ h_nd₁
                      rw [h_empty] at h_out₁; cases h_out₁)
                (by intro nid nd h_nd d p h_kind
                    dsimp [w_log, World.logOutput] at h_nd
                    exact h_delay_w nid nd h_nd d p h_kind)
            have h_nid_lt : nid < in2 := by rw [← h_node]; exact h_all ev h_ev
            obtain ⟨nd₀, h_nd₀, h_inp_eq, h_out_eq⟩ := processNEvents_inputs_preserved w_log pos' nid nd h_nd
            dsimp [w_log, World.logOutput] at h_nd₀
            obtain ⟨nd₁, h_nd₁, h_inp₁, h_out₁⟩ := simFoldl_inputs_preserved
              (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
              t1 t2 pos' in1 in2 t2 nid nd₀ h_nd₀
            have h_in2_eq : in2 = (buildChain World.empty "A" c1).2.nextId := by
              dsimp [in2]; simp [buildChain, buildChainPre, World.addNode]
            have h_lt' : nid < (buildChain World.empty "A" c1).2.nextId := by rw [← h_in2_eq]; exact h_nid_lt
            have h_old := buildChain_getNode_old (buildChain World.empty "A" c1).2 "B" c2 nid h_lt'
            have h_nd₁' : (buildChain World.empty "A" c1).2.getNode nid = some nd₁ := by rwa [← h_old]
            dsimp [buildChain] at h_nd₁'
            intro h_in2_in
            rw [h_inp_eq, h_inp₁] at h_in2_in
            have h_inp₂ := connectChain_inputs_mem
              (buildChainPre World.empty "A" c1).2.2 (buildChainPre World.empty "A" c1).2.1
              nid nd₁ h_nd₁' in2 h_in2_in
            cases h_inp₂ with
            | inl h_mem =>
              have h_lt_in2 := buildChainPre_chainIds_lt_nextId World.empty "A" c1 in2 h_mem
              have h_nextId : (buildChainPre World.empty "A" c1).2.1.nextId =
                  (buildChain World.empty "A" c1).2.nextId := by dsimp [buildChain]; simp [connectChain_nextId]
              rw [h_in2_eq, ← h_nextId] at h_lt_in2
              omega
            | inr h_mem =>
              obtain ⟨nd₂, h_nd₂, h_inp₂⟩ := h_mem
              have h_empty := buildChainPre_empty_inputs "A" c1 nid nd₂ h_nd₂
              rw [h_empty] at h_inp₂
              cases h_inp₂
          · intro nid nd h_nd d p h_kind
            obtain ⟨nd₀, h_nd₀, h_kind_eq⟩ := processNEvents_kind_preserved w_log pos' nid nd h_nd
            rw [h_kind_eq] at h_kind
            have h_nd₀'' : w_t₂.getNode nid = some nd₀ := by
              have h_nodes : w_log.nodes = w_t₂.nodes := by dsimp [w_log]
              dsimp [World.getNode] at h_nd₀ ⊢
              rw [h_nodes] at h_nd₀
              exact h_nd₀
            exact h_delay_w nid nd₀ h_nd₀'' d p h_kind
        rw [h_comm_pos, h_comm_pos']
        -- Step 2: Use processNEvents_stepUntilNextTick_eq
        rw [processNEvents_stepUntilNextTick_eq, processNEvents_stepUntilNextTick_eq]


/-- After one simBody step at tick t₂, the output logs agree for insertion
    positions `pos` and `pos'`. -/
theorem pos_indep_w1_log_eq (c1 c2 : ChainSpec) (t1 t2 pos pos' : Nat)
    (_ : ∀ d ∈ c1.middleDelays, ValidDelay d)
    (_ : ValidDelay c1.lastDelay)
    (_ : ∀ d ∈ c2.middleDelays, ValidDelay d)
    (_ : ValidDelay c2.lastDelay) :
    let in1 := (buildChain World.empty "A" c1).1
    let in2 := (buildChain (buildChain World.empty "A" c1).2 "B" c2).1
    let w_t₂ := (List.range t2).foldl (simBody t1 t2 pos' in1 in2)
        (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
    let w₁_pos := simBody t1 t2 pos in1 in2 w_t₂ 0
    let w₁_pos' := simBody t1 t2 pos' in1 in2 w_t₂ 0
    (h_t1_lt_t2 : t1 < t2) →
    (h_t₂_tick : w_t₂.tick = t2) →
    (h_delay_w : ∀ nid nd, w_t₂.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2) →
    (h_wt2_nodeId_lt : ∀ ev ∈ w_t₂.events, ev.nodeId < in2) →
    w₁_pos.outputLog = w₁_pos'.outputLog := by
        intro in1 in2 w_t₂ w₁_pos w₁_pos' h_t1_lt_t2 h_t₂_tick h_delay_w h_wt2_nodeId_lt
        dsimp (config := { zeta := true }) [w₁_pos, w₁_pos', simBody]
        split_ifs <;> simp [World.setInput_tick, World.logOutput_tick, h_t₂_tick] at * <;> try omega
        set w_log := w_t₂.logOutput (toString "tick " ++ t2.repr)
        -- Both sides: commute setInput with stepUntilNextTick, then remove processNEvents
        have h_comm_log_pos : ((processNEvents w_log pos).setInput in2 15).stepUntilNextTick.outputLog =
            ((processNEvents w_log pos).stepUntilNextTick.setInput in2 15).outputLog := by
          apply setInput_stepUntilNextTick_comm_outputLog
          · intro ev h_ev h_tick
            have h_all : ∀ ev ∈ (processNEvents w_log pos).events, ev.nodeId < in2 :=
              processNEvents_nodeId_lt w_log pos in2
                (by intro ev' h_ev'; dsimp [w_log, World.logOutput] at h_ev'; exact h_wt2_nodeId_lt ev' h_ev')
                (by intro nid nd h_nd h_lt out h_out
                    dsimp [w_log, World.logOutput] at h_nd
                    obtain ⟨nd₀, h_nd₀, h_inp, h_outp⟩ := simFoldl_inputs_preserved
                      (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
                      t1 t2 pos' in1 in2 t2 nid nd h_nd
                    rw [h_outp] at h_out
                    have h_in2_eq : in2 = (buildChain World.empty "A" c1).2.nextId := by
                      dsimp [in2]; simp [buildChain, buildChainPre, World.addNode]
                    have h_lt' : nid < (buildChain World.empty "A" c1).2.nextId := by rw [← h_in2_eq]; exact h_lt
                    have h_old := buildChain_getNode_old (buildChain World.empty "A" c1).2 "B" c2 nid h_lt'
                    have h_nd₀' : (buildChain World.empty "A" c1).2.getNode nid = some nd₀ := by rwa [← h_old]
                    dsimp [buildChain] at h_nd₀'
                    have h_out₀ := connectChain_outputs_subset
                      (buildChainPre World.empty "A" c1).2.2 (buildChainPre World.empty "A" c1).2.1
                      nid nd₀ h_nd₀' out h_out
                    cases h_out₀ with
                    | inl h_mem =>
                      have h_lt_out := buildChainPre_chainIds_lt_nextId World.empty "A" c1 out h_mem
                      have h_nextId : (buildChainPre World.empty "A" c1).2.1.nextId =
                          (buildChain World.empty "A" c1).2.nextId := by dsimp [buildChain]; simp [connectChain_nextId]
                      rwa [h_in2_eq, ← h_nextId]
                    | inr h_mem =>
                      obtain ⟨nd₁, h_nd₁, h_out₁⟩ := h_mem
                      have h_empty := buildChainPre_empty_outputs "A" c1 nid nd₁ h_nd₁
                      rw [h_empty] at h_out₁; cases h_out₁)
                (by intro nid nd h_nd d p h_kind; dsimp [w_log, World.logOutput] at h_nd; exact h_delay_w nid nd h_nd d p h_kind)
            have h_lt := h_all ev h_ev
            omega
          · intro nid nd h_nd ⟨ev, h_ev, h_ev_tick, h_node⟩
            have h_all : ∀ ev ∈ (processNEvents w_log pos).events, ev.nodeId < in2 :=
              processNEvents_nodeId_lt w_log pos in2
                (by intro ev' h_ev'; dsimp [w_log, World.logOutput] at h_ev'; exact h_wt2_nodeId_lt ev' h_ev')
                (by intro nid nd h_nd h_lt out h_out
                    dsimp [w_log, World.logOutput] at h_nd
                    obtain ⟨nd₀, h_nd₀, h_inp, h_outp⟩ := simFoldl_inputs_preserved
                      (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
                      t1 t2 pos' in1 in2 t2 nid nd h_nd
                    rw [h_outp] at h_out
                    have h_in2_eq : in2 = (buildChain World.empty "A" c1).2.nextId := by
                      dsimp [in2]; simp [buildChain, buildChainPre, World.addNode]
                    have h_lt' : nid < (buildChain World.empty "A" c1).2.nextId := by rw [← h_in2_eq]; exact h_lt
                    have h_old := buildChain_getNode_old (buildChain World.empty "A" c1).2 "B" c2 nid h_lt'
                    have h_nd₀' : (buildChain World.empty "A" c1).2.getNode nid = some nd₀ := by rwa [← h_old]
                    dsimp [buildChain] at h_nd₀'
                    have h_out₀ := connectChain_outputs_subset
                      (buildChainPre World.empty "A" c1).2.2 (buildChainPre World.empty "A" c1).2.1
                      nid nd₀ h_nd₀' out h_out
                    cases h_out₀ with
                    | inl h_mem =>
                      have h_lt_out := buildChainPre_chainIds_lt_nextId World.empty "A" c1 out h_mem
                      have h_nextId : (buildChainPre World.empty "A" c1).2.1.nextId =
                          (buildChain World.empty "A" c1).2.nextId := by dsimp [buildChain]; simp [connectChain_nextId]
                      rwa [h_in2_eq, ← h_nextId]
                    | inr h_mem =>
                      obtain ⟨nd₁, h_nd₁, h_out₁⟩ := h_mem
                      have h_empty := buildChainPre_empty_outputs "A" c1 nid nd₁ h_nd₁
                      rw [h_empty] at h_out₁; cases h_out₁)
                (by intro nid nd h_nd d p h_kind; dsimp [w_log, World.logOutput] at h_nd; exact h_delay_w nid nd h_nd d p h_kind)
            have h_nid_lt : nid < in2 := by rw [← h_node]; exact h_all ev h_ev
            obtain ⟨nd₀, h_nd₀, h_inp_eq, h_out_eq⟩ := processNEvents_inputs_preserved w_log pos nid nd h_nd
            dsimp [w_log, World.logOutput] at h_nd₀
            obtain ⟨nd₁, h_nd₁, h_inp₁, h_out₁⟩ := simFoldl_inputs_preserved
              (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
              t1 t2 pos' in1 in2 t2 nid nd₀ h_nd₀
            have h_in2_eq : in2 = (buildChain World.empty "A" c1).2.nextId := by
              dsimp [in2]; simp [buildChain, buildChainPre, World.addNode]
            have h_lt' : nid < (buildChain World.empty "A" c1).2.nextId := by rw [← h_in2_eq]; exact h_nid_lt
            have h_old := buildChain_getNode_old (buildChain World.empty "A" c1).2 "B" c2 nid h_lt'
            have h_nd₁' : (buildChain World.empty "A" c1).2.getNode nid = some nd₁ := by rwa [← h_old]
            dsimp [buildChain] at h_nd₁'
            intro h_in2_in
            rw [h_inp_eq, h_inp₁] at h_in2_in
            have h_inp₂ := connectChain_inputs_mem
              (buildChainPre World.empty "A" c1).2.2 (buildChainPre World.empty "A" c1).2.1
              nid nd₁ h_nd₁' in2 h_in2_in
            cases h_inp₂ with
            | inl h_mem =>
              have h_lt_in2 := buildChainPre_chainIds_lt_nextId World.empty "A" c1 in2 h_mem
              have h_nextId : (buildChainPre World.empty "A" c1).2.1.nextId =
                  (buildChain World.empty "A" c1).2.nextId := by dsimp [buildChain]; simp [connectChain_nextId]
              rw [h_in2_eq, ← h_nextId] at h_lt_in2; omega
            | inr h_mem =>
              obtain ⟨nd₂, h_nd₂, h_inp₂⟩ := h_mem
              have h_empty := buildChainPre_empty_inputs "A" c1 nid nd₂ h_nd₂
              rw [h_empty] at h_inp₂; cases h_inp₂
          · -- h_sep_out
            intro nid nd h_nd ⟨ev, h_ev, h_ev_tick, h_node⟩ out_id h_mem_out nd_out h_nd_out
            have h_all : ∀ ev ∈ (processNEvents w_log pos).events, ev.nodeId < in2 :=
              processNEvents_nodeId_lt w_log pos in2
                (by intro ev' h_ev'; dsimp [w_log, World.logOutput] at h_ev'; exact h_wt2_nodeId_lt ev' h_ev')
                (by intro nid nd h_nd h_lt out h_out
                    dsimp [w_log, World.logOutput] at h_nd
                    obtain ⟨nd₀, h_nd₀, h_inp, h_outp⟩ := simFoldl_inputs_preserved
                      (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
                      t1 t2 pos' in1 in2 t2 nid nd h_nd
                    rw [h_outp] at h_out
                    have h_in2_eq : in2 = (buildChain World.empty "A" c1).2.nextId := by
                      dsimp [in2]; simp [buildChain, buildChainPre, World.addNode]
                    have h_lt' : nid < (buildChain World.empty "A" c1).2.nextId := by rw [← h_in2_eq]; exact h_lt
                    have h_old := buildChain_getNode_old (buildChain World.empty "A" c1).2 "B" c2 nid h_lt'
                    have h_nd₀' : (buildChain World.empty "A" c1).2.getNode nid = some nd₀ := by rwa [← h_old]
                    dsimp [buildChain] at h_nd₀'
                    have h_out₀ := connectChain_outputs_subset
                      (buildChainPre World.empty "A" c1).2.2 (buildChainPre World.empty "A" c1).2.1
                      nid nd₀ h_nd₀' out h_out
                    cases h_out₀ with
                    | inl h_mem =>
                      have h_lt_out := buildChainPre_chainIds_lt_nextId World.empty "A" c1 out h_mem
                      have h_nextId : (buildChainPre World.empty "A" c1).2.1.nextId =
                          (buildChain World.empty "A" c1).2.nextId := by dsimp [buildChain]; simp [connectChain_nextId]
                      rwa [h_in2_eq, ← h_nextId]
                    | inr h_mem =>
                      obtain ⟨nd₁, h_nd₁, h_out₁⟩ := h_mem
                      have h_empty := buildChainPre_empty_outputs "A" c1 nid nd₁ h_nd₁
                      rw [h_empty] at h_out₁; cases h_out₁)
                (by intro nid nd h_nd d p h_kind; dsimp [w_log, World.logOutput] at h_nd; exact h_delay_w nid nd h_nd d p h_kind)
            have h_nid_lt : nid < in2 := by rw [← h_node]; exact h_all ev h_ev
            obtain ⟨nd₀, h_nd₀, h_inp_eq, h_out_eq⟩ := processNEvents_inputs_preserved w_log pos nid nd h_nd
            dsimp [w_log, World.logOutput] at h_nd₀
            obtain ⟨nd₁, h_nd₁, h_inp₁, h_out₁⟩ := simFoldl_inputs_preserved
              (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
              t1 t2 pos' in1 in2 t2 nid nd₀ h_nd₀
            have h_in2_eq : in2 = (buildChain World.empty "A" c1).2.nextId := by
              dsimp [in2]; simp [buildChain, buildChainPre, World.addNode]
            have h_lt' : nid < (buildChain World.empty "A" c1).2.nextId := by rw [← h_in2_eq]; exact h_nid_lt
            have h_old := buildChain_getNode_old (buildChain World.empty "A" c1).2 "B" c2 nid h_lt'
            have h_nd₁' : (buildChain World.empty "A" c1).2.getNode nid = some nd₁ := by rwa [← h_old]
            dsimp [buildChain] at h_nd₁'
            -- out_id is an output of nid, need to show in2 ∉ nd_out.inputs
            rw [h_out_eq, h_out₁] at h_mem_out
            have h_out_lt : out_id < in2 := by
              have h_out₀ := connectChain_outputs_subset
                (buildChainPre World.empty "A" c1).2.2 (buildChainPre World.empty "A" c1).2.1
                nid nd₁ h_nd₁' out_id h_mem_out
              cases h_out₀ with
              | inl h_mem =>
                have h_lt_out := buildChainPre_chainIds_lt_nextId World.empty "A" c1 out_id h_mem
                have h_nextId : (buildChainPre World.empty "A" c1).2.1.nextId =
                    (buildChain World.empty "A" c1).2.nextId := by dsimp [buildChain]; simp [connectChain_nextId]
                rwa [h_in2_eq, ← h_nextId]
              | inr h_mem =>
                obtain ⟨nd₂, h_nd₂, h_out₂⟩ := h_mem
                have h_empty := buildChainPre_empty_outputs "A" c1 nid nd₂ h_nd₂
                rw [h_empty] at h_out₂; cases h_out₂
            -- nd_out is at out_id < in2, so its inputs are from chain c1
            obtain ⟨nd_out₀, h_nd_out₀, h_inp_out₀, h_out_out₀⟩ := processNEvents_inputs_preserved w_log pos out_id nd_out h_nd_out
            have h_nd_out_wt2 : w_t₂.getNode out_id = some nd_out₀ := by
              dsimp [w_log, World.logOutput] at h_nd_out₀ ⊢
              have h_nodes : w_t₂.nodes = (w_log).nodes := by dsimp [w_log]
              dsimp [World.getNode] at h_nd_out₀ ⊢; rw [h_nodes]; exact h_nd_out₀
            obtain ⟨nd_out₁, h_nd_out₁, h_inp_out, h_out_out⟩ := simFoldl_inputs_preserved
              (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
              t1 t2 pos' in1 in2 t2 out_id nd_out₀ h_nd_out_wt2
            have h_lt_out' : out_id < (buildChain World.empty "A" c1).2.nextId := by rw [← h_in2_eq]; exact h_out_lt
            have h_old_out := buildChain_getNode_old (buildChain World.empty "A" c1).2 "B" c2 out_id h_lt_out'
            have h_nd_out₁' : (buildChain World.empty "A" c1).2.getNode out_id = some nd_out₁ := by rwa [← h_old_out]
            dsimp [buildChain] at h_nd_out₁'
            intro h_in2_in
            rw [h_inp_out₀, h_inp_out] at h_in2_in
            have h_inp₂ := connectChain_inputs_mem
              (buildChainPre World.empty "A" c1).2.2 (buildChainPre World.empty "A" c1).2.1
              out_id nd_out₁ h_nd_out₁' in2 h_in2_in
            cases h_inp₂ with
            | inl h_mem =>
              have h_lt_in2 := buildChainPre_chainIds_lt_nextId World.empty "A" c1 in2 h_mem
              have h_nextId : (buildChainPre World.empty "A" c1).2.1.nextId =
                  (buildChain World.empty "A" c1).2.nextId := by dsimp [buildChain]; simp [connectChain_nextId]
              rw [h_in2_eq, ← h_nextId] at h_lt_in2; omega
            | inr h_mem =>
              obtain ⟨nd₂, h_nd₂, h_inp₂⟩ := h_mem
              have h_empty := buildChainPre_empty_inputs "A" c1 out_id nd₂ h_nd₂
              rw [h_empty] at h_inp₂; cases h_inp₂
          · -- h_outputs_ne
            intro nid nd h_nd ⟨ev, h_ev, h_ev_tick, h_node⟩ out_id h_mem_out
            have h_all : ∀ ev ∈ (processNEvents w_log pos).events, ev.nodeId < in2 :=
              processNEvents_nodeId_lt w_log pos in2
                (by intro ev' h_ev'; dsimp [w_log, World.logOutput] at h_ev'; exact h_wt2_nodeId_lt ev' h_ev')
                (by intro nid nd h_nd h_lt out h_out
                    dsimp [w_log, World.logOutput] at h_nd
                    obtain ⟨nd₀, h_nd₀, h_inp, h_outp⟩ := simFoldl_inputs_preserved
                      (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
                      t1 t2 pos' in1 in2 t2 nid nd h_nd
                    rw [h_outp] at h_out
                    have h_in2_eq : in2 = (buildChain World.empty "A" c1).2.nextId := by
                      dsimp [in2]; simp [buildChain, buildChainPre, World.addNode]
                    have h_lt' : nid < (buildChain World.empty "A" c1).2.nextId := by rw [← h_in2_eq]; exact h_lt
                    have h_old := buildChain_getNode_old (buildChain World.empty "A" c1).2 "B" c2 nid h_lt'
                    have h_nd₀' : (buildChain World.empty "A" c1).2.getNode nid = some nd₀ := by rwa [← h_old]
                    dsimp [buildChain] at h_nd₀'
                    have h_out₀ := connectChain_outputs_subset
                      (buildChainPre World.empty "A" c1).2.2 (buildChainPre World.empty "A" c1).2.1
                      nid nd₀ h_nd₀' out h_out
                    cases h_out₀ with
                    | inl h_mem =>
                      have h_lt_out := buildChainPre_chainIds_lt_nextId World.empty "A" c1 out h_mem
                      have h_nextId : (buildChainPre World.empty "A" c1).2.1.nextId =
                          (buildChain World.empty "A" c1).2.nextId := by dsimp [buildChain]; simp [connectChain_nextId]
                      rwa [h_in2_eq, ← h_nextId]
                    | inr h_mem =>
                      obtain ⟨nd₁, h_nd₁, h_out₁⟩ := h_mem
                      have h_empty := buildChainPre_empty_outputs "A" c1 nid nd₁ h_nd₁
                      rw [h_empty] at h_out₁; cases h_out₁)
                (by intro nid nd h_nd d p h_kind; dsimp [w_log, World.logOutput] at h_nd; exact h_delay_w nid nd h_nd d p h_kind)
            have h_nid_lt : nid < in2 := by rw [← h_node]; exact h_all ev h_ev
            obtain ⟨nd₀, h_nd₀, h_inp_eq, h_out_eq⟩ := processNEvents_inputs_preserved w_log pos nid nd h_nd
            dsimp [w_log, World.logOutput] at h_nd₀
            obtain ⟨nd₁, h_nd₁, h_inp₁, h_out₁⟩ := simFoldl_inputs_preserved
              (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
              t1 t2 pos' in1 in2 t2 nid nd₀ h_nd₀
            have h_in2_eq : in2 = (buildChain World.empty "A" c1).2.nextId := by
              dsimp [in2]; simp [buildChain, buildChainPre, World.addNode]
            have h_lt' : nid < (buildChain World.empty "A" c1).2.nextId := by rw [← h_in2_eq]; exact h_nid_lt
            have h_old := buildChain_getNode_old (buildChain World.empty "A" c1).2 "B" c2 nid h_lt'
            have h_nd₁' : (buildChain World.empty "A" c1).2.getNode nid = some nd₁ := by rwa [← h_old]
            dsimp [buildChain] at h_nd₁'
            rw [h_out_eq, h_out₁] at h_mem_out
            have h_out₀ := connectChain_outputs_subset
              (buildChainPre World.empty "A" c1).2.2 (buildChainPre World.empty "A" c1).2.1
              nid nd₁ h_nd₁' out_id h_mem_out
            cases h_out₀ with
            | inl h_mem =>
              have h_lt_out := buildChainPre_chainIds_lt_nextId World.empty "A" c1 out_id h_mem
              have h_nextId : (buildChainPre World.empty "A" c1).2.1.nextId =
                  (buildChain World.empty "A" c1).2.nextId := by dsimp [buildChain]; simp [connectChain_nextId]
              rw [h_nextId, ← h_in2_eq] at h_lt_out; omega
            | inr h_mem =>
              obtain ⟨nd₂, h_nd₂, h_out₂⟩ := h_mem
              have h_empty := buildChainPre_empty_outputs "A" c1 nid nd₂ h_nd₂
              rw [h_empty] at h_out₂; cases h_out₂
          · -- h_no_output: in2's outputs aren't output nodes
            intro nd h_nd out_id h_mem_out nd_out h_nd_out name hk
            obtain ⟨nd₀, h_nd₀, _, h_outp₀⟩ := processNEvents_inputs_preserved w_log pos in2 nd h_nd
            obtain ⟨nd_out₀, h_nd_out₀, _, _⟩ := processNEvents_inputs_preserved w_log pos out_id nd_out h_nd_out
            obtain ⟨nd_out₁, h_nd_out₁, h_kind₁⟩ := processNEvents_kind_preserved w_log pos out_id nd_out h_nd_out
            have h_nd₀_wt2 : w_t₂.getNode in2 = some nd₀ := by
              dsimp [w_log] at h_nd₀; rwa [World.logOutput_getNode] at h_nd₀
            have h_nd_out₀_wt2 : w_t₂.getNode out_id = some nd_out₀ := by
              dsimp [w_log] at h_nd_out₀; rwa [World.logOutput_getNode] at h_nd_out₀
            have h_no := w_t2_in2_outputs_not_output c1 c2 t1 t2 pos' nd₀ h_nd₀_wt2 out_id
              (by rwa [← h_outp₀]) nd_out₀ h_nd_out₀_wt2 name
            have h_nd_out_eq : nd_out₀ = nd_out₁ :=
              Option.some.inj (h_nd_out₀.symm.trans h_nd_out₁)
            have h_contra : nd_out₀.kind = .output name := by
              rw [h_nd_out_eq]
              exact h_kind₁.symm.trans hk
            exact h_no h_contra
          · -- h_delay
            intro nid nd h_nd d p h_kind
            obtain ⟨nd₀, h_nd₀, h_kind_eq⟩ := processNEvents_kind_preserved w_log pos nid nd h_nd
            rw [h_kind_eq] at h_kind
            dsimp [w_log, World.logOutput] at h_nd₀
            exact h_delay_w nid nd₀ h_nd₀ d p h_kind
        have h_comm_log_pos' : ((processNEvents w_log pos').setInput in2 15).stepUntilNextTick.outputLog =
            ((processNEvents w_log pos').stepUntilNextTick.setInput in2 15).outputLog := by
          apply setInput_stepUntilNextTick_comm_outputLog
          · intro ev h_ev h_tick
            have h_all : ∀ ev ∈ (processNEvents w_log pos').events, ev.nodeId < in2 :=
              processNEvents_nodeId_lt w_log pos' in2
                (by intro ev' h_ev'; dsimp [w_log, World.logOutput] at h_ev'; exact h_wt2_nodeId_lt ev' h_ev')
                (by intro nid nd h_nd h_lt out h_out
                    dsimp [w_log, World.logOutput] at h_nd
                    obtain ⟨nd₀, h_nd₀, h_inp, h_outp⟩ := simFoldl_inputs_preserved
                      (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
                      t1 t2 pos' in1 in2 t2 nid nd h_nd
                    rw [h_outp] at h_out
                    have h_in2_eq : in2 = (buildChain World.empty "A" c1).2.nextId := by
                      dsimp [in2]; simp [buildChain, buildChainPre, World.addNode]
                    have h_lt' : nid < (buildChain World.empty "A" c1).2.nextId := by rw [← h_in2_eq]; exact h_lt
                    have h_old := buildChain_getNode_old (buildChain World.empty "A" c1).2 "B" c2 nid h_lt'
                    have h_nd₀' : (buildChain World.empty "A" c1).2.getNode nid = some nd₀ := by rwa [← h_old]
                    dsimp [buildChain] at h_nd₀'
                    have h_out₀ := connectChain_outputs_subset
                      (buildChainPre World.empty "A" c1).2.2 (buildChainPre World.empty "A" c1).2.1
                      nid nd₀ h_nd₀' out h_out
                    cases h_out₀ with
                    | inl h_mem =>
                      have h_lt_out := buildChainPre_chainIds_lt_nextId World.empty "A" c1 out h_mem
                      have h_nextId : (buildChainPre World.empty "A" c1).2.1.nextId =
                          (buildChain World.empty "A" c1).2.nextId := by dsimp [buildChain]; simp [connectChain_nextId]
                      rwa [h_in2_eq, ← h_nextId]
                    | inr h_mem =>
                      obtain ⟨nd₁, h_nd₁, h_out₁⟩ := h_mem
                      have h_empty := buildChainPre_empty_outputs "A" c1 nid nd₁ h_nd₁
                      rw [h_empty] at h_out₁; cases h_out₁)
                (by intro nid nd h_nd d p h_kind; dsimp [w_log, World.logOutput] at h_nd; exact h_delay_w nid nd h_nd d p h_kind)
            have h_lt := h_all ev h_ev
            omega
          · intro nid nd h_nd ⟨ev, h_ev, h_ev_tick, h_node⟩
            have h_all : ∀ ev ∈ (processNEvents w_log pos').events, ev.nodeId < in2 :=
              processNEvents_nodeId_lt w_log pos' in2
                (by intro ev' h_ev'; dsimp [w_log, World.logOutput] at h_ev'; exact h_wt2_nodeId_lt ev' h_ev')
                (by intro nid nd h_nd h_lt out h_out
                    dsimp [w_log, World.logOutput] at h_nd
                    obtain ⟨nd₀, h_nd₀, h_inp, h_outp⟩ := simFoldl_inputs_preserved
                      (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
                      t1 t2 pos' in1 in2 t2 nid nd h_nd
                    rw [h_outp] at h_out
                    have h_in2_eq : in2 = (buildChain World.empty "A" c1).2.nextId := by
                      dsimp [in2]; simp [buildChain, buildChainPre, World.addNode]
                    have h_lt' : nid < (buildChain World.empty "A" c1).2.nextId := by rw [← h_in2_eq]; exact h_lt
                    have h_old := buildChain_getNode_old (buildChain World.empty "A" c1).2 "B" c2 nid h_lt'
                    have h_nd₀' : (buildChain World.empty "A" c1).2.getNode nid = some nd₀ := by rwa [← h_old]
                    dsimp [buildChain] at h_nd₀'
                    have h_out₀ := connectChain_outputs_subset
                      (buildChainPre World.empty "A" c1).2.2 (buildChainPre World.empty "A" c1).2.1
                      nid nd₀ h_nd₀' out h_out
                    cases h_out₀ with
                    | inl h_mem =>
                      have h_lt_out := buildChainPre_chainIds_lt_nextId World.empty "A" c1 out h_mem
                      have h_nextId : (buildChainPre World.empty "A" c1).2.1.nextId =
                          (buildChain World.empty "A" c1).2.nextId := by dsimp [buildChain]; simp [connectChain_nextId]
                      rwa [h_in2_eq, ← h_nextId]
                    | inr h_mem =>
                      obtain ⟨nd₁, h_nd₁, h_out₁⟩ := h_mem
                      have h_empty := buildChainPre_empty_outputs "A" c1 nid nd₁ h_nd₁
                      rw [h_empty] at h_out₁; cases h_out₁)
                (by intro nid nd h_nd d p h_kind; dsimp [w_log, World.logOutput] at h_nd; exact h_delay_w nid nd h_nd d p h_kind)
            have h_nid_lt : nid < in2 := by rw [← h_node]; exact h_all ev h_ev
            obtain ⟨nd₀, h_nd₀, h_inp_eq, h_out_eq⟩ := processNEvents_inputs_preserved w_log pos' nid nd h_nd
            dsimp [w_log, World.logOutput] at h_nd₀
            obtain ⟨nd₁, h_nd₁, h_inp₁, h_out₁⟩ := simFoldl_inputs_preserved
              (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
              t1 t2 pos' in1 in2 t2 nid nd₀ h_nd₀
            have h_in2_eq : in2 = (buildChain World.empty "A" c1).2.nextId := by
              dsimp [in2]; simp [buildChain, buildChainPre, World.addNode]
            have h_lt' : nid < (buildChain World.empty "A" c1).2.nextId := by rw [← h_in2_eq]; exact h_nid_lt
            have h_old := buildChain_getNode_old (buildChain World.empty "A" c1).2 "B" c2 nid h_lt'
            have h_nd₁' : (buildChain World.empty "A" c1).2.getNode nid = some nd₁ := by rwa [← h_old]
            dsimp [buildChain] at h_nd₁'
            intro h_in2_in
            rw [h_inp_eq, h_inp₁] at h_in2_in
            have h_inp₂ := connectChain_inputs_mem
              (buildChainPre World.empty "A" c1).2.2 (buildChainPre World.empty "A" c1).2.1
              nid nd₁ h_nd₁' in2 h_in2_in
            cases h_inp₂ with
            | inl h_mem =>
              have h_lt_in2 := buildChainPre_chainIds_lt_nextId World.empty "A" c1 in2 h_mem
              have h_nextId : (buildChainPre World.empty "A" c1).2.1.nextId =
                  (buildChain World.empty "A" c1).2.nextId := by dsimp [buildChain]; simp [connectChain_nextId]
              rw [h_in2_eq, ← h_nextId] at h_lt_in2; omega
            | inr h_mem =>
              obtain ⟨nd₂, h_nd₂, h_inp₂⟩ := h_mem
              have h_empty := buildChainPre_empty_inputs "A" c1 nid nd₂ h_nd₂
              rw [h_empty] at h_inp₂; cases h_inp₂
          · -- h_sep_out for pos'
            intro nid nd h_nd ⟨ev, h_ev, h_ev_tick, h_node⟩ out_id h_mem_out nd_out h_nd_out
            have h_all : ∀ ev ∈ (processNEvents w_log pos').events, ev.nodeId < in2 :=
              processNEvents_nodeId_lt w_log pos' in2
                (by intro ev' h_ev'; dsimp [w_log, World.logOutput] at h_ev'; exact h_wt2_nodeId_lt ev' h_ev')
                (by intro nid nd h_nd h_lt out h_out
                    dsimp [w_log, World.logOutput] at h_nd
                    obtain ⟨nd₀, h_nd₀, h_inp, h_outp⟩ := simFoldl_inputs_preserved
                      (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
                      t1 t2 pos' in1 in2 t2 nid nd h_nd
                    rw [h_outp] at h_out
                    have h_in2_eq : in2 = (buildChain World.empty "A" c1).2.nextId := by
                      dsimp [in2]; simp [buildChain, buildChainPre, World.addNode]
                    have h_lt' : nid < (buildChain World.empty "A" c1).2.nextId := by rw [← h_in2_eq]; exact h_lt
                    have h_old := buildChain_getNode_old (buildChain World.empty "A" c1).2 "B" c2 nid h_lt'
                    have h_nd₀' : (buildChain World.empty "A" c1).2.getNode nid = some nd₀ := by rwa [← h_old]
                    dsimp [buildChain] at h_nd₀'
                    have h_out₀ := connectChain_outputs_subset
                      (buildChainPre World.empty "A" c1).2.2 (buildChainPre World.empty "A" c1).2.1
                      nid nd₀ h_nd₀' out h_out
                    cases h_out₀ with
                    | inl h_mem =>
                      have h_lt_out := buildChainPre_chainIds_lt_nextId World.empty "A" c1 out h_mem
                      have h_nextId : (buildChainPre World.empty "A" c1).2.1.nextId =
                          (buildChain World.empty "A" c1).2.nextId := by dsimp [buildChain]; simp [connectChain_nextId]
                      rwa [h_in2_eq, ← h_nextId]
                    | inr h_mem =>
                      obtain ⟨nd₁, h_nd₁, h_out₁⟩ := h_mem
                      have h_empty := buildChainPre_empty_outputs "A" c1 nid nd₁ h_nd₁
                      rw [h_empty] at h_out₁; cases h_out₁)
                (by intro nid nd h_nd d p h_kind; dsimp [w_log, World.logOutput] at h_nd; exact h_delay_w nid nd h_nd d p h_kind)
            have h_nid_lt : nid < in2 := by rw [← h_node]; exact h_all ev h_ev
            obtain ⟨nd₀, h_nd₀, h_inp_eq, h_out_eq⟩ := processNEvents_inputs_preserved w_log pos' nid nd h_nd
            dsimp [w_log, World.logOutput] at h_nd₀
            obtain ⟨nd₁, h_nd₁, h_inp₁, h_out₁⟩ := simFoldl_inputs_preserved
              (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
              t1 t2 pos' in1 in2 t2 nid nd₀ h_nd₀
            have h_in2_eq : in2 = (buildChain World.empty "A" c1).2.nextId := by
              dsimp [in2]; simp [buildChain, buildChainPre, World.addNode]
            have h_lt' : nid < (buildChain World.empty "A" c1).2.nextId := by rw [← h_in2_eq]; exact h_nid_lt
            have h_old := buildChain_getNode_old (buildChain World.empty "A" c1).2 "B" c2 nid h_lt'
            have h_nd₁' : (buildChain World.empty "A" c1).2.getNode nid = some nd₁ := by rwa [← h_old]
            dsimp [buildChain] at h_nd₁'
            rw [h_out_eq, h_out₁] at h_mem_out
            have h_out_lt : out_id < in2 := by
              have h_out₀ := connectChain_outputs_subset
                (buildChainPre World.empty "A" c1).2.2 (buildChainPre World.empty "A" c1).2.1
                nid nd₁ h_nd₁' out_id h_mem_out
              cases h_out₀ with
              | inl h_mem =>
                have h_lt_out := buildChainPre_chainIds_lt_nextId World.empty "A" c1 out_id h_mem
                have h_nextId : (buildChainPre World.empty "A" c1).2.1.nextId =
                    (buildChain World.empty "A" c1).2.nextId := by dsimp [buildChain]; simp [connectChain_nextId]
                rwa [h_in2_eq, ← h_nextId]
              | inr h_mem =>
                obtain ⟨nd₂, h_nd₂, h_out₂⟩ := h_mem
                have h_empty := buildChainPre_empty_outputs "A" c1 nid nd₂ h_nd₂
                rw [h_empty] at h_out₂; cases h_out₂
            obtain ⟨nd_out₀, h_nd_out₀, h_inp_out₀, h_out_out₀⟩ := processNEvents_inputs_preserved w_log pos' out_id nd_out h_nd_out
            have h_nd_out_wt2 : w_t₂.getNode out_id = some nd_out₀ := by
              dsimp [w_log, World.logOutput] at h_nd_out₀ ⊢
              have h_nodes : w_t₂.nodes = (w_log).nodes := by dsimp [w_log]
              dsimp [World.getNode] at h_nd_out₀ ⊢; rw [h_nodes]; exact h_nd_out₀
            obtain ⟨nd_out₁, h_nd_out₁, h_inp_out, h_out_out⟩ := simFoldl_inputs_preserved
              (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
              t1 t2 pos' in1 in2 t2 out_id nd_out₀ h_nd_out_wt2
            have h_lt_out' : out_id < (buildChain World.empty "A" c1).2.nextId := by rw [← h_in2_eq]; exact h_out_lt
            have h_old_out := buildChain_getNode_old (buildChain World.empty "A" c1).2 "B" c2 out_id h_lt_out'
            have h_nd_out₁' : (buildChain World.empty "A" c1).2.getNode out_id = some nd_out₁ := by rwa [← h_old_out]
            dsimp [buildChain] at h_nd_out₁'
            intro h_in2_in
            rw [h_inp_out₀, h_inp_out] at h_in2_in
            have h_inp₂ := connectChain_inputs_mem
              (buildChainPre World.empty "A" c1).2.2 (buildChainPre World.empty "A" c1).2.1
              out_id nd_out₁ h_nd_out₁' in2 h_in2_in
            cases h_inp₂ with
            | inl h_mem =>
              have h_lt_in2 := buildChainPre_chainIds_lt_nextId World.empty "A" c1 in2 h_mem
              have h_nextId : (buildChainPre World.empty "A" c1).2.1.nextId =
                  (buildChain World.empty "A" c1).2.nextId := by dsimp [buildChain]; simp [connectChain_nextId]
              rw [h_in2_eq, ← h_nextId] at h_lt_in2; omega
            | inr h_mem =>
              obtain ⟨nd₂, h_nd₂, h_inp₂⟩ := h_mem
              have h_empty := buildChainPre_empty_inputs "A" c1 out_id nd₂ h_nd₂
              rw [h_empty] at h_inp₂; cases h_inp₂
          · -- h_outputs_ne for pos'
            intro nid nd h_nd ⟨ev, h_ev, h_ev_tick, h_node⟩ out_id h_mem_out
            have h_all : ∀ ev ∈ (processNEvents w_log pos').events, ev.nodeId < in2 :=
              processNEvents_nodeId_lt w_log pos' in2
                (by intro ev' h_ev'; dsimp [w_log, World.logOutput] at h_ev'; exact h_wt2_nodeId_lt ev' h_ev')
                (by intro nid nd h_nd h_lt out h_out
                    dsimp [w_log, World.logOutput] at h_nd
                    obtain ⟨nd₀, h_nd₀, h_inp, h_outp⟩ := simFoldl_inputs_preserved
                      (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
                      t1 t2 pos' in1 in2 t2 nid nd h_nd
                    rw [h_outp] at h_out
                    have h_in2_eq : in2 = (buildChain World.empty "A" c1).2.nextId := by
                      dsimp [in2]; simp [buildChain, buildChainPre, World.addNode]
                    have h_lt' : nid < (buildChain World.empty "A" c1).2.nextId := by rw [← h_in2_eq]; exact h_lt
                    have h_old := buildChain_getNode_old (buildChain World.empty "A" c1).2 "B" c2 nid h_lt'
                    have h_nd₀' : (buildChain World.empty "A" c1).2.getNode nid = some nd₀ := by rwa [← h_old]
                    dsimp [buildChain] at h_nd₀'
                    have h_out₀ := connectChain_outputs_subset
                      (buildChainPre World.empty "A" c1).2.2 (buildChainPre World.empty "A" c1).2.1
                      nid nd₀ h_nd₀' out h_out
                    cases h_out₀ with
                    | inl h_mem =>
                      have h_lt_out := buildChainPre_chainIds_lt_nextId World.empty "A" c1 out h_mem
                      have h_nextId : (buildChainPre World.empty "A" c1).2.1.nextId =
                          (buildChain World.empty "A" c1).2.nextId := by dsimp [buildChain]; simp [connectChain_nextId]
                      rwa [h_in2_eq, ← h_nextId]
                    | inr h_mem =>
                      obtain ⟨nd₁, h_nd₁, h_out₁⟩ := h_mem
                      have h_empty := buildChainPre_empty_outputs "A" c1 nid nd₁ h_nd₁
                      rw [h_empty] at h_out₁; cases h_out₁)
                (by intro nid nd h_nd d p h_kind; dsimp [w_log, World.logOutput] at h_nd; exact h_delay_w nid nd h_nd d p h_kind)
            have h_nid_lt : nid < in2 := by rw [← h_node]; exact h_all ev h_ev
            obtain ⟨nd₀, h_nd₀, h_inp_eq, h_out_eq⟩ := processNEvents_inputs_preserved w_log pos' nid nd h_nd
            dsimp [w_log, World.logOutput] at h_nd₀
            obtain ⟨nd₁, h_nd₁, h_inp₁, h_out₁⟩ := simFoldl_inputs_preserved
              (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
              t1 t2 pos' in1 in2 t2 nid nd₀ h_nd₀
            have h_in2_eq : in2 = (buildChain World.empty "A" c1).2.nextId := by
              dsimp [in2]; simp [buildChain, buildChainPre, World.addNode]
            have h_lt' : nid < (buildChain World.empty "A" c1).2.nextId := by rw [← h_in2_eq]; exact h_nid_lt
            have h_old := buildChain_getNode_old (buildChain World.empty "A" c1).2 "B" c2 nid h_lt'
            have h_nd₁' : (buildChain World.empty "A" c1).2.getNode nid = some nd₁ := by rwa [← h_old]
            dsimp [buildChain] at h_nd₁'
            rw [h_out_eq, h_out₁] at h_mem_out
            have h_out₀ := connectChain_outputs_subset
              (buildChainPre World.empty "A" c1).2.2 (buildChainPre World.empty "A" c1).2.1
              nid nd₁ h_nd₁' out_id h_mem_out
            cases h_out₀ with
            | inl h_mem =>
              have h_lt_out := buildChainPre_chainIds_lt_nextId World.empty "A" c1 out_id h_mem
              have h_nextId : (buildChainPre World.empty "A" c1).2.1.nextId =
                  (buildChain World.empty "A" c1).2.nextId := by dsimp [buildChain]; simp [connectChain_nextId]
              rw [h_nextId, ← h_in2_eq] at h_lt_out; omega
            | inr h_mem =>
              obtain ⟨nd₂, h_nd₂, h_out₂⟩ := h_mem
              have h_empty := buildChainPre_empty_outputs "A" c1 nid nd₂ h_nd₂
              rw [h_empty] at h_out₂; cases h_out₂
          · -- h_no_output for pos'
            intro nd h_nd out_id h_mem_out nd_out h_nd_out name hk
            obtain ⟨nd₀, h_nd₀, _, h_outp₀⟩ := processNEvents_inputs_preserved w_log pos' in2 nd h_nd
            obtain ⟨nd_out₀, h_nd_out₀, _, _⟩ := processNEvents_inputs_preserved w_log pos' out_id nd_out h_nd_out
            obtain ⟨nd_out₁, h_nd_out₁, h_kind₁⟩ := processNEvents_kind_preserved w_log pos' out_id nd_out h_nd_out
            have h_nd₀_wt2 : w_t₂.getNode in2 = some nd₀ := by
              dsimp [w_log] at h_nd₀; rwa [World.logOutput_getNode] at h_nd₀
            have h_nd_out₀_wt2 : w_t₂.getNode out_id = some nd_out₀ := by
              dsimp [w_log] at h_nd_out₀; rwa [World.logOutput_getNode] at h_nd_out₀
            have h_no := w_t2_in2_outputs_not_output c1 c2 t1 t2 pos' nd₀ h_nd₀_wt2 out_id
              (by rwa [← h_outp₀]) nd_out₀ h_nd_out₀_wt2 name
            have h_nd_out_eq : nd_out₀ = nd_out₁ :=
              Option.some.inj (h_nd_out₀.symm.trans h_nd_out₁)
            have h_contra : nd_out₀.kind = .output name := by
              rw [h_nd_out_eq]
              exact h_kind₁.symm.trans hk
            exact h_no h_contra
          · -- h_delay for pos'
            intro nid nd h_nd d p h_kind
            obtain ⟨nd₀, h_nd₀, h_kind_eq⟩ := processNEvents_kind_preserved w_log pos' nid nd h_nd
            rw [h_kind_eq] at h_kind
            dsimp [w_log, World.logOutput] at h_nd₀
            exact h_delay_w nid nd₀ h_nd₀ d p h_kind
        rw [h_comm_log_pos, h_comm_log_pos']
        rw [processNEvents_stepUntilNextTick_eq, processNEvents_stepUntilNextTick_eq]

