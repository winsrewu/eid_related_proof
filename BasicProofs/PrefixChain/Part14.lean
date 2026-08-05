import BasicProofs.PrefixChain.Part13


open BasicRedstoneSim

/-- `stepUntilNextTick` preserves existence of a node. -/
theorem World.stepUntilNextTick_getNode_some (w : World) (nid : Nat) :
    (∃ nd, w.getNode nid = some nd) → ∃ nd', w.stepUntilNextTick.getNode nid = some nd' := by
  revert nid
  induction w using World.stepUntilNextTick.induct with
  | case1 w h_step =>
    intro nid h
    rw [stepUntilNextTick_of_step_none w h_step]
    rcases h with ⟨nd, hnd⟩
    exact ⟨nd, hnd⟩
  | case2 w w' h_step ih =>
    intro nid h
    obtain ⟨nd₁, h₁⟩ := World.step_getNode_some w nid h w' h_step
    have h_sunt : w.stepUntilNextTick = w'.stepUntilNextTick := by
      rw [World.stepUntilNextTick, h_step]
    rw [h_sunt]
    exact ih nid ⟨nd₁, h₁⟩

/-- `processNEvents` preserves existence of a node. -/
theorem processNEvents_getNode_some (w : World) (n nid : Nat) :
    (∃ nd, w.getNode nid = some nd) → ∃ nd', (processNEvents w n).getNode nid = some nd' := by
  induction n generalizing w with
  | zero => intro h; simpa [processNEvents] using h
  | succ n' ih =>
    intro h
    dsimp [processNEvents]
    cases h_step : w.step with
    | none =>
      simpa [h_step] using h
    | some w' =>
      simp []
      obtain ⟨nd₁, h₁⟩ := World.step_getNode_some w nid h w' h_step
      exact ih w' ⟨nd₁, h₁⟩

/-- `simBody` preserves existence of a node. -/
theorem simBody_getNode_some (t1 t2 pos in1 in2 : Nat) (w : World) (i nid : Nat) :
    (∃ nd, w.getNode nid = some nd) → ∃ nd', (simBody t1 t2 pos in1 in2 w i).getNode nid = some nd' := by
  intro h
  dsimp (config := { zeta := true }) [simBody]
  have hL : ∃ nd, (w.logOutput s!"tick {w.tick}").getNode nid = some nd := by
    rcases h with ⟨nd, hn⟩; exact ⟨nd, by rw [World.logOutput_getNode]; exact hn⟩
  split_ifs with h_t1 h_t2
  · -- t1, t2: logOutput + setInput in1 + processNEvents pos + setInput in2 + stepUntilNextTick
    set wL := w.logOutput s!"tick {w.tick}"
    set wA := wL.setInput in1 15
    set wB := processNEvents wA pos
    set wC := wB.setInput in2 15
    obtain ⟨ndA, hnA⟩ := World.setInput_getNode_some wL in1 nid 15 hL
    obtain ⟨ndB, hnB⟩ := processNEvents_getNode_some wA pos nid ⟨ndA, hnA⟩
    obtain ⟨ndC, hnC⟩ := World.setInput_getNode_some wB in2 nid 15 ⟨ndB, hnB⟩
    exact World.stepUntilNextTick_getNode_some wC nid ⟨ndC, hnC⟩
  · -- t1, not t2: logOutput + setInput in1 + stepUntilNextTick
    set wL := w.logOutput s!"tick {w.tick}"
    set wA := wL.setInput in1 15
    obtain ⟨ndA, hnA⟩ := World.setInput_getNode_some wL in1 nid 15 hL
    exact World.stepUntilNextTick_getNode_some wA nid ⟨ndA, hnA⟩
  · -- not t1, t2: logOutput + processNEvents pos + setInput in2 + stepUntilNextTick
    set wL := w.logOutput s!"tick {w.tick}"
    set wB := processNEvents wL pos
    set wC := wB.setInput in2 15
    obtain ⟨ndB, hnB⟩ := processNEvents_getNode_some wL pos nid hL
    obtain ⟨ndC, hnC⟩ := World.setInput_getNode_some wB in2 nid 15 ⟨ndB, hnB⟩
    exact World.stepUntilNextTick_getNode_some wC nid ⟨ndC, hnC⟩
  · -- not t1, not t2: logOutput + stepUntilNextTick
    set wL := w.logOutput s!"tick {w.tick}"
    exact World.stepUntilNextTick_getNode_some wL nid hL

/-- `simFoldl` preserves existence of a node. -/
theorem simFoldl_getNode_some (w : World) (t1 t2 pos in1 in2 n nid : Nat) :
    (∃ nd, w.getNode nid = some nd) →
    ∃ nd', ((List.range n).foldl (simBody t1 t2 pos in1 in2) w).getNode nid = some nd' := by
  induction n with
  | zero => intro h; simpa [List.range_zero, List.foldl_nil] using h
  | succ n' ih =>
    intro h
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    obtain ⟨nd₁, h₁⟩ := ih h
    exact simBody_getNode_some t1 t2 pos in1 in2
      ((List.range n').foldl (simBody t1 t2 pos in1 in2) w) n' nid ⟨nd₁, h₁⟩

/-- `connectChain` preserves existence of a node. -/
theorem connectChain_getNode_some (w : World) (ids : List Nat) (nid : Nat) :
    (∃ nd, w.getNode nid = some nd) → ∃ nd', (connectChain w ids).getNode nid = some nd' := by
  intro h
  dsimp [connectChain]
  let stepFn : World → Nat × Nat → World := fun w₀ p =>
    (w₀.updateNode p.2 (fun nd => { nd with inputs := nd.inputs ++ [p.1] })).updateNode p.1
      (fun nd => { nd with outputs := nd.outputs ++ [p.2] })
  have h_step : ∀ (ps : List (Nat × Nat)) (w' : World),
      (∃ nd, w'.getNode nid = some nd) →
      ∃ nd', (ps.foldl stepFn w').getNode nid = some nd' := by
    intro ps w' h'
    revert h'
    induction ps generalizing w' with
    | nil => intro h'; simpa [stepFn] using h'
    | cons p ps ih =>
      intro h'
      rcases p with ⟨prev, curr⟩
      simp only [List.foldl_cons]
      have h₁ : ∃ nd, (stepFn w' (prev, curr)).getNode nid = some nd := by
        dsimp [stepFn]
        obtain ⟨nd₁, hn₁⟩ := World.updateNode_getNode_some w' curr nid
          (fun nd => { nd with inputs := nd.inputs ++ [prev] }) h'
        obtain ⟨nd₂, hn₂⟩ := World.updateNode_getNode_some
          (w'.updateNode curr (fun nd => { nd with inputs := nd.inputs ++ [prev] })) prev nid
          (fun nd => { nd with outputs := nd.outputs ++ [curr] }) ⟨nd₁, hn₁⟩
        exact ⟨nd₂, hn₂⟩
      exact ih (stepFn w' (prev, curr)) h₁
  exact h_step (ids.zip (ids.drop 1)) w h

/-- `setInput` preserves the `kind` of every node. -/
theorem setInput_map_kind (w : World) (in2 level : Nat) :
    ∀ nid, ((w.setInput in2 level).getNode nid).map (·.kind) = (w.getNode nid).map (·.kind) := by
  intro nid
  dsimp [World.setInput]
  rw [World.notifyOutputs_getNode]
  by_cases h : nid = in2
  · subst h
    cases h_gn : w.getNode nid with
    | none =>
      have h_upd : (w.updateNode nid (fun nd => { nd with sigLevel := level })).getNode nid = none :=
        World.updateNode_getNode_none w nid (fun nd => { nd with sigLevel := level }) h_gn
      simp [h_upd]
    | some nd =>
      have h_upd : (w.updateNode nid (fun nd => { nd with sigLevel := level })).getNode nid =
          some ({ nd with sigLevel := level } : NodeData) :=
        World.updateNode_getNode_eq w nid (fun nd => { nd with sigLevel := level }) nd h_gn
      simp [h_upd]
  · exact congrArg (Option.map (·.kind)) (World.updateNode_getNode_ne w in2 nid _ (Ne.symm h))

/-- `onScheduledTick id` preserves `getNode nid` for `nid ≠ id`. -/
theorem World.onScheduledTick_getNode_ne (w : World) (id nid : Nat) (h : nid ≠ id) :
    (w.onScheduledTick id).getNode nid = w.getNode nid := by
  cases h_gn : w.getNode id with
  | none => simp [World.onScheduledTick, h_gn]
  | some nd =>
    cases hk : nd.kind with
    | input => simp [World.onScheduledTick, h_gn, hk]
    | output name => simp [World.onScheduledTick, h_gn, hk]
    | observer =>
      simp (config := { zeta := true }) [World.onScheduledTick, h_gn, hk]
      rw [World.notifyOutputs_getNode]
      exact World.updateNode_getNode_ne w id nid _ (Ne.symm h)
    | repeater d p =>
      simp (config := { zeta := true }) [World.onScheduledTick, h_gn, hk]
      rw [World.notifyOutputs_getNode]
      exact World.updateNode_getNode_ne w id nid _ (Ne.symm h)

/-- In `buildChainPre w name c`, any node with id at least `w.nextId + 2` is not
    an observer (it is a repeater or the output node). -/
theorem buildChainPre_not_observer_ge2 (w : World) (name : String) (c : ChainSpec)
    (h_ids : ∀ p ∈ w.nodes, p.1 < w.nextId) :
    ∀ nid nd, (buildChainPre w name c).2.1.getNode nid = some nd →
      w.nextId + 2 ≤ nid → nd.kind ≠ .observer := by
  intro nid nd h_gn h_ge
  dsimp (config := { zeta := true }) [buildChainPre] at h_gn
  set w₁ := (w.addNode { kind := .input, sigLevel := 0, inputs := [], outputs := [] }).2
  set w₂ := (w₁.addNode { kind := .observer, sigLevel := 0, inputs := [], outputs := [] }).2
  set w₃ := (c.middleDelays.foldl repFoldlStep ([], w₂)).2
  set w₄ := (w₃.addNode { kind := .repeater c.lastDelay (-1), sigLevel := 0, inputs := [], outputs := [] }).2
  set w₅ := (w₄.addNode { kind := .output name, sigLevel := 0, inputs := [], outputs := [] }).2
  have h_ids_w₂ : ∀ p ∈ w₂.nodes, p.1 < w₂.nextId :=
    World.addNode_ids_lt_nextId w₁
      ({ kind := .observer, sigLevel := 0, inputs := [], outputs := [] } : NodeData)
      (World.addNode_ids_lt_nextId w
        ({ kind := .input, sigLevel := 0, inputs := [], outputs := [] } : NodeData) h_ids)
  have h_w2_nextId : w₂.nextId = w.nextId + 2 := by dsimp [w₂, w₁, World.addNode]
  have h_w3_nextId : w₃.nextId = w.nextId + 2 + c.middleDelays.length := by
    dsimp [w₃]; rw [foldl_repFoldlStep_nextId_eq, h_w2_nextId]
  have h_w4_nextId : w₄.nextId = w.nextId + 3 + c.middleDelays.length := by
    dsimp [w₄, World.addNode]; rw [h_w3_nextId]; omega
  have h_w5_nextId : w₅.nextId = w.nextId + 4 + c.middleDelays.length := by
    dsimp [w₅, World.addNode]; rw [h_w4_nextId]; omega
  by_cases h_lt3 : nid < w₃.nextId
  · -- nid is a middle repeater
    have h_j : nid - w₂.nextId < c.middleDelays.length := by
      rw [h_w3_nextId] at h_lt3; rw [h_w2_nextId]; omega
    have h_rep := foldl_repFoldlStep_getNode_rep c.middleDelays w₂ h_ids_w₂
      (nid - w₂.nextId) h_j
    have h_gn3 : w₃.getNode nid = some nd := by
      have h54 : w₅.getNode nid = w₄.getNode nid :=
        World.addNode_getNode_old w₄
          ({ kind := .output name, sigLevel := 0, inputs := [], outputs := [] } : NodeData)
          nid (by rw [h_w4_nextId]; omega)
      have h43 : w₄.getNode nid = w₃.getNode nid :=
        World.addNode_getNode_old w₃
          ({ kind := .repeater c.lastDelay (-1), sigLevel := 0, inputs := [], outputs := [] } : NodeData)
          nid (by omega)
      rw [h54, h43] at h_gn; exact h_gn
    have h_nid_eq : nid = w₂.nextId + (nid - w₂.nextId) := by omega
    rw [← h_nid_eq] at h_rep
    have h_nd_eq : nd = mkRepNode c.middleDelays[nid - w₂.nextId] :=
      Option.some_inj.mp (h_gn3.symm.trans h_rep)
    rw [h_nd_eq]; dsimp [mkRepNode]
    intro h; cases h
  · -- nid ≥ w₃.nextId : last repeater or output node
    have h_ge3 : w₃.nextId ≤ nid := by omega
    by_cases h_lt4 : nid < w₄.nextId
    · -- nid = w₃.nextId : last repeater
      have h_nid_eq : nid = w₃.nextId := by omega
      have h_fresh : w₄.getNode w₃.nextId =
          some { kind := .repeater c.lastDelay (-1), sigLevel := 0, inputs := [], outputs := [] } :=
        World.addNode_getNode_fresh w₃ _ (World.getNode_nextId_none w₃
          (foldl_repFoldlStep_ids_lt_nextId c.middleDelays [] w₂ h_ids_w₂))
      have h_gn4 : w₄.getNode nid = some nd := by
        have h54 : w₅.getNode nid = w₄.getNode nid :=
          World.addNode_getNode_old w₄
            ({ kind := .output name, sigLevel := 0, inputs := [], outputs := [] } : NodeData)
            nid (by rw [h_w4_nextId]; omega)
        rwa [h54] at h_gn
      rw [h_nid_eq] at h_gn4
      have h_nd_eq : nd = { kind := .repeater c.lastDelay (-1), sigLevel := 0, inputs := [], outputs := [] } :=
        Option.some_inj.mp (h_gn4.symm.trans h_fresh)
      rw [h_nd_eq]; intro h; cases h
    · -- nid ≥ w₄.nextId : output node (or out of range)
      have h_ge4 : w₄.nextId ≤ nid := by omega
      by_cases h_lt5 : nid < w₅.nextId
      · have h_nid_eq : nid = w₄.nextId := by omega
        have h_fresh : w₅.getNode w₄.nextId =
            some { kind := .output name, sigLevel := 0, inputs := [], outputs := [] } :=
          World.addNode_getNode_fresh w₄ _ (World.getNode_nextId_none w₄
            (World.addNode_ids_lt_nextId w₃
              ({ kind := .repeater c.lastDelay (-1), sigLevel := 0, inputs := [], outputs := [] } : NodeData)
              (foldl_repFoldlStep_ids_lt_nextId c.middleDelays [] w₂ h_ids_w₂)))
        have h_gn' : w₅.getNode w₄.nextId = some nd := by rwa [h_nid_eq] at h_gn
        have h_nd_eq : nd = { kind := .output name, sigLevel := 0, inputs := [], outputs := [] } :=
          Option.some_inj.mp (h_gn'.symm.trans h_fresh)
        rw [h_nd_eq]; intro h; cases h
      · -- nid ≥ w₅.nextId : no such node, contradiction
        have h_ge5 : w₅.nextId ≤ nid := by omega
        have h_ids_w₅ : ∀ p ∈ w₅.nodes, p.1 < w₅.nextId :=
          World.addNode_ids_lt_nextId w₄
            ({ kind := .output name, sigLevel := 0, inputs := [], outputs := [] } : NodeData)
            (World.addNode_ids_lt_nextId w₃
              ({ kind := .repeater c.lastDelay (-1), sigLevel := 0, inputs := [], outputs := [] } : NodeData)
              (foldl_repFoldlStep_ids_lt_nextId c.middleDelays [] w₂ h_ids_w₂))
        exfalso
        have h_none : w₅.getNode nid = none := by
          dsimp [World.getNode]
          have h : w₅.nodes.find? (fun (nid', _) => nid' == nid) = none := by
            apply List.find?_eq_none.mpr
            intro p h_p
            have h_lt := h_ids_w₅ p h_p
            simp; omega
          simp [h]
        rw [h_none] at h_gn; cases h_gn

/-- In `buildChain w name c`, among nodes with id at least `w.nextId`, the only
    observer is at `w.nextId + 1`. -/
theorem buildChain_observer_ids (w : World) (name : String) (c : ChainSpec)
    (h_ids : ∀ p ∈ w.nodes, p.1 < w.nextId) :
    ∀ nid nd, (buildChain w name c).2.getNode nid = some nd →
      nd.kind = .observer → w.nextId ≤ nid → nid = w.nextId + 1 := by
  intro nid nd h_gn h_obs h_ge
  dsimp [buildChain] at h_gn
  set base := (buildChainPre w name c).2.1
  set chainIds := (buildChainPre w name c).2.2
  obtain ⟨nd₀, h_nd₀, hk⟩ := connectChain_kind_preserved base chainIds nid nd h_gn
  rw [← hk] at h_obs
  by_cases h_lt_base : nid < w.nextId
  · omega
  · by_cases h_ge2 : w.nextId + 2 ≤ nid
    · exfalso
      exact buildChainPre_not_observer_ge2 w name c h_ids nid nd₀ h_nd₀ h_ge2 h_obs
    · have h_le : nid ≤ w.nextId + 1 := by omega
      by_cases h_eq : nid = w.nextId
      · exfalso
        have h_in : base.getNode w.nextId =
            some { kind := .input, sigLevel := 0, inputs := [], outputs := [] } :=
          buildChainPre_getNode_input w name c h_ids
        have h_nd₀_eq : nd₀ = { kind := .input, sigLevel := 0, inputs := [], outputs := [] } := by
          apply Option.some_inj.mp
          rw [← h_nd₀, h_eq]; exact h_in
        rw [h_nd₀_eq] at h_obs; cases h_obs
      · omega

/-- In the two-chain initial world, the only observer nodes are `in1 + 1` and `in2 + 1`. -/
theorem buildChain2_observer_ids (c1 c2 : ChainSpec) :
    let in1 := (buildChain World.empty "A" c1).1
    let in2 := (buildChain (buildChain World.empty "A" c1).2 "B" c2).1
    ∀ nid nd, (buildChain (buildChain World.empty "A" c1).2 "B" c2).2.getNode nid = some nd →
      nd.kind = .observer → nid = in1 + 1 ∨ nid = in2 + 1 := by
  intro in1 in2 nid nd h_gn h_obs
  set c1w := (buildChain World.empty "A" c1).2
  have h_in1_eq : in1 = World.empty.nextId := by
    dsimp [in1]; simp [buildChain, buildChainPre, World.addNode]
  have h_in2_eq : in2 = c1w.nextId := by
    dsimp [in2, c1w]; simp [buildChain, buildChainPre, World.addNode]
  by_cases h_lt : nid < c1w.nextId
  · -- nid is a c1 node
    have h_old := buildChain_getNode_old c1w "B" c2 nid h_lt
    have h_gn1 : c1w.getNode nid = some nd := by rwa [h_old] at h_gn
    have h_c1 := buildChain_observer_ids World.empty "A" c1
      (fun p hp => by simp [World.empty] at hp) nid nd h_gn1 h_obs
      (by dsimp [World.empty]; omega)
    left; rw [h_in1_eq]; exact h_c1
  · -- nid is a c2 node (nid ≥ c1w.nextId)
    have h_ge : c1w.nextId ≤ nid := by omega
    have h_c2 := buildChain_observer_ids c1w "B" c2
      (buildChain_ids_lt_nextId World.empty "A" c1 (fun p hp => by simp [World.empty] at hp))
      nid nd h_gn h_obs h_ge
    right; rw [h_in2_eq]; exact h_c2

/-- In `w_t₂`, an output of a c1 node (id `< in2`, not `in1`) is never an observer. -/
theorem w_t2_c1_outputs_not_observer (c1 c2 : ChainSpec) (t1 t2 pos' : Nat)
    (_ : t1 < t2) :
    let in1 := (buildChain World.empty "A" c1).1
    let in2 := (buildChain (buildChain World.empty "A" c1).2 "B" c2).1
    let w_t₂ := (List.range t2).foldl (simBody t1 t2 pos' in1 in2)
        (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
    ∀ nid, nid < in2 → nid ≠ in1 →
      ∀ nd, w_t₂.getNode nid = some nd → ∀ out_id ∈ nd.outputs,
        ∀ nd_out, w_t₂.getNode out_id = some nd_out → nd_out.kind ≠ .observer := by
  intro in1 in2 w_t₂ nid h_nid_lt h_nid_ne nd h_nd out_id h_out_mem nd_out h_nd_out h_obs
  set W₀ := (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
  set c1w := (buildChain World.empty "A" c1).2
  have h_in2_eq : in2 = c1w.nextId := by
    dsimp [in2, c1w]; simp [buildChain, buildChainPre, World.addNode]
  have h_in1_eq : in1 = World.empty.nextId := by
    dsimp [in1]; simp [buildChain, buildChainPre, World.addNode]
  -- outputs preserved back to W₀
  obtain ⟨nd₀, h_nd₀, _, h_outputs_eq⟩ :=
    simFoldl_inputs_preserved W₀ t1 t2 pos' in1 in2 t2 nid nd h_nd
  have h_out_mem₀ : out_id ∈ nd₀.outputs := by rwa [← h_outputs_eq]
  -- nid is a c1 node, so W₀.getNode nid = c1w.getNode nid
  have h_W0_c1 : W₀.getNode nid = c1w.getNode nid :=
    buildChain_getNode_old c1w "B" c2 nid (by rwa [h_in2_eq] at h_nid_lt)
  have h_c1w_nd₀ : c1w.getNode nid = some nd₀ := by rwa [← h_W0_c1]
  have h_c1w_nextId : c1w.nextId = c1.middleDelays.length + 4 := by
    dsimp [c1w]
    rw [buildChain_nextId, show (World.empty : World).nextId = 0 from rfl]
    omega
  -- consecutive outputs: nid's output is [nid + 1] (or empty)
  set i := nid - in1
  have h_i : nid = World.empty.nextId + i := by
    dsimp [i]
    rw [h_in1_eq, show (World.empty : World).nextId = 0 from rfl]
    omega
  have h_i_lt : i < c1.middleDelays.length + 4 := by
    dsimp [i]
    rw [h_in1_eq, show (World.empty : World).nextId = 0 from rfl]
    omega
  have h_consec := buildChain_outputs_consecutive World.empty "A" c1
    (by intro nid' nd' h; dsimp [World.getNode, World.empty] at h; cases h)
    (fun p hp => by simp [World.empty] at hp) i h_i_lt
  rw [← h_i] at h_consec
  have h_map : (c1w.getNode nid).map NodeData.outputs = some nd₀.outputs := by
    rw [h_c1w_nd₀]; simp
  rw [h_map] at h_consec
  injection h_consec with h_outputs_val
  rw [h_outputs_val] at h_out_mem₀
  split at h_out_mem₀
  · -- outputs = [nid + 1]
    simp at h_out_mem₀
    -- nd_out is an observer in w_t₂, so nd_out₀ is an observer in W₀
    obtain ⟨nd_out₀, h_nd_out₀, h_kind_eq⟩ :=
      simFoldl_kind_preserved W₀ t1 t2 pos' in1 in2 t2 out_id nd_out h_nd_out
    have h_obs₀ : nd_out₀.kind = .observer := by rwa [← h_kind_eq]
    have h_obs_ids := buildChain2_observer_ids c1 c2 out_id nd_out₀ h_nd_out₀ h_obs₀
    cases h_obs_ids with
    | inl h1 => omega
    | inr h2 => omega
  · -- outputs = [] : contradiction
    cases h_out_mem₀

/-- In `w_t₂` (the world just before tick `t₂`), chain c2's input node `in2` has
    output `[in2 + 1]`, and `in2 + 1` is an observer node. -/
theorem w_t2_in2_observer_struct (c1 c2 : ChainSpec) (t1 t2 pos' : Nat)
    (_ : t1 < t2) :
    let in1 := (buildChain World.empty "A" c1).1
    let in2 := (buildChain (buildChain World.empty "A" c1).2 "B" c2).1
    let w_t₂ := (List.range t2).foldl (simBody t1 t2 pos' in1 in2)
        (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
    (∃ nd, w_t₂.getNode in2 = some nd ∧ nd.outputs = [in2 + 1]) ∧
    (∃ nd, w_t₂.getNode (in2 + 1) = some nd ∧ nd.kind = .observer) := by
  intro in1 in2 w_t₂
  set wA := (buildChain World.empty "A" c1).2
  set wB := (buildChain wA "B" c2).2
  set wB_pre := (buildChainPre wA "B" c2).2.1
  set chainIds := (buildChainPre wA "B" c2).2.2
  have h_in2_eq : in2 = wA.nextId := by
    dsimp [in2, wA]; simp [buildChain, buildChainPre, World.addNode]
  have h_wB : wB = connectChain wB_pre chainIds := by
    dsimp [wB, wA, buildChain, buildChainPre, wB_pre, chainIds]
  -- chainIds begins with [in2, in2 + 1]
  obtain ⟨rest, h_chainIds⟩ : ∃ rest, chainIds = in2 :: (in2 + 1) :: rest := by
    dsimp (config := { zeta := true }) [chainIds, buildChainPre, in2, wA]
    refine ⟨_, rfl⟩
  have h_ids_A : ∀ p ∈ wA.nodes, p.1 < wA.nextId :=
    buildChain_ids_lt_nextId World.empty "A" c1 (fun p hp => by simp [World.empty] at hp)
  -- in2 in the pre-connect world is the input node
  have h_pre_in2 : wB_pre.getNode in2 =
      some { kind := .input, sigLevel := 0, inputs := [], outputs := [] } := by
    rw [h_in2_eq]
    exact buildChainPre_getNode_input wA "B" c2 h_ids_A
  have h_not_mem : in2 ∉ (in2 + 1) :: rest := by
    have h_nodup : (in2 :: (in2 + 1) :: rest).Nodup := by
      have := buildChain_chainIds_nodup wA c2
      rwa [← h_chainIds]
    exact h_nodup.notMem
  -- in2's outputs in the built world are [in2 + 1]
  have h_wB_in2 : ∃ nd, wB.getNode in2 = some nd ∧ nd.outputs = [in2 + 1] := by
    set nd_pre : NodeData := { kind := .input, sigLevel := 0, inputs := [], outputs := [] }
    have h_head := connectChain_head_outputs wB_pre in2 (in2 + 1) rest nd_pre h_pre_in2 h_not_mem
    refine ⟨{ nd_pre with outputs := nd_pre.outputs ++ [in2 + 1] }, ?_, ?_⟩
    · rw [h_wB, h_chainIds]; exact h_head
    · dsimp [nd_pre]
  -- in2 + 1 in the pre-connect world is the observer node
  have h_pre_obs : wB_pre.getNode (in2 + 1) =
      some { kind := .observer, sigLevel := 0, inputs := [], outputs := [] } := by
    rw [h_in2_eq]
    exact buildChainPre_getNode_observer wA "B" c2 h_ids_A
  have h_wB_obs : ∃ nd, wB.getNode (in2 + 1) = some nd ∧ nd.kind = .observer := by
    obtain ⟨nd', h_nd'⟩ : ∃ nd', wB.getNode (in2 + 1) = some nd' := by
      rw [h_wB]
      exact connectChain_getNode_some wB_pre chainIds (in2 + 1)
        ⟨{ kind := .observer, sigLevel := 0, inputs := [], outputs := [] }, h_pre_obs⟩
    obtain ⟨nd₀, h_nd₀, hk⟩ := connectChain_kind_preserved wB_pre chainIds (in2 + 1) nd' h_nd'
    refine ⟨nd', h_nd', ?_⟩
    have h_nd₀_eq : nd₀ = { kind := .observer, sigLevel := 0, inputs := [], outputs := [] } :=
      Option.some.inj (h_nd₀.symm.trans h_pre_obs)
    rw [← hk, h_nd₀_eq]
  constructor
  · -- outputs of in2
    obtain ⟨ndB, h_ndB, h_outB⟩ := h_wB_in2
    obtain ⟨nd₂, h_nd₂⟩ : ∃ nd₂, w_t₂.getNode in2 = some nd₂ :=
      simFoldl_getNode_some wB t1 t2 pos' in1 in2 t2 in2 ⟨ndB, h_ndB⟩
    obtain ⟨nd₀, h_nd₀, _, h_out⟩ := simFoldl_inputs_preserved wB t1 t2 pos' in1 in2 t2 in2 nd₂ h_nd₂
    have h_nd₀_eq : nd₀ = ndB := Option.some.inj (h_nd₀.symm.trans h_ndB)
    refine ⟨nd₂, h_nd₂, ?_⟩
    rw [h_out, h_nd₀_eq, h_outB]
  · -- kind of in2 + 1
    obtain ⟨ndB, h_ndB, hkB⟩ := h_wB_obs
    obtain ⟨nd₂, h_nd₂⟩ : ∃ nd₂, w_t₂.getNode (in2 + 1) = some nd₂ :=
      simFoldl_getNode_some wB t1 t2 pos' in1 in2 t2 (in2 + 1) ⟨ndB, h_ndB⟩
    obtain ⟨nd₀, h_nd₀, hk⟩ := simFoldl_kind_preserved wB t1 t2 pos' in1 in2 t2 (in2 + 1) nd₂ h_nd₂
    have h_nd₀_eq : nd₀ = ndB := Option.some.inj (h_nd₀.symm.trans h_ndB)
    refine ⟨nd₂, h_nd₂, ?_⟩
    rw [hk, h_nd₀_eq, hkB]

/-- The initial two-chain world has tick `0`. -/
theorem pos_indep_w0_tick (c1 c2 : ChainSpec) :
    (buildChain (buildChain World.empty "A" c1).2 "B" c2).2.tick = 0 := by
  dsimp (config := { zeta := true }) [buildChain, buildChainPre]
  suffices h_ct : ∀ w ids, (connectChain w ids).tick = w.tick by
    rw [h_ct]
    suffices h_fl : ∀ (d : List PNat) (ids : List Nat) (w : World),
        ((d.foldl repFoldlStep (ids, w)).2 : World).tick = w.tick by
      simp [World.addNode, World.empty, h_fl, h_ct]
    intro d ids w; induction d generalizing ids w with
    | nil => rfl
    | cons _ rest ih =>
      simp only [List.foldl_cons, repFoldlStep]
      rw [ih]; simp [World.addNode]
  intro w ids; dsimp [connectChain]
  induction ids.zip (ids.drop 1) generalizing w with
  | nil => rfl
  | cons p rest ih => cases p; simp [List.foldl_cons, ih]

/-- In the two-chain world, `in1 < in2`. -/
theorem pos_indep_in1_lt_in2 (c1 c2 : ChainSpec) :
    let in1 := (buildChain World.empty "A" c1).1
    let in2 := (buildChain (buildChain World.empty "A" c1).2 "B" c2).1
    in1 < in2 := by
  intro in1 in2
  have h1 : in1 = (buildChain World.empty "A" c1).1 := rfl
  have h2 : in2 = (buildChain (buildChain World.empty "A" c1).2 "B" c2).1 := rfl
  rw [h1, h2]
  have h_in1_eq : (buildChain World.empty "A" c1).1 = World.empty.nextId := by
    simp [buildChain, buildChainPre, World.addNode]
  have h_in2_eq : (buildChain (buildChain World.empty "A" c1).2 "B" c2).1 =
      (buildChain World.empty "A" c1).2.nextId := by
    simp [buildChain, buildChainPre, World.addNode]
  rw [h_in1_eq, h_in2_eq, buildChain_nextId]
  simp [World.empty]

/-- The world `w_t₂` (after folding ticks `0..t₂-1`) has tick `t₂`. -/
theorem pos_indep_wt2_tick (c1 c2 : ChainSpec) (t1 t2 pos' : Nat) :
    let in1 := (buildChain World.empty "A" c1).1
    let in2 := (buildChain (buildChain World.empty "A" c1).2 "B" c2).1
    let w_t₂ := (List.range t2).foldl (simBody t1 t2 pos' in1 in2)
        (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
    w_t₂.tick = t2 := by
  intro in1 in2 w_t₂
  dsimp [w_t₂, in1, in2]
  rw [simFoldl_tick (buildChain (buildChain World.empty "A" c1).2 "B" c2).2 t1 t2 pos'
    (buildChain World.empty "A" c1).1
    (buildChain (buildChain World.empty "A" c1).2 "B" c2).1 t2,
    pos_indep_w0_tick c1 c2]
  omega

/-- All repeater delays in `w_t₂` are `≥ 2`. -/
theorem pos_indep_wt2_delay (c1 c2 : ChainSpec) (t1 t2 pos' : Nat)
    (h1_middle : ∀ d ∈ c1.middleDelays, ValidDelay d)
    (h1_last : ValidDelay c1.lastDelay)
    (h2_middle : ∀ d ∈ c2.middleDelays, ValidDelay d)
    (h2_last : ValidDelay c2.lastDelay) :
    let in1 := (buildChain World.empty "A" c1).1
    let in2 := (buildChain (buildChain World.empty "A" c1).2 "B" c2).1
    let w_t₂ := (List.range t2).foldl (simBody t1 t2 pos' in1 in2)
        (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
    ∀ nid nd, w_t₂.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
  intro in1 in2 w_t₂ nid nd h_nd d p h_kind
  dsimp [w_t₂] at h_nd
  obtain ⟨nd₀, h_nd₀, h_kind_eq⟩ := simFoldl_kind_preserved
    (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
    t1 t2 pos' in1 in2 t2 nid nd h_nd
  rw [h_kind_eq] at h_kind
  dsimp [buildChain, buildChainPre] at h_nd₀
  have h_all : ∀ nid' nd', (buildChain (buildChain World.empty "A" c1).2 "B" c2).2.getNode nid' = some nd' →
      ∀ d' p', nd'.kind = .repeater d' p' → d' ≥ 2 := by
    have h_c1 : ∀ nid nd, (buildChain World.empty "A" c1).2.getNode nid = some nd →
        ∀ d p, nd.kind = .repeater d p → d ≥ 2 :=
      buildChain_repeater_delay_ge2 World.empty "A" c1
        (fun d hd => ValidDelay.ge2 (h1_middle d hd)) (ValidDelay.ge2 h1_last)
        (fun nid nd h => by simp [World.empty, World.getNode] at h)
        (fun p hp => by simp [World.empty] at hp)
    have h_ids : ∀ p ∈ (buildChain World.empty "A" c1).2.nodes,
        p.1 < (buildChain World.empty "A" c1).2.nextId :=
      buildChain_ids_lt_nextId World.empty "A" c1 (fun p hp => by simp [World.empty] at hp)
    exact buildChain_repeater_delay_ge2 (buildChain World.empty "A" c1).2 "B" c2
      (fun d hd => ValidDelay.ge2 (h2_middle d hd)) (ValidDelay.ge2 h2_last) h_c1 h_ids
  exact h_all nid nd₀ h_nd₀ d p h_kind

/-- If `w_t₂` has an event at tick `t₂`, then `t1 < t2`. -/
theorem pos_indep_t1_lt_t2 (c1 c2 : ChainSpec) (t1 t2 pos' : Nat) :
    let in1 := (buildChain World.empty "A" c1).1
    let in2 := (buildChain (buildChain World.empty "A" c1).2 "B" c2).1
    let w_t₂ := (List.range t2).foldl (simBody t1 t2 pos' in1 in2)
        (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
    (∃ ev ∈ w_t₂.events, ev.targetTick = t2) → t1 < t2 := by
  intro in1 in2 w_t₂ h_events
  apply Nat.lt_of_not_ge
  intro h_ge
  have h_no_ev := simFoldl_no_events_before_activation c1 c2 t1 t2 pos' h_ge
  have h_contra : w_t₂.events = [] := by
    dsimp [w_t₂]; exact h_no_ev t2 (le_refl t2)
  obtain ⟨ev, h_ev, _⟩ := h_events
  rw [h_contra] at h_ev; cases h_ev

/-- In `w_t₂`, every event targets a node with id `< in2` (a chain-c1 node). -/
theorem pos_indep_wt2_nodeId_lt (c1 c2 : ChainSpec) (t1 t2 pos' : Nat)
    (h1_middle : ∀ d ∈ c1.middleDelays, ValidDelay d)
    (h1_last : ValidDelay c1.lastDelay)
    (h2_middle : ∀ d ∈ c2.middleDelays, ValidDelay d)
    (h2_last : ValidDelay c2.lastDelay) :
    let in1 := (buildChain World.empty "A" c1).1
    let in2 := (buildChain (buildChain World.empty "A" c1).2 "B" c2).1
    let w_t₂ := (List.range t2).foldl (simBody t1 t2 pos' in1 in2)
        (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
    (h_in1_lt_in2 : in1 < in2) →
    ∀ ev ∈ w_t₂.events, ev.nodeId < in2 := by
        intro in1 in2 w_t₂ h_in1_lt_in2

        dsimp [w_t₂]
        apply simFoldl_nodeId_lt _ _ _ _ _ in2
        · intro ev h_ev
          have h_ev_empty : (buildChain (buildChain World.empty "A" c1).2 "B" c2).2.events = [] := by
            have h_addNode_ev : ∀ (w : World) (nd : NodeData), (w.addNode nd).2.events = w.events := by
              intro w nd; dsimp [World.addNode]
            have h_repFoldl_ev : ∀ (d : PNat) (acc : List Nat × World),
                (repFoldlStep acc d).2.events = acc.2.events := by
              intro d acc; dsimp [repFoldlStep]; rw [h_addNode_ev]
            have h_foldl_ev : ∀ (ds : List PNat) (acc : List Nat × World),
                (ds.foldl repFoldlStep acc).2.events = acc.2.events := by
              intro ds acc; induction ds generalizing acc with
              | nil => rfl
              | cons d rest ih => simp [List.foldl_cons, h_repFoldl_ev, ih]
            have h_buildChainPre_ev : ∀ (w : World) (name : String) (c : ChainSpec),
                (buildChainPre w name c).2.1.events = w.events := by
              intro w name c
              dsimp [buildChainPre]
              rw [h_addNode_ev, h_addNode_ev, h_foldl_ev, h_addNode_ev, h_addNode_ev]
            have h_buildChain_ev : ∀ (w : World) (name : String) (c : ChainSpec),
                (buildChain w name c).2.events = w.events := by
              intro w name c
              dsimp [buildChain]
              rw [connectChain_events, h_buildChainPre_ev]
            rw [h_buildChain_ev, h_buildChain_ev]
            rfl
          rw [h_ev_empty] at h_ev; cases h_ev
        · intro nid nd h_nd h_lt out h_out
          have h_in2_eq : in2 = (buildChain World.empty "A" c1).2.nextId := by
            dsimp [in2]; simp [buildChain, buildChainPre, World.addNode]
          have h_lt' : nid < (buildChain World.empty "A" c1).2.nextId := by rw [← h_in2_eq]; exact h_lt
          have h_old := buildChain_getNode_old (buildChain World.empty "A" c1).2 "B" c2 nid h_lt'
          have h_nd' : (buildChain World.empty "A" c1).2.getNode nid = some nd := by rwa [← h_old]
          dsimp [buildChain] at h_nd'
          have h_out₀ := connectChain_outputs_subset
            (buildChainPre World.empty "A" c1).2.2 (buildChainPre World.empty "A" c1).2.1
            nid nd h_nd' out h_out
          cases h_out₀ with
          | inl h_mem =>
            have h_lt_out := buildChainPre_chainIds_lt_nextId World.empty "A" c1 out h_mem
            have h_nextId : (buildChainPre World.empty "A" c1).2.1.nextId =
                (buildChain World.empty "A" c1).2.nextId := by dsimp [buildChain]; simp [connectChain_nextId]
            rwa [h_in2_eq, ← h_nextId]
          | inr h_mem =>
            obtain ⟨nd₀, h_nd₀, h_out₀⟩ := h_mem
            have h_empty := buildChainPre_empty_outputs "A" c1 nid nd₀ h_nd₀
            rw [h_empty] at h_out₀; cases h_out₀
        · intro nid nd h_nd d p h_kind
          have h_c1 : ∀ nid nd, (buildChain World.empty "A" c1).2.getNode nid = some nd →
              ∀ d p, nd.kind = .repeater d p → d ≥ 2 :=
            buildChain_repeater_delay_ge2 World.empty "A" c1
              (fun d hd => ValidDelay.ge2 (h1_middle d hd)) (ValidDelay.ge2 h1_last)
              (fun nid nd h => by simp [World.empty, World.getNode] at h)
              (fun p hp => by simp [World.empty] at hp)
          exact buildChain_repeater_delay_ge2 (buildChain World.empty "A" c1).2 "B" c2
            (fun d hd => ValidDelay.ge2 (h2_middle d hd)) (ValidDelay.ge2 h2_last) h_c1
            (buildChain_ids_lt_nextId World.empty "A" c1 (fun p hp => by simp [World.empty] at hp))
            nid nd h_nd d p h_kind
        · exact h_in1_lt_in2
        · intro nd h_nd out h_out
          have h_in2_eq : in2 = (buildChain World.empty "A" c1).2.nextId := by
            dsimp [in2]; simp [buildChain, buildChainPre, World.addNode]
          have h_in1_lt : in1 < (buildChain World.empty "A" c1).2.nextId := by rw [← h_in2_eq]; exact h_in1_lt_in2
          have h_old := buildChain_getNode_old (buildChain World.empty "A" c1).2 "B" c2 in1 h_in1_lt
          have h_nd' : (buildChain World.empty "A" c1).2.getNode in1 = some nd := by rwa [← h_old]
          dsimp [buildChain] at h_nd'
          have h_out₀ := connectChain_outputs_subset
            (buildChainPre World.empty "A" c1).2.2 (buildChainPre World.empty "A" c1).2.1
            in1 nd h_nd' out h_out
          cases h_out₀ with
          | inl h_mem =>
            have h_lt_out := buildChainPre_chainIds_lt_nextId World.empty "A" c1 out h_mem
            have h_nextId : (buildChainPre World.empty "A" c1).2.1.nextId =
                (buildChain World.empty "A" c1).2.nextId := by dsimp [buildChain]; simp [connectChain_nextId]
            rwa [h_in2_eq, ← h_nextId]
          | inr h_mem =>
            obtain ⟨nd₀, h_nd₀, h_out₀⟩ := h_mem
            have h_empty := buildChainPre_empty_outputs "A" c1 in1 nd₀ h_nd₀
            rw [h_empty] at h_out₀; cases h_out₀
        · intro k hk
          have h_tick := simFoldl_tick (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
            t1 t2 pos' (buildChain World.empty "A" c1).1
            (buildChain (buildChain World.empty "A" c1).2 "B" c2).1 k
          have h_init_tick : (buildChain (buildChain World.empty "A" c1).2 "B" c2).2.tick = 0 := by
            exact pos_indep_w0_tick c1 c2
          rw [h_tick, h_init_tick]; omega

/-- In `w_t₂`, no event targets `in1`. -/
theorem pos_indep_wt2_nodeId_ne_in1 (c1 c2 : ChainSpec) (t1 t2 pos' : Nat)
    (h1_middle : ∀ d ∈ c1.middleDelays, ValidDelay d)
    (h1_last : ValidDelay c1.lastDelay)
    (h2_middle : ∀ d ∈ c2.middleDelays, ValidDelay d)
    (h2_last : ValidDelay c2.lastDelay) :
    let in1 := (buildChain World.empty "A" c1).1
    let in2 := (buildChain (buildChain World.empty "A" c1).2 "B" c2).1
    let w_t₂ := (List.range t2).foldl (simBody t1 t2 pos' in1 in2)
        (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
    (h_in1_lt_in2 : in1 < in2) →
    ∀ ev ∈ w_t₂.events, ev.nodeId ≠ in1 := by
        intro in1 in2 w_t₂ h_in1_lt_in2

        dsimp [w_t₂]
        apply simFoldl_nodeId_ne _ t1 t2 pos' in1 in2 t2 in1
        · intro ev h_ev
          have h_ev_empty : (buildChain (buildChain World.empty "A" c1).2 "B" c2).2.events = [] := by
            have h_addNode_ev : ∀ (w : World) (nd : NodeData), (w.addNode nd).2.events = w.events := by
              intro w nd; dsimp [World.addNode]
            have h_repFoldl_ev : ∀ (d : PNat) (acc : List Nat × World),
                (repFoldlStep acc d).2.events = acc.2.events := by
              intro d acc; dsimp [repFoldlStep]; rw [h_addNode_ev]
            have h_foldl_ev : ∀ (ds : List PNat) (acc : List Nat × World),
                (ds.foldl repFoldlStep acc).2.events = acc.2.events := by
              intro ds acc; induction ds generalizing acc with
              | nil => rfl
              | cons d rest ih => simp [List.foldl_cons, h_repFoldl_ev, ih]
            have h_buildChainPre_ev : ∀ (w : World) (name : String) (c : ChainSpec),
                (buildChainPre w name c).2.1.events = w.events := by
              intro w name c
              dsimp [buildChainPre]
              rw [h_addNode_ev, h_addNode_ev, h_foldl_ev, h_addNode_ev, h_addNode_ev]
            have h_buildChain_ev : ∀ (w : World) (name : String) (c : ChainSpec),
                (buildChain w name c).2.events = w.events := by
              intro w name c
              dsimp [buildChain]
              rw [connectChain_events, h_buildChainPre_ev]
            rw [h_buildChain_ev, h_buildChain_ev]
            rfl
          rw [h_ev_empty] at h_ev; cases h_ev
        · intro nid nd h_nd out h_out
          -- outputs of the initial two-chain world never equal in1
          dsimp [buildChain] at h_nd
          set c1w := (buildChain World.empty "A" c1).2
          set c2ids := (buildChainPre c1w "B" c2).2.2
          set base₂ := (buildChainPre c1w "B" c2).2.1
          have h_in2_eq : c1w.nextId = in2 := by
            dsimp [in2, c1w]; simp [buildChain, buildChainPre, World.addNode]
          have h_split := connectChain_outputs_subset_drop1 c2ids base₂ nid nd h_nd out h_out
          rcases h_split with h_mem | ⟨nd₀, h_nd₀, h_out₀⟩
          · -- out ∈ c2ids.drop 1 ⊆ c2ids, so out ≥ c1w.nextId = in2 > in1
            have h_mem_ids : out ∈ c2ids := List.drop_subset 1 c2ids h_mem
            have h_ge := buildChainPre_chainIds_ge c1w "B" c2 out h_mem_ids
            intro h_eq; rw [h_eq] at h_ge; rw [h_in2_eq] at h_ge; omega
          · -- out ∈ nd₀.outputs with base₂.getNode nid = some nd₀
            dsimp [base₂] at h_nd₀
            by_cases h_lt : nid < c1w.nextId
            · -- nid is a c1 node; reduce to c1's connectChain
              have h_old := buildChainPre_getNode_old c1w "B" c2 nid h_lt
              have h_c1w : c1w.getNode nid = some nd₀ := by rwa [h_old] at h_nd₀
              dsimp [c1w, buildChain] at h_c1w
              set c1ids := (buildChainPre World.empty "A" c1).2.2
              set base₁ := (buildChainPre World.empty "A" c1).2.1
              have h_split1 := connectChain_outputs_subset_drop1 c1ids base₁ nid nd₀ h_c1w out h_out₀
              rcases h_split1 with h_mem1 | ⟨nd₁, h_nd₁, h_out₁⟩
              · -- out ∈ c1ids.drop 1; c1ids = range k and in1 = 0, so out ≥ 1 ≠ in1
                intro h_eq
                have h_in1_zero : in1 = 0 := by
                  dsimp [in1]; simp [buildChain, buildChainPre, World.addNode]; rfl
                set L := List.range (c1.middleDelays.length + 4)
                have h_c1ids : c1ids = L := by
                  dsimp [c1ids, L]
                  rw [buildChain_chainIds_range World.empty "A" c1]
                  simp [World.empty]
                rw [h_c1ids] at h_mem1
                obtain ⟨i, h_i_lt, h_i_eq⟩ := List.mem_iff_getElem.mp h_mem1
                dsimp [L] at h_i_eq
                simp only [List.getElem_drop, List.getElem_range] at h_i_eq
                rw [h_eq, h_in1_zero] at h_i_eq; omega
              · -- base₁ (pre-connect c1 world) has empty outputs
                have h_empty := buildChainPre_empty_outputs "A" c1 nid nd₁ h_nd₁
                rw [h_empty] at h_out₁; cases h_out₁
            · -- nid is a c2 node of buildChainPre; such nodes have empty outputs
              set j := nid - c1w.nextId
              have h_nid_eq : nid = c1w.nextId + j := by dsimp [j]; omega
              have h_ids_c1w : ∀ p ∈ c1w.nodes, p.1 < c1w.nextId :=
                buildChain_ids_lt_nextId World.empty "A" c1 (fun p hp => by simp [World.empty] at hp)
              have h_all : ∀ p ∈ base₂.nodes, p.1 < base₂.nextId := by
                dsimp (config := { zeta := true }) [base₂, buildChainPre]
                set w₁ := (c1w.addNode
                  { kind := .input, sigLevel := 0, inputs := [], outputs := [] }).2
                have h₁ : ∀ p ∈ w₁.nodes, p.1 < w₁.nextId :=
                  World.addNode_ids_lt_nextId c1w _ h_ids_c1w
                set w₂ := (w₁.addNode
                  { kind := .observer, sigLevel := 0, inputs := [], outputs := [] }).2
                have h₂ : ∀ p ∈ w₂.nodes, p.1 < w₂.nextId :=
                  World.addNode_ids_lt_nextId w₁ _ h₁
                set w₃ := (c2.middleDelays.foldl repFoldlStep ([], w₂)).2
                have h₃ : ∀ p ∈ w₃.nodes, p.1 < w₃.nextId :=
                  foldl_repFoldlStep_ids_lt_nextId c2.middleDelays [] w₂ h₂
                set w₄ := (w₃.addNode
                  { kind := .repeater c2.lastDelay (-1), sigLevel := 0, inputs := [], outputs := [] }).2
                have h₄ : ∀ p ∈ w₄.nodes, p.1 < w₄.nextId :=
                  World.addNode_ids_lt_nextId w₃ _ h₃
                exact World.addNode_ids_lt_nextId w₄
                  ({ kind := .output "B", sigLevel := 0, inputs := [], outputs := [] } : NodeData) h₄
              have h_nid_lt : nid < base₂.nextId := by
                by_contra h_notlt
                have h_ge : base₂.nextId ≤ nid := by omega
                have h_none : base₂.getNode nid = none := by
                  dsimp [World.getNode]
                  have h_find_none : base₂.nodes.find? (fun (nid', _) => nid' == nid) = none := by
                    apply List.find?_eq_none.mpr
                    intro p h_p
                    have h_lt := h_all p h_p
                    simp; omega
                  rw [h_find_none]
                rw [h_none] at h_nd₀; cases h_nd₀
              have h_j_lt : j < c2.middleDelays.length + 4 := by
                have h_nextId : base₂.nextId = c1w.nextId + (c2.middleDelays.length + 4) := by
                  dsimp (config := { zeta := true }) [base₂, buildChainPre]
                  simp [World.addNode_nextId, foldl_repFoldlStep_nextId] ; omega
                rw [h_nextId] at h_nid_lt
                dsimp [j]; omega
              obtain ⟨nd', h_nd', h_out_empty⟩ :=
                buildChainPre_getNode_chainId c1w "B" c2 h_ids_c1w j h_j_lt
              have h_nd₀_eq : nd₀ = nd' := by
                apply Option.some_inj.mp
                rw [← h_nd₀, h_nid_eq]; exact h_nd'
              rw [h_nd₀_eq, h_out_empty] at h_out₀; cases h_out₀
        · intro nid nd h_nd d p h_kind
          have h_c1 : ∀ nid nd, (buildChain World.empty "A" c1).2.getNode nid = some nd →
              ∀ d p, nd.kind = .repeater d p → d ≥ 2 :=
            buildChain_repeater_delay_ge2 World.empty "A" c1
              (fun d hd => ValidDelay.ge2 (h1_middle d hd)) (ValidDelay.ge2 h1_last)
              (fun nid nd h => by simp [World.empty, World.getNode] at h)
              (fun p hp => by simp [World.empty] at hp)
          exact buildChain_repeater_delay_ge2 (buildChain World.empty "A" c1).2 "B" c2
            (fun d hd => ValidDelay.ge2 (h2_middle d hd)) (ValidDelay.ge2 h2_last) h_c1
            (buildChain_ids_lt_nextId World.empty "A" c1 (fun p hp => by simp [World.empty] at hp))
            nid nd h_nd d p h_kind
        · intro k hk
          have h_tick := simFoldl_tick (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
            t1 t2 pos' (buildChain World.empty "A" c1).1
            (buildChain (buildChain World.empty "A" c1).2 "B" c2).1 k
          have h_init_tick : (buildChain (buildChain World.empty "A" c1).2 "B" c2).2.tick = 0 := by
            exact pos_indep_w0_tick c1 c2
          rw [h_tick, h_init_tick]; omega
