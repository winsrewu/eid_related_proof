import BasicProofs.PrefixChain.Part08


open BasicRedstoneSim

/-- `buildChain` preserves "all repeaters have delay ≥ 2". -/
theorem buildChain_repeater_delay_ge2 (w : World) (name : String) (c : ChainSpec)
    (h_middle : ∀ d ∈ c.middleDelays, d ≥ 2)
    (h_last : c.lastDelay ≥ 2)
    (h_w : ∀ nid nd, w.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2)
    (h_ids : ∀ p ∈ w.nodes, p.1 < w.nextId) :
    ∀ nid nd, (buildChain w name c).2.getNode nid = some nd →
    ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
  intro nid nd h_get d p h_kind
  dsimp [buildChain] at h_get
  -- connectChain preserves kinds, so trace back to buildChainPre
  obtain ⟨nd₀, h_nd₀, h_kind₀⟩ := connectChain_kind_preserved
    (buildChainPre w name c).2.1 (buildChainPre w name c).2.2 nid nd h_get
  rw [← h_kind₀] at h_kind
  -- Now prove the property for buildChainPre
  dsimp [buildChainPre] at h_nd₀
  -- Trace through the addNode calls
  -- w₀ = w, w₁ = addNode input, w₂ = addNode observer,
  -- w₃ = foldl repFoldlStep, w₄ = addNode lastRep, w₅ = addNode output
  set w₁ := (w.addNode { kind := .input, sigLevel := 0, inputs := [], outputs := [] }).2
  set w₂ := (w₁.addNode { kind := .observer, sigLevel := 0, inputs := [], outputs := [] }).2
  set w₃ := (c.middleDelays.foldl repFoldlStep ([], w₂)).2
  set w₄ := (w₃.addNode { kind := .repeater c.lastDelay (-1), sigLevel := 0, inputs := [], outputs := [] }).2
  set w₅ := (w₄.addNode { kind := .output name, sigLevel := 0, inputs := [], outputs := [] }).2
  -- h_nd₀ : w₅.getNode nid = some nd₀
  -- Prove property for each step
  have h₁ : ∀ nid nd, w₁.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2 :=
    addNode_preserves_delay_ge2 w { kind := .input, sigLevel := 0, inputs := [], outputs := [] }
      h_w (by intro d p h; cases h) (World.getNode_nextId_none w h_ids)
  have h_ids₁ : ∀ p ∈ w₁.nodes, p.1 < w₁.nextId :=
    World.addNode_ids_lt_nextId w { kind := .input, sigLevel := 0, inputs := [], outputs := [] } h_ids
  have h₂ : ∀ nid nd, w₂.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2 :=
    addNode_preserves_delay_ge2 w₁ { kind := .observer, sigLevel := 0, inputs := [], outputs := [] }
      h₁ (by intro d p h; cases h) (World.getNode_nextId_none w₁ h_ids₁)
  have h_ids₂ : ∀ p ∈ w₂.nodes, p.1 < w₂.nextId :=
    World.addNode_ids_lt_nextId w₁ { kind := .observer, sigLevel := 0, inputs := [], outputs := [] } h_ids₁
  have h₃ : ∀ nid nd, w₃.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2 :=
    repFoldl_preserves_delay_ge2 c.middleDelays ([], w₂) h₂ h_middle h_ids₂
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
  have h₄ : ∀ nid nd, w₄.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2 :=
    addNode_preserves_delay_ge2 w₃
      { kind := .repeater c.lastDelay (-1), sigLevel := 0, inputs := [], outputs := [] }
      h₃ (by intro d' p' h; injection h with h_d; subst h_d; exact h_last)
      (World.getNode_nextId_none w₃ h_ids₃)
  have h_ids₄ : ∀ p ∈ w₄.nodes, p.1 < w₄.nextId :=
    World.addNode_ids_lt_nextId w₃
      { kind := .repeater c.lastDelay (-1), sigLevel := 0, inputs := [], outputs := [] } h_ids₃
  have h₅ : ∀ nid nd, w₅.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2 :=
    addNode_preserves_delay_ge2 w₄ { kind := .output name, sigLevel := 0, inputs := [], outputs := [] }
      h₄ (by intro d p h; cases h) (World.getNode_nextId_none w₄ h_ids₄)
  exact h₅ nid nd₀ h_nd₀ d p h_kind

/-- `addNode` preserves "all repeaters have even delay". -/
theorem addNode_preserves_delay_even (w : World) (nd : NodeData)
    (h_w : ∀ nid nd, w.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → (d : Nat) % 2 = 0)
    (h_nd : ∀ d p, nd.kind = .repeater d p → (d : Nat) % 2 = 0)
    (h_fresh : w.getNode w.nextId = none) :
    ∀ nid nd', (w.addNode nd).2.getNode nid = some nd' →
    ∀ d p, nd'.kind = .repeater d p → (d : Nat) % 2 = 0 := by
  intro nid nd' h_get d p h_kind
  by_cases h_eq : nid = w.nextId
  · subst h_eq
    have h_new := World.addNode_getNode_fresh w nd h_fresh
    have h_eq_nd : nd' = nd := by
      have h : some nd' = some nd := h_get.symm.trans h_new
      injection h
    subst h_eq_nd
    exact h_nd d p h_kind
  · have h_old := World.addNode_getNode_old w nd nid h_eq
    rw [h_old] at h_get
    exact h_w nid nd' h_get d p h_kind

/-- The `repFoldlStep` foldl preserves "all repeaters have even delay". -/
theorem repFoldl_preserves_delay_even (delays : List PNat) :
    ∀ (acc : List Nat × World),
    (∀ nid nd, acc.2.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → (d : Nat) % 2 = 0) →
    (∀ d ∈ delays, (d : Nat) % 2 = 0) →
    (∀ p ∈ acc.2.nodes, p.1 < acc.2.nextId) →
    ∀ nid nd, (delays.foldl repFoldlStep acc).2.getNode nid = some nd →
    ∀ d p, nd.kind = .repeater d p → (d : Nat) % 2 = 0 := by
  induction delays with
  | nil =>
    intro acc h_acc h_delays h_ids nid nd h_get d p h_kind
    dsimp [List.foldl] at h_get
    exact h_acc nid nd h_get d p h_kind
  | cons d ds ih =>
    intro acc h_acc h_delays h_ids nid nd h_get d' p' h_kind
    dsimp [List.foldl] at h_get
    have h_d_even : (d : Nat) % 2 = 0 := h_delays d (by simp)
    have h_fresh : acc.2.getNode acc.2.nextId = none := World.getNode_nextId_none acc.2 h_ids
    have h_step : ∀ nid' nd', (repFoldlStep acc d).2.getNode nid' = some nd' →
        ∀ d'' p'', nd'.kind = .repeater d'' p'' → (d'' : Nat) % 2 = 0 := by
      dsimp [repFoldlStep]
      exact addNode_preserves_delay_even acc.2 (mkRepNode d) h_acc
        (by dsimp [mkRepNode]; intro d'' p'' h; injection h with h_d; subst h_d; exact h_d_even)
        h_fresh
    have h_ids' : ∀ p ∈ (repFoldlStep acc d).2.nodes, p.1 < (repFoldlStep acc d).2.nextId := by
      dsimp [repFoldlStep]
      exact World.addNode_ids_lt_nextId acc.2 (mkRepNode d) h_ids
    exact ih (repFoldlStep acc d) h_step
      (fun d'' h_mem => h_delays d'' (List.mem_cons_of_mem d h_mem))
      h_ids' nid nd h_get d' p' h_kind

/-- `buildChain` preserves "all repeaters have even delay". -/
theorem buildChain_repeater_delay_even (w : World) (name : String) (c : ChainSpec)
    (h_middle : ∀ d ∈ c.middleDelays, (d : Nat) % 2 = 0)
    (h_last : (c.lastDelay : Nat) % 2 = 0)
    (h_w : ∀ nid nd, w.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → (d : Nat) % 2 = 0)
    (h_ids : ∀ p ∈ w.nodes, p.1 < w.nextId) :
    ∀ nid nd, (buildChain w name c).2.getNode nid = some nd →
    ∀ d p, nd.kind = .repeater d p → (d : Nat) % 2 = 0 := by
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
  have h₁ : ∀ nid nd, w₁.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → (d : Nat) % 2 = 0 :=
    addNode_preserves_delay_even w { kind := .input, sigLevel := 0, inputs := [], outputs := [] }
      h_w (by intro d p h; cases h) (World.getNode_nextId_none w h_ids)
  have h_ids₁ : ∀ p ∈ w₁.nodes, p.1 < w₁.nextId :=
    World.addNode_ids_lt_nextId w { kind := .input, sigLevel := 0, inputs := [], outputs := [] } h_ids
  have h₂ : ∀ nid nd, w₂.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → (d : Nat) % 2 = 0 :=
    addNode_preserves_delay_even w₁ { kind := .observer, sigLevel := 0, inputs := [], outputs := [] }
      h₁ (by intro d p h; cases h) (World.getNode_nextId_none w₁ h_ids₁)
  have h_ids₂ : ∀ p ∈ w₂.nodes, p.1 < w₂.nextId :=
    World.addNode_ids_lt_nextId w₁ { kind := .observer, sigLevel := 0, inputs := [], outputs := [] } h_ids₁
  have h₃ : ∀ nid nd, w₃.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → (d : Nat) % 2 = 0 :=
    repFoldl_preserves_delay_even c.middleDelays ([], w₂) h₂ h_middle h_ids₂
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
  have h₄ : ∀ nid nd, w₄.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → (d : Nat) % 2 = 0 :=
    addNode_preserves_delay_even w₃
      { kind := .repeater c.lastDelay (-1), sigLevel := 0, inputs := [], outputs := [] }
      h₃ (by intro d' p' h; injection h with h_d; subst h_d; exact h_last)
      (World.getNode_nextId_none w₃ h_ids₃)
  have h_ids₄ : ∀ p ∈ w₄.nodes, p.1 < w₄.nextId :=
    World.addNode_ids_lt_nextId w₃
      { kind := .repeater c.lastDelay (-1), sigLevel := 0, inputs := [], outputs := [] } h_ids₃
  have h₅ : ∀ nid nd, w₅.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → (d : Nat) % 2 = 0 :=
    addNode_preserves_delay_even w₄ { kind := .output name, sigLevel := 0, inputs := [], outputs := [] }
      h₄ (by intro d p h; cases h) (World.getNode_nextId_none w₄ h_ids₄)
  exact h₅ nid nd₀ h_nd₀ d p h_kind

/-- `addNode` preserves "all repeaters have priority < 100". -/
theorem addNode_preserves_priority_lt_100 (w : World) (nd : NodeData)
    (h_w : ∀ nid nd, w.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 100)
    (h_nd : ∀ d p, nd.kind = .repeater d p → p < 100)
    (h_none : w.getNode w.nextId = none) :
    ∀ nid nd', (w.addNode nd).2.getNode nid = some nd' →
    ∀ d p, nd'.kind = .repeater d p → p < 100 := by
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

/-- `repFoldlStep` preserves "all repeaters have priority < 100". -/
theorem repFoldl_preserves_priority_lt_100 (delays : List PNat)
    (acc : List Nat × World)
    (h_acc : ∀ nid nd, acc.2.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 100)
    (h_ids : ∀ p ∈ acc.2.nodes, p.1 < acc.2.nextId) :
    ∀ nid nd, (delays.foldl repFoldlStep acc).2.getNode nid = some nd →
    ∀ d p, nd.kind = .repeater d p → p < 100 := by
  induction delays generalizing acc with
  | nil => intro nid nd h_get d p h_kind; simpa [List.foldl] using h_acc nid nd h_get d p h_kind
  | cons d ds ih =>
    intro nid nd h_get d' p h_kind
    dsimp [List.foldl, repFoldlStep] at h_get
    have h_ids' : ∀ p ∈ ((acc.2.addNode (mkRepNode d)).2).nodes, p.1 < (acc.2.addNode (mkRepNode d)).2.nextId :=
      World.addNode_ids_lt_nextId acc.2 (mkRepNode d) h_ids
    have h_acc' : ∀ nid nd, (acc.2.addNode (mkRepNode d)).2.getNode nid = some nd →
        ∀ d' p, nd.kind = .repeater d' p → p < 100 :=
      addNode_preserves_priority_lt_100 acc.2 (mkRepNode d) h_acc
        (by intro d' p h; dsimp [mkRepNode] at h; injection h with h_d h_p; subst h_d; subst h_p; omega)
        (World.getNode_nextId_none acc.2 h_ids)
    exact ih (acc.1 ++ [acc.2.nextId], (acc.2.addNode (mkRepNode d)).2) h_acc' h_ids' nid nd h_get d' p h_kind

/-- `buildChain` preserves "all repeaters have priority < 100". -/
theorem buildChain_repeater_priority_lt_100 (w : World) (name : String) (c : ChainSpec)
    (h_w : ∀ nid nd, w.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 100)
    (h_ids : ∀ p ∈ w.nodes, p.1 < w.nextId) :
    ∀ nid nd, (buildChain w name c).2.getNode nid = some nd →
    ∀ d p, nd.kind = .repeater d p → p < 100 := by
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
  have h₁ : ∀ nid nd, w₁.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 100 :=
    addNode_preserves_priority_lt_100 w { kind := .input, sigLevel := 0, inputs := [], outputs := [] }
      h_w (by intro d p h; cases h) (World.getNode_nextId_none w h_ids)
  have h_ids₁ : ∀ p ∈ w₁.nodes, p.1 < w₁.nextId :=
    World.addNode_ids_lt_nextId w { kind := .input, sigLevel := 0, inputs := [], outputs := [] } h_ids
  have h₂ : ∀ nid nd, w₂.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 100 :=
    addNode_preserves_priority_lt_100 w₁ { kind := .observer, sigLevel := 0, inputs := [], outputs := [] }
      h₁ (by intro d p h; cases h) (World.getNode_nextId_none w₁ h_ids₁)
  have h_ids₂ : ∀ p ∈ w₂.nodes, p.1 < w₂.nextId :=
    World.addNode_ids_lt_nextId w₁ { kind := .observer, sigLevel := 0, inputs := [], outputs := [] } h_ids₁
  have h₃ : ∀ nid nd, w₃.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 100 :=
    repFoldl_preserves_priority_lt_100 c.middleDelays ([], w₂) h₂ h_ids₂
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
  have h₄ : ∀ nid nd, w₄.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 100 :=
    addNode_preserves_priority_lt_100 w₃
      { kind := .repeater c.lastDelay (-1), sigLevel := 0, inputs := [], outputs := [] }
      h₃ (by intro d' p' h; injection h with h_d h_p; subst h_d; subst h_p; omega)
      (World.getNode_nextId_none w₃ h_ids₃)
  have h_ids₄ : ∀ p ∈ w₄.nodes, p.1 < w₄.nextId :=
    World.addNode_ids_lt_nextId w₃
      { kind := .repeater c.lastDelay (-1), sigLevel := 0, inputs := [], outputs := [] } h_ids₃
  have h₅ : ∀ nid nd, w₅.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 100 :=
    addNode_preserves_priority_lt_100 w₄ { kind := .output name, sigLevel := 0, inputs := [], outputs := [] }
      h₄ (by intro d p h; cases h) (World.getNode_nextId_none w₄ h_ids₄)
  exact h₅ nid nd₀ h_nd₀ d p h_kind

/-- `updateNode` preserves the invariant that all node IDs are < `nextId`. -/
theorem World.updateNode_ids_lt_nextId (w : World) (id : Nat) (f : NodeData → NodeData)
    (h : ∀ p ∈ w.nodes, p.1 < w.nextId) :
    ∀ p ∈ (w.updateNode id f).nodes, p.1 < (w.updateNode id f).nextId := by
  intro p hp
  dsimp [World.updateNode] at hp
  rw [List.mem_map] at hp
  obtain ⟨q, hq, hq'⟩ := hp
  have h_p1 : p.1 = q.1 := by
    cases q with | mk nid nd =>
    dsimp at hq'
    split_ifs at hq' <;> symm at hq' <;> subst hq' <;> rfl
  rw [h_p1]
  exact h q hq

/-- `connectChain` preserves the invariant that all node IDs are < `nextId`. -/
theorem connectChain_ids_lt_nextId (w : World) (ids : List Nat)
    (h : ∀ p ∈ w.nodes, p.1 < w.nextId) :
    ∀ p ∈ (connectChain w ids).nodes, p.1 < (connectChain w ids).nextId := by
  dsimp [connectChain]
  induction ids.zip (ids.drop 1) generalizing w with
  | nil => simpa using h
  | cons p rest ih =>
    simp only [List.foldl_cons]
    apply ih
    apply World.updateNode_ids_lt_nextId
    apply World.updateNode_ids_lt_nextId
    exact h

/-- `buildChain` preserves the invariant that all node IDs are < `nextId`. -/
theorem buildChain_ids_lt_nextId (w : World) (name : String) (c : ChainSpec)
    (h_ids : ∀ p ∈ w.nodes, p.1 < w.nextId) :
    ∀ p ∈ (buildChain w name c).2.nodes, p.1 < (buildChain w name c).2.nextId := by
  dsimp only [buildChain, buildChainPre]
  dsimp (config := { zeta := true })
  apply connectChain_ids_lt_nextId
  set w₁ := (w.addNode { kind := NodeKind.input, sigLevel := 0, inputs := [], outputs := [] }).2
  have h₁ : ∀ p ∈ w₁.nodes, p.1 < w₁.nextId :=
    World.addNode_ids_lt_nextId w { kind := .input, sigLevel := 0, inputs := [], outputs := [] } h_ids
  set w₂ := (w₁.addNode { kind := NodeKind.observer, sigLevel := 0, inputs := [], outputs := [] }).2
  have h₂ : ∀ p ∈ w₂.nodes, p.1 < w₂.nextId :=
    World.addNode_ids_lt_nextId w₁ { kind := .observer, sigLevel := 0, inputs := [], outputs := [] } h₁
  have h₃ : ∀ p ∈ (c.middleDelays.foldl repFoldlStep ([], w₂)).2.nodes,
      p.1 < (c.middleDelays.foldl repFoldlStep ([], w₂)).2.nextId :=
    foldl_repFoldlStep_ids_lt_nextId c.middleDelays [] w₂ h₂
  set w₃ := (c.middleDelays.foldl repFoldlStep ([], w₂)).2
  have h₄ : ∀ p ∈ (w₃.addNode { kind := NodeKind.repeater c.lastDelay (-1), sigLevel := 0, inputs := [], outputs := [] }).2.nodes,
      p.1 < (w₃.addNode { kind := NodeKind.repeater c.lastDelay (-1), sigLevel := 0, inputs := [], outputs := [] }).2.nextId :=
    World.addNode_ids_lt_nextId w₃ { kind := .repeater c.lastDelay (-1), sigLevel := 0, inputs := [], outputs := [] } h₃
  exact World.addNode_ids_lt_nextId _
    ({ kind := NodeKind.output name, sigLevel := 0, inputs := [], outputs := [] } : NodeData) h₄

/-- `foldl repFoldlStep` preserves existing nodes (those with ID < w.nextId). -/
theorem foldl_repFoldlStep_getNode_old (delays : List PNat) (ids : List Nat) (w : World)
    (id : Nat) (h : id < w.nextId) :
    (delays.foldl repFoldlStep (ids, w)).2.getNode id = w.getNode id := by
  induction delays generalizing ids w with
  | nil => rfl
  | cons d rest ih =>
    simp only [List.foldl_cons, repFoldlStep]
    have h_step : (w.addNode (mkRepNode d)).2.getNode id = w.getNode id :=
      World.addNode_getNode_old _ _ id (Nat.ne_of_lt h)
    have h_ih := ih (ids ++ [w.nextId]) (w.addNode (mkRepNode d)).2 (by
      dsimp [World.addNode]; omega)
    rw [h_ih, h_step]

/-- All IDs accumulated by `foldl repFoldlStep` are ≥ the threshold. -/
theorem foldl_repFoldlStep_ids_ge (delays : List PNat) (ids : List Nat) (w : World)
    (threshold : Nat) (h_ids : ∀ id ∈ ids, id ≥ threshold)
    (h_w : w.nextId ≥ threshold) :
    ∀ id ∈ (delays.foldl repFoldlStep (ids, w)).1, id ≥ threshold := by
  induction delays generalizing ids w with
  | nil => exact h_ids
  | cons d rest ih =>
    simp only [List.foldl_cons, repFoldlStep]
    have h_ids' : ∀ id ∈ ids ++ [w.nextId], id ≥ threshold := by
      intro id' h_id'
      simp [List.mem_append] at h_id'
      rcases h_id' with (h_id' | rfl)
      · exact h_ids id' h_id'
      · exact h_w
    have h_w' : (w.addNode (mkRepNode d)).2.nextId ≥ threshold := by
      dsimp [World.addNode]; omega
    exact ih (ids ++ [w.nextId]) (w.addNode (mkRepNode d)).2 h_ids' h_w'

/-- `foldl repFoldlStep` doesn't decrease nextId. -/
theorem foldl_repFoldlStep_nextId_ge (delays : List PNat) (ids : List Nat) (w : World) :
    w.nextId ≤ (delays.foldl repFoldlStep (ids, w)).2.nextId := by
  induction delays generalizing ids w with
  | nil => simp []
  | cons d rest ih =>
    simp only [List.foldl_cons, repFoldlStep]
    set w' := (w.addNode (mkRepNode d)).2
    have h_w' : w'.nextId = w.nextId + 1 := by dsimp [w', World.addNode]
    have h_ih := ih (ids ++ [w.nextId]) w'
    omega

/-- `buildChainPre` preserves existing nodes (those with ID < w.nextId). -/
theorem buildChainPre_getNode_old (w : World) (name : String) (c : ChainSpec)
    (id : Nat) (h : id < w.nextId) :
    (buildChainPre w name c).2.1.getNode id = w.getNode id := by
  dsimp (config := { zeta := true }) [buildChainPre]
  set w₁ := (w.addNode { kind := .input, sigLevel := 0, inputs := [], outputs := [] }).2
  set w₂ := (w₁.addNode { kind := .observer, sigLevel := 0, inputs := [], outputs := [] }).2
  set w₃ := (c.middleDelays.foldl repFoldlStep ([], w₂)).2
  set w₄ := (w₃.addNode { kind := .repeater c.lastDelay (-1), sigLevel := 0, inputs := [], outputs := [] }).2
  set w₅ := (w₄.addNode { kind := .output name, sigLevel := 0, inputs := [], outputs := [] }).2
  have h₁ : w₁.getNode id = w.getNode id := by
    apply World.addNode_getNode_old; dsimp [w₁, World.addNode]; omega
  have h₂ : w₂.getNode id = w₁.getNode id := by
    apply World.addNode_getNode_old; dsimp [w₂, w₁, World.addNode]; omega
  have h₃ : w₃.getNode id = w₂.getNode id := by
    apply foldl_repFoldlStep_getNode_old; dsimp [w₂, w₁, World.addNode]; omega
  have h_w3_ge : w₂.nextId ≤ w₃.nextId := by
    dsimp [w₃]; apply foldl_repFoldlStep_nextId_ge
  have h₄ : w₄.getNode id = w₃.getNode id := by
    apply World.addNode_getNode_old
    dsimp [w₂, w₁, World.addNode] at h_w3_ge ⊢; omega
  have h₅ : w₅.getNode id = w₄.getNode id := by
    apply World.addNode_getNode_old
    dsimp [w₅, w₄, w₃, w₂, w₁, World.addNode, repFoldlStep] at h_w3_ge ⊢; omega
  rw [h₅, h₄, h₃, h₂, h₁]

/-- All chain IDs from `buildChainPre` are ≥ w.nextId. -/
theorem buildChainPre_chainIds_ge (w : World) (name : String) (c : ChainSpec) :
    ∀ id ∈ (buildChainPre w name c).2.2, id ≥ w.nextId := by
  dsimp (config := { zeta := true }) [buildChainPre]
  intro id h_id
  simp [List.mem_append] at h_id
  rcases h_id with (h_id | h_id | h_id)
  · -- id = inputId = w.nextId
    subst h_id; dsimp [World.addNode]; omega
  · -- id = obsId = w.nextId + 1
    subst h_id; dsimp [World.addNode]; omega
  · -- id ∈ repIds ∨ id ∈ [lastRepId, outId]
    rcases h_id with (h_id | h_id)
    · -- id ∈ repIds from foldl
      set w₂ := (w.addNode { kind := .input, sigLevel := 0, inputs := [], outputs := [] }).2.addNode
        { kind := .observer, sigLevel := 0, inputs := [], outputs := [] } |>.2
      have h_foldl := foldl_repFoldlStep_ids_ge c.middleDelays ([] : List Nat) w₂ w.nextId
        (by intro id' h_id'; cases h_id') (by dsimp [w₂, World.addNode]; omega)
      exact h_foldl id h_id
    · -- id ∈ [lastRepId, outId]
      rcases h_id with (rfl | rfl)
      · -- id = lastRepId
        set w₂ := (w.addNode { kind := .input, sigLevel := 0, inputs := [], outputs := [] }).2.addNode
          { kind := .observer, sigLevel := 0, inputs := [], outputs := [] } |>.2
        have h_ge := foldl_repFoldlStep_nextId_ge c.middleDelays ([] : List Nat) w₂
        dsimp [w₂, World.addNode] at h_ge ⊢; omega
      · -- id = outId
        set w₂ := (w.addNode { kind := .input, sigLevel := 0, inputs := [], outputs := [] }).2.addNode
          { kind := .observer, sigLevel := 0, inputs := [], outputs := [] } |>.2
        have h_ge := foldl_repFoldlStep_nextId_ge c.middleDelays ([] : List Nat) w₂
        dsimp [w₂, World.addNode] at h_ge ⊢; omega

/-- A world with no events has no step. -/
theorem World.step_eq_none_of_events_nil (w : World) (h : w.events = []) :
    w.step = none := by
  dsimp (config := { zeta := true }) [World.step, World.popNextEvent]
  simp [h]

/-- `buildChain` preserves existing nodes (those with ID < w.nextId). -/
theorem buildChain_getNode_old (w : World) (name : String) (c : ChainSpec)
    (id : Nat) (h : id < w.nextId) :
    (buildChain w name c).2.getNode id = w.getNode id := by
  dsimp (config := { zeta := true }) [buildChain]
  set w_pre := (buildChainPre w name c).2.1
  set chainIds := (buildChainPre w name c).2.2
  rw [connectChain_getNode_of_not_mem chainIds id _ w_pre]
  · exact buildChainPre_getNode_old w name c id h
  · intro h_mem
    have h_ge := buildChainPre_chainIds_ge w name c id h_mem
    omega

/-- All IDs in `foldl repFoldlStep`'s accumulator are < the resulting nextId. -/
theorem foldl_repFoldlStep_accIds_lt_nextId (delays : List PNat)
    (initIds : List Nat) (w₀ : World)
    (h_init : ∀ id ∈ initIds, id < w₀.nextId) :
    ∀ id ∈ (delays.foldl repFoldlStep (initIds, w₀)).1,
    id < (delays.foldl repFoldlStep (initIds, w₀)).2.nextId := by
  induction delays generalizing initIds w₀ with
  | nil =>
    simpa using h_init
  | cons d rest ih =>
    simp only [List.foldl_cons, repFoldlStep]
    apply ih (initIds ++ [w₀.nextId]) ((w₀.addNode (mkRepNode d)).2)
    intro id h_id
    simp [List.mem_append] at h_id
    cases h_id with
    | inl h =>
      have h_lt := h_init id h
      dsimp [World.addNode]
      omega
    | inr h =>
      subst h
      dsimp [World.addNode]
      omega

/-- All IDs in `buildChainPre`'s chainIds are < the resulting nextId. -/
theorem buildChainPre_chainIds_lt_nextId (w : World) (name : String) (c : ChainSpec) :
    ∀ id ∈ (buildChainPre w name c).2.2, id < (buildChainPre w name c).2.1.nextId := by
  dsimp (config := { zeta := true }) [buildChainPre]
  intro id h_id
  simp [List.mem_append, World.addNode] at h_id ⊢
  rcases h_id with (rfl | rfl | h_id)
  · omega
  · omega
  · rcases h_id with (h_id | h_id)
    · -- id ∈ repIds from foldl
      have h_foldl := foldl_repFoldlStep_accIds_lt_nextId c.middleDelays ([] : List Nat)
        ((w.addNode { kind := .input, sigLevel := 0, inputs := [], outputs := [] }).2.addNode
          { kind := .observer, sigLevel := 0, inputs := [], outputs := [] } |>.2)
        (by intro id' h_id'; cases h_id')
      simp [World.addNode] at h_foldl ⊢
      have := h_foldl id h_id; omega
    · -- id ∈ [lastRepId, outId]
      rcases h_id with (rfl | rfl) <;> omega

/-- All nodes in `buildChainPre World.empty` have empty outputs. -/
theorem addNode_preserves_outputs_empty (w : World) (nd : NodeData)
    (h_ids : ∀ p ∈ w.nodes, p.1 < w.nextId)
    (h_w : ∀ nid nd', w.getNode nid = some nd' → nd'.outputs = [])
    (h_nd : nd.outputs = []) :
    ∀ nid nd', (w.addNode nd).2.getNode nid = some nd' → nd'.outputs = [] := by
  intro nid nd' h_get
  by_cases h_eq : nid = w.nextId
  · subst h_eq
    have h_fresh : w.getNode w.nextId = none := World.getNode_nextId_none w h_ids
    have h_new := World.addNode_getNode_fresh w nd h_fresh
    rw [h_new] at h_get
    injection h_get with h_nd'
    subst h_nd'
    exact h_nd
  · have h_old := World.addNode_getNode_old w nd nid h_eq
    rw [h_old] at h_get
    exact h_w nid nd' h_get

theorem repFoldlStep_preserves_outputs_empty (acc : List Nat × World) (d : PNat)
    (h_ids : ∀ p ∈ acc.2.nodes, p.1 < acc.2.nextId)
    (h_w : ∀ nid nd, acc.2.getNode nid = some nd → nd.outputs = []) :
    ∀ nid nd, (repFoldlStep acc d).2.getNode nid = some nd → nd.outputs = [] := by
  dsimp [repFoldlStep]
  exact addNode_preserves_outputs_empty acc.2 (mkRepNode d) h_ids h_w (by rfl)

theorem foldl_repFoldlStep_preserves_outputs_empty (delays : List PNat)
    (initIds : List Nat) (w₀ : World)
    (h_ids : ∀ p ∈ w₀.nodes, p.1 < w₀.nextId)
    (h_w : ∀ nid nd, w₀.getNode nid = some nd → nd.outputs = []) :
    ∀ nid nd, (delays.foldl repFoldlStep (initIds, w₀)).2.getNode nid = some nd →
    nd.outputs = [] := by
  induction delays generalizing initIds w₀ with
  | nil => simpa using h_w
  | cons d rest ih =>
    simp only [List.foldl_cons]
    apply ih
    · exact World.addNode_ids_lt_nextId _ _ h_ids
    · exact repFoldlStep_preserves_outputs_empty _ _ h_ids h_w

theorem buildChainPre_empty_outputs (name : String) (c : ChainSpec) :
    ∀ nid nd, (buildChainPre World.empty name c).2.1.getNode nid = some nd → nd.outputs = [] := by
  intro nid nd h_get
  dsimp [buildChainPre] at h_get
  have h₀ : ∀ nid' nd', (World.empty : World).getNode nid' = some nd' → nd'.outputs = [] := by
    intro nid' nd' h; simp [World.empty, World.getNode] at h
  have h_ids₀ : ∀ p ∈ (World.empty : World).nodes, p.1 < World.empty.nextId := by
    simp [World.empty]
  have h₁ := addNode_preserves_outputs_empty World.empty
    { kind := .input, sigLevel := 0, inputs := [], outputs := [] } h_ids₀ h₀ (by rfl)
  have h_ids₁ := World.addNode_ids_lt_nextId World.empty
    { kind := .input, sigLevel := 0, inputs := [], outputs := [] } h_ids₀
  have h₂ := addNode_preserves_outputs_empty _
    { kind := .observer, sigLevel := 0, inputs := [], outputs := [] } h_ids₁ h₁ (by rfl)
  have h_ids₂ := World.addNode_ids_lt_nextId _
    { kind := .observer, sigLevel := 0, inputs := [], outputs := [] } h_ids₁
  have h₃ := foldl_repFoldlStep_preserves_outputs_empty c.middleDelays [] _ h_ids₂ h₂
  have h_ids₃ : ∀ p ∈ (c.middleDelays.foldl repFoldlStep ([],
      (World.empty.addNode { kind := .input, sigLevel := 0, inputs := [], outputs := [] }).2.addNode
      { kind := .observer, sigLevel := 0, inputs := [], outputs := [] } |>.2)).2.nodes,
      p.1 < (c.middleDelays.foldl repFoldlStep ([],
      (World.empty.addNode { kind := .input, sigLevel := 0, inputs := [], outputs := [] }).2.addNode
      { kind := .observer, sigLevel := 0, inputs := [], outputs := [] } |>.2)).2.nextId :=
    foldl_repFoldlStep_ids_lt_nextId c.middleDelays [] _ h_ids₂
  have h₄ := addNode_preserves_outputs_empty _
    { kind := .repeater c.lastDelay (-1), sigLevel := 0, inputs := [], outputs := [] } h_ids₃ h₃ (by rfl)
  have h_ids₄ := World.addNode_ids_lt_nextId _
    { kind := .repeater c.lastDelay (-1), sigLevel := 0, inputs := [], outputs := [] } h_ids₃
  have h₅ := addNode_preserves_outputs_empty _
    { kind := .output name, sigLevel := 0, inputs := [], outputs := [] } h_ids₄ h₄ (by rfl)
  exact h₅ nid nd h_get

/-- All nodes in `buildChainPre World.empty` have empty inputs. -/
theorem addNode_preserves_inputs_empty (w : World) (nd : NodeData)
    (h_ids : ∀ p ∈ w.nodes, p.1 < w.nextId)
    (h_w : ∀ nid nd', w.getNode nid = some nd' → nd'.inputs = [])
    (h_nd : nd.inputs = []) :
    ∀ nid nd', (w.addNode nd).2.getNode nid = some nd' → nd'.inputs = [] := by
  intro nid nd' h_get
  by_cases h_eq : nid = w.nextId
  · subst h_eq
    have h_fresh : w.getNode w.nextId = none := World.getNode_nextId_none w h_ids
    have h_new := World.addNode_getNode_fresh w nd h_fresh
    rw [h_new] at h_get
    injection h_get with h_nd'
    subst h_nd'
    exact h_nd
  · have h_old := World.addNode_getNode_old w nd nid h_eq
    rw [h_old] at h_get
    exact h_w nid nd' h_get

theorem repFoldlStep_preserves_inputs_empty (acc : List Nat × World) (d : PNat)
    (h_ids : ∀ p ∈ acc.2.nodes, p.1 < acc.2.nextId)
    (h_w : ∀ nid nd, acc.2.getNode nid = some nd → nd.inputs = []) :
    ∀ nid nd, (repFoldlStep acc d).2.getNode nid = some nd → nd.inputs = [] := by
  dsimp [repFoldlStep]
  exact addNode_preserves_inputs_empty acc.2 (mkRepNode d) h_ids h_w (by rfl)

theorem foldl_repFoldlStep_preserves_inputs_empty (delays : List PNat)
    (initIds : List Nat) (w₀ : World)
    (h_ids : ∀ p ∈ w₀.nodes, p.1 < w₀.nextId)
    (h_w : ∀ nid nd, w₀.getNode nid = some nd → nd.inputs = []) :
    ∀ nid nd, (delays.foldl repFoldlStep (initIds, w₀)).2.getNode nid = some nd →
    nd.inputs = [] := by
  induction delays generalizing initIds w₀ with
  | nil => simpa using h_w
  | cons d rest ih =>
    simp only [List.foldl_cons]
    apply ih
    · exact World.addNode_ids_lt_nextId _ _ h_ids
    · exact repFoldlStep_preserves_inputs_empty _ _ h_ids h_w

theorem buildChainPre_empty_inputs (name : String) (c : ChainSpec) :
    ∀ nid nd, (buildChainPre World.empty name c).2.1.getNode nid = some nd → nd.inputs = [] := by
  intro nid nd h_get
  dsimp [buildChainPre] at h_get
  have h₀ : ∀ nid' nd', (World.empty : World).getNode nid' = some nd' → nd'.inputs = [] := by
    intro nid' nd' h; simp [World.empty, World.getNode] at h
  have h_ids₀ : ∀ p ∈ (World.empty : World).nodes, p.1 < World.empty.nextId := by
    simp [World.empty]
  have h₁ := addNode_preserves_inputs_empty World.empty
    { kind := .input, sigLevel := 0, inputs := [], outputs := [] } h_ids₀ h₀ (by rfl)
  have h_ids₁ := World.addNode_ids_lt_nextId World.empty
    { kind := .input, sigLevel := 0, inputs := [], outputs := [] } h_ids₀
  have h₂ := addNode_preserves_inputs_empty _
    { kind := .observer, sigLevel := 0, inputs := [], outputs := [] } h_ids₁ h₁ (by rfl)
  have h_ids₂ := World.addNode_ids_lt_nextId _
    { kind := .observer, sigLevel := 0, inputs := [], outputs := [] } h_ids₁
  have h₃ := foldl_repFoldlStep_preserves_inputs_empty c.middleDelays [] _ h_ids₂ h₂
  have h_ids₃ : ∀ p ∈ (c.middleDelays.foldl repFoldlStep ([],
      (World.empty.addNode { kind := .input, sigLevel := 0, inputs := [], outputs := [] }).2.addNode
      { kind := .observer, sigLevel := 0, inputs := [], outputs := [] } |>.2)).2.nodes,
      p.1 < (c.middleDelays.foldl repFoldlStep ([],
      (World.empty.addNode { kind := .input, sigLevel := 0, inputs := [], outputs := [] }).2.addNode
      { kind := .observer, sigLevel := 0, inputs := [], outputs := [] } |>.2)).2.nextId :=
    foldl_repFoldlStep_ids_lt_nextId c.middleDelays [] _ h_ids₂
  have h₄ := addNode_preserves_inputs_empty _
    { kind := .repeater c.lastDelay (-1), sigLevel := 0, inputs := [], outputs := [] } h_ids₃ h₃ (by rfl)
  have h_ids₄ := World.addNode_ids_lt_nextId _
    { kind := .repeater c.lastDelay (-1), sigLevel := 0, inputs := [], outputs := [] } h_ids₃
  have h₅ := addNode_preserves_inputs_empty _
    { kind := .output name, sigLevel := 0, inputs := [], outputs := [] } h_ids₄ h₄ (by rfl)
  exact h₅ nid nd h_get

/-- The input node created by `buildChainPre` is at `w.nextId`. -/
theorem buildChainPre_getNode_input (w : World) (name : String) (c : ChainSpec)
    (h_ids : ∀ p ∈ w.nodes, p.1 < w.nextId) :
    (buildChainPre w name c).2.1.getNode w.nextId =
    some { kind := .input, sigLevel := 0, inputs := [], outputs := [] } := by
  dsimp (config := { zeta := true }) [buildChainPre]
  set w₁ := (w.addNode { kind := .input, sigLevel := 0, inputs := [], outputs := [] }).2
  set w₂ := (w₁.addNode { kind := .observer, sigLevel := 0, inputs := [], outputs := [] }).2
  set w₃ := (c.middleDelays.foldl repFoldlStep ([], w₂)).2
  set w₄ := (w₃.addNode { kind := .repeater c.lastDelay (-1), sigLevel := 0, inputs := [], outputs := [] }).2
  set w₅ := (w₄.addNode { kind := .output name, sigLevel := 0, inputs := [], outputs := [] }).2
  have h₁ : w₁.getNode w.nextId =
      some { kind := .input, sigLevel := 0, inputs := [], outputs := [] } :=
    World.addNode_getNode_fresh w _ (World.getNode_nextId_none w h_ids)
  have h_ids₁ := World.addNode_ids_lt_nextId w
    ({ kind := .input, sigLevel := 0, inputs := [], outputs := [] } : NodeData) h_ids
  have h₂ : w₂.getNode w.nextId = w₁.getNode w.nextId := by
    apply World.addNode_getNode_old; dsimp [w₂, w₁, World.addNode]; omega
  have h₃ : w₃.getNode w.nextId = w₂.getNode w.nextId := by
    apply foldl_repFoldlStep_getNode_old; dsimp [w₂, w₁, World.addNode]; omega
  have h_w3_ge : w₂.nextId ≤ w₃.nextId := by
    dsimp [w₃]; apply foldl_repFoldlStep_nextId_ge
  have h₄ : w₄.getNode w.nextId = w₃.getNode w.nextId := by
    apply World.addNode_getNode_old
    dsimp [w₂, w₁, World.addNode] at h_w3_ge ⊢; omega
  have h₅ : w₅.getNode w.nextId = w₄.getNode w.nextId := by
    apply World.addNode_getNode_old
    dsimp [w₅, w₄, w₃, w₂, w₁, World.addNode, repFoldlStep] at h_w3_ge ⊢; omega
  rw [h₅, h₄, h₃, h₂, h₁]

/-- The observer node created by `buildChainPre` is at `w.nextId + 1`. -/
theorem buildChainPre_getNode_observer (w : World) (name : String) (c : ChainSpec)
    (h_ids : ∀ p ∈ w.nodes, p.1 < w.nextId) :
    (buildChainPre w name c).2.1.getNode (w.nextId + 1) =
    some { kind := .observer, sigLevel := 0, inputs := [], outputs := [] } := by
  dsimp (config := { zeta := true }) [buildChainPre]
  set w₁ := (w.addNode { kind := .input, sigLevel := 0, inputs := [], outputs := [] }).2
  set w₂ := (w₁.addNode { kind := .observer, sigLevel := 0, inputs := [], outputs := [] }).2
  set w₃ := (c.middleDelays.foldl repFoldlStep ([], w₂)).2
  set w₄ := (w₃.addNode { kind := .repeater c.lastDelay (-1), sigLevel := 0, inputs := [], outputs := [] }).2
  set w₅ := (w₄.addNode { kind := .output name, sigLevel := 0, inputs := [], outputs := [] }).2
  have h_ids₁ := World.addNode_ids_lt_nextId w
    ({ kind := .input, sigLevel := 0, inputs := [], outputs := [] } : NodeData) h_ids
  have h_nextId₁ : w₁.nextId = w.nextId + 1 := by dsimp [w₁, World.addNode]
  have h₂ : w₂.getNode (w.nextId + 1) =
      some { kind := .observer, sigLevel := 0, inputs := [], outputs := [] } := by
    rw [← h_nextId₁]
    exact World.addNode_getNode_fresh w₁ _ (World.getNode_nextId_none w₁ h_ids₁)
  have h₃ : w₃.getNode (w.nextId + 1) = w₂.getNode (w.nextId + 1) := by
    apply foldl_repFoldlStep_getNode_old
    dsimp [w₂, w₁, World.addNode]; omega
  have h_w3_ge : w₂.nextId ≤ w₃.nextId := by
    dsimp [w₃]; apply foldl_repFoldlStep_nextId_ge
  have h₄ : w₄.getNode (w.nextId + 1) = w₃.getNode (w.nextId + 1) := by
    apply World.addNode_getNode_old
    dsimp [w₂, w₁, World.addNode] at h_w3_ge ⊢; omega
  have h₅ : w₅.getNode (w.nextId + 1) = w₄.getNode (w.nextId + 1) := by
    apply World.addNode_getNode_old
    dsimp [w₅, w₄, w₃, w₂, w₁, World.addNode, repFoldlStep] at h_w3_ge ⊢; omega
  rw [h₅, h₄, h₃, h₂]

/-- After `connectChain w (hd :: hd₂ :: tl)` with `hd ∉ hd₂ :: tl`,
    the head node's outputs gain exactly `[hd₂]`. -/
theorem connectChain_head_outputs (w : World) (hd hd₂ : Nat) (tl : List Nat) (nd₀ : NodeData)
    (h₀ : w.getNode hd = some nd₀) (h_not : hd ∉ hd₂ :: tl) :
    (connectChain w (hd :: hd₂ :: tl)).getNode hd =
    some ({ nd₀ with outputs := nd₀.outputs ++ [hd₂] } : NodeData) := by
  set w₁ := (w.updateNode hd₂ (fun nd => { nd with inputs := nd.inputs ++ [hd] })).updateNode hd
    (fun nd => { nd with outputs := nd.outputs ++ [hd₂] })
  have h_decomp : connectChain w (hd :: hd₂ :: tl) = connectChain w₁ (hd₂ :: tl) := by
    dsimp [connectChain, w₁]
  rw [h_decomp, connectChain_getNode_of_not_mem (hd₂ :: tl) hd h_not w₁]
  dsimp [w₁]
  have h_ne : hd₂ ≠ hd := by intro h; apply h_not; simp [h]
  have h₁ : (w.updateNode hd₂ (fun nd => { nd with inputs := nd.inputs ++ [hd] })).getNode hd =
      some nd₀ := by
    rw [World.updateNode_getNode_ne w hd₂ hd _ h_ne]; exact h₀
  exact World.updateNode_getNode_eq _ hd _ nd₀ h₁

theorem World.onScheduledTick_nextId (w : World) (id : Nat) :
    (w.onScheduledTick id).nextId = w.nextId := by
  dsimp [World.onScheduledTick]
  split
  · rfl
  · rename_i nd; split
    · dsimp [World.updateNode]; exact World.notifyOutputs_nextId _ _
    · dsimp [World.updateNode]; exact World.notifyOutputs_nextId _ _
    · rfl

theorem World.step_nextId (w : World) :
    ∀ w', w.step = some w' → w'.nextId = w.nextId := by
  intro w' h
  dsimp [World.step] at h
  cases h_pop : w.popNextEvent with
  | none => simp [h_pop] at h
  | some p =>
    cases p with
    | mk ev w_pop =>
      simp only [h_pop] at h
      injection h with h_w'
      rw [← h_w', World.onScheduledTick_nextId]
      exact World.popNextEvent_nextId w ev w_pop h_pop

theorem processNEvents_nextId (w : World) (n : Nat) :
    (processNEvents w n).nextId = w.nextId := by
  induction n generalizing w with
  | zero => rfl
  | succ n' ih =>
    dsimp [processNEvents]
    cases h : w.step with
    | none => rfl
    | some w' => rw [ih w', World.step_nextId w w' h]

theorem World.stepUntilNextTick_nextId (w : World) :
    (w.stepUntilNextTick).nextId = w.nextId := by
  induction w using World.stepUntilNextTick.induct with
  | case1 w h =>
    rw [stepUntilNextTick_of_step_none w h]
  | case2 w w' h_step ih =>
    have h_sunt : w.stepUntilNextTick = w'.stepUntilNextTick := by
      rw [World.stepUntilNextTick, h_step]
    rw [h_sunt, ih, World.step_nextId w w' h_step]

theorem World.setInput_nextId (w : World) (id : Nat) (level : Nat) :
    (w.setInput id level).nextId = w.nextId := by
  dsimp (config := { zeta := true }) [World.setInput]
  rw [World.notifyOutputs_nextId]
  rfl

/-- `updateNode` calls commute for nodes when the IDs differ. -/
theorem updateNode_comm_nodes (w : World) (id₁ id₂ : Nat) (f g : NodeData → NodeData)
    (h_ne : id₁ ≠ id₂) :
    ((w.updateNode id₁ f).updateNode id₂ g).nodes =
    ((w.updateNode id₂ g).updateNode id₁ f).nodes := by
  have h_ne' : id₂ ≠ id₁ := Ne.symm h_ne
  dsimp [World.updateNode]
  rw [List.map_map, List.map_map]
  congr 1; ext ⟨nid, nd⟩
  all_goals
    by_cases h₁ : nid = id₁ <;> by_cases h₂ : nid = id₂
    · exfalso; exact h_ne (h₁.symm.trans h₂)
    · simp [h₁, h_ne]
    · simp [h₂, h_ne']
    · simp [h₁, h₂]

/-- `notifyOutputs` followed by `updateNode` gives the same nodes as just `updateNode`. -/
theorem notifyOutputs_updateNode_nodes (w : World) (id₁ id₂ : Nat) (f : NodeData → NodeData) :
    ((w.notifyOutputs id₁).updateNode id₂ f).nodes = (w.updateNode id₂ f).nodes := by
  dsimp [World.updateNode]; rw [World.notifyOutputs_nodes]

/-- `setInput` and `onScheduledTick` commute for nodes when `in2` is not
in the ticked node's inputs and `in2 ≠ id`. -/
theorem setInput_onScheduledTick_comm_nodes (w : World) (in2 id : Nat)
    (h_id_ne : id ≠ in2)
    (h_sep : ∀ nd, w.getNode id = some nd → in2 ∉ nd.inputs) :
    ((w.setInput in2 15).onScheduledTick id).nodes =
    ((w.onScheduledTick id).setInput in2 15).nodes := by
  have h_gis : (w.setInput in2 15).getInputSignal id = w.getInputSignal id :=
    setInput_getInputSignal_ne w in2 id 15 h_sep
  have h_getNode : (w.setInput in2 15).getNode id = w.getNode id := by
    dsimp [World.setInput]; rw [World.notifyOutputs_getNode]
    exact World.updateNode_getNode_ne w in2 id _ (Ne.symm h_id_ne)
  dsimp [World.onScheduledTick]
  rw [h_getNode, h_gis]
  split
  · simp [World.setInput, World.notifyOutputs_nodes]
  · rename_i nd
    split
    · -- repeater
      simp only [World.setInput, World.notifyOutputs_nodes, notifyOutputs_updateNode_nodes]
      apply updateNode_comm_nodes; exact Ne.symm h_id_ne
    · -- observer
      simp only [World.setInput, World.notifyOutputs_nodes, notifyOutputs_updateNode_nodes]
      apply updateNode_comm_nodes; exact Ne.symm h_id_ne
    · -- output/input
      rfl

/-- The filter of indexed events, mapped to events, equals the plain filter. -/
theorem zip_filter_map_snd_eq (idxs : List Nat) (l : List ScheduledEvent) (t : Nat)
    (h_len : idxs.length = l.length) :
    ((List.zip idxs l).filter (fun (_, e) => e.targetTick == t)).map Prod.snd =
    l.filter (fun e => e.targetTick == t) := by
  revert idxs h_len
  induction l with
  | nil => intro idxs h_len; cases idxs <;> simp_all
  | cons hd tl ih =>
    intro idxs h_len
    cases idxs with
    | nil => simp at h_len
    | cons hi ti =>
      simp only [List.length_cons] at h_len
      show ((List.zip (hi :: ti) (hd :: tl)).filter (fun (_, e) => e.targetTick == t)).map Prod.snd =
        (hd :: tl).filter (fun e => e.targetTick == t)
      simp only [List.zip, List.filter]
      have h_len' : ti.length = tl.length := by omega
      by_cases h_p : (hd.targetTick == t) = true <;> simp [h_p]
      · exact ih ti h_len'
      · exact ih ti h_len'
