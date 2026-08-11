import BasicProofs.GroupClustering.SimulationHealth


open BasicRedstoneSim

/-! # Group clustering — node layout of the built world

Chain `ci` in group `gi` occupies the consecutive ids
`chainBaseId groups gi ci` through
`chainBaseId groups gi ci + c.middleDelays.length + 3`:
input, observer, middle repeaters (priority −3), last repeater (priority −1),
output. In particular the chain's observer is `chainBaseId groups gi ci + 1`,
which is exactly what `(buildGroups groups).2[gi][ci]` returns. This part
proves the id arithmetic and the observer-id characterization; the getNode
layout of the individual nodes follows in the second half.
-/

/-- Number of nodes built for one chain. -/
def chainNodeCount (c : ChainSpec) : Nat := c.middleDelays.length + 4

/-- Total number of nodes built for one group. -/
def groupNodeCount (g : GroupSpec) : Nat := (g.map chainNodeCount).sum

/-- First node id of chain `ci` in group `gi` inside `(buildGroups groups).1`. -/
def chainBaseId (groups : List GroupSpec) (gi ci : Nat) : Nat :=
  ((groups.take gi).map groupNodeCount).sum +
  (((groupAt groups gi).take ci).map chainNodeCount).sum

/-- `groupAt` on a cons list, index 0. -/
theorem groupAt_zero (g : GroupSpec) (gs : List GroupSpec) :
    groupAt (g :: gs) 0 = g := by
  simp [groupAt]

/-- `groupAt` on a cons list, successor index. -/
theorem groupAt_succ (g : GroupSpec) (gs : List GroupSpec) (gi : Nat) :
    groupAt (g :: gs) (gi + 1) = groupAt gs gi := by
  simp [groupAt]

/-- Looking up index 0 of a cons list via `getElem?`. -/
private theorem cons_getElem?_zero {α : Type} (x : α) (xs : List α) :
    (x :: xs)[0]? = some x := by
  simp

/-- `buildChain` returns the fresh input id as its first component. -/
theorem buildChain_fst_nextId (w : World) (name : String) (c : ChainSpec) :
    (buildChain w name c).1 = w.nextId := by
  dsimp (config := { zeta := true }) [buildChain, buildChainPre]
  simp [World.addNode]

/-- Building one group's chains advances `nextId` by the group's node count. -/
theorem buildGroupChainsFrom_nextId (gi start : Nat) (w : World) (g : List ChainSpec) :
    (buildGroupChainsFrom gi start w g).1.nextId = w.nextId + groupNodeCount g := by
  induction g generalizing w start with
  | nil => simp [buildGroupChainsFrom, groupNodeCount]
  | cons c cs ih =>
    dsimp [buildGroupChainsFrom]
    rw [ih, buildChain_nextId]
    dsimp [groupNodeCount, chainNodeCount]
    omega

/-- Building all groups advances `nextId` by the total node count. -/
theorem buildGroupsFrom_nextId (start : Nat) (w : World) (groups : List GroupSpec) :
    (buildGroupsFrom start w groups).1.nextId =
    w.nextId + (groups.map groupNodeCount).sum := by
  induction groups generalizing w start with
  | nil => simp [buildGroupsFrom]
  | cons g gs ih =>
    dsimp [buildGroupsFrom]
    rw [ih, buildGroupChains, buildGroupChainsFrom_nextId]
    dsimp [groupNodeCount]
    omega

/-- The observer-id list of one group has one entry per chain. -/
theorem buildGroupChainsFrom_snd_length (gi start : Nat) (w : World)
    (g : List ChainSpec) :
    (buildGroupChainsFrom gi start w g).2.length = g.length := by
  induction g generalizing w start with
  | nil => simp [buildGroupChainsFrom]
  | cons c cs ih =>
    dsimp [buildGroupChainsFrom]
    rw [ih]

/-- Element `ci` of the observer-id list of one group is
    `w.nextId + (node counts of the preceding chains) + 1`. -/
theorem buildGroupChainsFrom_snd_getElem? (gi start : Nat) (w : World)
    (g : List ChainSpec) (ci : Nat) (h_ci : ci < g.length) :
    (buildGroupChainsFrom gi start w g).2[ci]? =
    some (w.nextId + ((g.take ci).map chainNodeCount).sum + 1) := by
  revert ci h_ci
  induction g generalizing w start with
  | nil => intro ci h_ci; cases h_ci
  | cons c cs ih =>
    intro ci h_ci
    dsimp [buildGroupChainsFrom]
    cases ci with
    | zero =>
      rw [cons_getElem?_zero, buildChain_fst_nextId]
      simp
    | succ ci' =>
      rw [List.getElem?_cons_succ]
      have h_ci' : ci' < cs.length := by simpa using h_ci
      rw [ih (start + 1) (buildChain w (chainName gi start) c).2 ci' h_ci',
        buildChain_nextId]
      congr 1
      simp [chainNodeCount]
      omega

/-- Combined lookup: the `ci`-th observer of group `gi` inside
    `buildGroupsFrom start w groups` has id
    `w.nextId + chainBaseId groups gi ci + 1`. -/
theorem buildGroupsFrom_snd_getElem_getElem? (start : Nat) (w : World)
    (groups : List GroupSpec) (gi ci : Nat)
    (h_gi : gi < groups.length) (h_ci : ci < (groupAt groups gi).length) :
    ((buildGroupsFrom start w groups).2[gi]?.getD [])[ci]? =
    some (w.nextId + chainBaseId groups gi ci + 1) := by
  revert gi ci h_gi h_ci
  induction groups generalizing w start with
  | nil => intro gi ci h_gi; cases h_gi
  | cons g gs ih =>
    intro gi ci h_gi h_ci
    dsimp [buildGroupsFrom]
    cases gi with
    | zero =>
      rw [cons_getElem?_zero, Option.getD_some]
      dsimp [buildGroupChains]
      rw [buildGroupChainsFrom_snd_getElem? start 0 w g ci (by
        simpa [groupAt_zero] using h_ci)]
      congr 1
      simp [chainBaseId, groupAt]
    | succ gi' =>
      rw [List.getElem?_cons_succ]
      have h_gi' : gi' < gs.length := by simpa using h_gi
      have h_ci' : ci < (groupAt gs gi').length := by
        simpa [groupAt_succ] using h_ci
      rw [ih (start + 1) (buildGroupChains start w g).1 gi' ci h_gi' h_ci']
      congr 1
      rw [buildGroupChains, buildGroupChainsFrom_nextId]
      simp [chainBaseId, groupAt]
      omega

/-- The observer ids of the built world, as used by the simulation. -/
theorem buildGroups_snd_getElem_getElem? (groups : List GroupSpec) (gi ci : Nat)
    (h_gi : gi < groups.length) (h_ci : ci < (groupAt groups gi).length) :
    ((buildGroups groups).2[gi]?.getD [])[ci]? =
    some (chainBaseId groups gi ci + 1) := by
  have h := buildGroupsFrom_snd_getElem_getElem? 0 World.empty groups gi ci h_gi h_ci
  simpa [buildGroups, World.empty] using h


/-! ## Node kinds of a single chain before wiring

Combined with `buildChainPre_getNode_input` and `buildChainPre_getNode_observer`
(from PrefixChain), these give the kind of every node of a freshly built chain.
-/

/-- The `k`-th middle repeater of a chain, before wiring. -/
theorem buildChainPre_getNode_middleRep (w : World) (name : String) (c : ChainSpec)
    (h_ids : ∀ p ∈ w.nodes, p.1 < w.nextId) (k : Nat)
    (h_k : k < c.middleDelays.length) :
    (buildChainPre w name c).2.1.getNode (w.nextId + 2 + k) =
    some (mkRepNode c.middleDelays[k]) := by
  dsimp (config := { zeta := true }) [buildChainPre]
  set w₁ := (w.addNode
    { kind := .input, sigLevel := 0, inputs := [], outputs := [] }).2
  set w₂ := (w₁.addNode
    { kind := .observer, sigLevel := 0, inputs := [], outputs := [] }).2
  set w₃ := (c.middleDelays.foldl repFoldlStep ([], w₂)).2
  set w₄ := (w₃.addNode
    { kind := .repeater c.lastDelay (-1), sigLevel := 0, inputs := [], outputs := [] }).2
  set w₅ := (w₄.addNode
    { kind := .output name, sigLevel := 0, inputs := [], outputs := [] }).2
  have h_ids₂ : ∀ p ∈ w₂.nodes, p.1 < w₂.nextId :=
    World.addNode_ids_lt_nextId w₁ _ (World.addNode_ids_lt_nextId w _ h_ids)
  have h_nextId₂ : w₂.nextId = w.nextId + 2 := by
    dsimp [w₂, w₁]
    rw [World.addNode_nextId, World.addNode_nextId]
  have h_nextId₃ : w₃.nextId = w.nextId + 2 + c.middleDelays.length := by
    dsimp [w₃]
    rw [foldl_repFoldlStep_nextId_eq, h_nextId₂]
  have h_rep₃ : w₃.getNode (w.nextId + 2 + k) = some (mkRepNode c.middleDelays[k]) := by
    have := foldl_repFoldlStep_getNode_rep c.middleDelays w₂ h_ids₂ k h_k
    rwa [h_nextId₂] at this
  have h_old₄ : w₄.getNode (w.nextId + 2 + k) = w₃.getNode (w.nextId + 2 + k) :=
    World.addNode_getNode_old w₃ _ (w.nextId + 2 + k) (by rw [h_nextId₃]; omega)
  have h_old₅ : w₅.getNode (w.nextId + 2 + k) = w₄.getNode (w.nextId + 2 + k) :=
    World.addNode_getNode_old w₄ _ (w.nextId + 2 + k) (by
      dsimp [w₄, World.addNode]; rw [h_nextId₃]; omega)
  rw [h_old₅, h_old₄]
  exact h_rep₃

/-- The last repeater of a chain, before wiring. -/
theorem buildChainPre_getNode_lastRep (w : World) (name : String) (c : ChainSpec)
    (h_ids : ∀ p ∈ w.nodes, p.1 < w.nextId) :
    (buildChainPre w name c).2.1.getNode (w.nextId + c.middleDelays.length + 2) =
    some { kind := .repeater c.lastDelay (-1), sigLevel := 0,
           inputs := [], outputs := [] } := by
  dsimp (config := { zeta := true }) [buildChainPre]
  set w₁ := (w.addNode
    { kind := .input, sigLevel := 0, inputs := [], outputs := [] }).2
  set w₂ := (w₁.addNode
    { kind := .observer, sigLevel := 0, inputs := [], outputs := [] }).2
  set w₃ := (c.middleDelays.foldl repFoldlStep ([], w₂)).2
  set w₄ := (w₃.addNode
    { kind := .repeater c.lastDelay (-1), sigLevel := 0, inputs := [], outputs := [] }).2
  have h_ids₂ : ∀ p ∈ w₂.nodes, p.1 < w₂.nextId :=
    World.addNode_ids_lt_nextId w₁ _ (World.addNode_ids_lt_nextId w _ h_ids)
  have h_nextId₃ : w₃.nextId = w.nextId + 2 + c.middleDelays.length := by
    dsimp [w₃]
    rw [foldl_repFoldlStep_nextId_eq]
    dsimp [w₂, w₁]
    rw [World.addNode_nextId, World.addNode_nextId]
  have h_old : (w₄.addNode
      { kind := .output name, sigLevel := 0, inputs := [], outputs := [] }).2.getNode
      (w.nextId + c.middleDelays.length + 2) =
      w₄.getNode (w.nextId + c.middleDelays.length + 2) :=
    World.addNode_getNode_old w₄ _ (w.nextId + c.middleDelays.length + 2) (by
      dsimp [w₄, World.addNode]; rw [h_nextId₃]; omega)
  rw [h_old]
  rw [show w.nextId + c.middleDelays.length + 2 = w₃.nextId from by
    rw [h_nextId₃]; omega]
  exact World.addNode_getNode_fresh w₃ _
    (World.getNode_nextId_none w₃ (foldl_repFoldlStep_ids_lt_nextId c.middleDelays [] w₂ h_ids₂))

/-- The output node of a chain, before wiring. -/
theorem buildChainPre_getNode_outputNode (w : World) (name : String) (c : ChainSpec)
    (h_ids : ∀ p ∈ w.nodes, p.1 < w.nextId) :
    (buildChainPre w name c).2.1.getNode (w.nextId + c.middleDelays.length + 3) =
    some { kind := .output name, sigLevel := 0, inputs := [], outputs := [] } := by
  dsimp (config := { zeta := true }) [buildChainPre]
  set w₁ := (w.addNode
    { kind := .input, sigLevel := 0, inputs := [], outputs := [] }).2
  set w₂ := (w₁.addNode
    { kind := .observer, sigLevel := 0, inputs := [], outputs := [] }).2
  set w₃ := (c.middleDelays.foldl repFoldlStep ([], w₂)).2
  set w₄ := (w₃.addNode
    { kind := .repeater c.lastDelay (-1), sigLevel := 0, inputs := [], outputs := [] }).2
  have h_ids₃ : ∀ p ∈ w₃.nodes, p.1 < w₃.nextId :=
    foldl_repFoldlStep_ids_lt_nextId c.middleDelays [] w₂ (by
      dsimp [w₂, w₁]
      exact World.addNode_ids_lt_nextId w₁ _ (World.addNode_ids_lt_nextId w _ h_ids))
  have h_nextId₄ : w₄.nextId = w.nextId + 3 + c.middleDelays.length := by
    dsimp [w₄, w₃]
    rw [World.addNode_nextId, foldl_repFoldlStep_nextId_eq]
    dsimp [w₂, w₁]
    rw [World.addNode_nextId, World.addNode_nextId]
    omega
  rw [show w.nextId + c.middleDelays.length + 3 = w₄.nextId from by
    rw [h_nextId₄]; omega]
  exact World.addNode_getNode_fresh w₄ _
    (World.getNode_nextId_none w₄ (World.addNode_ids_lt_nextId w₃ _ h_ids₃))

/-- A variant of `buildChain_outputs_consecutive` without the (unused)
    empty-outputs premise on the base world. -/
theorem buildChain_outputs_consecutive' (w : World) (name : String) (c : ChainSpec)
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


/-! ## Lifting node facts into the built world -/

/-- Building more chains of a group does not change `getNode` at old ids. -/
theorem buildGroupChainsFrom_getNode_old (gi start : Nat) (w : World)
    (g : List ChainSpec) (nid : Nat) (h_nid : nid < w.nextId) :
    (buildGroupChainsFrom gi start w g).1.getNode nid = w.getNode nid := by
  induction g generalizing w start with
  | nil => simp [buildGroupChainsFrom]
  | cons c cs ih =>
    dsimp [buildGroupChainsFrom]
    rw [ih (start + 1) (buildChain w (chainName gi start) c).2 (by
      rw [buildChain_nextId]; omega)]
    exact buildChain_getNode_old w (chainName gi start) c nid h_nid

/-- Building more groups does not change `getNode` at old ids. -/
theorem buildGroupsFrom_getNode_old (start : Nat) (w : World)
    (groups : List GroupSpec) (nid : Nat) (h_nid : nid < w.nextId) :
    (buildGroupsFrom start w groups).1.getNode nid = w.getNode nid := by
  induction groups generalizing w start with
  | nil => simp [buildGroupsFrom]
  | cons g gs ih =>
    dsimp [buildGroupsFrom, buildGroupChains]
    rw [ih (start + 1) (buildGroupChainsFrom start 0 w g).1 (by
      rw [buildGroupChainsFrom_nextId]; omega)]
    exact buildGroupChainsFrom_getNode_old start 0 w g nid h_nid

/-- Building a group's chains splits at any prefix: building all of `g`
    equals building the first `ci` chains, then the rest. -/
theorem buildGroupChainsFrom_eq_take_drop (gi start : Nat) (w : World)
    (g : List ChainSpec) (ci : Nat) (h_ci : ci ≤ g.length) :
    (buildGroupChainsFrom gi start w g).1 =
    (buildGroupChainsFrom gi (start + ci)
      (buildGroupChainsFrom gi start w (g.take ci)).1 (g.drop ci)).1 := by
  revert h_ci ci w start
  induction g with
  | nil =>
    intro start w ci h_ci
    cases ci with
    | zero => simp [buildGroupChainsFrom]
    | succ ci' => cases h_ci
  | cons c cs ih =>
    intro start w ci h_ci
    cases ci with
    | zero => simp [buildGroupChainsFrom]
    | succ ci' =>
      have h_ci' : ci' ≤ cs.length := by
        simp [List.length_cons] at h_ci
        omega
      dsimp [buildGroupChainsFrom]
      rw [ih (start + 1) (buildChain w (chainName gi start) c).2 ci' h_ci']
      apply congrArg (fun n => (buildGroupChainsFrom gi n
        (buildGroupChainsFrom gi (start + 1)
          (buildChain w (chainName gi start) c).2 (cs.take ci')).1
        (cs.drop ci')).1)
      omega

/-- Building all groups splits at any prefix: building all of `groups`
    equals building the first `gi` groups, then the rest. -/
theorem buildGroupsFrom_eq_take_drop (start : Nat) (w : World)
    (groups : List GroupSpec) (gi : Nat) (h_gi : gi ≤ groups.length) :
    (buildGroupsFrom start w groups).1 =
    (buildGroupsFrom (start + gi)
      (buildGroupsFrom start w (groups.take gi)).1 (groups.drop gi)).1 := by
  revert h_gi gi w start
  induction groups with
  | nil =>
    intro start w gi h_gi
    cases gi with
    | zero => simp [buildGroupsFrom]
    | succ gi' => cases h_gi
  | cons g gs ih =>
    intro start w gi h_gi
    cases gi with
    | zero => simp [buildGroupsFrom]
    | succ gi' =>
      have h_gi' : gi' ≤ gs.length := by
        simp [List.length_cons] at h_gi
        omega
      dsimp [buildGroupsFrom, buildGroupChains]
      rw [ih (start + 1) (buildGroupChainsFrom start 0 w g).1 gi' h_gi']
      apply congrArg (fun n => (buildGroupsFrom n
        (buildGroupsFrom (start + 1)
          (buildGroupChainsFrom start 0 w g).1 (gs.take gi')).1
        (gs.drop gi')).1)
      omega


instance : Inhabited GroupSpec := ⟨[]⟩
instance : Inhabited ChainSpec := ⟨defaultSpec⟩

/-- Dropping `i` elements from a list with `i < length` yields a cons
    (stated with `getElem?`/`getD`, matching `groupAt`/`chainAt`). -/
private theorem drop_eq_cons? {α : Type} [Inhabited α] (l : List α) (i : Nat)
    (h : i < l.length) :
    l.drop i = l[i]?.getD default :: l.drop (i + 1) := by
  revert i h
  induction l with
  | nil => intro i h; cases h
  | cons x xs ih =>
    intro i h
    cases i with
    | zero => simp [List.drop]
    | succ i' =>
      simp only [List.drop, List.getElem?_cons_succ]
      apply ih
      simpa [List.length_cons] using h

/-- In bounds, `getD` does not depend on the default value. -/
private theorem getD_getElem?_cong {α : Type} (l : List α) (i : Nat)
    (h : i < l.length) (d₁ d₂ : α) : l[i]?.getD d₁ = l[i]?.getD d₂ := by
  revert i h
  induction l with
  | nil => intro i h; cases h
  | cons x xs ih =>
    intro i h
    cases i with
    | zero => simp
    | succ i' =>
      simp only [List.getElem?_cons_succ]
      apply ih
      simpa [List.length_cons] using h

/-- Decompose the built world around chain `(gi, ci)`: the final world is
    obtained by building that chain on top of the world `W_ci` of all earlier
    chains, whose `nextId` is exactly `chainBaseId groups gi ci`, and then
    building the remaining chains and groups. -/
theorem buildGroups_chain_decomp (groups : List GroupSpec) (gi ci : Nat)
    (h_gi : gi < groups.length) (h_ci : ci < (groupAt groups gi).length) :
    ∃ (W_ci : World),
      W_ci = (buildGroupChainsFrom gi 0
        (buildGroupsFrom 0 World.empty (groups.take gi)).1
        ((groupAt groups gi).take ci)).1 ∧
      W_ci.nextId = chainBaseId groups gi ci ∧
      (buildGroups groups).1 =
      (buildGroupsFrom (gi + 1)
        (buildGroupChainsFrom gi (ci + 1)
          (buildChain W_ci (chainName gi ci) (chainAt groups gi ci)).2
          ((groupAt groups gi).drop (ci + 1))).1
        (groups.drop (gi + 1))).1 := by
  set W_g := (buildGroupsFrom 0 World.empty (groups.take gi)).1
  set W_ci := (buildGroupChainsFrom gi 0 W_g ((groupAt groups gi).take ci)).1
  refine ⟨W_ci, rfl, ?_, ?_⟩
  · dsimp [W_ci, W_g]
    rw [buildGroupChainsFrom_nextId, buildGroupsFrom_nextId]
    dsimp [chainBaseId, groupNodeCount, World.empty]
    omega
  · dsimp [buildGroups]
    rw [buildGroupsFrom_eq_take_drop 0 World.empty groups gi (le_of_lt h_gi)]
    have h_drop_g : groups.drop gi = groupAt groups gi :: groups.drop (gi + 1) := by
      dsimp [groupAt]
      exact drop_eq_cons? groups gi h_gi
    rw [h_drop_g, show 0 + gi = gi from by omega]
    dsimp [buildGroupsFrom, buildGroupChains]
    rw [buildGroupChainsFrom_eq_take_drop gi 0 W_g (groupAt groups gi) ci
      (le_of_lt h_ci)]
    have h_drop_c : (groupAt groups gi).drop ci =
        chainAt groups gi ci :: (groupAt groups gi).drop (ci + 1) := by
      dsimp [chainAt]
      exact drop_eq_cons? (groupAt groups gi) ci h_ci
    rw [h_drop_c, show 0 + ci = ci from by omega]
    dsimp [buildGroupChainsFrom]
    rfl

/-! ## Node structure of individual chains in the built world

For chain `(gi, ci)` with `base := chainBaseId groups gi ci` and
`m := (chainAt groups gi ci).middleDelays.length`, the chain's nodes are
`base` (input), `base + 1` (observer), `base + 2 .. base + 1 + m` (middle
repeaters, priority −3), `base + 2 + m` (last repeater, priority −1) and
`base + 3 + m` (the output node named `chainName gi ci`). Only kinds and
outputs are characterized: inputs and signal levels never influence event
spawning or the output order.
-/

/-- All ids of the pre-chain world of chain `(gi, ci)` are below its
    `nextId`. -/
private theorem buildGroups_chain_pre_ids (groups : List GroupSpec) (gi ci : Nat)
    (_ : gi < groups.length) (_ : ci < (groupAt groups gi).length)
    (W_ci : World)
    (h_Wci : W_ci = (buildGroupChainsFrom gi 0
      (buildGroupsFrom 0 World.empty (groups.take gi)).1
      ((groupAt groups gi).take ci)).1) :
    ∀ p ∈ W_ci.nodes, p.1 < W_ci.nextId := by
  rw [h_Wci]
  intro p hp
  have h_ids_g : ∀ (a : Nat) (b : NodeData), (a, b) ∈
      (buildGroupsFrom 0 World.empty (groups.take gi)).1.nodes →
      a < (buildGroupsFrom 0 World.empty (groups.take gi)).1.nextId := by
    intro a b hab
    exact buildGroupsFrom_ids_lt_nextId 0 World.empty (groups.take gi)
      (by simp [World.empty]) a b hab
  exact buildGroupChainsFrom_ids_lt_nextId gi 0
    (buildGroupsFrom 0 World.empty (groups.take gi)).1 ((groupAt groups gi).take ci)
    h_ids_g p.1 p.2 (by rw [Prod.eta p]; exact hp)

/-- Lift `getNode` at a node of chain `(gi, ci)` from the built world down
    to the world right after that chain was built. -/
private theorem buildGroups_chain_getNode_lift (groups : List GroupSpec)
    (gi ci j : Nat)
    (h_gi : gi < groups.length) (h_ci : ci < (groupAt groups gi).length)
    (h_j : j < (chainAt groups gi ci).middleDelays.length + 4) :
    ∃ W_ci,
      W_ci = (buildGroupChainsFrom gi 0
        (buildGroupsFrom 0 World.empty (groups.take gi)).1
        ((groupAt groups gi).take ci)).1 ∧
      W_ci.nextId = chainBaseId groups gi ci ∧
      (buildGroups groups).1.getNode (chainBaseId groups gi ci + j) =
      (buildChain W_ci (chainName gi ci) (chainAt groups gi ci)).2.getNode
        (chainBaseId groups gi ci + j) := by
  obtain ⟨W_ci, h_Wci, h_b, h_eq⟩ := buildGroups_chain_decomp groups gi ci h_gi h_ci
  refine ⟨W_ci, h_Wci, h_b, ?_⟩
  rw [h_eq]
  rw [buildGroupsFrom_getNode_old (gi + 1)
    (buildGroupChainsFrom gi (ci + 1)
      (buildChain W_ci (chainName gi ci) (chainAt groups gi ci)).2
      ((groupAt groups gi).drop (ci + 1))).1
    (groups.drop (gi + 1)) (chainBaseId groups gi ci + j) (by
      rw [buildGroupChainsFrom_nextId, buildChain_nextId, h_b]
      dsimp [groupNodeCount]
      omega)]
  rw [buildGroupChainsFrom_getNode_old gi (ci + 1)
    (buildChain W_ci (chainName gi ci) (chainAt groups gi ci)).2
    ((groupAt groups gi).drop (ci + 1)) (chainBaseId groups gi ci + j) (by
      rw [buildChain_nextId, h_b]
      omega)]

/-- In the built world, the observer of chain `(gi, ci)` has kind `observer`
    and its single output is the chain's first repeater. -/
theorem buildGroups_observer_node (groups : List GroupSpec) (gi ci : Nat)
    (h_gi : gi < groups.length) (h_ci : ci < (groupAt groups gi).length) :
    ∃ nd, (buildGroups groups).1.getNode (chainBaseId groups gi ci + 1) = some nd ∧
      nd.kind = NodeKind.observer ∧
      nd.outputs = [chainBaseId groups gi ci + 2] := by
  obtain ⟨W_ci, h_Wci, h_b, h_lift⟩ :=
    buildGroups_chain_getNode_lift groups gi ci 1 h_gi h_ci (by omega)
  set c := chainAt groups gi ci
  set base := chainBaseId groups gi ci
  have h_ids := buildGroups_chain_pre_ids groups gi ci h_gi h_ci W_ci h_Wci
  have h_out := buildChain_outputs_consecutive' W_ci (chainName gi ci) c h_ids 1
    (by omega)
  rw [h_b] at h_out
  have h_if : (if 1 + 1 < c.middleDelays.length + 4 then [base + 1 + 1] else []) =
      [base + 2] := by
    simp [show 1 + 1 < c.middleDelays.length + 4 from by omega]
  rw [h_if] at h_out
  cases h_gn : (buildChain W_ci (chainName gi ci) c).2.getNode (base + 1) with
  | none => simp [h_gn] at h_out
  | some nd =>
    simp only [h_gn] at h_out
    injection h_out with h_outputs
    refine ⟨nd, ?_, ?_, h_outputs⟩
    · rw [h_lift]
      exact h_gn
    · dsimp [buildChain] at h_gn
      obtain ⟨nd₀, h_nd₀, h_kind⟩ := connectChain_kind_preserved
        (buildChainPre W_ci (chainName gi ci) c).2.1
        (buildChainPre W_ci (chainName gi ci) c).2.2 (base + 1) nd h_gn
      have h_pre := buildChainPre_getNode_observer W_ci (chainName gi ci) c h_ids
      rw [h_b] at h_pre
      rw [h_pre] at h_nd₀
      have h_eq : nd₀ =
          { kind := .observer, sigLevel := 0, inputs := [], outputs := [] } := by
        apply Option.some_inj.mp
        rw [← h_nd₀]
      rw [← h_kind, h_eq]

/-- In the built world, the `k`-th middle repeater of chain `(gi, ci)` has
    kind `repeater middleDelays[k] (−3)` and its single output is the next
    node of the chain. -/
theorem buildGroups_middleRep_node (groups : List GroupSpec) (gi ci k : Nat)
    (h_gi : gi < groups.length) (h_ci : ci < (groupAt groups gi).length)
    (h_k : k < (chainAt groups gi ci).middleDelays.length) :
    ∃ nd, (buildGroups groups).1.getNode (chainBaseId groups gi ci + 2 + k) = some nd ∧
      nd.kind = NodeKind.repeater (chainAt groups gi ci).middleDelays[k] (-3) ∧
      nd.outputs = [chainBaseId groups gi ci + 3 + k] := by
  obtain ⟨W_ci, h_Wci, h_b, h_lift⟩ :=
    buildGroups_chain_getNode_lift groups gi ci (2 + k) h_gi h_ci (by omega)
  set c := chainAt groups gi ci
  set base := chainBaseId groups gi ci
  have h_assoc : chainBaseId groups gi ci + 2 + k = base + (2 + k) := by
    dsimp [base]
    omega
  rw [h_assoc]
  have h_ids := buildGroups_chain_pre_ids groups gi ci h_gi h_ci W_ci h_Wci
  have h_out := buildChain_outputs_consecutive' W_ci (chainName gi ci) c h_ids
    (2 + k) (by dsimp [c]; omega)
  rw [h_b] at h_out
  have h_if : (if 2 + k + 1 < c.middleDelays.length + 4
      then [base + (2 + k) + 1] else []) = [base + 3 + k] := by
    simp [show 2 + k + 1 < c.middleDelays.length + 4 from by dsimp [c]; omega]
    omega
  rw [h_if] at h_out
  cases h_gn : (buildChain W_ci (chainName gi ci) c).2.getNode (base + (2 + k)) with
  | none => simp [h_gn] at h_out
  | some nd =>
    simp only [h_gn] at h_out
    injection h_out with h_outputs
    refine ⟨nd, ?_, ?_, h_outputs⟩
    · rw [h_lift]
      exact h_gn
    · dsimp [buildChain] at h_gn
      obtain ⟨nd₀, h_nd₀, h_kind⟩ := connectChain_kind_preserved
        (buildChainPre W_ci (chainName gi ci) c).2.1
        (buildChainPre W_ci (chainName gi ci) c).2.2 (base + (2 + k)) nd h_gn
      have h_pre := buildChainPre_getNode_middleRep W_ci (chainName gi ci) c h_ids k h_k
      rw [h_b] at h_pre
      rw [show base + 2 + k = base + (2 + k) from by omega] at h_pre
      rw [h_pre] at h_nd₀
      have h_eq : nd₀ = mkRepNode c.middleDelays[k] := by
        apply Option.some_inj.mp
        rw [← h_nd₀]
      rw [← h_kind, h_eq]
      dsimp [mkRepNode]

/-- In the built world, the last repeater of chain `(gi, ci)` has kind
    `repeater lastDelay (−1)` and its single output is the output node. -/
theorem buildGroups_lastRep_node (groups : List GroupSpec) (gi ci : Nat)
    (h_gi : gi < groups.length) (h_ci : ci < (groupAt groups gi).length) :
    ∃ nd, (buildGroups groups).1.getNode
        (chainBaseId groups gi ci + (chainAt groups gi ci).middleDelays.length + 2) =
      some nd ∧
      nd.kind = NodeKind.repeater (chainAt groups gi ci).lastDelay (-1) ∧
      nd.outputs = [chainBaseId groups gi ci +
        (chainAt groups gi ci).middleDelays.length + 3] := by
  obtain ⟨W_ci, h_Wci, h_b, h_lift⟩ :=
    buildGroups_chain_getNode_lift groups gi ci
      ((chainAt groups gi ci).middleDelays.length + 2) h_gi h_ci (by omega)
  set c := chainAt groups gi ci
  set base := chainBaseId groups gi ci
  have h_assoc : chainBaseId groups gi ci + c.middleDelays.length + 2 =
      base + (c.middleDelays.length + 2) := by
    dsimp [base]
    omega
  rw [h_assoc]
  have h_ids := buildGroups_chain_pre_ids groups gi ci h_gi h_ci W_ci h_Wci
  have h_out := buildChain_outputs_consecutive' W_ci (chainName gi ci) c h_ids
    (c.middleDelays.length + 2) (by omega)
  rw [h_b] at h_out
  have h_if : (if c.middleDelays.length + 2 + 1 < c.middleDelays.length + 4
      then [base + (c.middleDelays.length + 2) + 1] else []) =
      [base + c.middleDelays.length + 3] := by
    simp [show c.middleDelays.length + 2 + 1 < c.middleDelays.length + 4 from by
      omega]
    omega
  rw [h_if] at h_out
  cases h_gn : (buildChain W_ci (chainName gi ci) c).2.getNode
      (base + (c.middleDelays.length + 2)) with
  | none => simp [h_gn] at h_out
  | some nd =>
    simp only [h_gn] at h_out
    injection h_out with h_outputs
    refine ⟨nd, ?_, ?_, h_outputs⟩
    · rw [h_lift]
      exact h_gn
    · dsimp [buildChain] at h_gn
      obtain ⟨nd₀, h_nd₀, h_kind⟩ := connectChain_kind_preserved
        (buildChainPre W_ci (chainName gi ci) c).2.1
        (buildChainPre W_ci (chainName gi ci) c).2.2
        (base + (c.middleDelays.length + 2)) nd h_gn
      have h_pre := buildChainPre_getNode_lastRep W_ci (chainName gi ci) c h_ids
      rw [h_b] at h_pre
      rw [show base + c.middleDelays.length + 2 =
          base + (c.middleDelays.length + 2) from by omega] at h_pre
      rw [h_pre] at h_nd₀
      have h_eq : nd₀ =
          { kind := .repeater c.lastDelay (-1), sigLevel := 0, inputs := [], outputs := [] } := by
        apply Option.some_inj.mp
        rw [← h_nd₀]
      rw [← h_kind, h_eq]

/-- In the built world, the output node of chain `(gi, ci)` has kind
    `output (chainName gi ci)` and no outputs. -/
theorem buildGroups_output_node (groups : List GroupSpec) (gi ci : Nat)
    (h_gi : gi < groups.length) (h_ci : ci < (groupAt groups gi).length) :
    ∃ nd, (buildGroups groups).1.getNode
        (chainBaseId groups gi ci + (chainAt groups gi ci).middleDelays.length + 3) =
      some nd ∧
      nd.kind = NodeKind.output (chainName gi ci) ∧
      nd.outputs = [] := by
  obtain ⟨W_ci, h_Wci, h_b, h_lift⟩ :=
    buildGroups_chain_getNode_lift groups gi ci
      ((chainAt groups gi ci).middleDelays.length + 3) h_gi h_ci (by omega)
  set c := chainAt groups gi ci
  set base := chainBaseId groups gi ci
  have h_assoc : chainBaseId groups gi ci + c.middleDelays.length + 3 =
      base + (c.middleDelays.length + 3) := by
    dsimp [base]
    omega
  rw [h_assoc]
  have h_ids := buildGroups_chain_pre_ids groups gi ci h_gi h_ci W_ci h_Wci
  have h_out := buildChain_outputs_consecutive' W_ci (chainName gi ci) c h_ids
    (c.middleDelays.length + 3) (by omega)
  rw [h_b] at h_out
  have h_if : (if c.middleDelays.length + 3 + 1 < c.middleDelays.length + 4
      then [base + (c.middleDelays.length + 3) + 1] else []) = [] := by
    simp
  rw [h_if] at h_out
  cases h_gn : (buildChain W_ci (chainName gi ci) c).2.getNode
      (base + (c.middleDelays.length + 3)) with
  | none => simp [h_gn] at h_out
  | some nd =>
    simp only [h_gn] at h_out
    injection h_out with h_outputs
    refine ⟨nd, ?_, ?_, h_outputs⟩
    · rw [h_lift]
      exact h_gn
    · dsimp [buildChain] at h_gn
      obtain ⟨nd₀, h_nd₀, h_kind⟩ := connectChain_kind_preserved
        (buildChainPre W_ci (chainName gi ci) c).2.1
        (buildChainPre W_ci (chainName gi ci) c).2.2
        (base + (c.middleDelays.length + 3)) nd h_gn
      have h_pre := buildChainPre_getNode_outputNode W_ci (chainName gi ci) c h_ids
      rw [h_b] at h_pre
      rw [show base + c.middleDelays.length + 3 =
          base + (c.middleDelays.length + 3) from by omega] at h_pre
      rw [h_pre] at h_nd₀
      have h_eq : nd₀ =
          { kind := .output (chainName gi ci), sigLevel := 0, inputs := [], outputs := [] } := by
        apply Option.some_inj.mp
        rw [← h_nd₀]
      rw [← h_kind, h_eq]
