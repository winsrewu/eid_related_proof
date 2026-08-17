import Proofs.Model.Basic
import Proofs.Model.NodeLayout
import Proofs.Model.WorldInvariants
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Pairwise
import Mathlib.Data.List.Lemmas
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Convert
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push


open BasicRedstoneSim

/-! # Node-kind lookups for built chains

`getNode` facts attributing node ids (allocated by `buildChainPre`) to their
kinds. These let the event reasoning know what each chain node does when its
scheduled event fires. -/

/-- The repeater fold does not disturb the lookup of an id that predates it. -/
theorem repFoldl_getNode_of_lt (l : List (PNat × Int)) (acc : List Nat × World)
    (id : Nat) (h : id < acc.2.nextId) :
    (l.foldl repFoldlStep acc).2.getNode id = acc.2.getNode id := by
  revert h
  induction l generalizing acc with
  | nil => intro _; rfl
  | cons hd tl ih =>
    intro h
    simp only [List.foldl_cons]
    have hstep : id < (repFoldlStep acc hd).2.nextId := by
      dsimp [repFoldlStep, World.addNode]; omega
    rw [ih (repFoldlStep acc hd) hstep]
    dsimp [repFoldlStep]
    exact getNode_addNode_of_lt acc.2 (mkRepNode hd.1 hd.2) id h

/-- The observer node of a built chain sits at `w.nextId + 1` and has kind
    `observer`. -/
theorem buildChainPre_getNode_observer (w : World) (name : String)
    (c : ChainSpec) (hw : idsBounded w) :
    (buildChainPre w name c).2.1.getNode (w.nextId + 1) =
      some { kind := .observer, sigLevel := 0, inputs := [], outputs := [] } := by
  let inputND : NodeData :=
    { kind := .input, sigLevel := 0, inputs := [], outputs := [] }
  let obsND : NodeData :=
    { kind := .observer, sigLevel := 0, inputs := [], outputs := [] }
  dsimp [buildChainPre]
  -- peel the output addNode
  rw [getNode_addNode_of_lt]
  · -- peel the last-repeater addNode
    rw [getNode_addNode_of_lt]
    · -- peel the repeater fold
      rw [repFoldl_getNode_of_lt]
      · -- goal: getNode ((w.addNode inputND).2.addNode obsND).2 (w.nextId+1)
        have hid : (w.addNode inputND).2.nextId = w.nextId + 1 := by
          simp [World.addNode]
        have hself := getNode_addNode_self (w.addNode inputND).2 obsND
          (addNode_idsBounded w inputND hw)
        rw [← hid]
        exact hself
      · dsimp [World.addNode]; omega
    · dsimp [World.addNode, repFoldlStep]; rw [repFoldl_nextId]
      simp; omega
  · dsimp [World.addNode, repFoldlStep]; rw [repFoldl_nextId]
    simp; omega

/-- The output node of a built chain sits at `w.nextId + 3 + repLen` and has
    kind `.output name`. -/
theorem buildChainPre_getNode_output (w : World) (name : String)
    (c : ChainSpec) (hw : idsBounded w) :
    (buildChainPre w name c).2.1.getNode
      (w.nextId + 3 + (c.middleDelays.zip c.middlePriorities).length) =
      some { kind := .output name, sigLevel := 0, inputs := [], outputs := [] } := by
  let inputND : NodeData :=
    { kind := .input, sigLevel := 0, inputs := [], outputs := [] }
  let obsND : NodeData :=
    { kind := .observer, sigLevel := 0, inputs := [], outputs := [] }
  let lastRepND : NodeData :=
    { kind := .repeater c.lastDelay c.lastPriority, sigLevel := 0,
      inputs := [], outputs := [] }
  let outputND : NodeData :=
    { kind := .output name, sigLevel := 0, inputs := [], outputs := [] }
  dsimp [buildChainPre]
  -- the output is the outermost addNode; getNode_addNode_self places it at the
  -- pre-output world's nextId, which equals w.nextId + 3 + repLen
  have hid : w.nextId + 3 + (c.middleDelays.zip c.middlePriorities).length =
      (((c.middleDelays.zip c.middlePriorities).foldl repFoldlStep
        ([], ((w.addNode inputND).2.addNode obsND).2)).2.addNode lastRepND).2.nextId := by
    rw [addNode_nextId, repFoldl_nextId, addNode_nextId, addNode_nextId]
    omega
  rw [hid]
  have hIB : idsBounded
      (((c.middleDelays.zip c.middlePriorities).foldl repFoldlStep
        ([], ((w.addNode inputND).2.addNode obsND).2)).2.addNode lastRepND).2 := by
    apply addNode_idsBounded
    apply repFoldl_idsBounded
    apply addNode_idsBounded
    apply addNode_idsBounded
    exact hw
  exact getNode_addNode_self _ outputND hIB

/-- The last repeater of a built chain sits at `w.nextId + 2 + repLen` and has
    kind `.repeater c.lastDelay c.lastPriority`. -/
theorem buildChainPre_getNode_lastRep (w : World) (name : String)
    (c : ChainSpec) (hw : idsBounded w) :
    (buildChainPre w name c).2.1.getNode
      (w.nextId + 2 + (c.middleDelays.zip c.middlePriorities).length) =
      some {
        kind := NodeKind.repeater c.lastDelay c.lastPriority,
        sigLevel := 0, inputs := [], outputs := [] } := by
  let inputND : NodeData :=
    { kind := .input, sigLevel := 0, inputs := [], outputs := [] }
  let obsND : NodeData :=
    { kind := .observer, sigLevel := 0, inputs := [], outputs := [] }
  let lastRepND : NodeData :=
    { kind := .repeater c.lastDelay c.lastPriority, sigLevel := 0,
      inputs := [], outputs := [] }
  dsimp [buildChainPre]
  -- peel the output addNode
  rw [getNode_addNode_of_lt]
  · -- goal: getNode repRes.2... .addNode lastRepND world (w.nextId+2+repLen)
    have hid : w.nextId + 2 + (c.middleDelays.zip c.middlePriorities).length =
        ((c.middleDelays.zip c.middlePriorities).foldl repFoldlStep
          ([], ((w.addNode inputND).2.addNode obsND).2)).2.nextId := by
      rw [repFoldl_nextId, addNode_nextId, addNode_nextId]
    rw [hid]
    have hIB : idsBounded
        ((c.middleDelays.zip c.middlePriorities).foldl repFoldlStep
          ([], ((w.addNode inputND).2.addNode obsND).2)).2 := by
      apply repFoldl_idsBounded
      apply addNode_idsBounded
      apply addNode_idsBounded
      exact hw
    exact getNode_addNode_self _ lastRepND hIB
  · dsimp [World.addNode, repFoldlStep]; rw [repFoldl_nextId]
    simp

/-- Building a chain does not disturb the lookup of an id below the starting
    `nextId` (all of a chain's nodes are allocated at or above `w.nextId`). -/
theorem buildChainPre_getNode_of_lt (w : World) (name : String) (c : ChainSpec)
    (id : Nat) (h : id < w.nextId) :
    (buildChainPre w name c).2.1.getNode id = w.getNode id := by
  let inputND : NodeData :=
    { kind := .input, sigLevel := 0, inputs := [], outputs := [] }
  let obsND : NodeData :=
    { kind := .observer, sigLevel := 0, inputs := [], outputs := [] }
  let lastRepND : NodeData :=
    { kind := .repeater c.lastDelay c.lastPriority, sigLevel := 0,
      inputs := [], outputs := [] }
  let outputND : NodeData :=
    { kind := .output name, sigLevel := 0, inputs := [], outputs := [] }
  dsimp [buildChainPre]
  -- peel output, lastRep addNodes, the repeater fold, then observer, input
  rw [getNode_addNode_of_lt]
  · rw [getNode_addNode_of_lt]
    · rw [repFoldl_getNode_of_lt]
      · rw [getNode_addNode_of_lt]
        · rw [getNode_addNode_of_lt]
          all_goals (first | rfl | omega)
        · dsimp [World.addNode]; omega
      · dsimp [World.addNode]; omega
    · dsimp [World.addNode, repFoldlStep]; rw [repFoldl_nextId]; simp; omega
  · dsimp [World.addNode, repFoldlStep]; rw [repFoldl_nextId]; simp; omega

/-- The wired world of a built chain is `connectChain` applied to the
    pre-world and the chain-id list. -/
theorem buildChain_world (w : World) (name : String) (c : ChainSpec) :
    (buildChain w name c).2 =
      connectChain (buildChainPre w name c).2.1 (buildChainPre w name c).2.2 := by
  dsimp [buildChain]

/-- Building a chain preserves `getNode` of ids below the starting `nextId`. -/
theorem buildChain_getNode_of_lt (w : World) (name : String) (c : ChainSpec)
    (id : Nat) (h : id < w.nextId) :
    (buildChain w name c).2.getNode id = w.getNode id := by
  rw [buildChain_world]
  rw [connectChain_getNode_of_notMem _ _ id]
  · exact buildChainPre_getNode_of_lt w name c id h
  · intro hin
    -- every chain id is `w.nextId + i`, hence `≥ w.nextId > id`
    rw [buildChainPre_chainIds] at hin
    rcases List.mem_map.mp hin with ⟨y, _, hyid⟩
    omega

/-- Looking up the `k`-th chain node after wiring (`w.nextId + k =
    chainIds[k]`): the pre-world node gains input `w.nextId + k - 1` (if
    `k > 0`) and output `w.nextId + k + 1` (if present). -/
theorem buildChain_getNode_wired (w : World) (name : String) (c : ChainSpec)
    (k : Nat) (hk : k < (buildChainPre w name c).2.2.length) :
    (buildChain w name c).2.getNode (w.nextId + k) =
      ((buildChainPre w name c).2.1.getNode (w.nextId + k)).map fun nd =>
        { nd with
          inputs := nd.inputs ++ if _ : 0 < k then [w.nextId + k - 1] else [],
          outputs := nd.outputs ++
            if _ : k + 1 < (buildChainPre w name c).2.2.length then
              [w.nextId + k + 1] else [] } := by
  rw [buildChain_world]
  have hidk : (buildChainPre w name c).2.2[k]'hk = w.nextId + k :=
    buildChainPre_chainIds_getElem w name c k hk
  rw [← hidk]
  rw [connectChain_getNode _ _ k hk (buildChainPre_chainIds_nodup w name c)]
  rw [hidk]
  congr 1
  funext nd
  -- reconcile `chainIds[k-1]`/`chainIds[k+1]` with `w.nextId + k ∓ 1`.
  -- Only the `0 < k` (inputs-present) branch needs `omega`, because
  -- `w.nextId + (k+1)` is defeq to `w.nextId + k + 1` but
  -- `w.nextId + (k-1)` is not defeq to `w.nextId + k - 1`.
  by_cases hk0 : 0 < k
  · by_cases hk1 : k + 1 < (buildChainPre w name c).2.2.length
    · simp [hk0, hk1, buildChainPre_chainIds_getElem]; omega
    · simp [hk0, hk1, buildChainPre_chainIds_getElem]; omega
  · by_cases hk1 : k + 1 < (buildChainPre w name c).2.2.length
    · simp [hk0, hk1, buildChainPre_chainIds_getElem]; omega
    · simp [hk0, hk1]

/-! ## Concrete wired node lookups -/

/-- After wiring, the observer node (`w.nextId + 1`) has input `w.nextId`
    (the input node) and output `w.nextId + 2` (the first repeater). -/
theorem buildChain_getNode_observer_wired (w : World) (name : String)
    (c : ChainSpec) (hw : idsBounded w) :
    (buildChain w name c).2.getNode (w.nextId + 1) =
      some { kind := .observer, sigLevel := 0, inputs := [w.nextId],
             outputs := [w.nextId + 2] } := by
  have h1 : 1 < (buildChainPre w name c).2.2.length := by
    rw [buildChainPre_chainIds]; simp
  have h2 : 2 < (buildChainPre w name c).2.2.length := by
    rw [buildChainPre_chainIds]; simp
  rw [buildChain_getNode_wired w name c 1 h1]
  rw [buildChainPre_getNode_observer w name c hw]
  simp [h2]

/-- After wiring, the output node (`w.nextId + 3 + repLen`) has input
    `w.nextId + 2 + repLen` (the last repeater) and no outputs. -/
theorem buildChain_getNode_output_wired (w : World) (name : String)
    (c : ChainSpec) (hw : idsBounded w) :
    (buildChain w name c).2.getNode
      (w.nextId + 3 + (c.middleDelays.zip c.middlePriorities).length) =
      some { kind := .output name, sigLevel := 0,
             inputs := [w.nextId + 2 + (c.middleDelays.zip c.middlePriorities).length],
             outputs := [] } := by
  set repLen := (c.middleDelays.zip c.middlePriorities).length
  have hlen : (buildChainPre w name c).2.2.length = repLen + 4 := by
    rw [buildChainPre_chainIds]; dsimp [repLen]; simp
  have hk : repLen + 3 < (buildChainPre w name c).2.2.length := by omega
  rw [show w.nextId + 3 + repLen = w.nextId + (repLen + 3) by omega]
  rw [buildChain_getNode_wired w name c (repLen + 3) hk]
  have hget : (buildChainPre w name c).2.1.getNode (w.nextId + (repLen + 3)) =
      some { kind := .output name, sigLevel := 0, inputs := [], outputs := [] } := by
    rw [show w.nextId + (repLen + 3) = w.nextId + 3 + repLen by omega]
    exact buildChainPre_getNode_output w name c hw
  rw [hget]
  simp [repLen, hlen]
  omega

/-- After wiring, the last repeater (`w.nextId + 2 + repLen`) has input
    `w.nextId + 1 + repLen` and output `w.nextId + 3 + repLen` (the output
    node). -/
theorem buildChain_getNode_lastRep_wired (w : World) (name : String)
    (c : ChainSpec) (hw : idsBounded w) :
    (buildChain w name c).2.getNode
      (w.nextId + 2 + (c.middleDelays.zip c.middlePriorities).length) =
      some {
        kind := NodeKind.repeater c.lastDelay c.lastPriority,
        sigLevel := 0,
        inputs := [w.nextId + 1 + (c.middleDelays.zip c.middlePriorities).length],
        outputs := [w.nextId + 3 + (c.middleDelays.zip c.middlePriorities).length] } := by
  set repLen := (c.middleDelays.zip c.middlePriorities).length
  have hlen : (buildChainPre w name c).2.2.length = repLen + 4 := by
    rw [buildChainPre_chainIds]; dsimp [repLen]; simp
  have hk : repLen + 2 < (buildChainPre w name c).2.2.length := by omega
  rw [show w.nextId + 2 + repLen = w.nextId + (repLen + 2) by omega]
  rw [buildChain_getNode_wired w name c (repLen + 2) hk]
  have hget : (buildChainPre w name c).2.1.getNode (w.nextId + (repLen + 2)) =
      some {
        kind := NodeKind.repeater c.lastDelay c.lastPriority,
        sigLevel := 0, inputs := [], outputs := [] } := by
    rw [show w.nextId + (repLen + 2) = w.nextId + 2 + repLen by omega]
    exact buildChainPre_getNode_lastRep w name c hw
  rw [hget]
  simp [repLen, hlen]
  omega

/-- The node added by the `k`-th step of the repeater fold (id
    `acc.2.nextId + k`) is `mkRepNode (l[k].1) (l[k].2)`. -/
theorem repFoldl_getNode_nth (l : List (PNat × Int)) (acc : List Nat × World)
    (k : Nat) (hk : k < l.length) (hB : idsBounded acc.2) :
    (l.foldl repFoldlStep acc).2.getNode (acc.2.nextId + k) =
      some (mkRepNode l[k].1 l[k].2) := by
  revert hk hB
  induction l generalizing acc k with
  | nil => intro hk _; cases hk
  | cons hd tl ih =>
    intro hk hB
    cases k with
    | zero =>
      simp only [List.foldl_cons]
      have h0 : acc.2.nextId + 0 = acc.2.nextId := by omega
      have hl : (hd :: tl)[0] = hd := by simp
      rw [h0, hl]
      rw [repFoldl_getNode_of_lt tl (repFoldlStep acc hd) acc.2.nextId
        (by dsimp [repFoldlStep, World.addNode]; omega)]
      dsimp [repFoldlStep]
      exact getNode_addNode_self acc.2 (mkRepNode hd.1 hd.2) hB
    | succ k' =>
      simp only [List.foldl_cons]
      have hstep : acc.2.nextId + k'.succ =
          (repFoldlStep acc hd).2.nextId + k' := by
        dsimp [repFoldlStep, World.addNode]; omega
      have hkt : k' < tl.length := by dsimp at hk; omega
      have hl : (hd :: tl)[k'.succ] = tl[k']'hkt := by simp
      rw [hstep, hl]
      refine ih (repFoldlStep acc hd) k' hkt ?_
      dsimp [repFoldlStep]
      exact addNode_idsBounded acc.2 (mkRepNode hd.1 hd.2) hB

/-- The `j`-th middle repeater of a built chain sits at `w.nextId + 2 + j`. -/
theorem buildChainPre_getNode_middleRep (w : World) (name : String)
    (c : ChainSpec) (j : Nat)
    (hj : j < (c.middleDelays.zip c.middlePriorities).length)
    (hw : idsBounded w) :
    (buildChainPre w name c).2.1.getNode (w.nextId + 2 + j) =
      some (mkRepNode ((c.middleDelays.zip c.middlePriorities)[j]'hj).1
        ((c.middleDelays.zip c.middlePriorities)[j]'hj).2) := by
  let inputND : NodeData :=
    { kind := .input, sigLevel := 0, inputs := [], outputs := [] }
  let obsND : NodeData :=
    { kind := .observer, sigLevel := 0, inputs := [], outputs := [] }
  let lastRepND : NodeData :=
    { kind := .repeater c.lastDelay c.lastPriority, sigLevel := 0,
      inputs := [], outputs := [] }
  let outputND : NodeData :=
    { kind := .output name, sigLevel := 0, inputs := [], outputs := [] }
  dsimp [buildChainPre]
  -- peel the output addNode
  rw [getNode_addNode_of_lt]
  · -- peel the last-repeater addNode
    rw [getNode_addNode_of_lt]
    · -- at the fold result: use repFoldl_getNode_nth
      have hid : w.nextId + 2 + j =
          ((w.addNode inputND).2.addNode obsND).2.nextId + j := by
        simp [World.addNode]
      rw [hid]
      exact repFoldl_getNode_nth (c.middleDelays.zip c.middlePriorities)
        ([], ((w.addNode inputND).2.addNode obsND).2) j hj (by
          apply addNode_idsBounded
          apply addNode_idsBounded
          exact hw)
    · -- lastRep peel bound: w.nextId + 2 + j < repRes.2.nextId
      rw [repFoldl_nextId, addNode_nextId, addNode_nextId]
      omega
  · -- output peel bound
    rw [addNode_nextId, repFoldl_nextId, addNode_nextId, addNode_nextId]
    omega

/-- After wiring, the `j`-th middle repeater (`w.nextId + 2 + j`) has input
    `w.nextId + 1 + j` and output `w.nextId + 3 + j`. -/
theorem buildChain_getNode_middleRep_wired (w : World) (name : String)
    (c : ChainSpec) (j : Nat)
    (hj : j < (c.middleDelays.zip c.middlePriorities).length)
    (hw : idsBounded w) :
    (buildChain w name c).2.getNode (w.nextId + 2 + j) =
      some { kind := NodeKind.repeater
               ((c.middleDelays.zip c.middlePriorities)[j]'hj).1
               ((c.middleDelays.zip c.middlePriorities)[j]'hj).2,
             sigLevel := 0,
             inputs := [w.nextId + 1 + j],
             outputs := [w.nextId + 3 + j] } := by
  set repLen := (c.middleDelays.zip c.middlePriorities).length
  have hlen : (buildChainPre w name c).2.2.length = repLen + 4 := by
    rw [buildChainPre_chainIds]; dsimp [repLen]; simp
  have hjr : j < repLen := hj
  have hk : 2 + j < (buildChainPre w name c).2.2.length := by omega
  rw [show w.nextId + 2 + j = w.nextId + (2 + j) by omega]
  rw [buildChain_getNode_wired w name c (2 + j) hk]
  have hget : (buildChainPre w name c).2.1.getNode (w.nextId + (2 + j)) =
      some (mkRepNode ((c.middleDelays.zip c.middlePriorities)[j]'hj).1
        ((c.middleDelays.zip c.middlePriorities)[j]'hj).2) := by
    rw [show w.nextId + (2 + j) = w.nextId + 2 + j by omega]
    exact buildChainPre_getNode_middleRep w name c j hj hw
  rw [hget]
  simp [hlen]
  -- the outputs dite `2 + j + 1 < len` is true by hjr; split and discard the
  -- impossible false branch
  split
  · have hi : w.nextId + (2 + j) - 1 = w.nextId + 1 + j := by omega
    have ho : w.nextId + (2 + j) + 1 = w.nextId + 3 + j := by omega
    simp [hi, ho, mkRepNode]
  · exfalso; omega
