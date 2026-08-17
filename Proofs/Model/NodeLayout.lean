import Proofs.Model.Basic
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

/-! # Node layout of built chains

`buildChainPre`/`buildChain` allocate consecutive node ids. This module pins
down the layout so that events can be attributed to a specific chain and a
specific stage of that chain.

For a chain built on a world with `nextId = n`:
  * input    = n
  * observer = n + 1
  * middle repeater k = n + 2 + k   (k = 0 .. repLen-1)
  * last repeater = n + 2 + repLen
  * output   = n + 3 + repLen
where `repLen = (middleDelays.zip middlePriorities).length`. -/

/-! ## nextId bookkeeping for addNode and the repeater fold -/

/-- One `repFoldlStep` increments `nextId` by 1 and appends the old
    `nextId` to the id list. -/
theorem repFoldlStep_shape (acc : List Nat × World) (dp : PNat × Int) :
    (repFoldlStep acc dp).2.nextId = acc.2.nextId + 1 ∧
    (repFoldlStep acc dp).1 = acc.1 ++ [acc.2.nextId] := by
  dsimp [repFoldlStep]
  dsimp [World.addNode]
  constructor <;> rfl

/-- Folding `repFoldlStep` over `l` raises `nextId` by `l.length`, for any
    starting accumulator. -/
theorem repFoldl_nextId_gen (l : List (PNat × Int)) (acc : List Nat × World) :
    (l.foldl repFoldlStep acc).2.nextId = acc.2.nextId + l.length := by
  induction l generalizing acc with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rw [ih (repFoldlStep acc hd), (repFoldlStep_shape acc hd).1]
    simp [List.length]
    omega

/-- Folding `repFoldlStep` over `l` starting from `([], w)` raises `nextId`
    by `l.length`. -/
theorem repFoldl_nextId (l : List (PNat × Int)) (w : World) :
    (l.foldl repFoldlStep ([], w)).2.nextId = w.nextId + l.length := by
  simpa using repFoldl_nextId_gen l ([], w)

/-! ## range identities (for the id-list layout) -/

/-- `range.loop n` prepends `[0, ..., n-1]` in front of the accumulator. -/
theorem range_loop_append (n : Nat) (acc : List Nat) :
    List.range.loop n acc = List.range.loop n [] ++ acc := by
  induction n generalizing acc with
  | zero => simp [List.range.loop]
  | succ n ih =>
    simp only [List.range.loop]
    rw [ih (n :: acc), ih [n]]
    simp [List.append_assoc]

/-- `range (n + 1) = range n ++ [n]`. -/
theorem range_succ_append (n : Nat) :
    List.range (n + 1) = List.range n ++ [n] := by
  dsimp only [List.range]
  have h : List.range.loop (n + 1) [] = List.range.loop n [n] := by
    simp [List.range.loop]
  rw [h]
  exact range_loop_append n [n]

/-- `range n` shifted by `x`, with the top element split off. -/
theorem range_map_strong (n x : Nat) :
    (List.range n).map (fun i => x + i) ++ [x + n] =
      [x] ++ (List.range n).map (fun i => x + 1 + i) := by
  induction n generalizing x with
  | zero => simp [List.range, List.range.loop]
  | succ n ih =>
    simp only [range_succ_append, List.map_append]
    have h1 : List.map (fun i => x + i) [n] = [x + n] := by simp
    have h2 : List.map (fun i => x + 1 + i) [n] = [x + 1 + n] := by simp
    rw [h1, h2]
    rw [ih]
    rw [List.append_assoc]
    have hadd : x + (n + 1) = x + 1 + n := by omega
    rw [hadd]

/-! ## id-list layout of the repeater fold -/


/-- The id list produced by the repeater fold is `ids0` followed by the
    consecutive ids `w0.nextId, w0.nextId + 1, ...`. -/
theorem repFoldl_ids_list_gen (l : List (PNat × Int)) (ids0 : List Nat)
    (w0 : World) :
    (l.foldl repFoldlStep (ids0, w0)).1 =
      ids0 ++ (List.range l.length).map (fun i => w0.nextId + i) := by
  induction l generalizing ids0 w0 with
  | nil => simp [List.range, List.range.loop]
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rw [ih (repFoldlStep (ids0, w0) hd).1 (repFoldlStep (ids0, w0) hd).2]
    rw [(repFoldlStep_shape (ids0, w0) hd).2,
      (repFoldlStep_shape (ids0, w0) hd).1]
    -- goal: (ids0 ++ [w0.nextId]) ++ range(tl.length).map (w0.nextId + 1 + ·)
    --      = ids0 ++ range(tl.length + 1).map (w0.nextId + ·)
    rw [List.append_assoc]
    have hsplit : [w0.nextId] ++
        (List.range tl.length).map (fun i => w0.nextId + 1 + i) =
      (List.range (tl.length + 1)).map (fun i => w0.nextId + i) := by
      rw [← range_map_strong, range_succ_append, List.map_append]
      simp
    rw [hsplit]
    rfl

/-! ## addNode facts -/

/-- `addNode` returns the current `nextId` and bumps it by 1. -/
theorem addNode_fst (w : World) (nd : NodeData) : (w.addNode nd).1 = w.nextId :=
  rfl

@[simp] theorem addNode_nextId (w : World) (nd : NodeData) :
    (w.addNode nd).2.nextId = w.nextId + 1 := rfl

@[simp] theorem addNode_nodes (w : World) (nd : NodeData) :
    (w.addNode nd).2.nodes = w.nodes ++ [(w.nextId, nd)] := rfl

/-- `connectChain` does not change `nextId`. -/
theorem connectChain_nextId (w : World) (ids : List Nat) :
    (connectChain w ids).nextId = w.nextId := by
  unfold connectChain
  generalize hp : ids.zip (ids.drop 1) = pairs
  clear hp ids
  induction pairs generalizing w with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.foldl_cons]
    cases p with
    | mk prev curr =>
      dsimp only
      rw [ih]
      simp [World.updateNode]

/-! ## buildChainPre layout -/

/-- Pure list identity: `[x, x+1] ++ (x+2+·) '' range m ++ [x+2+m, x+3+m]`
    is the consecutive block `(x+·) '' range (m+4)`. -/
theorem chainIds_layout (x m : Nat) :
    [x, x + 1] ++ (List.range m).map (fun i => x + 2 + i) ++
      [x + 2 + m, x + 3 + m] =
    (List.range (m + 4)).map (fun i => x + i) := by
  induction m generalizing x with
  | zero => dsimp [List.range, List.range.loop]
  | succ m ih =>
    -- expand the LHS middle map's `range (m + 1)`
    rw [show List.range (m + 1) = List.range m ++ [m] from
      range_succ_append m, List.map_append]
    -- expand the RHS `range (m + 1 + 4)`
    rw [show m + 1 + 4 = m + 4 + 1 by omega, range_succ_append,
      List.map_append]
    -- reduce the two singleton maps
    have hm : List.map (fun i => x + 2 + i) [m] = [x + 2 + m] := by simp
    have htop : List.map (fun i => x + i) [m + 4] = [x + (m + 4)] := by simp
    rw [hm, htop]
    -- fold the RHS `range (m+4)` map back via the IH
    rw [← ih]
    have h1 : x + 2 + (m + 1) = x + 3 + m := by omega
    have h2 : x + 3 + (m + 1) = x + 4 + m := by omega
    have h3 : x + (m + 4) = x + 4 + m := by omega
    simp [h1, h2, h3, List.append_assoc]

/-- The input id of a built chain is the world's `nextId`. -/
theorem buildChainPre_inputId (w : World) (name : String) (c : ChainSpec) :
    (buildChainPre w name c).1 = w.nextId := rfl

/-- The chain-id list of a built chain is the consecutive block
    `w.nextId, w.nextId + 1, ..., w.nextId + 3 + repLen`. -/
theorem buildChainPre_chainIds (w : World) (name : String) (c : ChainSpec) :
    (buildChainPre w name c).2.2 =
      (List.range ((c.middleDelays.zip c.middlePriorities).length + 4)).map
        (fun i => w.nextId + i) := by
  dsimp [buildChainPre]
  simp [addNode_fst, addNode_nextId, repFoldl_ids_list_gen,
    repFoldl_nextId_gen]
  set repLen := min c.middleDelays.length c.middlePriorities.length
  rw [show w.nextId + 1 + 1 = w.nextId + 2 by omega]
  have htail : w.nextId + 2 + repLen + 1 = w.nextId + 3 + repLen := by omega
  rw [htail]
  exact chainIds_layout w.nextId repLen

/-- Transport `getElem` across a list equality (the bound is cast along the
    equality; the two proof arguments are irrelevant). -/
theorem getElem_transport {l1 l2 : List Nat} (h : l1 = l2) (k : Nat)
    (hk : k < l1.length) : l1[k]'hk = l2[k]'(h ▸ hk) := by
  cases h
  rfl

/-- The `k`-th chain id of a built chain is `w.nextId + k`. -/
theorem buildChainPre_chainIds_getElem (w : World) (name : String)
    (c : ChainSpec) (k : Nat)
    (hk : k < (buildChainPre w name c).2.2.length) :
    (buildChainPre w name c).2.2[k]'hk = w.nextId + k := by
  rw [getElem_transport (buildChainPre_chainIds w name c) k hk]
  simp only [List.getElem_map, List.getElem_range]

/-- The chain-id list of a built chain has no duplicates. -/
theorem buildChainPre_chainIds_nodup (w : World) (name : String)
    (c : ChainSpec) : (buildChainPre w name c).2.2.Nodup := by
  rw [buildChainPre_chainIds]
  exact List.Nodup.map (fun _ _ hab => by omega) List.nodup_range

/-- `buildChainPre` raises `nextId` by `4 + repLen`. -/
theorem buildChainPre_nextId (w : World) (name : String) (c : ChainSpec) :
    (buildChainPre w name c).2.1.nextId =
      w.nextId + 4 + (c.middleDelays.zip c.middlePriorities).length := by
  dsimp [buildChainPre, World.addNode]
  rw [repFoldl_nextId]
  simp
  omega

/-- `buildChain` raises `nextId` by `4 + repLen`. -/
theorem buildChain_nextId (w : World) (name : String) (c : ChainSpec) :
    (buildChain w name c).2.nextId =
      w.nextId + 4 + (c.middleDelays.zip c.middlePriorities).length := by
  dsimp [buildChain]
  rw [connectChain_nextId, buildChainPre_nextId]
