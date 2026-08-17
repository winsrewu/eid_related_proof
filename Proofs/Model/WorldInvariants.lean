import Proofs.Model.Basic
import Proofs.Model.NodeLayout
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

/-! # World invariants and node lookup

Well-formedness invariant (every node id strictly below `nextId`) and the
resulting `getNode` lookup facts. These let an event be attributed to the
unique chain node that carries its `nodeId`. -/

/-- Every node id is strictly below `nextId`. -/
def idsBounded (w : World) : Prop :=
  ∀ p ∈ w.nodes, p.1 < w.nextId

theorem empty_idsBounded : idsBounded World.empty := by
  dsimp [World.empty, idsBounded]; intro p h; cases h

/-- `addNode` preserves `idsBounded`. -/
theorem addNode_idsBounded (w : World) (nd : NodeData)
    (h : idsBounded w) : idsBounded (w.addNode nd).2 := by
  intro p hp
  simp only [World.addNode, List.mem_append, List.mem_singleton] at hp ⊢
  rcases hp with hp | rfl
  · exact Nat.lt_trans (h p hp) (by omega)
  · omega

/-- `updateNode` preserves `idsBounded`. -/
theorem updateNode_idsBounded (w : World) (id : Nat)
    (f : NodeData → NodeData) (h : idsBounded w) :
    idsBounded (w.updateNode id f) := by
  intro p hp
  have hnext : (w.updateNode id f).nextId = w.nextId := by dsimp [World.updateNode]
  rw [hnext]
  dsimp [World.updateNode] at hp
  rcases List.mem_map.mp hp with ⟨q, hq, hqp⟩
  rcases q with ⟨qid, qnd⟩
  have hp1 : p.1 = qid := by
    have hfst := congrArg Prod.fst hqp.symm
    by_cases hid : qid == id <;> simp [hid] at hfst <;> exact hfst
  rw [hp1]
  exact h ⟨qid, qnd⟩ hq

/-- `connectChain` preserves `idsBounded`. -/
theorem connectChain_idsBounded (w : World) (ids : List Nat)
    (h : idsBounded w) : idsBounded (connectChain w ids) := by
  unfold connectChain
  generalize hp : ids.zip (ids.drop 1) = pairs
  clear hp ids
  induction pairs generalizing w h with
  | nil => exact h
  | cons p ps ih =>
    simp only [List.foldl_cons]
    cases p with
    | mk prev curr =>
      dsimp only
      apply ih
      exact updateNode_idsBounded _ prev _
        (updateNode_idsBounded _ curr _ h)

/-- The repeater fold preserves `idsBounded`, for any starting accumulator. -/
theorem repFoldl_idsBounded_gen (l : List (PNat × Int)) (acc : List Nat × World)
    (h : idsBounded acc.2) : idsBounded (l.foldl repFoldlStep acc).2 := by
  induction l generalizing acc h with
  | nil => exact h
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    apply ih
    dsimp [repFoldlStep]
    exact addNode_idsBounded acc.2 (mkRepNode hd.1 hd.2) h

/-- The repeater fold preserves `idsBounded`. -/
theorem repFoldl_idsBounded (l : List (PNat × Int)) (w : World)
    (h : idsBounded w) : idsBounded (l.foldl repFoldlStep ([], w)).2 :=
  repFoldl_idsBounded_gen l ([], w) h

/-- `buildChain` preserves `idsBounded`. -/
theorem buildChain_idsBounded (w : World) (name : String) (c : ChainSpec)
    (h : idsBounded w) : idsBounded (buildChain w name c).2 := by
  dsimp [buildChain]
  exact connectChain_idsBounded _ _ (addNode_idsBounded _ _
    (addNode_idsBounded _ _ (repFoldl_idsBounded _ _ (addNode_idsBounded _ _
      (addNode_idsBounded _ _ h)))))

/-! ## getNode lookup -/

/-- `a < b` implies `(a == b) = false`. -/
theorem nat_beq_false_of_lt (a b : Nat) (h : a < b) : (a == b) = false := by
  by_cases hbeq : (a == b) = true
  · exfalso
    exact Nat.ne_of_lt h (Nat.eq_of_beq_eq_true (by simpa using hbeq))
  · cases hval : (a == b)
    · rfl
    · exact (hbeq hval).elim

/-- `find?` over a list whose first components are all `< n` finds nothing
    matching `n`. -/
theorem find?_none_of_lt (l : List (Nat × NodeData)) (n : Nat)
    (h : ∀ p ∈ l, p.1 < n) :
    l.find? (fun p => p.1 == n) = none := by
  revert h
  induction l with
  | nil => intro _; rfl
  | cons a as ih =>
    intro h
    have hbeq : (a.1 == n) = false :=
      nat_beq_false_of_lt a.1 n (h a (List.mem_cons.mpr (Or.inl rfl)))
    dsimp [List.find?]
    rw [hbeq]
    dsimp
    apply ih
    intro q hq
    exact h q (List.mem_cons.mpr (Or.inr hq))

/-- `(n == n) = true`.  Uses `Nat.beq_eq : (x.beq y = true) = (x = y)`;
    `simp` unfolds `==` to `Nat.beq` and reflects. -/
theorem nat_beq_true_self (n : Nat) : (n == n) = true := by
  simp

/-- `a = b` implies `(a == b) = true`. -/
theorem nat_beq_true_of_eq (a b : Nat) (h : a = b) : (a == b) = true := by
  simpa [Nat.beq_eq] using h

/-- `find?` over `l ++ [(n, nd)]` finds `(n, nd)` when all ids in `l` are
    `< n`. -/
theorem find?_append_singleton_match (l : List (Nat × NodeData)) (n : Nat)
    (nd : NodeData) (h : ∀ p ∈ l, p.1 < n) :
    (l ++ [(n, nd)]).find? (fun (nid, _) => nid == n) = some (n, nd) := by
  revert h
  induction l with
  | nil => intro _; dsimp [List.find?]; simp
  | cons a as ih =>
    intro h
    have hbeq : (a.1 == n) = false :=
      nat_beq_false_of_lt a.1 n (h a (List.mem_cons.mpr (Or.inl rfl)))
    dsimp [List.find?]
    rw [hbeq]
    dsimp
    apply ih
    intro q hq
    exact h q (List.mem_cons.mpr (Or.inr hq))

/-- Looking up the freshly added node returns it. -/
theorem getNode_addNode_self (w : World) (nd : NodeData)
    (h : idsBounded w) : (w.addNode nd).2.getNode w.nextId = some nd := by
  dsimp [World.addNode, World.getNode]
  rw [find?_append_singleton_match _ _ _ h]

/-- `a ≠ b` implies `(a == b) = false`. -/
theorem nat_beq_false_of_ne (a b : Nat) (h : a ≠ b) : (a == b) = false := by
  by_cases hbeq : (a == b) = true
  · exfalso
    exact h (Nat.eq_of_beq_eq_true (by simpa using hbeq))
  · cases hb : (a == b) <;> simp_all

/-- `find?` over `l ++ [x]` equals `find?` over `l` when `x` does not match. -/
theorem find?_append_nomatch (l : List (Nat × NodeData))
    (x : Nat × NodeData) (pred : (Nat × NodeData) → Bool)
    (hx : pred x = false) : (l ++ [x]).find? pred = l.find? pred := by
  have hsingle : ([x] : List (Nat × NodeData)).find? pred = none := by
    dsimp [List.find?]; rw [hx]
  rw [List.find?_append, hsingle]
  cases h : l.find? pred <;> simp

/-- Adding a node does not change the lookup of an existing (lower) id. -/
theorem getNode_addNode_of_lt (w : World) (nd : NodeData) (id : Nat)
    (h : id < w.nextId) : (w.addNode nd).2.getNode id = w.getNode id := by
  dsimp [World.addNode, World.getNode]
  rw [find?_append_nomatch _ _ _ ?_]
  exact nat_beq_false_of_ne w.nextId id (Nat.ne_of_gt h)

/-! ## Interaction of `find?` with `map` (for `updateNode`) -/

/-- `find?` commutes with `map` when `g` preserves the predicate. -/
theorem find?_map_preserving {α : Type} (g : α → α) (pred : α → Bool)
    (hinv : ∀ x, pred (g x) = pred x) (l : List α) :
    (l.map g).find? pred = (l.find? pred).map g := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    dsimp [List.find?, List.map]
    rw [hinv a]
    cases hpa : pred a
    · exact ih
    · simp

/-- `find?` is unchanged by a map that fixes every element the predicate
    accepts. -/
theorem find?_map_fixing {α : Type} (g : α → α) (pred : α → Bool)
    (hinv : ∀ x, pred (g x) = pred x)
    (hfix : ∀ x, pred x = true → g x = x) (l : List α) :
    (l.map g).find? pred = l.find? pred := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    dsimp [List.find?, List.map]
    rw [hinv a]
    cases hpa : pred a
    · exact ih
    · simp [hfix a hpa]

/-- When `find?` returns `some a`, the predicate holds at `a`. -/
theorem find?_some {α : Type} (l : List α) (pred : α → Bool) (a : α)
    (h : l.find? pred = some a) : pred a = true := by
  revert a h
  induction l with
  | nil => intro a h; cases h
  | cons x xs ih =>
    intro a h
    dsimp [List.find?] at h
    by_cases hpx : pred x = true
    · simp [hpx] at h
      have ha : x = a := by simpa using h
      rw [← ha]
      exact hpx
    · have hpf : pred x = false := by cases hpx' : pred x <;> simp_all
      simp [hpf] at h
      exact ih a h

/-- Updating one node leaves a different node's lookup unchanged. -/
theorem getNode_updateNode_ne (w : World) (id id' : Nat)
    (f : NodeData → NodeData) (hne : id' ≠ id) :
    (w.updateNode id f).getNode id' = w.getNode id' := by
  dsimp [World.updateNode, World.getNode]
  have hmap :
      (w.nodes.map (fun (nid, nd) =>
          if nid == id then (nid, f nd) else (nid, nd))).find?
        (fun (nid, _) => nid == id') =
      w.nodes.find? (fun (nid, _) => nid == id') := by
    apply find?_map_fixing
    · intro x
      cases x with | mk nid nd
      dsimp
      split <;> rfl
    · intro x hx
      cases x with | mk nid nd
      dsimp at hx ⊢
      have hnid : nid = id' := Nat.eq_of_beq_eq_true (by simpa using hx)
      have hn : nid ≠ id := fun heq => hne (hnid.symm.trans heq)
      simp [nat_beq_false_of_ne nid id hn]
  rw [hmap]

/-- Updating a node applies `f` to the looked-up value. -/
theorem getNode_updateNode_self (w : World) (id : Nat)
    (f : NodeData → NodeData) (nd : NodeData)
    (h : w.getNode id = some nd) :
    (w.updateNode id f).getNode id = some (f nd) := by
  dsimp [World.getNode] at h
  have hfind : w.nodes.find? (fun (nid, _) => nid == id) = some (id, nd) := by
    generalize hf : w.nodes.find? (fun (nid, _) => nid == id) = o at h
    cases o with
    | none => cases h
    | some p =>
      rcases p with ⟨nid0, nd0⟩
      have hnd : nd0 = nd := by simpa using h
      have hnid : nid0 = id := by
        have hpred := find?_some w.nodes (fun (nid, _) => nid == id) (nid0, nd0) hf
        exact Nat.eq_of_beq_eq_true (by simpa using hpred)
      rw [hnid, hnd]
  dsimp [World.updateNode, World.getNode]
  have hinv : ∀ x : Nat × NodeData,
      (fun (nid, _) => nid == id)
        ((fun (nid, nd0) => if nid == id then (nid, f nd0) else (nid, nd0)) x) =
      (fun (nid, _) => nid == id) x := by
    intro x
    cases x with | mk nid nd0
    dsimp
    split <;> rfl
  have hmap :
      (w.nodes.map (fun (nid, nd0) =>
          if nid == id then (nid, f nd0) else (nid, nd0))).find?
        (fun (nid, _) => nid == id) = some (id, f nd) := by
    rw [find?_map_preserving
      (fun (nid, nd0) => if nid == id then (nid, f nd0) else (nid, nd0))
      (fun (nid, _) => nid == id) hinv w.nodes, hfind]
    dsimp
    simp
  rw [hmap]

/-- Updating an absent node leaves its lookup absent. -/
theorem getNode_updateNode_none (w : World) (id : Nat) (f : NodeData → NodeData)
    (h : w.getNode id = none) : (w.updateNode id f).getNode id = none := by
  dsimp [World.getNode] at h
  have hfind : w.nodes.find? (fun (nid, _) => nid == id) = none := by
    generalize hf : w.nodes.find? (fun (nid, _) => nid == id) = o at h
    cases o with
    | none => rfl
    | some p =>
      rcases p with ⟨nid0, nd0⟩
      dsimp at h
      cases h
  dsimp [World.updateNode, World.getNode]
  have hinv : ∀ x : Nat × NodeData,
      (fun (nid, _) => nid == id)
        ((fun (nid, nd0) => if nid == id then (nid, f nd0) else (nid, nd0)) x) =
      (fun (nid, _) => nid == id) x := by
    intro x
    cases x with | mk nid nd0
    dsimp
    split <;> rfl
  have hmap :
      (w.nodes.map (fun (nid, nd0) =>
          if nid == id then (nid, f nd0) else (nid, nd0))).find?
        (fun (nid, _) => nid == id) = none := by
    rw [find?_map_preserving
      (fun (nid, nd0) => if nid == id then (nid, f nd0) else (nid, nd0))
      (fun (nid, _) => nid == id) hinv w.nodes, hfind]
    dsimp
  rw [hmap]

/-- `updateNode` with a kind-preserving `f` preserves the looked-up kind. -/
theorem getNode_updateNode_kind (w : World) (id : Nat) (f : NodeData → NodeData)
    (hf : ∀ nd, (f nd).kind = nd.kind) (id' : Nat) :
    Option.map NodeData.kind ((w.updateNode id f).getNode id') =
      Option.map NodeData.kind (w.getNode id') := by
  by_cases hne : id' = id
  · rw [hne]
    by_cases hsome : ∃ nd, w.getNode id = some nd
    · rcases hsome with ⟨nd, hget⟩
      rw [getNode_updateNode_self w id f nd hget, hget]
      dsimp [Option.map]
      rw [hf nd]
    · have hnone : w.getNode id = none := by
        cases hnd : w.getNode id
        · rfl
        · exfalso
          exact hsome ⟨_, hnd⟩
      rw [hnone, getNode_updateNode_none w id f hnone]
  · rw [getNode_updateNode_ne w id id' f hne]

/-- `connectChain` preserves the kind of every node. -/
theorem connectChain_kind (w : World) (ids : List Nat) (id : Nat) :
    Option.map NodeData.kind ((connectChain w ids).getNode id) =
      Option.map NodeData.kind (w.getNode id) := by
  unfold connectChain
  generalize hp : ids.zip (ids.drop 1) = pairs
  clear hp ids
  induction pairs generalizing w with
  | nil => rfl
  | cons p ps ih =>
    cases p with
    | mk prev curr =>
      simp only [List.foldl_cons]
      rw [ih, getNode_updateNode_kind, getNode_updateNode_kind]
      · intro nd; rfl
      · intro nd; rfl

/-- `updateNode` maps the looked-up value by `f` (or stays `none`). -/
theorem getNode_updateNode_map (w : World) (id : Nat) (f : NodeData → NodeData) :
    (w.updateNode id f).getNode id = (w.getNode id).map f := by
  cases hnd : w.getNode id with
  | none => rw [getNode_updateNode_none w id f hnd]; rfl
  | some nd => rw [getNode_updateNode_self w id f nd hnd]; rfl

/-- `connectChain` recursion: wire `a → b`, then wire the tail. -/
theorem connectChain_cons_cons (w : World) (a b : Nat) (rest : List Nat) :
    connectChain w (a :: b :: rest) =
    connectChain
      ((w.updateNode b (fun nd => { nd with inputs := nd.inputs ++ [a] })).updateNode a
        (fun nd => { nd with outputs := nd.outputs ++ [b] }))
      (b :: rest) := by
  dsimp [connectChain]

/-- Wiring a chain does not disturb the lookup of an id outside the chain. -/
theorem connectChain_getNode_of_notMem (w : World) (ids : List Nat) (x : Nat)
    (h : x ∉ ids) : (connectChain w ids).getNode x = w.getNode x := by
  revert h
  induction ids generalizing w with
  | nil => intro _; dsimp [connectChain]
  | cons a as ih =>
    intro h
    cases as with
    | nil => dsimp [connectChain, List.zip, List.zipWith]
    | cons b rest =>
      rw [connectChain_cons_cons]
      rw [ih _ (by intro hx; exact h (List.mem_cons_of_mem a hx))]
      have hxa : x ≠ a := by
        intro heq
        subst heq
        exact h (List.mem_cons.mpr (Or.inl rfl))
      have hxb : x ≠ b := by
        intro heq
        subst heq
        exact h (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
      rw [getNode_updateNode_ne _ a x _ hxa, getNode_updateNode_ne _ b x _ hxb]

/-- Complete wiring characterization: after `connectChain w ids` (ids
    duplicate-free), node `ids[k]` has gained input `ids[k-1]` (if `k > 0`)
    and output `ids[k+1]` (if `k + 1 < ids.length`). -/
theorem connectChain_getNode (w : World) (ids : List Nat) (k : Nat)
    (hk : k < ids.length) (hnd : ids.Nodup) :
    (connectChain w ids).getNode (ids[k]'hk) =
      (w.getNode (ids[k]'hk)).map fun nd =>
        { nd with
          inputs :=
            nd.inputs ++
              if h : 0 < k then [(ids[k - 1]'(by omega))] else [],
          outputs :=
            nd.outputs ++
              if h : k + 1 < ids.length then [(ids[k + 1]'h)] else [] } := by
  revert hk hnd
  induction ids generalizing w k with
  | nil => intro hk _; cases hk
  | cons a as ih =>
    intro hk hnd
    cases as with
    | nil =>
      -- ids = [a], k = 0: no pairs, nothing wired
      have hk0 : k = 0 := by dsimp at hk; omega
      subst hk0
      dsimp [connectChain, List.zip, List.zipWith]
      cases w.getNode a <;> simp
    | cons b rest =>
      rw [connectChain_cons_cons]
      cases k with
      | zero =>
        -- target a: only gains output b
        have hnotm : a ∉ b :: rest := (List.nodup_cons.mp hnd).1
        have hab : a ≠ b := by
          intro heq
          exact hnotm (heq ▸ List.mem_cons.mpr (Or.inl rfl))
        dsimp
        rw [connectChain_getNode_of_notMem _ _ _ hnotm,
          getNode_updateNode_map, getNode_updateNode_ne _ b a _ hab]
        cases hget : w.getNode a <;> simp
      | succ k' =>
        -- target (b :: rest)[k']; apply the IH to the wired tail
        have hk' : k' < (b :: rest).length := by dsimp at hk ⊢; omega
        have hnd' : (b :: rest).Nodup := (List.nodup_cons.mp hnd).2
        have hshift : (a :: b :: rest)[k' + 1] = (b :: rest)[k'] := by rfl
        rw [hshift]
        rw [ih _ k' hk' hnd']
        cases k' with
        | zero =>
          -- target b: gains input a from the step, outputs from the IH
          have hab : a ≠ b := by
            intro heq
            exact (List.nodup_cons.mp hnd).1
              (heq ▸ List.mem_cons.mpr (Or.inl rfl))
          dsimp
          rw [getNode_updateNode_ne _ a b _ (Ne.symm hab),
            getNode_updateNode_map]
          cases w.getNode b <;> simp
        | succ k'' =>
          -- target (b :: rest)[k''.succ] = rest[k''] ∈ rest: untouched by step
          have hk'' : k'' < rest.length := by dsimp at hk'; omega
          have hshift2 : (b :: rest)[k''.succ] = rest[k''] := by rfl
          rw [hshift2]
          have hxb : rest[k''] ≠ b := by
            intro heq
            exact (List.nodup_cons.mp hnd').1 (heq ▸ List.getElem_mem hk'')
          have hxa : rest[k''] ≠ a := by
            intro heq
            exact (List.nodup_cons.mp hnd).1
              (heq ▸ List.mem_cons_of_mem b (List.getElem_mem hk''))
          rw [getNode_updateNode_ne _ a _ _ hxa,
            getNode_updateNode_ne _ b _ _ hxb]
          cases w.getNode rest[k''] <;> simp [List.getElem_cons_succ]
