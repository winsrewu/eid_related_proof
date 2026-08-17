import Proofs.Model.Basic
import Proofs.Model.NodeLayout
import Proofs.Model.WorldInvariants
import Proofs.Model.ChainNodes
import Mathlib.Data.List.Defs
import Mathlib.Data.List.Basic
import Mathlib.Tactic


open BasicRedstoneSim

/-! # Multi-chain layout

`buildChainsFrom` lays the chains out back to back in node-id space. This
module pins down the per-chain id ranges and the observer-id list so that an
event can be attributed to a unique chain. -/

/-- Number of nodes one built chain adds to the world. -/
def chainNodeCount (c : ChainSpec) : Nat :=
  4 + (c.middleDelays.zip c.middlePriorities).length

/-- `buildChain` adds `chainNodeCount c` nodes. -/
theorem buildChain_nextId' (w : World) (name : String) (c : ChainSpec) :
    (buildChain w name c).2.nextId = w.nextId + chainNodeCount c := by
  dsimp [chainNodeCount]
  rw [buildChain_nextId]
  omega

/-- The nextId after building a list of chains is the starting nextId plus the
    sum of the per-chain node counts. -/
theorem buildChainsFrom_nextId (start : Nat) (w : World)
    (specs : List ChainSpec) :
    (buildChainsFrom start w specs).1.nextId =
      w.nextId + (specs.map chainNodeCount).sum := by
  induction specs generalizing start w with
  | nil => dsimp [buildChainsFrom]
  | cons c cs ih =>
    dsimp only [buildChainsFrom]
    rw [ih (start + 1) ((buildChain w (chainName start) c).2)]
    rw [buildChain_nextId']
    simp [chainNodeCount, List.map, List.sum]
    omega

/-- The observer-id list returned by `buildChainsFrom` has one entry per
    spec. -/
theorem buildChainsFrom_observers_length (start : Nat) (w : World)
    (specs : List ChainSpec) :
    (buildChainsFrom start w specs).2.length = specs.length := by
  induction specs generalizing start w with
  | nil => dsimp [buildChainsFrom]
  | cons c cs ih =>
    dsimp only [buildChainsFrom]
    simp [ih (start + 1) ((buildChain w (chainName start) c).2)]

/-- The `i`-th observer id is the starting `nextId` plus the total node count
    of the preceding chains, plus 1. -/
theorem buildChainsFrom_observers_getElem (start : Nat) (w : World)
    (specs : List ChainSpec) (i : Nat)
    (hi : i < (buildChainsFrom start w specs).2.length) :
    (buildChainsFrom start w specs).2[i]'hi =
      w.nextId + ((specs.take i).map chainNodeCount).sum + 1 := by
  induction specs generalizing start w i with
  | nil =>
    dsimp [buildChainsFrom] at hi
    exact (Nat.not_lt_zero i hi).elim
  | cons c cs ih =>
    cases i with
    | zero =>
      dsimp only [buildChainsFrom]
      simp [buildChain, buildChainPre, addNode_fst]
    | succ i' =>
      dsimp only [buildChainsFrom] at hi ⊢
      have hlen : (((buildChain w (chainName start) c).1 + 1) ::
          (buildChainsFrom (start + 1)
            ((buildChain w (chainName start) c).2) cs).2).length =
          (buildChainsFrom (start + 1)
            ((buildChain w (chainName start) c).2) cs).2.length + 1 := by rfl
      rw [hlen] at hi
      have hi' : i' < (buildChainsFrom (start + 1)
          ((buildChain w (chainName start) c).2) cs).2.length := by omega
      have hreduce :
          (((buildChain w (chainName start) c).1 + 1) ::
              (buildChainsFrom (start + 1)
                ((buildChain w (chainName start) c).2) cs).2)[i'.succ]'hi =
            (buildChainsFrom (start + 1)
              ((buildChain w (chainName start) c).2) cs).2[i']'hi' := by rfl
      rw [hreduce]
      rw [ih (start + 1) ((buildChain w (chainName start) c).2) i' hi']
      rw [buildChain_nextId']
      simp [chainNodeCount, List.take]
      omega

/-- `buildChains` starts from `World.empty` (nextId 0), so the `i`-th observer
    id is 1 plus the total node count of the preceding chains. -/
theorem buildChains_observer_getElem (specs : List ChainSpec) (i : Nat)
    (hi : i < (buildChains specs).2.length) :
    (buildChains specs).2[i]'hi = ((specs.take i).map chainNodeCount).sum + 1 := by
  dsimp [buildChains]
  rw [buildChainsFrom_observers_getElem 0 World.empty specs i hi]
  simp [World.empty]

/-- The total nextId after building all chains on `World.empty`. -/
theorem buildChains_nextId (specs : List ChainSpec) :
    (buildChains specs).1.nextId = (specs.map chainNodeCount).sum := by
  dsimp [buildChains]
  rw [buildChainsFrom_nextId]
  simp [World.empty]

/-- Building a list of chains does not disturb the lookup of an id below the
    starting `nextId`. -/
theorem buildChainsFrom_getNode_of_lt (start : Nat) (w : World)
    (specs : List ChainSpec) (id : Nat) (h : id < w.nextId) :
    (buildChainsFrom start w specs).1.getNode id = w.getNode id := by
  induction specs generalizing start w with
  | nil => dsimp [buildChainsFrom]
  | cons c cs ih =>
    dsimp only [buildChainsFrom]
    rw [ih (start + 1) ((buildChain w (chainName start) c).2) (by
      rw [buildChain_nextId']; omega)]
    exact buildChain_getNode_of_lt w (chainName start) c id h

/-- Building all chains on `World.empty` does not disturb a lookup of an
    impossible id (`World.empty.nextId = 0`). -/
theorem buildChains_getNode_of_lt (specs : List ChainSpec) (id : Nat)
    (h : id < 0) : (buildChains specs).1.getNode id = World.empty.getNode id := by
  exfalso; omega

/-- Advancing `buildChainsFrom` by `n` chains: the final world is obtained by
    first building `take n` specs, then building `drop n` specs on the
    result. -/
theorem buildChainsFrom_advance (start : Nat) (w : World)
    (specs : List ChainSpec) (n : Nat) :
    (buildChainsFrom start w specs).1 =
      (buildChainsFrom (start + n)
        (buildChainsFrom start w (specs.take n)).1 (specs.drop n)).1 := by
  induction n generalizing start w specs with
  | zero =>
    simp [List.take, List.drop, buildChainsFrom]
  | succ n ih =>
    cases specs with
    | nil => simp [List.take, List.drop, buildChainsFrom]
    | cons c cs =>
      let w' := (buildChain w (chainName start) c).2
      have ht : (c :: cs).take n.succ = c :: cs.take n := by simp [List.take]
      have hd : (c :: cs).drop n.succ = cs.drop n := by simp [List.drop]
      have hbuild : (buildChainsFrom start w (c :: cs.take n)).1 =
          (buildChainsFrom (start + 1) w' (cs.take n)).1 := by
        dsimp [buildChainsFrom, w']
      have hlhs : (buildChainsFrom start w (c :: cs)).1 =
          (buildChainsFrom (start + 1) w' cs).1 := by
        dsimp [buildChainsFrom, w']
      rw [hlhs, ht, hd, hbuild]
      have hs : start + n.succ = start + 1 + n := by omega
      rw [hs]
      exact ih (start + 1) w' cs

/-- Building `l ++ [c]` is the same as building `l` and then appending chain
    `c`. -/
theorem buildChainsFrom_append_one (start : Nat) (w : World)
    (l : List ChainSpec) (c : ChainSpec) :
    (buildChainsFrom start w (l ++ [c])).1 =
      (buildChain (buildChainsFrom start w l).1
        (chainName (start + l.length)) c).2 := by
  induction l generalizing start w with
  | nil =>
    dsimp [buildChainsFrom]
  | cons x xs ih =>
    let w' := (buildChain w (chainName start) x).2
    have hlhs : (buildChainsFrom start w ((x :: xs) ++ [c])).1 =
        (buildChainsFrom (start + 1) w' (xs ++ [c])).1 := by
      rw [List.cons_append]
      dsimp [buildChainsFrom, w']
    rw [hlhs, ih (start + 1) w']
    have hW : (buildChainsFrom start w (x :: xs)).1 =
        (buildChainsFrom (start + 1) w' xs).1 := by
      dsimp [buildChainsFrom, w']
    rw [hW]
    have harg : start + 1 + xs.length = start + (x :: xs).length := by
      change start + 1 + xs.length = start + (xs.length + 1)
      omega
    rw [harg]

/-- `drop i` peels off the `i`-th element as the head. -/
theorem drop_eq_cons_getElem {α : Type} (l : List α) (i : Nat)
    (hi : i < l.length) : l.drop i = l[i]'hi :: l.drop (i + 1) := by
  revert hi
  induction l generalizing i with
  | nil => intro hi; exact (Nat.not_lt_zero _ hi).elim
  | cons x xs ih =>
    intro hi
    cases i with
    | zero => simp [List.drop]
    | succ i' =>
      have hi' : i' < xs.length := Nat.lt_of_succ_lt_succ hi
      have hget : (x :: xs)[i'.succ]'hi = xs[i']'hi' := by rfl
      simp only [List.drop]
      rw [hget]
      exact ih i' hi'

/-- Splitting `buildChainsFrom` at index `i`: the final world is obtained by
    building the first `i` chains, then chain `i`, then the remaining
    chains. -/
theorem buildChainsFrom_world_split (start : Nat) (w : World)
    (specs : List ChainSpec) (i : Nat) (hi : i < specs.length) :
    (buildChainsFrom start w specs).1 =
      (buildChainsFrom (start + i + 1)
        (buildChain (buildChainsFrom start w (specs.take i)).1
          (chainName (start + i)) (specs[i]'hi)).2
        (specs.drop (i + 1))).1 := by
  have hadv := buildChainsFrom_advance start w specs i
  rw [hadv, drop_eq_cons_getElem specs i hi]
  dsimp [buildChainsFrom]

/-- `buildChainsFrom` preserves `idsBounded`. -/
theorem buildChainsFrom_idsBounded (start : Nat) (w : World)
    (specs : List ChainSpec) (h : idsBounded w) :
    idsBounded (buildChainsFrom start w specs).1 := by
  induction specs generalizing start w with
  | nil => dsimp [buildChainsFrom]; exact h
  | cons c cs ih =>
    dsimp only [buildChainsFrom]
    apply ih (start + 1) ((buildChain w (chainName start) c).2)
    exact buildChain_idsBounded w (chainName start) c h

/-- `buildChains` produces an `idsBounded` world. -/
theorem buildChains_idsBounded (specs : List ChainSpec) :
    idsBounded (buildChains specs).1 :=
  buildChainsFrom_idsBounded 0 World.empty specs empty_idsBounded

/-- The world built by `buildChainsFrom`, restricted to a node id that belongs
    to chain `i`, agrees with the world right after chain `i` was built. -/
theorem buildChainsFrom_getNode_chain (start : Nat) (w : World)
    (specs : List ChainSpec) (i : Nat) (hi : i < specs.length) (id : Nat)
    (hid : id < (buildChain (buildChainsFrom start w (specs.take i)).1
        (chainName (start + i)) (specs[i]'hi)).2.nextId) :
    (buildChainsFrom start w specs).1.getNode id =
      (buildChain (buildChainsFrom start w (specs.take i)).1
        (chainName (start + i)) (specs[i]'hi)).2.getNode id := by
  rw [buildChainsFrom_world_split start w specs i hi]
  exact buildChainsFrom_getNode_of_lt (start + i + 1)
    (buildChain (buildChainsFrom start w (specs.take i)).1
      (chainName (start + i)) (specs[i]'hi)).2
    (specs.drop (i + 1)) id hid

/-- Positive lookup: chain `i`'s observer node in the built world. Its base id
    is the total node count of the preceding chains. -/
theorem buildChains_getNode_observer (specs : List ChainSpec) (i : Nat)
    (hi : i < specs.length) :
    (buildChains specs).1.getNode (((specs.take i).map chainNodeCount).sum + 1) =
      some { kind := .observer, sigLevel := 0,
             inputs := [((specs.take i).map chainNodeCount).sum],
             outputs := [((specs.take i).map chainNodeCount).sum + 2] } := by
  set base := ((specs.take i).map chainNodeCount).sum with hbase
  have hWnext : (buildChainsFrom 0 World.empty (specs.take i)).1.nextId = base := by
    dsimp [base]
    rw [buildChainsFrom_nextId]
    simp [World.empty]
  have hid : base + 1 < (buildChain (buildChainsFrom 0 World.empty (specs.take i)).1
      (chainName (0 + i)) (specs[i]'hi)).2.nextId := by
    rw [buildChain_nextId', hWnext]
    dsimp [chainNodeCount]
    omega
  dsimp only [buildChains]
  rw [buildChainsFrom_getNode_chain 0 World.empty specs i hi (base + 1) hid]
  rw [← hWnext]
  exact buildChain_getNode_observer_wired
    (buildChainsFrom 0 World.empty (specs.take i)).1
    (chainName (0 + i)) (specs[i]'hi)
    (buildChainsFrom_idsBounded 0 World.empty (specs.take i) empty_idsBounded)

/-- Positive lookup: chain `i`'s output node in the built world. -/
theorem buildChains_getNode_output (specs : List ChainSpec) (i : Nat)
    (hi : i < specs.length) :
    (buildChains specs).1.getNode
      (((specs.take i).map chainNodeCount).sum + 3 +
        ((specs[i]'hi).middleDelays.zip (specs[i]'hi).middlePriorities).length) =
      some { kind := .output (chainName (0 + i)), sigLevel := 0,
             inputs := [((specs.take i).map chainNodeCount).sum + 2 +
               ((specs[i]'hi).middleDelays.zip (specs[i]'hi).middlePriorities).length],
             outputs := [] } := by
  set base := ((specs.take i).map chainNodeCount).sum with hbase
  set c := specs[i]'hi with hc
  set repLen := (c.middleDelays.zip c.middlePriorities).length with hrepLen
  have hWnext : (buildChainsFrom 0 World.empty (specs.take i)).1.nextId = base := by
    dsimp [base]
    rw [buildChainsFrom_nextId]
    simp [World.empty]
  have hid : base + 3 + repLen < (buildChain
      (buildChainsFrom 0 World.empty (specs.take i)).1
      (chainName (0 + i)) c).2.nextId := by
    rw [buildChain_nextId', hWnext]
    dsimp [chainNodeCount, c, repLen]
    omega
  dsimp only [buildChains]
  rw [buildChainsFrom_getNode_chain 0 World.empty specs i hi (base + 3 + repLen) hid]
  rw [← hWnext]
  exact buildChain_getNode_output_wired
    (buildChainsFrom 0 World.empty (specs.take i)).1
    (chainName (0 + i)) c
    (buildChainsFrom_idsBounded 0 World.empty (specs.take i) empty_idsBounded)

/-- Positive lookup: chain `i`'s last repeater in the built world. -/
theorem buildChains_getNode_lastRep (specs : List ChainSpec) (i : Nat)
    (hi : i < specs.length) :
    (buildChains specs).1.getNode
      (((specs.take i).map chainNodeCount).sum + 2 +
        ((specs[i]'hi).middleDelays.zip (specs[i]'hi).middlePriorities).length) =
      some { kind := NodeKind.repeater (specs[i]'hi).lastDelay (specs[i]'hi).lastPriority,
             sigLevel := 0,
             inputs := [((specs.take i).map chainNodeCount).sum + 1 +
               ((specs[i]'hi).middleDelays.zip (specs[i]'hi).middlePriorities).length],
             outputs := [((specs.take i).map chainNodeCount).sum + 3 +
               ((specs[i]'hi).middleDelays.zip (specs[i]'hi).middlePriorities).length] } := by
  set base := ((specs.take i).map chainNodeCount).sum with hbase
  set c := specs[i]'hi with hc
  set repLen := (c.middleDelays.zip c.middlePriorities).length with hrepLen
  have hWnext : (buildChainsFrom 0 World.empty (specs.take i)).1.nextId = base := by
    dsimp [base]
    rw [buildChainsFrom_nextId]
    simp [World.empty]
  have hid : base + 2 + repLen < (buildChain
      (buildChainsFrom 0 World.empty (specs.take i)).1
      (chainName (0 + i)) c).2.nextId := by
    rw [buildChain_nextId', hWnext]
    dsimp [chainNodeCount, c, repLen]
    omega
  dsimp only [buildChains]
  rw [buildChainsFrom_getNode_chain 0 World.empty specs i hi (base + 2 + repLen) hid]
  rw [← hWnext]
  exact buildChain_getNode_lastRep_wired
    (buildChainsFrom 0 World.empty (specs.take i)).1
    (chainName (0 + i)) c
    (buildChainsFrom_idsBounded 0 World.empty (specs.take i) empty_idsBounded)

/-- Positive lookup: chain `i`'s `j`-th middle repeater in the built world. -/
theorem buildChains_getNode_middleRep (specs : List ChainSpec) (i : Nat)
    (hi : i < specs.length) (j : Nat)
    (hj : j < ((specs[i]'hi).middleDelays.zip (specs[i]'hi).middlePriorities).length) :
    (buildChains specs).1.getNode (((specs.take i).map chainNodeCount).sum + 2 + j) =
      some { kind := NodeKind.repeater
               (((specs[i]'hi).middleDelays.zip (specs[i]'hi).middlePriorities)[j]'hj).1
               (((specs[i]'hi).middleDelays.zip (specs[i]'hi).middlePriorities)[j]'hj).2,
             sigLevel := 0,
             inputs := [((specs.take i).map chainNodeCount).sum + 1 + j],
             outputs := [((specs.take i).map chainNodeCount).sum + 3 + j] } := by
  set base := ((specs.take i).map chainNodeCount).sum with hbase
  set c := specs[i]'hi with hc
  have hWnext : (buildChainsFrom 0 World.empty (specs.take i)).1.nextId = base := by
    dsimp [base]
    rw [buildChainsFrom_nextId]
    simp [World.empty]
  have hid : base + 2 + j < (buildChain
      (buildChainsFrom 0 World.empty (specs.take i)).1
      (chainName (0 + i)) c).2.nextId := by
    rw [buildChain_nextId', hWnext]
    dsimp [chainNodeCount, c]
    omega
  dsimp only [buildChains]
  rw [buildChainsFrom_getNode_chain 0 World.empty specs i hi (base + 2 + j) hid]
  rw [← hWnext]
  exact buildChain_getNode_middleRep_wired
    (buildChainsFrom 0 World.empty (specs.take i)).1
    (chainName (0 + i)) c j hj
    (buildChainsFrom_idsBounded 0 World.empty (specs.take i) empty_idsBounded)
