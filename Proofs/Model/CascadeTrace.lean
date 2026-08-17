import Proofs.Model.BurstInvariance
import Proofs.Model.CascadeTiming
import Proofs.Model.MultiChain

open BasicRedstoneSim
open List

/-! # Cascade trace — per-chain event attribution

Node ids, stage timing and stage events of the built chains. The trace
induction itself (stage events exist and keep their class order as they
march from the observer to the last repeater) builds on these.

Chain `i` occupies node ids
`chainBaseId specs i + 0 .. chainBaseId specs i + 3 + repLenAt specs i`:
input, observer, the middle repeaters, the last repeater, output. Stage
`s` (0-based over `middleDelays ++ [lastDelay]`) is the repeater at
`chainBaseId specs i + 2 + s`. -/

/-! ## Node id functions -/

/-- Number of repeaters of chain `i` minus one is the last stage index;
    `repLenAt` is the number of middle repeaters. -/
def repLenAt (specs : List ChainSpec) (i : Nat) : Nat :=
  (specAt specs i).middleDelays.length

/-- Base node id of chain `i` in the built world. -/
def chainBaseId (specs : List ChainSpec) (i : Nat) : Nat :=
  ((specs.take i).map chainNodeCount).sum

/-- Chain `i`'s observer node id. -/
def chainObserverId (specs : List ChainSpec) (i : Nat) : Nat :=
  chainBaseId specs i + 1

/-- Chain `i`'s stage-`s` repeater node id: middle repeater for
    `s < repLenAt specs i`, last repeater for `s = repLenAt specs i`. -/
def chainRepId (specs : List ChainSpec) (i s : Nat) : Nat :=
  chainBaseId specs i + 2 + s

/-- Chain `i`'s output node id. -/
def chainOutputId (specs : List ChainSpec) (i : Nat) : Nat :=
  chainBaseId specs i + 3 + repLenAt specs i

/-! ## Stage delays and priorities -/

/-- Delay of chain `i`'s stage-`s` repeater (middle delay for
    `s < repLenAt`, last delay otherwise). -/
def stageDelayAt (specs : List ChainSpec) (i s : Nat) : PNat :=
  ((specAt specs i).middleDelays[s]?.getD (specAt specs i).lastDelay)

/-- Priority of chain `i`'s stage-`s` repeater. -/
def stagePriAt (specs : List ChainSpec) (i s : Nat) : Int :=
  ((specAt specs i).middlePriorities[s]?.getD (specAt specs i).lastPriority)

theorem stageDelayAt_of_lt (specs : List ChainSpec) (i s : Nat)
    (hs : s < (specAt specs i).middleDelays.length) :
    stageDelayAt specs i s = (specAt specs i).middleDelays[s]'hs := by
  dsimp [stageDelayAt]
  rw [List.getElem?_eq_getElem hs]
  rfl

theorem stagePriAt_of_lt (specs : List ChainSpec) (i s : Nat)
    (hpri : (specAt specs i).priLenOk)
    (hs : s < (specAt specs i).middleDelays.length) :
    stagePriAt specs i s =
      (specAt specs i).middlePriorities[s]'
        (by dsimp [ChainSpec.priLenOk] at hpri; omega) := by
  dsimp [stagePriAt]
  rw [List.getElem?_eq_getElem
    (by dsimp [ChainSpec.priLenOk] at hpri; omega)]
  rfl

theorem stageDelayAt_of_eq (specs : List ChainSpec) (i : Nat)
    (hs : (specAt specs i).middleDelays.length ≤ s) :
    stageDelayAt specs i s = (specAt specs i).lastDelay := by
  dsimp [stageDelayAt]
  rw [List.getElem?_eq_none hs]
  rfl

theorem stagePriAt_of_eq (specs : List ChainSpec) (i : Nat)
    (hpri : (specAt specs i).priLenOk)
    (hs : (specAt specs i).middleDelays.length ≤ s) :
    stagePriAt specs i s = (specAt specs i).lastPriority := by
  dsimp [stagePriAt]
  rw [List.getElem?_eq_none
    (by dsimp [ChainSpec.priLenOk] at hpri; omega)]
  rfl

/-- `specAt` agrees with the indexed lookup in range. -/
theorem specAt_eq_getElem (specs : List ChainSpec) (i : Nat)
    (hi : i < specs.length) : specAt specs i = specs[i]'hi := by
  dsimp [specAt]
  rw [List.getElem?_eq_getElem hi]
  rfl

/-! ## Stage timing

`chainTickList c a` holds the firing ticks of the whole cascade of a
chain activated at tick `a`: index 0 is the observer firing (`a + 2`),
index `s + 1` is repeater stage `s`, and the last index is the output
tick `a + chainDelay c`. -/

/-- Observer firing tick of chain `i`. -/
def obsTickOf (T : Nat) (specs : List ChainSpec) (i : Nat) : Nat :=
  actTickOf T specs i + 2

/-- Firing tick of chain `i`'s stage-`s` repeater when everything outputs
    on tick `T` (index `s + 1` of the chain's tick list). -/
def stageTickOf (T : Nat) (specs : List ChainSpec) (i s : Nat) : Nat :=
  (chainTickList (specAt specs i) (actTickOf T specs i))[s + 1]?.getD 0

/-- The observer event of chain `i`. -/
def obsEventOf (T : Nat) (specs : List ChainSpec) (i : Nat) :
    ScheduledEvent :=
  { targetTick := obsTickOf T specs i, priority := 0,
    nodeId := chainObserverId specs i }

/-- The stage-`s` event of chain `i`. -/
def stageEventOf (T : Nat) (specs : List ChainSpec) (i s : Nat) :
    ScheduledEvent :=
  { targetTick := stageTickOf T specs i s,
    priority := stagePriAt specs i s, nodeId := chainRepId specs i s }

/-! ## Timing arithmetic -/

/-- `cumSums` head. -/
theorem cumSums_getElem_zero (ds : List Nat) (s : Nat) :
    (cumSums ds s)[0]? = some s := by
  cases ds with
  | nil =>
    dsimp [cumSums]
    rw [List.getElem?_eq_getElem (by dsimp [List.length]; omega)]
    rfl
  | cons d rest =>
    dsimp [cumSums]
    rw [List.getElem?_eq_getElem (by dsimp [List.length]; omega)]
    rfl

/-- The head value of a nonempty `cumSums`. -/
theorem cumSums_head (ds : List Nat) (s : Nat)
    (h : 0 < (cumSums ds s).length) : (cumSums ds s)[0]'h = s := by
  induction ds with
  | nil => dsimp [cumSums]
  | cons d rest ih => dsimp [cumSums]

/-- `cumSums` successor: element `k + 1` equals element `k` plus delay
    `k`. -/
theorem cumSums_getElem_succ (ds : List Nat) (s : Nat) (k : Nat)
    (hk : k + 1 < (cumSums ds s).length) :
    (cumSums ds s)[k + 1]'hk =
      (cumSums ds s)[k]'(by have := cumSums_length ds s; omega) +
        ds[k]'(by have := cumSums_length ds s; omega) := by
  revert k hk
  induction ds generalizing s with
  | nil =>
    intro k hk
    dsimp [cumSums, List.length] at hk
    omega
  | cons d rest ih =>
    intro k hk
    dsimp [cumSums] at hk ⊢
    cases k with
    | zero =>
      exact cumSums_head rest (s + d) (by
        dsimp [List.length] at hk
        omega)
    | succ k' =>
      have hk' : k' + 1 < (cumSums rest (s + d)).length := by
        change k'.succ + 1 < (cumSums rest (s + d)).length + 1 at hk
        omega
      exact ih (s + d) k' hk'

/-- The observer fires at the head of the tick list. -/
theorem chainTickList_getElem_zero (c : ChainSpec) (t : Nat) :
    (chainTickList c t)[0]? = some (t + 2) := by
  dsimp [chainTickList]
  exact cumSums_getElem_zero _ _

/-! ## Node lookups in the built world -/

/-- Unified repeater lookup: stage `s` of chain `i` (middle for
    `s < repLenAt`, last for `s = repLenAt`). -/
theorem buildChains_getNode_rep (specs : List ChainSpec) (i s : Nat)
    (hi : i < specs.length) (hpri : (specAt specs i).priLenOk)
    (hs : s ≤ (specAt specs i).middleDelays.length) :
    (buildChains specs).1.getNode (chainRepId specs i s) =
      some { kind := NodeKind.repeater (stageDelayAt specs i s)
               (stagePriAt specs i s),
             sigLevel := 0,
             inputs := [chainBaseId specs i + 1 + s],
             outputs := [chainBaseId specs i + 3 + s] } := by
  dsimp [chainRepId, chainBaseId, stageDelayAt, stagePriAt]
  rw [specAt_eq_getElem specs i hi] at hpri hs ⊢
  by_cases hlt : s < (specs[i]'hi).middleDelays.length
  · have hzip : s < ((specs[i]'hi).middleDelays.zip
        (specs[i]'hi).middlePriorities).length := by
      dsimp [ChainSpec.priLenOk] at hpri
      rw [List.length_zip, hpri, min_self]
      exact hlt
    rw [buildChains_getNode_middleRep specs i hi s hzip]
    have hp : s < (specs[i]'hi).middlePriorities.length := by
      dsimp [ChainSpec.priLenOk] at hpri
      omega
    rw [List.getElem?_eq_getElem hlt, List.getElem?_eq_getElem hp]
    simp [List.zip, List.getElem_zipWith]
  · have heq : s = (specs[i]'hi).middleDelays.length := by omega
    subst heq
    have hzip : ((specs[i]'hi).middleDelays.zip
        (specs[i]'hi).middlePriorities).length =
        (specs[i]'hi).middleDelays.length := by
      dsimp [ChainSpec.priLenOk] at hpri
      rw [List.length_zip, hpri, min_self]
    rw [← hzip, buildChains_getNode_lastRep specs i hi]
    rw [List.getElem?_eq_none (l := (specs[i]'hi).middleDelays) (by omega),
      List.getElem?_eq_none (l := (specs[i]'hi).middlePriorities) (by
        dsimp [ChainSpec.priLenOk] at hpri
        omega)]
    rfl

/-- Observer lookup restated with the id function. -/
theorem buildChains_getNode_observer' (specs : List ChainSpec) (i : Nat)
    (hi : i < specs.length) :
    (buildChains specs).1.getNode (chainObserverId specs i) =
      some { kind := NodeKind.observer, sigLevel := 0,
             inputs := [chainBaseId specs i],
             outputs := [chainBaseId specs i + 2] } := by
  dsimp [chainObserverId, chainBaseId]
  exact buildChains_getNode_observer specs i hi

/-- Output lookup restated with the id function. -/
theorem buildChains_getNode_output' (specs : List ChainSpec) (i : Nat)
    (hi : i < specs.length) (hpri : (specAt specs i).priLenOk) :
    (buildChains specs).1.getNode (chainOutputId specs i) =
      some { kind := NodeKind.output (chainName i), sigLevel := 0,
             inputs := [chainBaseId specs i + 2 + repLenAt specs i],
             outputs := [] } := by
  dsimp [chainOutputId, chainBaseId, repLenAt]
  rw [specAt_eq_getElem specs i hi] at hpri ⊢
  have hzip : ((specs[i]'hi).middleDelays.zip
      (specs[i]'hi).middlePriorities).length =
      (specs[i]'hi).middleDelays.length := by
    dsimp [ChainSpec.priLenOk] at hpri
    rw [List.length_zip, hpri, min_self]
  rw [← hzip, buildChains_getNode_output specs i hi]
  have hname : chainName (0 + i) = chainName i := by
    dsimp [chainName]
    congr 1
    omega
  rw [hname]

/-! ## Observer list of the built world -/

/-- The observer list returned by `buildChains` has one entry per spec. -/
theorem buildChains_observers_length (specs : List ChainSpec) :
    (buildChains specs).2.length = specs.length := by
  dsimp [buildChains]
  exact buildChainsFrom_observers_length 0 World.empty specs

/-- The `i`-th observer id is `chainObserverId specs i`. -/
theorem observers_getElem_eq_chainObserverId (specs : List ChainSpec)
    (i : Nat) (hi : i < (buildChains specs).2.length) :
    (buildChains specs).2[i]'hi = chainObserverId specs i := by
  rw [buildChains_observer_getElem specs i hi]
  dsimp [chainObserverId, chainBaseId]

/-! ## The stage-tick recurrence

The firing ticks of a chain's stages walk the delay list: stage 0 fires at
`activation + 2 + d₀`, each stage fires its delay after the previous one,
and the last stage fires at the output tick. Stated on the `getElem?` /
`getD` surface so out-of-range indices stay junk-free. -/

/-- The last element of `l ++ [x]` sits at index `l.length`. -/
private theorem getElem?_append_singleton_length {α : Type} (l : List α)
    (x : α) : (l ++ [x])[l.length]? = some x := by
  rw [List.getElem?_append]
  simp

/-- Coerced middle-delay map: cons reduction. -/
private theorem map_coe_cons (d : PNat) (rest : List PNat) :
    (d :: rest).map (fun x => (x : Nat)) =
      (d : Nat) :: rest.map (fun x => (x : Nat)) := by
  dsimp [List.map, List.flatMap]

/-- A chain's tick list has one entry per stage plus the observer. -/
theorem chainTickList_length (c : ChainSpec) (t : Nat) :
    (chainTickList c t).length = c.middleDelays.length + 2 := by
  dsimp [chainTickList]
  rw [cumSums_length]
  set mids := c.middleDelays with hmids
  set last := c.lastDelay with hlast
  induction mids with
  | nil => dsimp [List.flatMap, List.map, List.length]
  | cons d rest ih =>
    dsimp [List.flatMap, List.map, List.length] at ih ⊢
    omega

/-- The last stage fires at the output tick `T`. -/
theorem stageTickOf_last (T : Nat) (specs : List ChainSpec) (i : Nat)
    (hfit : chainDelay (specAt specs i) ≤ T) :
    stageTickOf T specs i (repLenAt specs i) = T := by
  dsimp [stageTickOf, repLenAt]
  set c := specAt specs i with hc
  set a := actTickOf T specs i with ha
  obtain ⟨init, htl⟩ := chainTickList_append c a
  have hlen : init.length = c.middleDelays.length + 1 := by
    have := congrArg List.length htl
    rw [List.length_append, List.length_singleton] at this
    rw [chainTickList_length] at this
    omega
  rw [htl, ← hlen]
  rw [getElem?_append_singleton_length]
  dsimp [Option.getD, a]
  dsimp [actTickOf]
  rw [← hc]
  exact Nat.sub_add_cancel hfit

/-- `cumSums` successor on the `getElem?` / `getD` surface. -/
theorem cumSums_getElem_succ_getD (ds : List Nat) (s : Nat) (k : Nat)
    (hk : k + 1 < (cumSums ds s).length) :
    (cumSums ds s)[k + 1]?.getD 0 =
      (cumSums ds s)[k]?.getD 0 + ds[k]?.getD 0 := by
  revert k hk
  induction ds generalizing s with
  | nil =>
    intro k hk
    dsimp [cumSums, List.length] at hk
    omega
  | cons d rest ih =>
    intro k hk
    dsimp [cumSums] at hk ⊢
    cases k with
    | zero =>
      rw [cumSums_getElem_zero rest (s + d)]
      dsimp [Option.getD]
      rfl
    | succ k' =>
      rw [getElem?_cons_succ, getElem?_cons_succ]
      exact ih (s + d) k' (by omega)

/-- The `k`-th delay of `middleDelays ++ [lastDelay]` coerced, as a
    `getElem?` / `getD` lookup. -/
theorem delays_getElem_getD (c : ChainSpec) (k : Nat)
    (hk : k ≤ c.middleDelays.length) :
    ((c.middleDelays.map (fun d => (d : Nat))) ++
      [(c.lastDelay : Nat)])[k]?.getD 0 =
        ↑(c.middleDelays[k]?.getD c.lastDelay) := by
  set mids := c.middleDelays with hmids
  set last := c.lastDelay with hlast
  revert k hk
  induction mids with
  | nil =>
    intro k hk
    dsimp [List.length] at hk
    have hz : k = 0 := by omega
    subst hz
    dsimp [List.map, List.flatMap]
    rw [List.getElem?_eq_getElem (by dsimp [List.length]; omega)]
    simp
  | cons d rest ih =>
    intro k hk
    cases k with
    | zero =>
      dsimp [List.map, List.flatMap]
      rw [List.getElem?_eq_getElem (by dsimp [List.length]; omega)]
      rw [List.getElem?_eq_getElem (by dsimp [List.length]; omega)]
      simp
    | succ k' =>
      dsimp [List.map, List.flatMap]
      exact ih k' (by dsimp [List.length] at hk; omega)

/-- Stage 0 fires at activation + 2 + the first stage delay. -/
theorem stageTickOf_zero (T : Nat) (specs : List ChainSpec) (i : Nat) :
    stageTickOf T specs i 0 =
      actTickOf T specs i + 2 + (stageDelayAt specs i 0 : Nat) := by
  dsimp [stageTickOf, stageDelayAt]
  set c := specAt specs i with hc
  set a := actTickOf T specs i with ha
  have h1 : (chainTickList c a)[0 + 1]?.getD 0 =
      (chainTickList c a)[0]?.getD 0 +
        ((c.middleDelays[0]?.getD c.lastDelay : PNat) : Nat) := by
    dsimp [chainTickList]
    rw [cumSums_getElem_succ_getD _ _ 0 (by change 0 + 1 < (chainTickList c a).length; rw [chainTickList_length]; omega)]
    rw [cumSums_getElem_zero _ (a + 2)]
    dsimp [Option.getD]
    congr 1
    exact delays_getElem_getD c 0 (by omega)
  rw [h1, chainTickList_getElem_zero c a]
  dsimp [Option.getD]

/-- Stage `s + 1` fires its delay after stage `s`. -/
theorem stageTickOf_succ (T : Nat) (specs : List ChainSpec) (i s : Nat)
    (hs : s + 1 ≤ (specAt specs i).middleDelays.length) :
    stageTickOf T specs i (s + 1) =
      stageTickOf T specs i s + (stageDelayAt specs i (s + 1) : Nat) := by
  dsimp [stageTickOf]
  set c := specAt specs i with hc
  set a := actTickOf T specs i with ha
  have h1 : (chainTickList c a)[s + 1 + 1]?.getD 0 =
      (chainTickList c a)[s + 1]?.getD 0 +
        ((c.middleDelays[s + 1]?.getD c.lastDelay : PNat) : Nat) := by
    dsimp [chainTickList]
    rw [cumSums_getElem_succ_getD _ _ (s + 1) (by change s + 1 + 1 < (chainTickList c a).length; rw [chainTickList_length]; omega)]
    congr 1
    exact delays_getElem_getD c (s + 1) hs
  rw [h1]
  dsimp [stageDelayAt]

