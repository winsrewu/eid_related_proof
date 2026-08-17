import Proofs.Model.ChainIds

open BasicRedstoneSim
open World
open List

/-! # The cascade spawn function and the exact firing equation. -/

/-! ## The cascade spawn function

The event a fired cascade event appends, defined by searching the chain
index (observer events spawn stage 0; stage-`s` events with
`s < repLenAt` spawn stage `s + 1`; last repeaters spawn nothing). -/

private def obsSpawnSearch (T : Nat) (specs : List ChainSpec)
    (e : ScheduledEvent) : List Nat → Option ScheduledEvent
  | [] => none
  | i :: rest =>
    if e = obsEventOf T specs i then some (stageEventOf T specs i 0)
    else obsSpawnSearch T specs e rest

private def stageSpawnSearch (T : Nat) (specs : List ChainSpec)
    (e : ScheduledEvent) : List (Nat × Nat) → Option ScheduledEvent
  | [] => none
  | ⟨i, s⟩ :: rest =>
    if e = stageEventOf T specs i s then
      some (stageEventOf T specs i (s + 1))
    else stageSpawnSearch T specs e rest

/-- The cascade spawn of an event. -/
def cascadeSpawn (T : Nat) (specs : List ChainSpec)
    (e : ScheduledEvent) : List ScheduledEvent :=
  match obsSpawnSearch T specs e (List.range specs.length) with
  | some ev => [ev]
  | none =>
    match stageSpawnSearch T specs e
        ((List.range specs.length).flatMap (fun i =>
          (List.range (repLenAt specs i)).map (fun s => (i, s)))) with
    | some ev => [ev]
    | none => []

private theorem obsSpawnSearch_none (T : Nat) (specs : List ChainSpec)
    (e : ScheduledEvent) (l : List Nat)
    (hnone : ∀ j ∈ l, e ≠ obsEventOf T specs j) :
    obsSpawnSearch T specs e l = none := by
  induction l with
  | nil => dsimp [obsSpawnSearch]
  | cons a rest ih =>
    dsimp [obsSpawnSearch]
    rw [if_neg (hnone a (List.mem_cons.mpr (Or.inl rfl)))]
    exact ih (fun j hj => hnone j (List.mem_cons.mpr (Or.inr hj)))

private theorem stageSpawnSearch_none (T : Nat) (specs : List ChainSpec)
    (e : ScheduledEvent) (l : List (Nat × Nat))
    (hnone : ∀ p ∈ l, e ≠ stageEventOf T specs p.1 p.2) :
    stageSpawnSearch T specs e l = none := by
  induction l with
  | nil => dsimp [stageSpawnSearch]
  | cons p rest ih =>
    rcases p with ⟨j, t⟩
    dsimp [stageSpawnSearch]
    rw [if_neg (hnone (j, t) (List.mem_cons.mpr (Or.inl rfl)))]
    exact ih (fun q hq => hnone q (List.mem_cons.mpr (Or.inr hq)))

private theorem obsSpawnSearch_mem (T : Nat) (specs : List ChainSpec)
    (l : List Nat) (hl : ∀ x ∈ l, x < specs.length) (i : Nat)
    (hi : i ∈ l) :
    obsSpawnSearch T specs (obsEventOf T specs i) l =
      some (stageEventOf T specs i 0) := by
  induction l generalizing i with
  | nil => cases hi
  | cons a rest ih =>
    dsimp [obsSpawnSearch]
    by_cases heq : obsEventOf T specs i = obsEventOf T specs a
    · rw [if_pos heq]
      have hnode := congrArg (fun ev => ev.nodeId) heq
      dsimp [obsEventOf] at hnode
      have hai : a = i := by
        apply Eq.symm
        exact chainObserverId_inj specs i a (hl i hi)
          (hl a (List.mem_cons.mpr (Or.inl rfl))) hnode
      subst hai
      rfl
    · rw [if_neg heq]
      apply ih
      · intro x hx
        exact hl x (List.mem_cons.mpr (Or.inr hx))
      · rcases List.mem_cons.mp hi with rfl | hrest
        · exfalso
          exact heq rfl
        · exact hrest

/-- `(i, s)` sits in the stage-search list when `s < repLenAt`. -/
private theorem stagePair_mem (specs : List ChainSpec) (i s : Nat)
    (hi : i < specs.length) (hs : s < repLenAt specs i) :
    (i, s) ∈ (List.range specs.length).flatMap (fun i =>
      (List.range (repLenAt specs i)).map (fun s => (i, s))) := by
  rw [List.mem_flatMap]
  refine ⟨i, List.mem_range.mpr hi, ?_⟩
  rw [List.mem_map]
  exact ⟨s, List.mem_range.mpr hs, rfl⟩

private theorem stageSpawnSearch_mem (T : Nat) (specs : List ChainSpec)
    (l : List (Nat × Nat))
    (hl : ∀ p ∈ l, p.1 < specs.length ∧ p.2 ≤ repLenAt specs p.1 ∧
      (specAt specs p.1).priLenOk)
    (i s : Nat) (hi : i < specs.length)
    (hpri : (specAt specs i).priLenOk)
    (hs : s < repLenAt specs i)
    (hp : (i, s) ∈ l) :
    stageSpawnSearch T specs (stageEventOf T specs i s) l =
      some (stageEventOf T specs i (s + 1)) := by
  induction l generalizing i s with
  | nil => cases hp
  | cons p rest ih =>
    rcases p with ⟨j, t⟩
    dsimp [stageSpawnSearch]
    by_cases heq : stageEventOf T specs i s = stageEventOf T specs j t
    · rw [if_pos heq]
      have hnode := congrArg (fun ev => ev.nodeId) heq
      dsimp [stageEventOf] at hnode
      obtain ⟨hji, hts⟩ := chainRepId_inj specs i j s t hi
        (hl (j, t) (List.mem_cons.mpr (Or.inl rfl))).1
        (Nat.le_of_lt hs)
        (hl (j, t) (List.mem_cons.mpr (Or.inl rfl))).2.1
        hpri
        (hl (j, t) (List.mem_cons.mpr (Or.inl rfl))).2.2 hnode
      subst hji
      subst hts
      rfl
    · rw [if_neg heq]
      apply ih
      · intro q hq
        exact hl q (List.mem_cons.mpr (Or.inr hq))
      · exact hi
      · exact hpri
      · exact hs
      · rcases List.mem_cons.mp hp with hpair | hrest
        · exfalso
          have hij := congrArg Prod.fst hpair
          have hst := congrArg Prod.snd hpair
          subst hij
          subst hst
          exact heq rfl
        · exact hrest

/-- Observer events spawn the stage-0 event of their chain. -/
theorem cascadeSpawn_obs (T : Nat) (specs : List ChainSpec) (i : Nat)
    (hi : i < specs.length) :
    cascadeSpawn T specs (obsEventOf T specs i) =
      [stageEventOf T specs i 0] := by
  dsimp [cascadeSpawn]
  rw [obsSpawnSearch_mem T specs (List.range specs.length)
    (fun x hx => List.mem_range.mp hx) i (List.mem_range.mpr hi)]

/-- Middle stage events spawn their successor stage event. -/
theorem cascadeSpawn_stage (T : Nat) (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (i s : Nat) (hi : i < specs.length)
    (hs : s < repLenAt specs i) :
    cascadeSpawn T specs (stageEventOf T specs i s) =
      [stageEventOf T specs i (s + 1)] := by
  dsimp [cascadeSpawn]
  have hobsNone : obsSpawnSearch T specs (stageEventOf T specs i s)
      (List.range specs.length) = none := by
    apply obsSpawnSearch_none
    intro j hj heq
    have hnode := congrArg (fun ev => ev.nodeId) heq
    dsimp [stageEventOf, obsEventOf, chainRepId, chainObserverId]
      at hnode
    have hjLen : j < specs.length := List.mem_range.mp hj
    have hsLe : s ≤ repLenAt specs i := Nat.le_of_lt hs
    have hpri : (specAt specs i).priLenOk := (h_valid i hi).1
    by_cases hlt : i < j
    · have hltNext := chainRepId_lt_nextBase specs i s hsLe hpri
      dsimp [chainRepId] at hltNext
      have hsucc := chainBaseId_succ specs i hi
      rw [← hsucc] at hltNext
      have hmono : chainBaseId specs (i + 1) ≤ chainBaseId specs j :=
        chainBaseId_mono specs (i + 1) j (by omega)
      have h1 : chainBaseId specs i + 2 + s < chainBaseId specs j :=
        Nat.lt_of_lt_of_le hltNext hmono
      omega
    · by_cases hgt : j < i
      · have hmono : chainBaseId specs (j + 1) ≤ chainBaseId specs i :=
          chainBaseId_mono specs (j + 1) i (by omega)
        have hsucc := chainBaseId_succ specs j hjLen
        have hcnt : 2 ≤ chainNodeCount (specAt specs j) := by
          dsimp [chainNodeCount]
          omega
        have hlt' : chainBaseId specs j + 1 <
            chainBaseId specs j + chainNodeCount (specAt specs j) := by
          omega
        rw [← hsucc] at hlt'
        have hstep : chainBaseId specs j + 1 < chainBaseId specs i :=
          Nat.lt_of_lt_of_le hlt' hmono
        omega
      · have heqij : i = j := by omega
        subst heqij
        omega
  rw [hobsNone]
  rw [stageSpawnSearch_mem T specs
    ((List.range specs.length).flatMap (fun i =>
      (List.range (repLenAt specs i)).map (fun s => (i, s))))
    ?_ i s hi ((h_valid i hi).1) hs (stagePair_mem specs i s hi hs)]
  intro p hp
  obtain ⟨j, hj, hpj⟩ := List.mem_flatMap.mp hp
  rcases p with ⟨pj, ps⟩
  rw [List.mem_map] at hpj
  obtain ⟨t, ht, hpt⟩ := hpj
  have hpj1 := congrArg Prod.fst hpt
  have hpj2 := congrArg Prod.snd hpt
  subst hpj1
  subst hpj2
  refine ⟨List.mem_range.mp hj,
    Nat.le_of_lt (List.mem_range.mp ht),
    (h_valid j (List.mem_range.mp hj)).1⟩

/-- The last repeater spawns nothing. -/
theorem cascadeSpawn_lastRep (T : Nat) (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (i : Nat) (hi : i < specs.length) :
    cascadeSpawn T specs
      (stageEventOf T specs i (repLenAt specs i)) = [] := by
  dsimp [cascadeSpawn]
  have hobsNone : obsSpawnSearch T specs
      (stageEventOf T specs i (repLenAt specs i))
      (List.range specs.length) = none := by
    apply obsSpawnSearch_none
    intro j hj heq
    have hnode := congrArg (fun ev => ev.nodeId) heq
    dsimp [stageEventOf, obsEventOf, chainRepId, chainObserverId]
      at hnode
    have hjLen : j < specs.length := List.mem_range.mp hj
    have hpri : (specAt specs i).priLenOk := (h_valid i hi).1
    have hltNext := chainRepId_lt_nextBase specs i (repLenAt specs i)
      (by dsimp [repLenAt]; omega) hpri
    dsimp [chainRepId] at hltNext
    by_cases hlt : i < j
    · have hmono : chainBaseId specs (i + 1) ≤ chainBaseId specs j :=
        chainBaseId_mono specs (i + 1) j (by omega)
      have hsucc := chainBaseId_succ specs i hi
      rw [← hsucc] at hltNext
      have h1 : chainBaseId specs i + 2 + repLenAt specs i <
          chainBaseId specs j :=
        Nat.lt_of_lt_of_le hltNext hmono
      omega
    · by_cases hgt : j < i
      · have hmono : chainBaseId specs (j + 1) ≤ chainBaseId specs i :=
          chainBaseId_mono specs (j + 1) i (by omega)
        have hsucc := chainBaseId_succ specs j hjLen
        have hcnt : 2 ≤ chainNodeCount (specAt specs j) := by
          dsimp [chainNodeCount]
          omega
        have hlt' : chainBaseId specs j + 1 <
            chainBaseId specs j + chainNodeCount (specAt specs j) := by
          omega
        rw [← hsucc] at hlt'
        have hstep : chainBaseId specs j + 1 < chainBaseId specs i :=
          Nat.lt_of_lt_of_le hlt' hmono
        omega
      · have heqij : i = j := by omega
        subst heqij
        omega
  have hstageNone : stageSpawnSearch T specs
      (stageEventOf T specs i (repLenAt specs i))
      ((List.range specs.length).flatMap (fun i =>
        (List.range (repLenAt specs i)).map (fun s => (i, s)))) =
      none := by
    apply stageSpawnSearch_none
    intro p hp heq
    rcases p with ⟨pj, ps⟩
    have hnode := congrArg (fun ev => ev.nodeId) heq
    dsimp [stageEventOf] at hnode
    obtain ⟨j, hj, hpj⟩ := List.mem_flatMap.mp hp
    rw [List.mem_map] at hpj
    obtain ⟨t, ht, hpt⟩ := hpj
    have hpj1 : pj = j := (congrArg Prod.fst hpt).symm
    have hps1 : ps = t := (congrArg Prod.snd hpt).symm
    rw [hpj1, hps1] at hnode
    have hjLen : j < specs.length := List.mem_range.mp hj
    have hpri_j : (specAt specs j).priLenOk :=
      (h_valid j hjLen).1
    have hpri_i : (specAt specs i).priLenOk := (h_valid i hi).1
    obtain ⟨hji, hts⟩ := chainRepId_inj specs i j (repLenAt specs i) t
      hi hjLen (by dsimp [repLenAt]; omega)
      (Nat.le_of_lt (List.mem_range.mp ht)) hpri_i hpri_j hnode
    subst hji
    subst hts
    exact Nat.lt_irrefl (repLenAt specs i) (List.mem_range.mp ht)
  rw [hobsNone, hstageNone]

/-! ## Exact firing equation in cascadeSpawn form -/

/-- Firing a popped cascade event appends exactly its cascade spawn. -/
theorem firing_cascadeSpawn_eq (T : Nat) (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (w : World) (e : ScheduledEvent) (wp : World)
    (hpop : w.popNextEvent = some (e, wp))
    (hgood : CascadeGood T specs w)
    (hwiring : ∀ id, (w.getNode id).map wiring =
      ((buildChains specs).1.getNode id).map wiring) :
    (wp.onScheduledTick e.nodeId).events =
      wp.events ++ cascadeSpawn T specs e := by
  obtain ⟨idx, hidx, herase, htickE, hget⟩ :=
    popNextEvent_eraseIdx w e wp hpop
  have hmem : e ∈ w.events := by
    rw [← hget]
    exact List.getElem_mem hidx
  have hwWp : ∀ id, (wp.getNode id).map wiring =
      ((buildChains specs).1.getNode id).map wiring := by
    intro id
    rw [World.getNode_of_nodes_eq wp w (popNextEvent_nodes w e wp hpop)
      id, hwiring]
  rcases hgood e hmem with ⟨i, hi, rfl⟩ | hstage
  · -- observer event
    have hnode : (obsEventOf T specs i).nodeId =
        chainObserverId specs i := rfl
    rw [hnode]
    have htickWp : wp.tick = obsTickOf T specs i := by
      rw [World.popNextEvent_tick w (obsEventOf T specs i) wp hpop,
        ← htickE]
      rfl
    have hobs : ∃ nd, wp.getNode (chainObserverId specs i) = some nd ∧
        nd.kind = NodeKind.observer ∧
        nd.outputs = [chainRepId specs i 0] := by
      have hb := buildChains_getNode_observer' specs i hi
      have houts : [chainBaseId specs i + 2] = [chainRepId specs i 0] := by
        dsimp [chainRepId]
      rw [houts] at hb
      exact wiring_kind_exists wp (buildChains specs).1
        (chainObserverId specs i) NodeKind.observer
        [chainRepId specs i 0] (hwWp (chainObserverId specs i))
        ⟨{ kind := NodeKind.observer, sigLevel := 0, inputs := [chainBaseId specs i], outputs := [chainRepId specs i 0] }, hb, rfl, rfl⟩
    have hrep : ∃ nd, wp.getNode (chainRepId specs i 0) = some nd ∧
        nd.kind = NodeKind.repeater (stageDelayAt specs i 0)
          (stagePriAt specs i 0) := by
      have hb := buildChains_getNode_rep specs i 0 hi
        ((h_valid i hi).1) (by omega)
      obtain ⟨nd, hgetN, hkindN, _⟩ := wiring_kind_exists wp
        (buildChains specs).1 (chainRepId specs i 0)
        (NodeKind.repeater (stageDelayAt specs i 0)
          (stagePriAt specs i 0)) [chainBaseId specs i + 3 + 0]
        (hwWp (chainRepId specs i 0))
        ⟨{ kind := NodeKind.repeater (stageDelayAt specs i 0) (stagePriAt specs i 0), sigLevel := 0, inputs := [chainBaseId specs i + 1 + 0], outputs := [chainBaseId specs i + 3 + 0] }, hb, rfl, rfl⟩
      exact ⟨nd, hgetN, hkindN⟩
    rw [fires_observer_stage0_kind wp T specs i htickWp hobs hrep]
    rw [cascadeSpawn_obs T specs i hi]
  · -- stage event of chain i
    rcases hstage with ⟨i, hi, s, hs, rfl⟩
    have hnode : (stageEventOf T specs i s).nodeId =
        chainRepId specs i s := rfl
    rw [hnode]
    have hpri : (specAt specs i).priLenOk := (h_valid i hi).1
    have htickWp : wp.tick = stageTickOf T specs i s := by
      rw [World.popNextEvent_tick w (stageEventOf T specs i s) wp hpop,
        ← htickE]
      rfl
    by_cases hlt : s < (specAt specs i).middleDelays.length
    · -- middle stage
      have hrep : ∃ nd, wp.getNode (chainRepId specs i s) = some nd ∧
          nd.kind = NodeKind.repeater (stageDelayAt specs i s)
            (stagePriAt specs i s) ∧
          nd.outputs = [chainRepId specs i (s + 1)] := by
        have hb := buildChains_getNode_rep specs i s hi hpri (by omega)
        have houts : [chainBaseId specs i + 3 + s] =
            [chainRepId specs i (s + 1)] := by
          congr 1
          dsimp [chainRepId]
          omega
        rw [houts] at hb
        exact wiring_kind_exists wp (buildChains specs).1
          (chainRepId specs i s)
          (NodeKind.repeater (stageDelayAt specs i s)
            (stagePriAt specs i s)) [chainRepId specs i (s + 1)]
          (hwWp (chainRepId specs i s))
          ⟨{ kind := NodeKind.repeater (stageDelayAt specs i s) (stagePriAt specs i s), sigLevel := 0, inputs := [chainBaseId specs i + 1 + s], outputs := [chainRepId specs i (s + 1)] }, hb, rfl, rfl⟩
      have hnext : ∃ nd, wp.getNode (chainRepId specs i (s + 1)) =
          some nd ∧
        nd.kind = NodeKind.repeater (stageDelayAt specs i (s + 1))
          (stagePriAt specs i (s + 1)) := by
        have hb := buildChains_getNode_rep specs i (s + 1) hi hpri
          (by omega)
        obtain ⟨nd, hgetN, hkindN, _⟩ := wiring_kind_exists wp
          (buildChains specs).1 (chainRepId specs i (s + 1))
          (NodeKind.repeater (stageDelayAt specs i (s + 1))
            (stagePriAt specs i (s + 1)))
          [chainBaseId specs i + 3 + (s + 1)]
          (hwWp (chainRepId specs i (s + 1)))
          ⟨{ kind := NodeKind.repeater (stageDelayAt specs i (s + 1)) (stagePriAt specs i (s + 1)), sigLevel := 0, inputs := [chainBaseId specs i + 1 + (s + 1)], outputs := [chainBaseId specs i + 3 + (s + 1)] }, hb, rfl, rfl⟩
        exact ⟨nd, hgetN, hkindN⟩
      rw [fires_rep_stage_kind wp T specs i s (by omega) htickWp hrep
        hnext]
      rw [cascadeSpawn_stage T specs h_valid i s hi hlt]
    · -- last repeater
      have heqLen : s = (specAt specs i).middleDelays.length := by omega
      subst heqLen
      have hrep : ∃ nd, wp.getNode
          (chainRepId specs i (repLenAt specs i)) = some nd ∧
        nd.kind = NodeKind.repeater
          (stageDelayAt specs i (repLenAt specs i))
          (stagePriAt specs i (repLenAt specs i)) ∧
        nd.outputs = [chainOutputId specs i] := by
        have hb := buildChains_getNode_rep specs i (repLenAt specs i) hi
          hpri (by dsimp [repLenAt]; omega)
        obtain ⟨nd, hgetN, hkindN, houtsN⟩ := wiring_kind_exists wp
          (buildChains specs).1 (chainRepId specs i (repLenAt specs i))
          (NodeKind.repeater (stageDelayAt specs i (repLenAt specs i))
            (stagePriAt specs i (repLenAt specs i)))
          [chainBaseId specs i + 3 + repLenAt specs i]
          (hwWp (chainRepId specs i (repLenAt specs i)))
          ⟨{ kind := NodeKind.repeater (stageDelayAt specs i (repLenAt specs i)) (stagePriAt specs i (repLenAt specs i)), sigLevel := 0, inputs := [chainBaseId specs i + 1 + repLenAt specs i], outputs := [chainBaseId specs i + 3 + repLenAt specs i] }, hb, rfl, rfl⟩
        exact ⟨nd, hgetN, hkindN, by rw [houtsN]; dsimp [chainOutputId]⟩
      have hout : ∃ nd, wp.getNode (chainOutputId specs i) = some nd ∧
          nd.kind = NodeKind.output (chainName i) := by
        have hb := buildChains_getNode_output' specs i hi hpri
        obtain ⟨nd, hgetN, hkindN, _⟩ := wiring_kind_exists wp
          (buildChains specs).1 (chainOutputId specs i)
          (NodeKind.output (chainName i)) []
          (hwWp (chainOutputId specs i))
          ⟨{ kind := NodeKind.output (chainName i), sigLevel := 0, inputs := [chainBaseId specs i + 2 + repLenAt specs i], outputs := [] }, hb, rfl, rfl⟩
        exact ⟨nd, hgetN, hkindN⟩
      change (wp.onScheduledTick
          (chainRepId specs i (repLenAt specs i))).events =
        wp.events ++ cascadeSpawn T specs
          (stageEventOf T specs i (repLenAt specs i))
      rw [fires_lastRep_events_kind wp specs i hrep hout]
      rw [cascadeSpawn_lastRep T specs h_valid i hi]
      rw [List.append_nil]

