import Proofs.Model.CascadeSpawn

open BasicRedstoneSim
open World
open List

/-! # Membership accounting, event history and cascade spawn shape. -/

/-! ## Membership accounting across pops and drains -/

/-- Every event in a cascade spawn is itself a cascade event. -/
theorem cascadeSpawn_mem_good (T : Nat) (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (e f : ScheduledEvent) (hf : f ∈ cascadeSpawn T specs e)
    (hcl : IsCascadeEv T specs e) : IsCascadeEv T specs f := by
  rcases hcl with ⟨i, hi, heq⟩ | hstage
  · subst heq
    rw [cascadeSpawn_obs T specs i hi] at hf
    rcases List.mem_singleton.mp hf with rfl
    exact Or.inr ⟨i, hi, 0, by omega, rfl⟩
  · rcases hstage with ⟨i, hi, s, hs, heq⟩
    subst heq
    by_cases hlt : s < (specAt specs i).middleDelays.length
    · rw [cascadeSpawn_stage T specs h_valid i s hi hlt] at hf
      rcases List.mem_singleton.mp hf with rfl
      exact Or.inr ⟨i, hi, s + 1, by omega, rfl⟩
    · have heqLen : s = (specAt specs i).middleDelays.length := by
        omega
      subst heqLen
      change f ∈ cascadeSpawn T specs
        (stageEventOf T specs i (repLenAt specs i)) at hf
      rw [cascadeSpawn_lastRep T specs h_valid i hi] at hf
      cases hf

/-- `processNEvents` keeps events or appends cascade spawns of events
    due at the starting tick. -/
private theorem processNEvents_mem_spawn (T : Nat)
    (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (w : World) (n : Nat) (e : ScheduledEvent)
    (hgood : CascadeGood T specs w)
    (hwiring : ∀ id, (w.getNode id).map wiring =
      ((buildChains specs).1.getNode id).map wiring) :
    e ∈ (processNEvents w n).events →
    e ∈ w.events ∨
    ∃ x, e ∈ cascadeSpawn T specs x ∧ x.targetTick = w.tick := by
  induction n generalizing w with
  | zero =>
    dsimp [processNEvents]
    intro he
    exact Or.inl he
  | succ n ih =>
    dsimp [processNEvents]
    cases hstep : w.step with
    | none =>
      intro he
      exact Or.inl he
    | some w' =>
      intro he
      dsimp [World.step] at hstep
      cases hpop : w.popNextEvent with
      | none => simp [hpop] at hstep
      | some pr =>
        rcases pr with ⟨e0, wp⟩
        have hw' : w' = wp.onScheduledTick e0.nodeId := by
          apply Eq.symm
          simpa [World.step, hpop] using hstep
        obtain ⟨idx, hidx, herase, htickE, hget⟩ :=
          popNextEvent_eraseIdx w e0 wp hpop
        have hgoodWp : CascadeGood T specs wp := by
          intro f hf
          rw [herase] at hf
          exact hgood f (List.mem_of_mem_eraseIdx hf)
        have hwiringWp : ∀ id, (wp.getNode id).map wiring =
            ((buildChains specs).1.getNode id).map wiring := by
          intro id
          rw [World.getNode_of_nodes_eq wp w
            (popNextEvent_nodes w e0 wp hpop) id, hwiring]
        have hgoodW' : CascadeGood T specs w' := by
          rw [hw']
          dsimp [CascadeGood]
          rw [firing_cascadeSpawn_eq T specs h_valid w e0 wp hpop
            hgood hwiring]
          intro f hf
          rcases List.mem_append.mp hf with hf | hf
          · exact hgoodWp f hf
          · exact cascadeSpawn_mem_good T specs h_valid e0 f hf
              (hgood e0 (by rw [← hget]; exact List.getElem_mem hidx))
        have hwiringW' : ∀ id, (w'.getNode id).map wiring =
            ((buildChains specs).1.getNode id).map wiring := by
          intro id
          rw [hw', onScheduledTick_getNode_wiring,
            World.getNode_of_nodes_eq wp w
              (popNextEvent_nodes w e0 wp hpop) id, hwiring]
        have hsplit := ih w' hgoodW' hwiringW' he
        rcases hsplit with hkeep | ⟨x, hxs, hxt⟩
        · rw [hw'] at hkeep
          rw [firing_cascadeSpawn_eq T specs h_valid w e0 wp hpop
            hgood hwiring] at hkeep
          rcases List.mem_append.mp hkeep with hkeep | hspawn
          · rw [herase] at hkeep
            exact Or.inl (List.mem_of_mem_eraseIdx hkeep)
          · exact Or.inr ⟨e0, hspawn, htickE⟩
        · exact Or.inr ⟨x, hxs, by
            rw [hxt, hw', World.onScheduledTick_tick,
              World.popNextEvent_tick w e0 wp hpop]⟩

/-- The drain keeps events or appends cascade spawns of popped
    events. -/
theorem stepUNT_mem_split (T : Nat) (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (w : World) (hgood : CascadeGood T specs w)
    (hwiring : ∀ id, (w.getNode id).map wiring =
      ((buildChains specs).1.getNode id).map wiring)
    (e : ScheduledEvent) :
    e ∈ w.stepUntilNextTick.events →
    e ∈ w.events ∨
    ∃ x ∈ popSeq w, e ∈ cascadeSpawn T specs x := by
  induction w using World.stepUntilNextTick.induct with
  | case1 x hstep =>
    rw [stepUntilNextTick_of_step_none x hstep]
    intro he
    exact Or.inl he
  | case2 x w' hstep ih =>
    have hsunt : x.stepUntilNextTick = w'.stepUntilNextTick := by
      rw [World.stepUntilNextTick, hstep]
    dsimp [World.step] at hstep
    cases hpop : x.popNextEvent with
    | none => simp [hpop] at hstep
    | some pr =>
      rcases pr with ⟨e0, wp⟩
      have hw' : w' = wp.onScheduledTick e0.nodeId := by
        apply Eq.symm
        simpa [World.step, hpop] using hstep
      obtain ⟨idx, hidx, herase, htickE, hget⟩ :=
        popNextEvent_eraseIdx x e0 wp hpop
      have hpopSeq : popSeq x = e0 :: popSeq w' := by
        rw [popSeq_of_popNextEvent_some x e0 wp hpop, ← hw']
      have hgoodWp : CascadeGood T specs wp := by
        intro f hf
        rw [herase] at hf
        exact hgood f (List.mem_of_mem_eraseIdx hf)
      have hwiringWp : ∀ id, (wp.getNode id).map wiring =
          ((buildChains specs).1.getNode id).map wiring := by
        intro id
        rw [World.getNode_of_nodes_eq wp x
          (popNextEvent_nodes x e0 wp hpop) id, hwiring]
      have hgoodW' : CascadeGood T specs w' := by
        rw [hw']
        dsimp [CascadeGood]
        rw [firing_cascadeSpawn_eq T specs h_valid x e0 wp hpop
          hgood hwiring]
        intro f hf
        rcases List.mem_append.mp hf with hf | hf
        · exact hgoodWp f hf
        · exact cascadeSpawn_mem_good T specs h_valid e0 f hf
            (hgood e0 (by rw [← hget]; exact List.getElem_mem hidx))
      have hwiringW' : ∀ id, (w'.getNode id).map wiring =
          ((buildChains specs).1.getNode id).map wiring := by
        intro id
        rw [hw', onScheduledTick_getNode_wiring,
          World.getNode_of_nodes_eq wp x
            (popNextEvent_nodes x e0 wp hpop) id, hwiring]
      intro he
      rw [hsunt] at he
      have hsplit := ih hgoodW' hwiringW' he
      rcases hsplit with hkeep | ⟨y, hy, hys⟩
      · rw [hw'] at hkeep
        rw [firing_cascadeSpawn_eq T specs h_valid x e0 wp hpop
          hgood hwiring] at hkeep
        rcases List.mem_append.mp hkeep with hkeep | hspawn
        · rw [herase] at hkeep
          exact Or.inl (List.mem_of_mem_eraseIdx hkeep)
        · exact Or.inr ⟨e0, by
            rw [hpopSeq]
            exact List.mem_cons.mpr (Or.inl rfl), hspawn⟩
      · exact Or.inr ⟨y, by
          rw [hpopSeq]
          exact List.mem_cons.mpr (Or.inr hy), hys⟩

private theorem simBurst_cons_split (t : Nat) (observers : List Nat)
    (pos : Nat → Nat → Nat) (w : World) (i k : Nat)
    (ps : List (Nat × Nat)) :
    simBurst t observers pos w ((i, k) :: ps) =
      match observers[i]? with
      | some oid => simBurst t observers pos
          (activateChain (processNEvents w (pos t k)) oid) ps
      | none => simBurst t observers pos
          (processNEvents w (pos t k)) ps := by
  cases hobs : observers[i]? with
  | none =>
    dsimp [simBurst]
    rw [hobs]
  | some oid =>
    dsimp [simBurst]
    rw [hobs]

/-- The burst keeps events, appends activations, or appends cascade
    spawns of events due at the burst tick. -/
theorem simBurst_mem_split (T : Nat) (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (t : Nat) (observers : List Nat) (pos : Nat → Nat → Nat)
    (w : World) (pairs : List (Nat × Nat))
    (hgood : CascadeGood T specs w)
    (hwiring : ∀ id, (w.getNode id).map wiring =
      ((buildChains specs).1.getNode id).map wiring)
    (htick : w.tick = t)
    (hact : ∀ p ∈ pairs, ∀ oid, observers[p.1]? = some oid →
      IsCascadeEv T specs (obsActEvt t oid))
    (e : ScheduledEvent) :
    e ∈ (simBurst t observers pos w pairs).events →
    e ∈ w.events ∨
    e ∈ obsActEvts t observers pairs ∨
    ∃ x, e ∈ cascadeSpawn T specs x ∧ x.targetTick = t := by
  induction pairs generalizing w with
  | nil =>
    dsimp [simBurst]
    intro he
    exact Or.inl he
  | cons p ps ih =>
    rcases p with ⟨i, k⟩
    rw [simBurst_cons_split]
    cases hobs : observers[i]? with
    | none =>
      dsimp
      intro he
      have hgoodP : CascadeGood T specs (processNEvents w (pos t k)) :=
        processNEvents_good T specs h_valid w (pos t k) hgood hwiring
      have hwiringP : ∀ id,
          ((processNEvents w (pos t k)).getNode id).map wiring =
            ((buildChains specs).1.getNode id).map wiring := by
        intro id
        rw [processNEvents_getNode_wiring w (pos t k) id, hwiring]
      have htickP : (processNEvents w (pos t k)).tick = t := by
        rw [processNEvents_tick, htick]
      have hsplit := ih (processNEvents w (pos t k)) hgoodP hwiringP
        htickP
        (fun q hq oid' hget =>
          hact q (List.mem_cons.mpr (Or.inr hq)) oid' hget) he
      rcases hsplit with hkeep | hacts | ⟨x, hxs, hxt⟩
      · rcases processNEvents_mem_spawn T specs h_valid w (pos t k) e
          hgood hwiring hkeep with hkeep | ⟨x, hxs, hxt'⟩
        · exact Or.inl hkeep
        · exact Or.inr (Or.inr ⟨x, hxs, by rw [hxt', htick]⟩)
      · exact Or.inr (Or.inl (by
          have hskip : obsActEvts t observers ((i, k) :: ps) =
              obsActEvts t observers ps := by
            dsimp [obsActEvts, List.filterMap]
            rw [hobs]
            dsimp
          rw [hskip]
          exact hacts))
      · exact Or.inr (Or.inr ⟨x, hxs, hxt⟩)
    | some oid =>
      dsimp
      intro he
      have hgoodP : CascadeGood T specs (processNEvents w (pos t k)) :=
        processNEvents_good T specs h_valid w (pos t k) hgood hwiring
      have hwiringP : ∀ id,
          ((processNEvents w (pos t k)).getNode id).map wiring =
            ((buildChains specs).1.getNode id).map wiring := by
        intro id
        rw [processNEvents_getNode_wiring w (pos t k) id, hwiring]
      have htickP : (processNEvents w (pos t k)).tick = t := by
        rw [processNEvents_tick, htick]
      have hgoodA : CascadeGood T specs
          (activateChain (processNEvents w (pos t k)) oid) := by
        dsimp [CascadeGood]
        intro f hf
        rw [activateChain, World.scheduleEvent_events] at hf
        rcases List.mem_append.mp hf with hf | hf
        · exact hgoodP f hf
        · rcases List.mem_singleton.mp hf with rfl
          have hevt : { targetTick := (processNEvents w (pos t k)).tick + 2, priority := 0, nodeId := oid } = obsActEvt t oid := by
            dsimp [obsActEvt]
            congr 1
            rw [processNEvents_tick, htick]
          rw [hevt]
          exact hact (i, k) (List.mem_cons.mpr (Or.inl rfl)) oid hobs
      have hwiringA : ∀ id,
          ((activateChain (processNEvents w (pos t k)) oid).getNode
            id).map wiring =
            ((buildChains specs).1.getNode id).map wiring := by
        intro id
        rw [activateChain_getNode_wiring, hwiringP]
      have htickA :
          (activateChain (processNEvents w (pos t k)) oid).tick = t := by
        rw [activateChain_tick, processNEvents_tick, htick]
      have hsplit := ih
        (activateChain (processNEvents w (pos t k)) oid) hgoodA
        hwiringA htickA
        (fun q hq oid' hget =>
          hact q (List.mem_cons.mpr (Or.inr hq)) oid' hget) he
      rcases hsplit with hkeep | hacts | ⟨x, hxs, hxt⟩
      · rw [activateChain, World.scheduleEvent_events] at hkeep
        rcases List.mem_append.mp hkeep with hkeep | hspawn
        · rcases processNEvents_mem_spawn T specs h_valid w (pos t k)
            e hgood hwiring hkeep with hkeep | ⟨x, hxs, hxt'⟩
          · exact Or.inl hkeep
          · exact Or.inr (Or.inr ⟨x, hxs, by rw [hxt', htick]⟩)
        · rcases List.mem_singleton.mp hspawn with rfl
          have hevt : { targetTick := (processNEvents w (pos t k)).tick + 2, priority := 0, nodeId := oid } = obsActEvt t oid := by
            dsimp [obsActEvt]
            congr 1
            rw [processNEvents_tick, htick]
          rw [hevt]
          apply Or.inr
          apply Or.inl
          dsimp [obsActEvts, List.filterMap]
          rw [hobs]
          dsimp
          exact List.mem_cons.mpr (Or.inl rfl)
      · apply Or.inr
        apply Or.inl
        dsimp [obsActEvts, List.filterMap]
        rw [hobs]
        dsimp
        exact List.mem_cons.mpr (Or.inr hacts)
      · exact Or.inr (Or.inr ⟨x, hxs, hxt⟩)

/-- Burst activations of valid chains are observer events of those
    chains. -/
theorem burst_activation_cascade (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (h_perm : actOrd.Perm (List.range specs.length))
    (t : Nat) (p : Nat × Nat)
    (hp : p ∈ (actOrd.filter (fun i =>
      decide (i < (buildChains specs).2.length) &&
        (actTickOf T specs i == t))).zipIdx)
    (oid : Nat)
    (hget : (buildChains specs).2[p.1]? = some oid) :
    IsCascadeEv T specs (obsActEvt t oid) := by
  obtain ⟨k, hkPos, hpk⟩ := List.exists_mem_zipIdx'.mp ⟨p, hp, rfl⟩
  have hp1 : p.1 = (actOrd.filter (fun i =>
      decide (i < (buildChains specs).2.length) &&
        (actTickOf T specs i == t)))[k]'hkPos :=
    congrArg Prod.fst hpk
  have hmemF := List.getElem_mem hkPos
  rw [List.mem_filter] at hmemF
  obtain ⟨hiOrd, hcond⟩ := hmemF
  rw [Bool.and_eq_true] at hcond
  have hlt : (actOrd.filter (fun i =>
      decide (i < (buildChains specs).2.length) &&
        (actTickOf T specs i == t)))[k]'hkPos <
      (buildChains specs).2.length := by
    rw [decide_eq_true_eq] at hcond
    exact hcond.1
  have htick : actTickOf T specs (p.1) = t := by
    rw [hp1]
    exact Nat.eq_of_beq_eq_true (by simpa using hcond.2)
  have hiSpec : p.1 < specs.length := by
    rw [hp1]
    exact List.mem_range.mp ((List.Perm.mem_iff h_perm).mp hiOrd)
  have hp1' : p.1 < (buildChains specs).2.length := by
    rw [hp1]
    exact hlt
  rw [List.getElem?_eq_getElem hp1'] at hget
  have hoid := Option.some.inj hget
  rw [observers_getElem_eq_chainObserverId specs p.1 hp1'] at hoid
  apply Or.inl
  refine ⟨p.1, hiSpec, ?_⟩
  dsimp [obsActEvt, obsEventOf, obsTickOf]
  rw [← hoid, htick]

/-- Events one tick later survive from before, arrive as activations,
    or are cascade spawns of events due at that tick. -/
theorem simWorld_succ_mem_split (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length)) (t : Nat)
    (e : ScheduledEvent) :
    e ∈ (simWorld T specs actOrd pos (t + 1)).events →
    e ∈ (simWorld T specs actOrd pos t).events ∨
    e ∈ obsActEvts t (buildChains specs).2
      ((actOrd.filter (fun i =>
        decide (i < (buildChains specs).2.length) &&
          (actTickOf T specs i == t))).zipIdx) ∨
    ∃ x, e ∈ cascadeSpawn T specs x ∧ x.targetTick = t := by
  rw [simWorld_succ]
  set wT := simWorld T specs actOrd pos t
  dsimp only [simBody]
  set wLog := wT.logOutput s!"tick {wT.tick}"
  have htickLog : wLog.tick = t := by
    dsimp only [wLog, wT]
    rw [World.logOutput_tick, simWorld_tick]
  rw [htickLog]
  set F := actOrd.filter (fun i =>
    decide (i < (buildChains specs).2.length) &&
      (actTickOf T specs i == t))
  intro he
  have hgoodLog : CascadeGood T specs wLog := by
    dsimp only [wLog, World.logOutput]
    exact simWorld_classification T specs actOrd pos h_valid h_perm t
  have hwiringLog : ∀ id, (wLog.getNode id).map wiring =
      ((buildChains specs).1.getNode id).map wiring := by
    intro id
    dsimp only [wLog, wT, World.logOutput, World.getNode]
    exact simWorld_getNode_wiring T specs actOrd pos t id
  have hactF : ∀ p ∈ F.zipIdx, ∀ oid,
      (buildChains specs).2[p.1]? = some oid →
      IsCascadeEv T specs (obsActEvt t oid) :=
    fun p hp oid hget =>
      burst_activation_cascade T specs actOrd h_perm t p hp oid hget
  have hgoodB : CascadeGood T specs
      (simBurst t (buildChains specs).2 pos wLog (F.zipIdx)) :=
    simBurst_good T specs h_valid t (buildChains specs).2 pos wLog
      (F.zipIdx) hgoodLog hwiringLog htickLog hactF
  have hwiringB : ∀ id,
      ((simBurst t (buildChains specs).2 pos wLog (F.zipIdx)).getNode
        id).map wiring =
      ((buildChains specs).1.getNode id).map wiring := by
    intro id
    rw [simBurst_getNode_wiring, hwiringLog]
  have hsplit := stepUNT_mem_split T specs h_valid
    (simBurst t (buildChains specs).2 pos wLog (F.zipIdx)) hgoodB
    hwiringB e he
  rcases hsplit with hkeep | ⟨x, hxpop, hxs⟩
  · have hbsplit := simBurst_mem_split T specs h_valid t
      (buildChains specs).2 pos wLog (F.zipIdx) hgoodLog hwiringLog
      htickLog hactF e hkeep
    rcases hbsplit with hlog | hacts | ⟨y, hys, hyt⟩
    · exact Or.inl (by
        dsimp only [wLog, World.logOutput] at hlog
        exact hlog)
    · exact Or.inr (Or.inl hacts)
    · exact Or.inr (Or.inr ⟨y, hys, hyt⟩)
  · have hdue := popSeq_mem_due
      (simBurst t (buildChains specs).2 pos wLog (F.zipIdx)) x hxpop
    exact Or.inr (Or.inr ⟨x, hxs, by
      rw [hdue.1, simBurst_tick, htickLog]⟩)

/-! ## Event history and nodup arithmetic -/

/-- Valid priorities are nonzero. -/
theorem ValidPriority_ne_zero {p : Int} (h : ValidPriority p) :
    p ≠ 0 := by
  rcases h with rfl | rfl | rfl <;> omega

/-- Queued cascade events were appended strictly before the tick:
    observers after their chain's activation, stage events after their
    predecessor fired. -/
def EventHistory (T : Nat) (specs : List ChainSpec) (t : Nat)
    (e : ScheduledEvent) : Prop :=
  (∀ i < specs.length, e = obsEventOf T specs i →
    actTickOf T specs i < t) ∧
  (∀ i < specs.length, e = stageEventOf T specs i 0 →
    obsTickOf T specs i < t) ∧
  ∀ i < specs.length, ∀ s, s ≤ repLenAt specs i →
    e = stageEventOf T specs i (s + 1) →
    stageTickOf T specs i s < t

/-- Observer events determine the chain. -/
theorem obsEventOf_inj (T : Nat) (specs : List ChainSpec) (i j : Nat)
    (hi : i < specs.length) (hj : j < specs.length)
    (h : obsEventOf T specs i = obsEventOf T specs j) : i = j := by
  have hnode := congrArg (fun ev => ev.nodeId) h
  dsimp [obsEventOf, chainObserverId] at hnode
  by_cases hij : i < j
  · exfalso
    have := chainBaseId_lt_chainBaseId specs i j hi hj hij
    omega
  · by_cases hji : j < i
    · exfalso
      have := chainBaseId_lt_chainBaseId specs j i hj hi hji
      omega
    · omega

/-- Stage events determine the chain and the stage. -/
theorem stageEventOf_inj (T : Nat) (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (i j s u : Nat)
    (hi : i < specs.length) (hj : j < specs.length)
    (hs : s ≤ repLenAt specs i) (hu : u ≤ repLenAt specs j)
    (h : stageEventOf T specs i s = stageEventOf T specs j u) :
    i = j ∧ s = u := by
  have hnode := congrArg (fun ev => ev.nodeId) h
  dsimp [stageEventOf, chainRepId] at hnode
  exact chainRepId_inj specs i j s u hi hj hs hu
    (h_valid i hi).1 (h_valid j hj).1 hnode

/-- An observer event is never a stage event. -/
theorem obsEventOf_ne_stageEventOf (T : Nat) (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (i j s : Nat)
    (hi : i < specs.length) (hj : j < specs.length)
    (hs : s ≤ repLenAt specs j) :
    obsEventOf T specs i ≠ stageEventOf T specs j s := by
  intro h
  have hnode := congrArg (fun ev => ev.nodeId) h
  dsimp [obsEventOf, stageEventOf, chainObserverId, chainRepId] at hnode
  by_cases hij : i < j
  · have hsucc := chainBaseId_succ specs i hi
    have hmono : chainBaseId specs (i + 1) ≤ chainBaseId specs j :=
      chainBaseId_mono specs (i + 1) j (by omega)
    have hcnt : 2 ≤ chainNodeCount (specAt specs i) := by
      dsimp [chainNodeCount]
      omega
    omega
  · by_cases hji : j < i
    · have hsucc := chainBaseId_succ specs j hj
      have hmono : chainBaseId specs (j + 1) ≤ chainBaseId specs i :=
        chainBaseId_mono specs (j + 1) i (by omega)
      have hpri : (specAt specs j).priLenOk := (h_valid j hj).1
      have hzip : ((specAt specs j).middleDelays.zip
          (specAt specs j).middlePriorities).length =
          (specAt specs j).middleDelays.length := by
        dsimp [ChainSpec.priLenOk] at hpri
        rw [List.length_zip, hpri, min_self]
      have hbound : chainBaseId specs j + 2 + s <
          chainBaseId specs j + chainNodeCount (specAt specs j) := by
        dsimp [chainNodeCount, repLenAt] at hs ⊢
        rw [hzip]
        omega
      omega
    · have heq : i = j := by omega
      subst heq
      omega

/-! ## Cascade spawn shape, injectivity, timing -/

/-- Every stage delay of a valid spec is a valid delay. -/
theorem stageDelayAt_valid (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (i s : Nat) (hi : i < specs.length) :
    ValidDelay (stageDelayAt specs i s) := by
  dsimp [stageDelayAt]
  by_cases hget : s < (specAt specs i).middleDelays.length
  · rw [List.getElem?_eq_getElem hget]
    exact (h_valid i hi).2.1 _ (List.getElem_mem hget)
  · rw [List.getElem?_eq_none (by omega)]
    exact (h_valid i hi).2.2.1

/-- Membership in a cascade spawn determines the fired event's
    shape. -/
theorem cascadeSpawn_shape (T : Nat) (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (x e : ScheduledEvent) (he : e ∈ cascadeSpawn T specs x)
    (hcl : IsCascadeEv T specs x) :
    (∃ i < specs.length, x = obsEventOf T specs i ∧
      e = stageEventOf T specs i 0) ∨
    ∃ (i : Nat) (_ : i < specs.length) (s : Nat),
      s < repLenAt specs i ∧
      x = stageEventOf T specs i s ∧
      e = stageEventOf T specs i (s + 1) := by
  rcases hcl with ⟨i, hi, hx⟩ | hstage
  · subst hx
    rw [cascadeSpawn_obs T specs i hi] at he
    rcases List.mem_singleton.mp he with rfl
    exact Or.inl ⟨i, hi, rfl, rfl⟩
  · rcases hstage with ⟨i, hi, s, hs, hx⟩
    subst hx
    by_cases hlt : s < (specAt specs i).middleDelays.length
    · rw [cascadeSpawn_stage T specs h_valid i s hi hlt] at he
      rcases List.mem_singleton.mp he with rfl
      exact Or.inr ⟨i, hi, s, by dsimp [repLenAt]; omega, rfl, rfl⟩
    · have heqLen : s = (specAt specs i).middleDelays.length := by
        omega
      subst heqLen
      change e ∈ cascadeSpawn T specs
        (stageEventOf T specs i (repLenAt specs i)) at he
      rw [cascadeSpawn_lastRep T specs h_valid i hi] at he
      cases he

/-- The cascade spawn determines the fired event. -/
theorem cascadeSpawn_inj (T : Nat) (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (x y e : ScheduledEvent)
    (hx : e ∈ cascadeSpawn T specs x)
    (hy : e ∈ cascadeSpawn T specs y)
    (hcx : IsCascadeEv T specs x) (hcy : IsCascadeEv T specs y) :
    x = y := by
  rcases cascadeSpawn_shape T specs h_valid x e hx hcx with
      ⟨i, hi, hxobs, he1⟩ | ⟨i, hi, s, hs, hxst, he1⟩
  · rcases cascadeSpawn_shape T specs h_valid y e hy hcy with
        ⟨j, hj, hyobs, he2⟩ | ⟨j, hj, u, hu, hyp, he2⟩
    · have hij := (stageEventOf_inj T specs h_valid i j 0 0 hi hj
        (by omega) (by omega) (he1.symm.trans he2)).1
      subst hij
      rw [hxobs, hyobs]
    · have hsu := (stageEventOf_inj T specs h_valid i j 0 (u + 1) hi hj
        (by omega) (by omega) (he1.symm.trans he2)).2
      omega
  · rcases cascadeSpawn_shape T specs h_valid y e hy hcy with
        ⟨j, hj, hyobs, he2⟩ | ⟨j, hj, u, hu, hyp, he2⟩
    · exfalso
      have hsu := (stageEventOf_inj T specs h_valid i j (s + 1) 0
        hi hj (by omega) (by omega) (he1.symm.trans he2)).2
      omega
    · have hpair := stageEventOf_inj T specs h_valid i j (s + 1) (u + 1)
        hi hj (by omega) (by omega) (he1.symm.trans he2)
      have hseq : s = u := by omega
      rw [hxst, hyp, hpair.1, hseq]

/-- A cascade spawn targets a strictly later tick than the fired
    event. -/
theorem cascadeSpawn_target_gt (T : Nat) (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (x e : ScheduledEvent) (t : Nat)
    (he : e ∈ cascadeSpawn T specs x) (hcl : IsCascadeEv T specs x)
    (htick : x.targetTick = t) : e.targetTick > t := by
  rcases cascadeSpawn_shape T specs h_valid x e he hcl with
      ⟨i, hi, hxobs, heq⟩ | ⟨i, hi, s, hs, hxst, heq⟩
  · rw [hxobs] at htick
    dsimp [obsEventOf, obsTickOf] at htick
    rw [heq]
    dsimp [stageEventOf]
    have h0 : stageTickOf T specs i 0 =
        obsTickOf T specs i + (stageDelayAt specs i 0 : Nat) := by
      rw [stageTickOf_zero]
      dsimp [obsTickOf]
    rw [h0]
    dsimp [obsTickOf]
    rw [htick]
    have hd : 2 ≤ (stageDelayAt specs i 0 : Nat) :=
      ValidDelay.ge2 (stageDelayAt_valid specs h_valid i 0 hi)
    omega
  · rw [hxst] at htick
    dsimp [stageEventOf] at htick
    rw [heq]
    dsimp [stageEventOf]
    rw [stageTickOf_succ T specs i s (by dsimp [repLenAt] at hs; omega)]
    rw [htick]
    have hd : 2 ≤ (stageDelayAt specs i (s + 1) : Nat) :=
      ValidDelay.ge2 (stageDelayAt_valid specs h_valid i (s + 1) hi)
    omega

