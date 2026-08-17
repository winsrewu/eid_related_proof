import Proofs.Model.StageDescent

open BasicRedstoneSim
open World
open List

/-! # Event classification and its preservation through the loop. -/

/-! ## Instantiating the obligations in tick-start worlds -/

/-- A stage repeater's wiring with the successor expressed as a
    `chainRepId`. -/
theorem simWorld_rep_wiring_succ (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat) (t i s : Nat)
    (hi : i < specs.length) (hpri : (specAt specs i).priLenOk)
    (hs : s + 1 ≤ (specAt specs i).middleDelays.length) :
    ∃ nd, (simWorld T specs actOrd pos t).getNode (chainRepId specs i s) =
        some nd ∧
      nd.kind = NodeKind.repeater (stageDelayAt specs i s)
        (stagePriAt specs i s) ∧
      nd.outputs = [chainRepId specs i (s + 1)] := by
  obtain ⟨nd, hget, hkind, hout⟩ :=
    simWorld_rep_wiring T specs actOrd pos t i s hi hpri (by omega)
  refine ⟨nd, hget, hkind, ?_⟩
  rw [hout]
  congr 1
  dsimp [chainRepId]
  omega

/-- The last repeater's wiring with the output node id. -/
theorem simWorld_lastRep_wiring (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat) (t i : Nat)
    (hi : i < specs.length) (hpri : (specAt specs i).priLenOk) :
    ∃ nd, (simWorld T specs actOrd pos t).getNode
        (chainRepId specs i (repLenAt specs i)) = some nd ∧
      nd.kind = NodeKind.repeater (stageDelayAt specs i (repLenAt specs i))
        (stagePriAt specs i (repLenAt specs i)) ∧
      nd.outputs = [chainOutputId specs i] := by
  obtain ⟨nd, hget, hkind, hout⟩ := simWorld_rep_wiring T specs actOrd
    pos t i (repLenAt specs i) hi hpri (by dsimp [repLenAt]; omega)
  refine ⟨nd, hget, hkind, ?_⟩
  rw [hout]
  dsimp [chainOutputId]

/-- The output node keeps its kind in every tick-start world. -/
theorem simWorld_output_kind (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat) (t i : Nat)
    (hi : i < specs.length) (hpri : (specAt specs i).priLenOk) :
    ∃ nd, (simWorld T specs actOrd pos t).getNode (chainOutputId specs i) =
        some nd ∧
      nd.kind = NodeKind.output (chainName i) := by
  have hw := simWorld_getNode_wiring T specs actOrd pos t
    (chainOutputId specs i)
  rw [buildChains_getNode_output' specs i hi hpri] at hw
  dsimp [wiring] at hw
  cases hget : (simWorld T specs actOrd pos t).getNode
      (chainOutputId specs i) with
  | none =>
    rw [hget] at hw
    dsimp [Option.map] at hw
    cases hw
  | some nd =>
    rw [hget] at hw
    dsimp [Option.map] at hw
    injection hw with htriple
    dsimp [wiring] at htriple
    exact ⟨nd, rfl, congrArg Prod.fst htriple⟩

/-- The observer of chain `i` keeps its kind and output wiring in every
    tick-start world. -/
theorem simWorld_observer_wiring (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat) (t i : Nat)
    (hi : i < specs.length) :
    ∃ nd, (simWorld T specs actOrd pos t).getNode
        (chainObserverId specs i) = some nd ∧
      nd.kind = NodeKind.observer ∧
      nd.outputs = [chainRepId specs i 0] := by
  have hw := simWorld_getNode_wiring T specs actOrd pos t
    (chainObserverId specs i)
  rw [buildChains_getNode_observer' specs i hi] at hw
  dsimp [wiring] at hw
  cases hget : (simWorld T specs actOrd pos t).getNode
      (chainObserverId specs i) with
  | none =>
    rw [hget] at hw
    dsimp [Option.map] at hw
    cases hw
  | some nd =>
    rw [hget] at hw
    dsimp [Option.map] at hw
    injection hw with htriple
    dsimp [wiring] at htriple
    have hkind := congrArg Prod.fst htriple
    have hout : nd.outputs = [chainRepId specs i 0] := by
      have := congrArg Prod.snd htriple
      rw [Prod.mk.injEq] at this
      rw [this.2]
      dsimp [chainRepId]
    exact ⟨nd, rfl, hkind, hout⟩

/-! ## Event classification

Every event ever queued during the simulation is either a chain's observer
event or one of its repeater-stage events. The induction walks
`processNEvents` / the drain / bursts / ticks: each pop fires a node whose
spawn is again a cascade event (the same chain, one stage further down). -/

/-- An event is a cascade event when it is a chain's observer event or a
    chain's stage-`s` event. -/
def IsCascadeEv (T : Nat) (specs : List ChainSpec)
    (e : ScheduledEvent) : Prop :=
  (∃ i < specs.length, e = obsEventOf T specs i) ∨
  ∃ (i : Nat) (_ : i < specs.length) (s : Nat),
    s ≤ (specAt specs i).middleDelays.length ∧
      e = stageEventOf T specs i s

/-- A world's queue consists only of cascade events. -/
def CascadeGood (T : Nat) (specs : List ChainSpec) (w : World) : Prop :=
  ∀ e ∈ w.events, IsCascadeEv T specs e

/-- Left cancellation of append. -/
private theorem append_left_cancel {α : Type} (l a b : List α)
    (h : l ++ a = l ++ b) : a = b := by
  induction l generalizing a b with
  | nil => simpa using h
  | cons x xs ih =>
    injection h with _ hrest
    exact ih a b hrest

/-- Matching wiring transfers a kind-and-outputs lookup between
    worlds. -/
theorem wiring_kind_exists (v w : World) (id : Nat)
    (K : NodeKind) (O : List Nat)
    (hwv : (v.getNode id).map wiring = (w.getNode id).map wiring)
    (hbuild : ∃ nd, w.getNode id = some nd ∧ nd.kind = K ∧
      nd.outputs = O) :
    ∃ nd, v.getNode id = some nd ∧ nd.kind = K ∧ nd.outputs = O := by
  obtain ⟨nd, hget, hkind, houts⟩ := hbuild
  cases hgetV : v.getNode id with
  | none =>
    rw [hgetV, hget] at hwv
    dsimp [Option.map] at hwv
    cases hwv
  | some nd' =>
    rw [hgetV, hget] at hwv
    dsimp [Option.map] at hwv
    injection hwv with htriple
    dsimp [wiring] at htriple
    refine ⟨nd', rfl, ?_, ?_⟩
    · rw [← hkind]
      exact congrArg Prod.fst htriple
    · rw [← houts]
      have := congrArg Prod.snd htriple
      rw [Prod.mk.injEq] at this
      exact this.2

/-- `CascadeGood` transfers across equal event queues. -/
private theorem cascadeGood_of_events_eq {T : Nat}
    {specs : List ChainSpec} (v w : World)
    (hev : v.events = w.events) (hgood : CascadeGood T specs w) :
    CascadeGood T specs v := by
  intro e he
  rw [hev] at he
  exact hgood e he

/-! ## The built world's queue is empty -/

/-- `connectChain` adds no events. -/
private theorem connectChain_events (w : World) (ids : List Nat) :
    (connectChain w ids).events = w.events := by
  dsimp [connectChain]
  generalize hp : ids.zip (ids.drop 1) = pairs
  clear hp
  induction pairs generalizing w with
  | nil => rfl
  | cons p ps ih =>
    rw [List.foldl_cons]
    cases p with
    | mk prev curr =>
      dsimp
      rw [ih, updateNode_events, updateNode_events]

/-- `addNode` adds no events. -/
private theorem addNode_events (w : World) (nd : NodeData) :
    (w.addNode nd).2.events = w.events := by
  dsimp [World.addNode]

/-- The repeater-adding fold adds no events. -/
private theorem repFoldl_events (l : List (PNat × Int))
    (acc : List Nat × World) :
    (l.foldl repFoldlStep acc).2.events = acc.2.events := by
  induction l generalizing acc with
  | nil => dsimp [List.foldl]
  | cons dp rest ih =>
    rw [List.foldl_cons, ih (repFoldlStep acc dp)]
    dsimp [repFoldlStep]
    rw [addNode_events]

/-- `buildChain` adds no events. -/
private theorem buildChain_events (w : World) (name : String)
    (c : ChainSpec) : (buildChain w name c).2.events = w.events := by
  dsimp [buildChain, buildChainPre, World.addNode]
  rw [connectChain_events, repFoldl_events]

/-- `buildChainsFrom` adds no events. -/
private theorem buildChainsFrom_events (start : Nat) (w : World)
    (specs : List ChainSpec) :
    (buildChainsFrom start w specs).1.events = w.events := by
  induction specs generalizing start w with
  | nil => dsimp [buildChainsFrom]
  | cons c cs ih =>
    dsimp only [buildChainsFrom]
    rw [ih (start + 1) ((buildChain w (chainName start) c).2)]
    exact buildChain_events w (chainName start) c

/-- The built world's queue is empty. -/
theorem buildChains_events (specs : List ChainSpec) :
    (buildChains specs).1.events = [] := by
  dsimp [buildChains]
  rw [buildChainsFrom_events]
  dsimp [World.empty]

/-! ## Firing a popped cascade event spawns cascade events -/

/-- The events appended by firing a popped cascade event are cascade
    events of the same chain. -/
private theorem firing_news_Good (T : Nat) (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (w : World) (e : ScheduledEvent) (wp : World)
    (hpop : w.popNextEvent = some (e, wp))
    (hgood : CascadeGood T specs w)
    (hwiring : ∀ id, (w.getNode id).map wiring =
      ((buildChains specs).1.getNode id).map wiring)
    (news : List ScheduledEvent)
    (hnews : (wp.onScheduledTick e.nodeId).events = wp.events ++ news) :
    ∀ f ∈ news, IsCascadeEv T specs f := by
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
  · -- observer event: firing spawns the stage-0 event
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
    have hfire := fires_observer_stage0_kind wp T specs i htickWp hobs
      hrep
    have hcan := append_left_cancel wp.events news
      [stageEventOf T specs i 0] (hnews.symm.trans hfire)
    intro f hf
    rw [hcan] at hf
    rcases List.mem_singleton.mp hf with rfl
    exact Or.inr ⟨i, hi, 0, by omega, rfl⟩
  · -- stage event of chain i
    rcases hstage with ⟨i, hi, s, hs, rfl⟩
    have hpri : (specAt specs i).priLenOk := (h_valid i hi).1
    have htickWp : wp.tick = stageTickOf T specs i s := by
      rw [World.popNextEvent_tick w (stageEventOf T specs i s) wp hpop,
        ← htickE]
      rfl
    by_cases hlt : s < (specAt specs i).middleDelays.length
    · -- middle stage: firing spawns the stage-(s+1) event
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
      have hfire := fires_rep_stage_kind wp T specs i s (by omega)
        htickWp hrep hnext
      have hcan := append_left_cancel wp.events news
        [stageEventOf T specs i (s + 1)] (hnews.symm.trans hfire)
      intro f hf
      rw [hcan] at hf
      rcases List.mem_singleton.mp hf with rfl
      exact Or.inr ⟨i, hi, s + 1, by omega, rfl⟩
    · -- last repeater: firing appends no events
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
      have hfire := fires_lastRep_events_kind wp specs i hrep hout
      have hcan : news = [] := by
        have := hnews.symm.trans hfire
        simpa using this
      intro f hf
      rw [hcan] at hf
      cases hf

/-! ## Classification is preserved through the loop -/

/-- `processNEvents` preserves cascade classification. -/
theorem processNEvents_good (T : Nat) (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (w : World) (n : Nat)
    (hgood : CascadeGood T specs w)
    (hwiring : ∀ id, (w.getNode id).map wiring =
      ((buildChains specs).1.getNode id).map wiring) :
    CascadeGood T specs (processNEvents w n) := by
  induction n generalizing w with
  | zero => dsimp [processNEvents]; exact hgood
  | succ n ih =>
    dsimp [processNEvents]
    cases hstep : w.step with
    | none => exact hgood
    | some w' =>
      apply ih
      · dsimp [World.step] at hstep
        cases hpop : w.popNextEvent with
        | none => simp [hpop] at hstep
        | some pr =>
          rcases pr with ⟨e, wp⟩
          have hw' : w' = wp.onScheduledTick e.nodeId := by
            apply Eq.symm
            simpa [World.step, hpop] using hstep
          rw [hw']
          intro f hf
          obtain ⟨news, hnews, _⟩ :=
            onScheduledTick_events_append wp e.nodeId
          rw [hnews] at hf
          rcases List.mem_append.mp hf with hf | hf
          · obtain ⟨idx, hidx, herase, _, _⟩ :=
              popNextEvent_eraseIdx w e wp hpop
            rw [herase] at hf
            exact hgood f (List.mem_of_mem_eraseIdx hf)
          · exact firing_news_Good T specs h_valid w e wp hpop hgood
              hwiring news hnews f hf
      · intro id
        rw [step_getNode_wiring w w' hstep id, hwiring]

/-- The full drain preserves cascade classification. -/
theorem stepUNT_good (T : Nat) (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (w : World)
    (hgood : CascadeGood T specs w)
    (hwiring : ∀ id, (w.getNode id).map wiring =
      ((buildChains specs).1.getNode id).map wiring) :
    CascadeGood T specs w.stepUntilNextTick := by
  induction w using World.stepUntilNextTick.induct with
  | case1 x hstep =>
    rw [stepUntilNextTick_of_step_none x hstep]
    exact hgood
  | case2 x w' hstep ih =>
    have hsunt : x.stepUntilNextTick = w'.stepUntilNextTick := by
      rw [World.stepUntilNextTick, hstep]
    rw [hsunt]
    apply ih
    · dsimp [World.step] at hstep
      cases hpop : x.popNextEvent with
      | none => simp [hpop] at hstep
      | some pr =>
        rcases pr with ⟨e, wp⟩
        have hw' : w' = wp.onScheduledTick e.nodeId := by
          apply Eq.symm
          simpa [World.step, hpop] using hstep
        rw [hw']
        intro f hf
        obtain ⟨news, hnews, _⟩ :=
          onScheduledTick_events_append wp e.nodeId
        rw [hnews] at hf
        rcases List.mem_append.mp hf with hf | hf
        · obtain ⟨idx, hidx, herase, _, _⟩ :=
            popNextEvent_eraseIdx x e wp hpop
          rw [herase] at hf
          exact hgood f (List.mem_of_mem_eraseIdx hf)
        · exact firing_news_Good T specs h_valid x e wp hpop hgood
            hwiring news hnews f hf
    · intro id
      rw [step_getNode_wiring x w' hstep id, hwiring]

/-- A burst preserves cascade classification when every appended
    activation event is itself a cascade event. -/
theorem simBurst_good (T : Nat) (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (t : Nat) (observers : List Nat) (pos : Nat → Nat → Nat)
    (w : World) (pairs : List (Nat × Nat))
    (hgood : CascadeGood T specs w)
    (hwiring : ∀ id, (w.getNode id).map wiring =
      ((buildChains specs).1.getNode id).map wiring)
    (htick : w.tick = t)
    (hact : ∀ p ∈ pairs, ∀ oid, observers[p.1]? = some oid →
      IsCascadeEv T specs (obsActEvt t oid)) :
    CascadeGood T specs (simBurst t observers pos w pairs) := by
  induction pairs generalizing w with
  | nil => dsimp [simBurst]; exact hgood
  | cons p ps ih =>
    rcases p with ⟨i, k⟩
    dsimp [simBurst, List.foldl]
    cases hobs : observers[i]? with
    | none =>
      dsimp
      apply ih
      · exact processNEvents_good T specs h_valid w (pos t k) hgood
          hwiring
      · intro id
        rw [processNEvents_getNode_wiring w (pos t k) id, hwiring]
      · rw [processNEvents_tick]
        exact htick
      · intro q hq oid' hget
        exact hact q (List.mem_cons.mpr (Or.inr hq)) oid' hget
    | some oid =>
      dsimp
      apply ih
      · dsimp [activateChain]
        intro f hf
        rw [World.scheduleEvent_events] at hf
        rcases List.mem_append.mp hf with hf | hf
        · exact processNEvents_good T specs h_valid w (pos t k) hgood
            hwiring f hf
        · rcases List.mem_singleton.mp hf with rfl
          have htick' : (processNEvents w (pos t k)).tick = t := by
            rw [processNEvents_tick, htick]
          rw [htick']
          exact hact (i, k) (List.mem_cons.mpr (Or.inl rfl)) oid hobs
      · intro id
        rw [activateChain_getNode_wiring,
          processNEvents_getNode_wiring, hwiring]
      · rw [activateChain_tick, processNEvents_tick]
        exact htick
      · intro q hq oid' hget
        exact hact q (List.mem_cons.mpr (Or.inr hq)) oid' hget

/-- Every event ever queued in the no-group simulation is a cascade
    event. -/
theorem simWorld_classification (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length)) (t : Nat) :
    CascadeGood T specs (simWorld T specs actOrd pos t) := by
  induction t with
  | zero =>
    rw [simWorld_zero]
    intro e he
    rw [buildChains_events] at he
    cases he
  | succ t ih =>
    rw [simWorld_succ]
    set wT := simWorld T specs actOrd pos t
    dsimp only [simBody]
    set wLog := wT.logOutput s!"tick {wT.tick}"
    apply stepUNT_good T specs h_valid
    · apply simBurst_good T specs h_valid
      · intro e he
        dsimp only [wLog, wT] at he
        rw [World.logOutput_events] at he
        exact ih e he
      · intro id
        dsimp only [wLog, wT, World.logOutput, World.getNode]
        exact simWorld_getNode_wiring T specs actOrd pos t id
      · rfl
      · set F := actOrd.filter (fun i =>
          decide (i < (buildChains specs).2.length) &&
            (actTickOf T specs i == wLog.tick))
        intro p hp oid hobsGet
        rcases p with ⟨ci, ck⟩
        obtain ⟨k, hkPos, hpk⟩ :=
          List.exists_mem_zipIdx'.mp ⟨(ci, ck), hp, rfl⟩
        rw [Prod.mk.injEq] at hpk
        rcases hpk with ⟨hci, hck⟩
        subst hci
        have hmemF := List.getElem_mem hkPos
        dsimp only [F] at hmemF
        rw [List.mem_filter] at hmemF
        obtain ⟨hjOrd, hjCond⟩ := hmemF
        rw [Bool.and_eq_true, decide_eq_true_eq] at hjCond
        have hltObs := hjCond.1
        have htickAct : actTickOf T specs (F[k]'hkPos) = wLog.tick :=
          Nat.eq_of_beq_eq_true (by simpa using hjCond.2)
        have hjSpec : (F[k]'hkPos) < specs.length :=
          List.mem_range.mp ((List.Perm.mem_iff h_perm).mp hjOrd)
        rw [List.getElem?_eq_getElem hltObs] at hobsGet
        have hoid := Option.some.inj hobsGet
        rw [observers_getElem_eq_chainObserverId specs (F[k]'hkPos)
          hltObs] at hoid
        exact Or.inl ⟨F[k]'hkPos, hjSpec, by
          dsimp [obsActEvt, obsEventOf, obsTickOf]
          rw [hoid.symm, htickAct.symm]⟩
    · intro id
      rw [simBurst_getNode_wiring]
      dsimp only [wLog, wT, World.logOutput, World.getNode]
      exact simWorld_getNode_wiring T specs actOrd pos t id

