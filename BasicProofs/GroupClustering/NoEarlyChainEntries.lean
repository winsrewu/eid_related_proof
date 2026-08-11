import BasicProofs.GroupClustering.LogShape
import BasicProofs.GroupClustering.OrderPreservationPremises

open BasicRedstoneSim List

/-! # Group clustering — no chain entries before the common output tick

Capstone input: every group activates so that all last repeaters fire at
one common tick `T` (`h_act`), all chains of a group have the same
`chainDelay` (`h_uniform`), and all delays are valid (≥ 2).

A chain-output entry (`gi:ci: 0` or `gi:ci: 15`) is appended only when a
last repeater fires, and a last repeater fires only when its stage
`m + 1` event is due — which happens exactly at tick `T`. This file
proves:

* firing a stage event with `j ≤ m` (observer or middle repeater) never
  appends a log entry (`stage_event_fire_no_log`);
* therefore `stepUntilNextTick`, `processNEvents`, `gSimBurst` and
  `gSimBody` append no entries at all while every due event is a
  non-final stage event (`stepUNT_outputLog_of_due_not_final`,
  `processNEvents_outputLog_of_due_not_final`,
  `gSimBurst_outputLog_of_due_not_final`,
  `gSimBody_no_chain_entry_before_T`);
* under `h_valid`, `h_uniform`, `h_act` the foldl log holds no chain
  entry at any tick `n ≤ T` (`gSimFoldl_no_chain_entry_before_T`);
* any block decomposition of the `groupSimulate` log has empty blocks
  before `T` (`groupSimulate_no_early_chain_entries`), discharging the
  `h_no_early` premise of LogShape's deliverables.

The due-event transfer relies on the LockstepComposition facts
`mem_processNEvents_due_back` and `mem_gSimBurst_due_back`: everything
appended during a tick targets a strictly later tick, so an event that
is still due was already queued.
-/

/-! ## Firing a non-final stage event appends no log entry -/

/-- Firing an observer whose single output is a repeater appends no log
    entry: the repeater's neighbor update only schedules an event. -/
private theorem onScheduledTick_observer_no_log (w : World) (nid rep : Nat)
    (nd nd_rep : NodeData) (d : PNat) (p : Int)
    (h_obs : w.getNode nid = some nd) (h_kind : nd.kind = .observer)
    (h_outputs : nd.outputs = [rep])
    (h_rep : w.getNode rep = some nd_rep)
    (h_kind_rep : nd_rep.kind = .repeater d p) :
    (w.onScheduledTick nid).outputLog = w.outputLog := by
  dsimp [World.onScheduledTick]
  rw [h_obs]
  simp only
  rw [h_kind]
  dsimp [World.notifyOutputs]
  have h_upd_gn : (w.updateNode nid
      (fun nd' => ({ nd' with sigLevel := 15 } : NodeData))).getNode nid =
      some ({ nd with sigLevel := 15 } : NodeData) :=
    World.updateNode_getNode_eq w nid _ nd h_obs
  rw [h_upd_gn]
  simp only
  rw [h_outputs]
  simp only [List.foldl_cons, List.foldl_nil]
  dsimp [World.onNeighborUpdate]
  have h_ne : nid ≠ rep := by
    intro h_eq
    have h_gn : w.getNode nid = w.getNode rep := congr_arg (fun i => w.getNode i) h_eq
    have h_nd_eq : nd = nd_rep := by rw [h_obs, h_rep] at h_gn; exact Option.some_inj.mp h_gn
    rw [← h_nd_eq, h_kind] at h_kind_rep
    injection h_kind_rep
  rw [World.updateNode_getNode_ne w nid rep _ h_ne, h_rep]
  simp only
  rw [h_kind_rep]
  simp [World.scheduleEvent_outputLog, World.updateNode]

/-- Firing a repeater whose single output is a repeater appends no log
    entry: the next repeater's neighbor update only schedules an
    event. -/
private theorem onScheduledTick_repeater_no_log (w : World) (nid nxt : Nat)
    (nd nd_next : NodeData) (d : PNat) (p p' : Int) (d' : PNat)
    (h_rep : w.getNode nid = some nd) (h_kind : nd.kind = .repeater d p)
    (h_outputs : nd.outputs = [nxt]) (h_ne : nid ≠ nxt)
    (h_next : w.getNode nxt = some nd_next)
    (h_kind_next : nd_next.kind = .repeater d' p') :
    (w.onScheduledTick nid).outputLog = w.outputLog := by
  dsimp [World.onScheduledTick]
  rw [h_rep]
  simp only
  rw [h_kind]
  dsimp [World.notifyOutputs]
  have h_upd_gn : (w.updateNode nid
      (fun nd' => ({ nd' with
          sigLevel := if w.getInputSignal nid > 0 then 15 else 0 } : NodeData))).getNode nid =
      some ({ nd with
          sigLevel := if w.getInputSignal nid > 0 then 15 else 0 } : NodeData) :=
    World.updateNode_getNode_eq w nid _ nd h_rep
  rw [h_upd_gn]
  simp only
  rw [h_outputs]
  simp only [List.foldl_cons, List.foldl_nil]
  dsimp [World.onNeighborUpdate]
  rw [World.updateNode_getNode_ne w nid nxt _ h_ne, h_next]
  simp only
  rw [h_kind_next]
  simp [World.scheduleEvent_outputLog, World.updateNode]

/-- Firing a stage event with `j ≤ m` (the observer or a middle
    repeater) appends no log entry. The fired node's single output is a
    repeater, whose neighbor update only schedules an event. -/
theorem stage_event_fire_no_log (groups : List GroupSpec) (actTick : Nat → Nat)
    (w : World) (gi ci j : Nat)
    (h_gi : gi < groups.length) (h_ci : ci < (groupAt groups gi).length)
    (h_j : j ≤ (chainAt groups gi ci).middleDelays.length)
    (h_layout : NodeLayoutOk groups w) :
    (w.onScheduledTick (stageEvent actTick groups gi ci j).nodeId).outputLog =
      w.outputLog := by
  set base := chainBaseId groups gi ci
  set c := chainAt groups gi ci
  set m := c.middleDelays.length
  have h_nodeId : (stageEvent actTick groups gi ci j).nodeId = base + 1 + j := by
    dsimp [stageEvent]
  rw [h_nodeId]
  cases j with
  | zero =>
    obtain ⟨nd_obs, h_obs, h_kind_obs, h_outs_obs⟩ := h_layout.1 gi ci h_gi h_ci
    by_cases h_m0 : m = 0
    · -- no middle repeaters: the observer's output is the last repeater
      obtain ⟨nd_rep, h_rep, h_kind_rep, _⟩ := h_layout.2.2.1 gi ci h_gi h_ci
      have h_idx : base + 2 = base + m + 2 := by omega
      have h_rep' : w.getNode (base + 2) = some nd_rep := by
        rw [h_idx]
        exact h_rep
      exact onScheduledTick_observer_no_log w (base + 1) (base + 2) nd_obs nd_rep
        c.lastDelay (-1) h_obs h_kind_obs h_outs_obs h_rep' h_kind_rep
    · -- at least one middle repeater: the observer's output is the first one
      have h_0lt : 0 < c.middleDelays.length := by omega
      obtain ⟨nd_rep, h_rep, h_kind_rep, _⟩ :=
        h_layout.2.1 gi ci 0 h_gi h_ci h_0lt
      exact onScheduledTick_observer_no_log w (base + 1) (base + 2) nd_obs nd_rep
        (c.middleDelays[0]'h_0lt) (-3) h_obs h_kind_obs h_outs_obs h_rep h_kind_rep
  | succ j' =>
    have h_j'_lt : j' < m := by omega
    obtain ⟨nd_rep, h_rep, h_kind_rep, h_outs_rep⟩ :=
      h_layout.2.1 gi ci j' h_gi h_ci h_j'_lt
    have h_idx : base + 1 + (j' + 1) = base + 2 + j' := by omega
    rw [h_idx]
    by_cases h_next : j' + 1 < m
    · -- the next node is the middle repeater `j' + 1`
      obtain ⟨nd_nxt, h_nxt, h_kind_nxt, _⟩ :=
        h_layout.2.1 gi ci (j' + 1) h_gi h_ci h_next
      have h_idx_nxt : base + 3 + j' = base + 2 + (j' + 1) := by omega
      have h_nxt' : w.getNode (base + 3 + j') = some nd_nxt := by
        rw [h_idx_nxt]
        exact h_nxt
      exact onScheduledTick_repeater_no_log w (base + 2 + j') (base + 3 + j')
        nd_rep nd_nxt (c.middleDelays[j']'h_j'_lt) (-3) (-3)
        (c.middleDelays[j' + 1]'h_next) h_rep h_kind_rep h_outs_rep
        (by omega) h_nxt' h_kind_nxt
    · -- the next node is the last repeater
      obtain ⟨nd_nxt, h_nxt, h_kind_nxt, _⟩ := h_layout.2.2.1 gi ci h_gi h_ci
      have h_idx_nxt : base + 3 + j' = base + m + 2 := by omega
      have h_nxt' : w.getNode (base + 3 + j') = some nd_nxt := by
        rw [h_idx_nxt]
        exact h_nxt
      exact onScheduledTick_repeater_no_log w (base + 2 + j') (base + 3 + j')
        nd_rep nd_nxt (c.middleDelays[j']'h_j'_lt) (-3) (-1) c.lastDelay
        h_rep h_kind_rep h_outs_rep (by omega) h_nxt' h_kind_nxt

/-! ## Due events of a stepped world were already queued -/

/-- `NodeLayoutOk` carries through `popNextEvent` (which does not touch
    the nodes). -/
private theorem NodeLayoutOk_popNextEvent (groups : List GroupSpec) (w : World)
    (ev : ScheduledEvent) (w_pop : World)
    (h_pop : w.popNextEvent = some (ev, w_pop)) :
    NodeLayoutOk groups w → NodeLayoutOk groups w_pop := by
  intro H
  have h_gn : ∀ nid, w_pop.getNode nid = w.getNode nid := by
    intro nid
    dsimp [World.getNode]
    rw [World.popNextEvent_nodes w ev w_pop h_pop]
  rcases H with ⟨hO, hM, hL, hOut⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro gi ci h_gi h_ci
    obtain ⟨nd, h, hk, ho⟩ := hO gi ci h_gi h_ci
    exact ⟨nd, by rw [h_gn]; exact h, hk, ho⟩
  · intro gi ci k h_gi h_ci h_k
    obtain ⟨nd, h, hk, ho⟩ := hM gi ci k h_gi h_ci h_k
    exact ⟨nd, by rw [h_gn]; exact h, hk, ho⟩
  · intro gi ci h_gi h_ci
    obtain ⟨nd, h, hk, ho⟩ := hL gi ci h_gi h_ci
    exact ⟨nd, by rw [h_gn]; exact h, hk, ho⟩
  · intro gi ci h_gi h_ci
    obtain ⟨nd, h, hk, ho⟩ := hOut gi ci h_gi h_ci
    exact ⟨nd, by rw [h_gn]; exact h, hk, ho⟩

/-- The due-event characterization carries through one step: everything
    appended by firing targets a strictly later tick, and the popped
    world's queue is a sublist of the original queue. -/
private theorem due_stage_of_step (groups : List GroupSpec)
    (actTick : Nat → Nat) (w w' : World) (h_step : w.step = some w')
    (h_due : ∀ ev ∈ w.events, ev.targetTick = w.tick →
      ∃ gi ci j, gi < groups.length ∧ ci < (groupAt groups gi).length ∧
        j ≤ (chainAt groups gi ci).middleDelays.length ∧
        ev = stageEvent actTick groups gi ci j) :
    ∀ ev ∈ w'.events, ev.targetTick = w'.tick →
      ∃ gi ci j, gi < groups.length ∧ ci < (groupAt groups gi).length ∧
        j ≤ (chainAt groups gi ci).middleDelays.length ∧
        ev = stageEvent actTick groups gi ci j := by
  intro ev h_ev h_tgt
  have h_tick_w' : w'.tick = w.tick := World.step_tick w w' h_step
  dsimp [World.step] at h_step
  cases h_pop : w.popNextEvent with
  | none => simp [h_pop] at h_step
  | some p =>
    rcases p with ⟨ev₀, w_pop⟩
    simp only [h_pop] at h_step
    injection h_step with h_w'
    obtain ⟨idx, _, h_erase, _, _, _⟩ :=
      World.popNextEvent_eraseIdx w ev₀ w_pop h_pop
    obtain ⟨new, h_app, h_fut⟩ :=
      World.onScheduledTick_appends_future w_pop ev₀.nodeId
    have h_ev_pop : ev ∈ w_pop.events := by
      rw [← h_w', h_app, List.mem_append] at h_ev
      rcases h_ev with h_ev | h_new
      · exact h_ev
      · have h_gt := h_fut ev h_new
        rw [World.popNextEvent_tick w ev₀ w_pop h_pop] at h_gt
        have h_tgt_w : ev.targetTick = w.tick := h_tgt.trans h_tick_w'
        omega
    rw [h_erase] at h_ev_pop
    exact h_due ev (List.eraseIdx_subset' w.events idx h_ev_pop)
      (h_tgt.trans h_tick_w')

/-- One step that pops a non-final stage event appends no log entry. -/
private theorem step_outputLog_of_due_not_final (groups : List GroupSpec)
    (actTick : Nat → Nat) (w w' : World) (h_step : w.step = some w')
    (h_layout : NodeLayoutOk groups w)
    (h_due : ∀ ev ∈ w.events, ev.targetTick = w.tick →
      ∃ gi ci j, gi < groups.length ∧ ci < (groupAt groups gi).length ∧
        j ≤ (chainAt groups gi ci).middleDelays.length ∧
        ev = stageEvent actTick groups gi ci j) :
    w'.outputLog = w.outputLog := by
  dsimp [World.step] at h_step
  cases h_pop : w.popNextEvent with
  | none => simp [h_pop] at h_step
  | some p =>
    rcases p with ⟨ev₀, w_pop⟩
    simp only [h_pop] at h_step
    injection h_step with h_w'
    obtain ⟨_, _, _, h_tick₀, h_mem₀, _⟩ :=
      World.popNextEvent_eraseIdx w ev₀ w_pop h_pop
    obtain ⟨gi, ci, j, h_gi, h_ci, h_j, h_ev₀⟩ := h_due ev₀ h_mem₀ h_tick₀
    have h_no_log := stage_event_fire_no_log groups actTick w_pop gi ci j
      h_gi h_ci h_j (NodeLayoutOk_popNextEvent groups w ev₀ w_pop h_pop h_layout)
    rw [← h_ev₀] at h_no_log
    calc w'.outputLog =
        (w_pop.onScheduledTick ev₀.nodeId).outputLog := by rw [h_w']
      _ = w_pop.outputLog := h_no_log
      _ = w.outputLog := World.popNextEvent_outputLog w ev₀ w_pop h_pop

/-! ## The drain, the pos-insertion and the burst append nothing -/

/-- While every due event is a non-final stage event, the drain of the
    tick appends no log entry. -/
theorem stepUNT_outputLog_of_due_not_final (groups : List GroupSpec)
    (actTick : Nat → Nat) (w : World)
    (h_layout : NodeLayoutOk groups w)
    (h_delay : ∀ nid nd, w.getNode nid = some nd → ∀ d p,
        nd.kind = .repeater d p → d ≥ 2)
    (h_due : ∀ ev ∈ w.events, ev.targetTick = w.tick →
      ∃ gi ci j, gi < groups.length ∧ ci < (groupAt groups gi).length ∧
        j ≤ (chainAt groups gi ci).middleDelays.length ∧
        ev = stageEvent actTick groups gi ci j) :
    w.stepUntilNextTick.outputLog = w.outputLog := by
  revert h_layout h_delay h_due
  induction w using World.stepUntilNextTick.induct with
  | case1 x h_step =>
    intro _ _ _
    rw [stepUntilNextTick_of_step_none x h_step]
  | case2 x w' h_step ih =>
    intro h_layout h_delay h_due
    have h_sunt : x.stepUntilNextTick = w'.stepUntilNextTick := by
      rw [World.stepUntilNextTick, h_step]
    calc x.stepUntilNextTick.outputLog =
        w'.stepUntilNextTick.outputLog := by rw [h_sunt]
      _ = w'.outputLog := ih
        (NodeLayoutOk_step groups x w' h_step h_layout)
        (step_delay_preserved x w' h_step h_delay)
        (due_stage_of_step groups actTick x w' h_step h_due)
      _ = x.outputLog :=
        step_outputLog_of_due_not_final groups actTick x w' h_step h_layout h_due

/-- While every due event is a non-final stage event, processing any
    number of events appends no log entry. -/
theorem processNEvents_outputLog_of_due_not_final (groups : List GroupSpec)
    (actTick : Nat → Nat) (w : World)
    (h_layout : NodeLayoutOk groups w)
    (h_delay : ∀ nid nd, w.getNode nid = some nd → ∀ d p,
        nd.kind = .repeater d p → d ≥ 2)
    (h_due : ∀ ev ∈ w.events, ev.targetTick = w.tick →
      ∃ gi ci j, gi < groups.length ∧ ci < (groupAt groups gi).length ∧
        j ≤ (chainAt groups gi ci).middleDelays.length ∧
        ev = stageEvent actTick groups gi ci j) :
    ∀ n, (processNEvents w n).outputLog = w.outputLog := by
  intro n
  revert h_layout h_delay h_due
  induction n generalizing w with
  | zero =>
    intro _ _ _
    simp [processNEvents]
  | succ n' ih =>
    intro h_layout h_delay h_due
    simp only [processNEvents]
    cases h_step : w.step with
    | none => rfl
    | some w' =>
      have h_log_step : w'.outputLog = w.outputLog :=
        step_outputLog_of_due_not_final groups actTick w w' h_step h_layout h_due
      calc (processNEvents w' n').outputLog = w'.outputLog :=
          ih w'
            (NodeLayoutOk_step groups w w' h_step h_layout)
            (step_delay_preserved w w' h_step h_delay)
            (due_stage_of_step groups actTick w w' h_step h_due)
        _ = w.outputLog := h_log_step

/-- `activateGroup` does not touch the output log. -/
private theorem activateGroup_outputLog' (w : World) (observers : List Nat) :
    (activateGroup w observers).outputLog = w.outputLog := by
  induction observers generalizing w with
  | nil => dsimp [activateGroup]
  | cons oid os ih =>
    dsimp [activateGroup, List.foldl_cons]
    set ev : ScheduledEvent :=
      { targetTick := w.tick + 2, priority := 0, nodeId := oid }
    change (activateGroup (w.scheduleEvent ev) os).outputLog = w.outputLog
    rw [ih, World.scheduleEvent_outputLog]

/-- While every event due at `t` is a non-final stage event, the burst
    phase appends no log entry: each pos-insertion processes only such
    events, and `activateGroup` only enqueues. -/
theorem gSimBurst_outputLog_of_due_not_final (groups : List GroupSpec)
    (actTick : Nat → Nat) (t : Nat) (obsAll : List (List Nat))
    (withinOrd pos : Nat → List Nat) (w : World)
    (pairs : List (Nat × Nat))
    (h_tick : w.tick = t)
    (h_layout : NodeLayoutOk groups w)
    (h_delay : ∀ nid nd, w.getNode nid = some nd → ∀ d p,
        nd.kind = .repeater d p → d ≥ 2)
    (h_due : ∀ ev ∈ w.events, ev.targetTick = t →
      ∃ gi ci j, gi < groups.length ∧ ci < (groupAt groups gi).length ∧
        j ≤ (chainAt groups gi ci).middleDelays.length ∧
        ev = stageEvent actTick groups gi ci j) :
    (gSimBurst t obsAll withinOrd pos w pairs).outputLog = w.outputLog := by
  induction pairs generalizing w with
  | nil => simp [gSimBurst]
  | cons p ps ih =>
    rcases p with ⟨gi, k⟩
    simp only [gSimBurst, List.foldl_cons]
    set m := (pos t)[k]?.getD 0
    set ordered : List Nat := (withinOrd gi).foldl (fun acc ci =>
      match (obsAll[gi]?.getD [])[ci]? with
      | some oid => acc ++ [oid]
      | none => acc) []
    set Wproc := processNEvents w m
    set W₁ := activateGroup Wproc ordered
    have h_log_proc : Wproc.outputLog = w.outputLog := by
      dsimp [Wproc]
      exact processNEvents_outputLog_of_due_not_final groups actTick w
        h_layout h_delay
        (fun ev h_ev h_tgt => h_due ev h_ev (h_tgt.trans h_tick)) m
    have h_tick_W₁ : W₁.tick = t := by
      dsimp [W₁, Wproc]
      rw [activateGroup_tick, processNEvents_tick, h_tick]
    have h_layout_W₁ : NodeLayoutOk groups W₁ :=
      NodeLayoutOk_activateGroup groups Wproc ordered
        (NodeLayoutOk_processNEvents groups w m h_layout)
    have h_delay_W₁ : ∀ nid nd, W₁.getNode nid = some nd → ∀ d p,
        nd.kind = .repeater d p → d ≥ 2 :=
      activateGroup_delay_preserved Wproc ordered
        (processNEvents_delay_preserved w m h_delay)
    have h_due_W₁ : ∀ ev ∈ W₁.events, ev.targetTick = t →
        ∃ gi' ci' j, gi' < groups.length ∧ ci' < (groupAt groups gi').length ∧
          j ≤ (chainAt groups gi' ci').middleDelays.length ∧
          ev = stageEvent actTick groups gi' ci' j := by
      intro ev h_ev h_tgt
      have h_ev_w : ev ∈ w.events := by
        have h_ev₁ : ev ∈ W₁.events := h_ev
        dsimp [W₁] at h_ev₁
        rw [activateGroup_events_map, List.mem_append] at h_ev₁
        rcases h_ev₁ with h_ev₁ | h_obs
        · exact mem_processNEvents_due_back w m ev h_ev₁
            (h_tgt.trans h_tick.symm)
        · rcases List.mem_map.mp h_obs with ⟨nid, _, h_ev_eq⟩
          have h_tgt' : ev.targetTick = Wproc.tick + 2 := by
            rw [← h_ev_eq]
          dsimp [Wproc] at h_tgt'
          rw [processNEvents_tick, h_tick] at h_tgt'
          omega
      exact h_due ev h_ev_w h_tgt
    calc (gSimBurst t obsAll withinOrd pos W₁ ps).outputLog = W₁.outputLog :=
        ih W₁ h_tick_W₁ h_layout_W₁ h_delay_W₁ h_due_W₁
      _ = Wproc.outputLog := activateGroup_outputLog' Wproc ordered
      _ = w.outputLog := h_log_proc

/-! ## One tick body appends only its tick entry -/

/-- While every event due at tick `n` is a non-final stage event, one
    `gSimBody` call appends exactly the tick entry `s!"tick {n}"` and
    nothing else. -/
theorem gSimBody_no_chain_entry_before_T (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (w : World) (n : Nat)
    (h_tick : w.tick = n)
    (h_layout : NodeLayoutOk groups w)
    (h_delay : ∀ nid nd, w.getNode nid = some nd → ∀ d p,
        nd.kind = .repeater d p → d ≥ 2)
    (h_due : ∀ ev ∈ w.events, ev.targetTick = n →
      ∃ gi ci j, gi < groups.length ∧ ci < (groupAt groups gi).length ∧
        j ≤ (chainAt groups gi ci).middleDelays.length ∧
        ev = stageEvent actTick groups gi ci j) :
    (gSimBody actTick (buildGroups groups).2 groupOrd withinOrd pos w n).outputLog =
      w.outputLog ++ [s!"tick {n}"] := by
  set obsAll := (buildGroups groups).2
  dsimp [gSimBody]
  simp only [h_tick]
  set W₁ := w.logOutput s!"tick {n}"
  set active := groupOrd.filter (fun gi =>
    decide (gi < obsAll.length) && (actTick gi == n))
  have h_log_W₁ : W₁.outputLog = w.outputLog ++ [s!"tick {n}"] := by
    dsimp [W₁, World.logOutput]
  have h_tick_W₁ : W₁.tick = n := by
    dsimp [W₁]
    exact h_tick
  have h_layout_W₁ : NodeLayoutOk groups W₁ :=
    NodeLayoutOk_logOutput groups w s!"tick {n}" h_layout
  have h_delay_W₁ : ∀ nid nd, W₁.getNode nid = some nd → ∀ d p,
      nd.kind = .repeater d p → d ≥ 2 := by
    intro nid nd h_nd d p h_kind
    have h_nd' : w.getNode nid = some nd := by
      rwa [World.logOutput_getNode] at h_nd
    exact h_delay nid nd h_nd' d p h_kind
  have h_due_W₁ : ∀ ev ∈ W₁.events, ev.targetTick = n →
      ∃ gi ci j, gi < groups.length ∧ ci < (groupAt groups gi).length ∧
        j ≤ (chainAt groups gi ci).middleDelays.length ∧
        ev = stageEvent actTick groups gi ci j := by
    intro ev h_ev
    have h_ev' : ev ∈ w.events := by
      rwa [World.logOutput_events] at h_ev
    intro h_tgt
    exact h_due ev h_ev' h_tgt
  split_ifs with h_active
  · -- no group activates at tick `n`: just the drain
    have h_log := stepUNT_outputLog_of_due_not_final groups actTick W₁
      h_layout_W₁ h_delay_W₁
      (fun ev h_ev h_tgt => h_due_W₁ ev h_ev (h_tgt.trans h_tick_W₁))
    rw [h_log, h_log_W₁]
  · -- some groups activate: the burst appends nothing, then the drain
    set W_B := gSimBurst n obsAll withinOrd pos W₁ (active.zipIdx)
    have h_burst : W_B.outputLog = W₁.outputLog :=
      gSimBurst_outputLog_of_due_not_final groups actTick n obsAll withinOrd
        pos W₁ (active.zipIdx) h_tick_W₁ h_layout_W₁ h_delay_W₁ h_due_W₁
    have h_due_WB : ∀ ev ∈ W_B.events, ev.targetTick = W_B.tick →
        ∃ gi ci j, gi < groups.length ∧ ci < (groupAt groups gi).length ∧
          j ≤ (chainAt groups gi ci).middleDelays.length ∧
          ev = stageEvent actTick groups gi ci j := by
      intro ev h_ev h_tgt
      have h_tick_WB : W_B.tick = n := by
        dsimp [W_B]
        rw [gSimBurst_tick, h_tick_W₁]
      have h_tgt' : ev.targetTick = n := by
        rwa [h_tick_WB] at h_tgt
      have h_ev_W₁ : ev ∈ W₁.events :=
        mem_gSimBurst_due_back n obsAll withinOrd pos W₁ (active.zipIdx) ev
          h_ev (h_tgt'.trans h_tick_W₁.symm)
      exact h_due_W₁ ev h_ev_W₁ h_tgt'
    have h_log := stepUNT_outputLog_of_due_not_final groups actTick W_B
      (NodeLayoutOk_gSimBurst groups n obsAll withinOrd pos W₁
        (active.zipIdx) h_layout_W₁)
      (gSimBurst_delay_preserved n obsAll withinOrd pos W₁ (active.zipIdx)
        h_delay_W₁)
      h_due_WB
    rw [h_log, h_burst, h_log_W₁]

/-! ## No chain entry in the foldl log before `T` -/

/-- The interpolated zero entry equals the literal zero entry. -/
private theorem chainEntry_zero_form' (nm : String) :
    (s!"{nm}: {(0 : Nat)}" : String) = s!"{nm}: 0" := by
  show nm ++ ": " ++ (0 : Nat).repr = nm ++ ": 0"
  rw [show (0 : Nat).repr = "0" from by decide, String.append_assoc]
  exact congrArg (fun t => nm ++ t)
    (by decide : (": " : String) ++ "0" = ": 0")

/-- The interpolated fifteen entry equals the literal fifteen entry. -/
private theorem chainEntry_fifteen_form' (nm : String) :
    (s!"{nm}: {(15 : Nat)}" : String) = s!"{nm}: 15" := by
  show nm ++ ": " ++ (15 : Nat).repr = nm ++ ": 15"
  rw [show (15 : Nat).repr = "15" from by decide, String.append_assoc]
  exact congrArg (fun t => nm ++ t)
    (by decide : (": " : String) ++ "15" = ": 15")

/-- A tick entry is never a chain entry. -/
private theorem tick_entry_not_chain_entry (n : Nat) (s : String)
    (h_chain : IsChainEntry s) : s ≠ s!"tick {n}" := by
  rcases h_chain with ⟨gi, ci, v, h_v, rfl⟩
  rcases h_v with rfl | rfl
  · intro h
    rw [chainEntry_zero_form'] at h
    exact (tick_entry_not_output n gi ci).1 h.symm
  · intro h
    rw [chainEntry_fifteen_form'] at h
    exact (tick_entry_not_output n gi ci).2 h.symm

/-- Under the common-output-tick setup, the `n`-tick foldl log holds no
    chain entry for any `n ≤ T`: a chain entry is appended only when a
    last-repeater stage event is due, and that happens first at tick
    `T`. -/
theorem gSimFoldl_no_chain_entry_before_T (T : Nat)
    (groups : List GroupSpec) (actTick : Nat → Nat)
    (groupOrd : List Nat) (withinOrd pos : Nat → List Nat)
    (h_valid : ∀ gi (c : ChainSpec), gi < groups.length →
        c ∈ groupAt groups gi →
        (∀ d ∈ c.middleDelays, ValidDelay d) ∧ ValidDelay c.lastDelay)
    (h_uniform : ∀ gi (c₁ c₂ : ChainSpec), gi < groups.length →
        c₁ ∈ groupAt groups gi → c₂ ∈ groupAt groups gi →
        chainDelay c₁ = chainDelay c₂)
    (h_act : ∀ gi, gi < groups.length → groupAt groups gi ≠ [] →
        actTick gi + groupDelay (groupAt groups gi) = T) :
    ∀ n, n ≤ T → ∀ s, IsChainEntry s →
      s ∉ (gSimFoldl actTick (buildGroups groups).2 groupOrd withinOrd pos
          (buildGroups groups).1 n).outputLog := by
  set obsAll := (buildGroups groups).2
  set w₀ := (buildGroups groups).1
  intro n
  induction n with
  | zero =>
    intro _ s _
    simp only [gSimFoldl, List.range_zero, List.foldl_nil]
    rw [buildGroups_outputLog]
    simp
  | succ n' ih =>
    intro h_le s h_chain
    have h_lt : n' < T := by omega
    simp only [gSimFoldl, List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil]
    set W : World := (List.range n').foldl
      (gSimBody actTick obsAll groupOrd withinOrd pos) w₀
    have h_tick_W : W.tick = n' := by
      change (gSimFoldl actTick obsAll groupOrd withinOrd pos w₀ n').tick = n'
      rw [gSimFoldl_tick, buildGroups_tick]
      omega
    have h_body : (gSimBody actTick obsAll groupOrd withinOrd pos W n').outputLog =
        W.outputLog ++ [s!"tick {n'}"] := by
      apply gSimBody_no_chain_entry_before_T groups actTick groupOrd withinOrd
        pos W n' h_tick_W
      · exact NodeLayoutOk_gSimFoldl groups actTick obsAll groupOrd withinOrd
          pos w₀ n' (NodeLayoutOk_buildGroups groups)
      · -- delay ≥ 2: `W` is the tick-`n'` simulation world
        show ∀ nid nd,
          (gSimWorld groups actTick groupOrd withinOrd pos n').getNode nid =
            some nd →
          ∀ d p, nd.kind = .repeater d p → d ≥ 2
        exact gSimWorld_delay_ge2 groups actTick groupOrd withinOrd pos n'
          h_valid
      · -- every due event of `W` is a non-final stage event
        intro ev h_ev h_tgt
        obtain ⟨gi, ci, j, h_gi, h_ci, _, h_ev₀, _⟩ :=
          gSimWorld_events_stageWindow groups actTick groupOrd withinOrd pos
            n' ev h_ev
        set m := (chainAt groups gi ci).middleDelays.length
        have h_st : stageTarget actTick groups gi ci j = n' := by
          rw [h_ev₀] at h_tgt
          dsimp [stageEvent] at h_tgt
          exact h_tgt
        have h_jm : j ≠ m + 1 := by
          intro h_jm
          have h_delay_eq : n' = actTick gi + chainDelay (chainAt groups gi ci) :=
            by
            rw [← h_st, h_jm, stageTarget_last]
          have h_ne : groupAt groups gi ≠ [] := by
            intro h
            have := h_ci
            rw [h] at this
            cases this
          cases h_grp : groupAt groups gi with
          | nil => exact absurd h_grp h_ne
          | cons c₀ cs =>
            have h_grp_delay : groupDelay (groupAt groups gi) =
                chainDelay (chainAt groups gi ci) := by
              rw [h_grp]
              dsimp only [groupDelay]
              exact h_uniform gi c₀ (chainAt groups gi ci) h_gi
                (by rw [h_grp]; simp) (chainAt_mem groups gi ci h_ci)
            have h_T := h_act gi h_gi h_ne
            rw [h_grp_delay] at h_T
            omega
        exact ⟨gi, ci, j, h_gi, h_ci, by omega, h_ev₀⟩
    rw [h_body]
    intro h_mem
    rcases List.mem_append.mp h_mem with h_mem | h_mem
    · exact ih (by omega) s h_chain h_mem
    · rw [List.mem_singleton] at h_mem
      exact tick_entry_not_chain_entry n' s h_chain h_mem

/-! ## Any block decomposition of the `groupSimulate` log has empty
    blocks before `T` -/

/-- Any block decomposition of the `groupSimulate T` log has empty block
    tails before `T`. The `h_shape` premise is the `groupSimulate_log_shape`
    equation with `logBlocks [] 0 chainAt (T + 1)` unfolded to its
    defining foldl. -/
theorem groupSimulate_no_early_chain_entries (T : Nat)
    (groups : List GroupSpec) (actTick : Nat → Nat)
    (groupOrd : List Nat) (withinOrd pos : Nat → List Nat)
    (h_valid : ∀ gi (c : ChainSpec), gi < groups.length →
        c ∈ groupAt groups gi →
        (∀ d ∈ c.middleDelays, ValidDelay d) ∧ ValidDelay c.lastDelay)
    (h_uniform : ∀ gi (c₁ c₂ : ChainSpec), gi < groups.length →
        c₁ ∈ groupAt groups gi → c₂ ∈ groupAt groups gi →
        chainDelay c₁ = chainDelay c₂)
    (h_act : ∀ gi, gi < groups.length → groupAt groups gi ≠ [] →
        actTick gi + groupDelay (groupAt groups gi) = T)
    (chainAt : Nat → List String)
    (h_shape : groupSimulate T groups actTick groupOrd withinOrd pos =
        (List.range (T + 1)).foldl
          (fun acc t => acc ++ (s!"tick {t}" :: chainAt t)) []) :
    ∀ t < T, chainAt t = [] := by
  set w₀ := (buildGroups groups).1
  set obsAll := (buildGroups groups).2
  obtain ⟨chainAt', h_prefix, h_chain', _, _⟩ :=
    gSimFoldl_log_shape_prefix actTick obsAll groupOrd withinOrd pos w₀ (T + 1)
      (buildGroups_OutputNamesOk groups) (buildGroups_SigLevelsOk groups)
  intro t h_t
  -- the two block decompositions agree on block `t`
  have h_ct : chainAt t = chainAt' t :=
    logBlocks_chainAt_eq_of_log_eq (T + 1) chainAt chainAt' h_chain' (by
      rw [logBlocks_zero_eq_foldl chainAt (T + 1), ← h_shape]
      dsimp [groupSimulate]
      rw [h_prefix (T + 1) (by omega), buildGroups_outputLog, buildGroups_tick])
      t (by omega)
  rw [h_ct]
  -- block `t` of `chainAt'` sits in the tick-`t + 1` prefix log, which
  -- holds no chain entry
  cases h_block : chainAt' t with
  | nil => rfl
  | cons s rest =>
    have h_s_mem : s ∈ chainAt' t := by
      rw [h_block]
      exact List.mem_cons.mpr (Or.inl rfl)
    have h_s_chain : IsChainEntry s := h_chain' t (by omega) s h_s_mem
    have h_mem_log : s ∈ (gSimFoldl actTick obsAll groupOrd withinOrd pos w₀
        (t + 1)).outputLog := by
      rw [h_prefix (t + 1) (by omega), buildGroups_outputLog, buildGroups_tick]
      exact mem_logBlocks_chain 0 t (t + 1) s chainAt' h_s_mem (by omega)
    exact absurd h_mem_log
      (gSimFoldl_no_chain_entry_before_T T groups actTick groupOrd withinOrd
        pos h_valid h_uniform h_act (t + 1) (by omega) s h_s_chain)
