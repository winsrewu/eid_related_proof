import Proofs.Model.CascadeTrace
import Mathlib.Data.List.Defs
import Mathlib.Data.List.Basic
import Mathlib.Tactic

open BasicRedstoneSim
open World
open List

/-! # Stage descent — the lockstep induction

The tick-start worlds `simWorld … t`, and the firing obligations that
carry a spec class's stage events through the cascade: firing the
observer spawns the stage-0 event, firing a middle repeater spawns the
next stage event, firing the last repeater logs the output. -/

/-! ## The tick-start worlds -/

/-- The world at the start of tick `t`: ticks `0 .. t-1` fully
    processed, tick counter at `t`. -/
def simWorld (T : Nat) (specs : List ChainSpec) (actOrd : List Nat)
    (pos : Nat → Nat → Nat) (t : Nat) : World :=
  simFoldl (actTickOf T specs) (buildChains specs).2 actOrd pos
    (buildChains specs).1 t

/-- `connectChain` preserves the tick. -/
private theorem connectChain_tick (w : World) (ids : List Nat) :
    (connectChain w ids).tick = w.tick := by
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
      rw [ih, updateNode_tick, updateNode_tick]

/-- `addNode` preserves the tick. -/
private theorem addNode_tick (w : World) (nd : NodeData) :
    (w.addNode nd).2.tick = w.tick := by
  dsimp [World.addNode]

/-- The repeater-adding fold preserves the tick. -/
private theorem repFoldl_tick (l : List (PNat × Int))
    (acc : List Nat × World) :
    (l.foldl repFoldlStep acc).2.tick = acc.2.tick := by
  induction l generalizing acc with
  | nil => dsimp [List.foldl]
  | cons dp rest ih =>
    rw [List.foldl_cons, ih (repFoldlStep acc dp)]
    dsimp [repFoldlStep]
    rw [addNode_tick]

/-- `buildChain` preserves the tick. -/
private theorem buildChain_tick (w : World) (name : String)
    (c : ChainSpec) : (buildChain w name c).2.tick = w.tick := by
  dsimp [buildChain, buildChainPre, World.addNode]
  rw [connectChain_tick, repFoldl_tick]

/-- `buildChainsFrom` preserves the tick. -/
private theorem buildChainsFrom_tick (start : Nat) (w : World)
    (specs : List ChainSpec) :
    (buildChainsFrom start w specs).1.tick = w.tick := by
  induction specs generalizing start w with
  | nil => dsimp [buildChainsFrom]
  | cons c cs ih =>
    dsimp only [buildChainsFrom]
    rw [ih (start + 1) ((buildChain w (chainName start) c).2)]
    exact buildChain_tick w (chainName start) c

/-- The built world starts at tick 0. -/
theorem buildChains_tick (specs : List ChainSpec) :
    (buildChains specs).1.tick = 0 := by
  dsimp [buildChains]
  rw [buildChainsFrom_tick]
  dsimp [World.empty]

/-- The world at the start of tick 0 is the built world. -/
theorem simWorld_zero (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat) :
    simWorld T specs actOrd pos 0 = (buildChains specs).1 := by
  dsimp [simWorld, simFoldl]

/-- One tick of `simWorld` is one `simBody`. -/
theorem simWorld_succ (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat) (t : Nat) :
    simWorld T specs actOrd pos (t + 1) =
      simBody (actTickOf T specs) (buildChains specs).2 actOrd pos
        (simWorld T specs actOrd pos t) t := by
  dsimp [simWorld, simFoldl]
  have h : List.range (t + 1) = List.range t ++ [t] := by
    rw [List.range_succ]
  rw [h, List.foldl_append]
  dsimp

/-- The tick-start world's counter is `t`. -/
theorem simWorld_tick (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat) (t : Nat) :
    (simWorld T specs actOrd pos t).tick = t := by
  dsimp [simWorld]
  rw [simFoldl_tick, buildChains_tick]
  omega

/-! ## Firing obligations

Each fired node appends exactly its successor event (or, for the last
repeater, exactly one log entry). Stated world-generically against
`getNode` hypotheses so the drain frame can supply them. -/

/-- Firing chain `i`'s observer spawns its stage-0 event. -/
theorem fires_observer_stage0 (w : World) (T : Nat)
    (specs : List ChainSpec) (i : Nat)
    (htick : w.tick = obsTickOf T specs i)
    (hgetObs : w.getNode (chainObserverId specs i) =
      some { kind := NodeKind.observer, sigLevel := 0,
             inputs := [chainBaseId specs i],
             outputs := [chainBaseId specs i + 2] })
    (hgetRep : w.getNode (chainRepId specs i 0) =
      some { kind := NodeKind.repeater (stageDelayAt specs i 0)
               (stagePriAt specs i 0),
             sigLevel := 0, inputs := [chainBaseId specs i + 1],
             outputs := [chainBaseId specs i + 3] }) :
    (w.onScheduledTick (chainObserverId specs i)).events =
      w.events ++ [stageEventOf T specs i 0] := by
  have hne : chainRepId specs i 0 ≠ chainObserverId specs i := by
    dsimp [chainRepId, chainObserverId]
    omega
  set ndObs : NodeData := { kind := NodeKind.observer, sigLevel := 0, inputs := [chainBaseId specs i], outputs := [chainBaseId specs i + 2] }
  set ndRep : NodeData := { kind := NodeKind.repeater (stageDelayAt specs i 0) (stagePriAt specs i 0), sigLevel := 0, inputs := [chainBaseId specs i + 1], outputs := [chainBaseId specs i + 3] }
  have heff := onScheduledTick_observer_schedules w
    (chainObserverId specs i) (chainRepId specs i 0) ndObs ndRep
    (stageDelayAt specs i 0) (stagePriAt specs i 0) hne hgetObs
    (by dsimp [ndObs]) (by dsimp [ndObs, chainRepId]) hgetRep
    (by dsimp [ndRep])
  rw [heff]
  have hev : { targetTick := w.tick + ↑(stageDelayAt specs i 0), priority := stagePriAt specs i 0, nodeId := chainRepId specs i 0 } = stageEventOf T specs i 0 := by
    dsimp [stageEventOf]
    have ht : w.tick + ↑(stageDelayAt specs i 0) = stageTickOf T specs i 0 := by
      rw [htick]
      dsimp [obsTickOf]
      rw [stageTickOf_zero]
    rw [ht]
  rw [hev]

/-- Firing chain `i`'s stage-`s` repeater spawns its stage-`s+1`
    event. -/
theorem fires_rep_stage (w : World) (T : Nat) (specs : List ChainSpec)
    (i s : Nat) (hs : s + 1 ≤ (specAt specs i).middleDelays.length)
    (htick : w.tick = stageTickOf T specs i s)
    (hgetRep : w.getNode (chainRepId specs i s) =
      some { kind := NodeKind.repeater (stageDelayAt specs i s)
               (stagePriAt specs i s),
             sigLevel := 0, inputs := [chainBaseId specs i + 1 + s],
             outputs := [chainBaseId specs i + 3 + s] })
    (hgetNext : w.getNode (chainRepId specs i (s + 1)) =
      some { kind := NodeKind.repeater (stageDelayAt specs i (s + 1))
               (stagePriAt specs i (s + 1)),
             sigLevel := 0, inputs := [chainBaseId specs i + 1 + (s + 1)],
             outputs := [chainBaseId specs i + 3 + (s + 1)] }) :
    (w.onScheduledTick (chainRepId specs i s)).events =
      w.events ++ [stageEventOf T specs i (s + 1)] := by
  have hne : chainRepId specs i (s + 1) ≠ chainRepId specs i s := by
    dsimp [chainRepId]
    omega
  set ndRep : NodeData := { kind := NodeKind.repeater (stageDelayAt specs i s) (stagePriAt specs i s), sigLevel := 0, inputs := [chainBaseId specs i + 1 + s], outputs := [chainBaseId specs i + 3 + s] }
  set ndNext : NodeData := { kind := NodeKind.repeater (stageDelayAt specs i (s + 1)) (stagePriAt specs i (s + 1)), sigLevel := 0, inputs := [chainBaseId specs i + 1 + (s + 1)], outputs := [chainBaseId specs i + 3 + (s + 1)] }
  have heff := onScheduledTick_repeater_schedules_next w
    (chainRepId specs i s) (chainRepId specs i (s + 1)) ndRep ndNext
    (stageDelayAt specs i s) (stagePriAt specs i s)
    (stagePriAt specs i (s + 1)) (stageDelayAt specs i (s + 1)) hne
    hgetRep (by dsimp [ndRep])
    (by dsimp [ndRep, chainRepId]; rw [List.cons.injEq]; simp; omega)
    hgetNext (by dsimp [ndNext])
  rw [heff]
  have hev : { targetTick := w.tick + ↑(stageDelayAt specs i (s + 1)), priority := stagePriAt specs i (s + 1), nodeId := chainRepId specs i (s + 1) } = stageEventOf T specs i (s + 1) := by
    dsimp [stageEventOf]
    have ht : w.tick + ↑(stageDelayAt specs i (s + 1)) = stageTickOf T specs i (s + 1) := by
      rw [htick]
      rw [← stageTickOf_succ T specs i s hs]
    rw [ht]
  rw [hev]

/-- Firing chain `i`'s last repeater adds no events. -/
theorem fires_lastRep_events (w : World)
    (specs : List ChainSpec) (i : Nat)
    (hgetRep : w.getNode (chainRepId specs i (repLenAt specs i)) =
      some { kind := NodeKind.repeater
               (stageDelayAt specs i (repLenAt specs i))
               (stagePriAt specs i (repLenAt specs i)),
             sigLevel := 0,
             inputs := [chainBaseId specs i + 1 + repLenAt specs i],
             outputs := [chainBaseId specs i + 3 + repLenAt specs i] })
    (hgetOut : w.getNode (chainOutputId specs i) =
      some { kind := NodeKind.output (chainName i), sigLevel := 0,
             inputs := [chainBaseId specs i + 2 + repLenAt specs i],
             outputs := [] }) :
    (w.onScheduledTick (chainRepId specs i (repLenAt specs i))).events =
      w.events := by
  have hne : chainOutputId specs i ≠ chainRepId specs i (repLenAt specs i) := by
    dsimp [chainOutputId, chainRepId, repLenAt]
    omega
  set ndRep : NodeData := { kind := NodeKind.repeater (stageDelayAt specs i (repLenAt specs i)) (stagePriAt specs i (repLenAt specs i)), sigLevel := 0, inputs := [chainBaseId specs i + 1 + repLenAt specs i], outputs := [chainBaseId specs i + 3 + repLenAt specs i] }
  set ndOut : NodeData := { kind := NodeKind.output (chainName i), sigLevel := 0, inputs := [chainBaseId specs i + 2 + repLenAt specs i], outputs := [] }
  obtain ⟨_, _, hevs⟩ := onScheduledTick_lastRep_logs w
    (chainRepId specs i (repLenAt specs i)) (chainOutputId specs i)
    ndRep ndOut (stageDelayAt specs i (repLenAt specs i))
    (stagePriAt specs i (repLenAt specs i)) (chainName i) hne hgetRep
    (by dsimp [ndRep]) (by dsimp [ndRep, chainOutputId, repLenAt])
    hgetOut (by dsimp [ndOut])
  exact hevs

/-- Firing chain `i`'s last repeater appends exactly one log
    entry. -/
theorem fires_lastRep_log (w : World)
    (specs : List ChainSpec) (i : Nat)
    (hgetRep : w.getNode (chainRepId specs i (repLenAt specs i)) =
      some { kind := NodeKind.repeater
               (stageDelayAt specs i (repLenAt specs i))
               (stagePriAt specs i (repLenAt specs i)),
             sigLevel := 0,
             inputs := [chainBaseId specs i + 1 + repLenAt specs i],
             outputs := [chainBaseId specs i + 3 + repLenAt specs i] })
    (hgetOut : w.getNode (chainOutputId specs i) =
      some { kind := NodeKind.output (chainName i), sigLevel := 0,
             inputs := [chainBaseId specs i + 2 + repLenAt specs i],
             outputs := [] }) :
    ∃ msg, (w.onScheduledTick (chainRepId specs i (repLenAt specs i))).outputLog = w.outputLog ++ [msg] := by
  have hne : chainOutputId specs i ≠ chainRepId specs i (repLenAt specs i) := by
    dsimp [chainOutputId, chainRepId, repLenAt]
    omega
  set ndRep : NodeData := { kind := NodeKind.repeater (stageDelayAt specs i (repLenAt specs i)) (stagePriAt specs i (repLenAt specs i)), sigLevel := 0, inputs := [chainBaseId specs i + 1 + repLenAt specs i], outputs := [chainBaseId specs i + 3 + repLenAt specs i] }
  set ndOut : NodeData := { kind := NodeKind.output (chainName i), sigLevel := 0, inputs := [chainBaseId specs i + 2 + repLenAt specs i], outputs := [] }
  obtain ⟨msg, hlog, _⟩ := onScheduledTick_lastRep_logs w
    (chainRepId specs i (repLenAt specs i)) (chainOutputId specs i)
    ndRep ndOut (stageDelayAt specs i (repLenAt specs i))
    (stagePriAt specs i (repLenAt specs i)) (chainName i) hne hgetRep
    (by dsimp [ndRep]) (by dsimp [ndRep, chainOutputId, repLenAt])
    hgetOut (by dsimp [ndOut])
  exact ⟨msg, hlog⟩

/-! ## Spawn transport

Popped events fire in pop order and append their spawns; the spawn lists
therefore appear as sublists of the resulting event queue. -/

/-- The empty list is a sublist of any list. -/
private theorem nil_sublist_of (l : List ScheduledEvent) : [] <+ l := by
  induction l with
  | nil => exact Sublist.slnil
  | cons x xs ih => exact Sublist.cons x ih

/-- A sublist stays a sublist when the host gains a prefix. -/
private theorem sublist_prefix_extend {α : Type} (v t u : List α)
    (h : t <+ u) : t <+ v ++ u := by
  induction v generalizing t u with
  | nil => simpa using h
  | cons x xs ih => exact Sublist.cons x (ih t u h)

/-- Prepending the same prefix preserves sublist. -/
private theorem cons_append_sublist {α : Type} (g l₁ l₂ : List α)
    (h : l₁ <+ l₂) : g ++ l₁ <+ g ++ l₂ := by
  induction g with
  | nil => simpa using h
  | cons x xs ih => exact Sublist.cons_cons x ih

/-- `spawnFold` over a sublist embeds into `spawnFold` over the whole
    list. -/
theorem spawnFold_sublist (spawn : ScheduledEvent → List ScheduledEvent)
    {es l : List ScheduledEvent} (h : es <+ l) :
    spawnFold spawn es <+ spawnFold spawn l := by
  induction h with
  | slnil =>
    dsimp [spawnFold]
    exact Sublist.slnil
  | cons a h ih =>
    dsimp [spawnFold]
    exact sublist_prefix_extend (spawn a) _ _ ih
  | cons_cons a h ih =>
    dsimp [spawnFold]
    exact cons_append_sublist (spawn a) _ _ ih

/-- Spawns of the first `n` pops accumulate as a sublist, behind an
    existing not-due carry. -/
theorem processNEvents_spawn_sublist (w : World) (n : Nat)
    (acc : List ScheduledEvent)
    (spawn : ScheduledEvent → List ScheduledEvent)
    (hacc : acc <+ w.events)
    (haccFut : ∀ e ∈ acc, e.targetTick ≠ w.tick)
    (hfut : ∀ (v : World) (e : ScheduledEvent), e ∈ v.events →
        e.targetTick = v.tick → ∀ e' ∈ spawn e, e'.targetTick > v.tick)
    (hfire : ∀ (v : World) (e : ScheduledEvent) (wp : World),
        v.popNextEvent = some (e, wp) →
        (wp.onScheduledTick e.nodeId).events = wp.events ++ spawn e) :
    acc ++ spawnFold spawn ((popSeq w).take n) <+
      (processNEvents w n).events := by
  induction n generalizing w acc with
  | zero =>
    dsimp [processNEvents, List.take, spawnFold]
    rw [List.append_nil]
    exact hacc
  | succ n ih =>
    dsimp [processNEvents]
    cases hstep : w.step with
    | none =>
      have hnone : w.popNextEvent = none := by
        dsimp [World.step] at hstep
        cases hp : w.popNextEvent <;> simp_all
      rw [popSeq_of_popNextEvent_none w hnone]
      dsimp [List.take, spawnFold]
      rw [List.append_nil]
      exact hacc
    | some w1 =>
      dsimp [World.step] at hstep
      cases hpop : w.popNextEvent with
      | none => simp [hpop] at hstep
      | some pr =>
        rcases pr with ⟨e, wp⟩
        have hw1 : w1 = wp.onScheduledTick e.nodeId := by
          apply Eq.symm
          simpa [World.step, hpop] using hstep
        subst hw1
        set w1' := wp.onScheduledTick e.nodeId with hw1'
        have hseq : popSeq w = e :: popSeq w1' := by
          rw [popSeq_of_popNextEvent_some w e wp hpop, hw1']
        rw [hseq, List.take_succ_cons]
        dsimp [spawnFold]
        rw [← List.append_assoc]
        have hdue := popSeq_mem_due w e
          (by rw [hseq]; exact List.mem_cons.mpr (Or.inl rfl))
        have haccWp : acc <+ wp.events := by
          obtain ⟨idx, hidx, herase, htickE, hget⟩ :=
            popNextEvent_eraseIdx w e wp hpop
          rw [herase]
          apply sublist_eraseIdx_of_notMem_nth hacc idx hidx
          rw [hget]
          intro he
          exact haccFut e he htickE
        have htickW1 : w1'.tick = w.tick := by
          dsimp [w1']
          rw [World.onScheduledTick_tick,
            World.popNextEvent_tick w e wp hpop]
        have hacc' : acc ++ spawn e <+ w1'.events := by
          have hfireE := hfire w e wp hpop
          dsimp [w1'] at hfireE ⊢
          rw [hfireE]
          exact Sublist.append haccWp (Sublist.refl (spawn e))
        have haccFut' : ∀ e' ∈ acc ++ spawn e, e'.targetTick ≠ w1'.tick := by
          intro e' he'
          rw [htickW1]
          rcases List.mem_append.mp he' with he' | he'
          · exact haccFut e' he'
          · have := hfut w e hdue.2 hdue.1 e' he'
            omega
        exact ih w1' (acc ++ spawn e) hacc' haccFut'

/-- Spawns of the first `n` pops accumulate as a sublist. -/
theorem processNEvents_spawns_sublist (w : World) (n : Nat)
    (spawn : ScheduledEvent → List ScheduledEvent)
    (hfut : ∀ (v : World) (e : ScheduledEvent), e ∈ v.events →
        e.targetTick = v.tick → ∀ e' ∈ spawn e, e'.targetTick > v.tick)
    (hfire : ∀ (v : World) (e : ScheduledEvent) (wp : World),
        v.popNextEvent = some (e, wp) →
        (wp.onScheduledTick e.nodeId).events = wp.events ++ spawn e) :
    spawnFold spawn ((popSeq w).take n) <+
      (processNEvents w n).events := by
  have := processNEvents_spawn_sublist w n [] spawn
    (nil_sublist_of w.events) (by simp) hfut hfire
  simpa using this

/-- The drain fires the whole pop sequence, so the spawns of any sublist
    of pops embed into the drained world's events. -/
theorem stepUNT_spawn_sublist (w : World)
    (spawn : ScheduledEvent → List ScheduledEvent)
    (logLen : ScheduledEvent → Nat)
    (hfut : ∀ (v : World) (e : ScheduledEvent), e ∈ v.events →
        e.targetTick = v.tick → ∀ e' ∈ spawn e, e'.targetTick > v.tick)
    (hfire : ∀ (v : World) (k : Nat) (hk : k < (popSeq v).length)
        (u : World),
        u.tick = v.tick →
        u.events = eraseEvents v.events ((popSeq v).take (k + 1)) ++
            spawnFold spawn ((popSeq v).take k) →
        (∀ id, id ∉ ((popSeq v).take k).map (fun e => e.nodeId) →
          u.getNode id = v.getNode id) →
        ∃ msgs : List String,
          (u.onScheduledTick ((popSeq v)[k]'hk).nodeId).events =
            u.events ++ spawn ((popSeq v)[k]'hk) ∧
          (u.onScheduledTick ((popSeq v)[k]'hk).nodeId).outputLog =
            u.outputLog ++ msgs ∧
          msgs.length = logLen ((popSeq v)[k]'hk) ∧
          ∀ id, id ≠ ((popSeq v)[k]'hk).nodeId →
            (u.onScheduledTick ((popSeq v)[k]'hk).nodeId).getNode id =
              u.getNode id)
    (es : List ScheduledEvent) (hes : es <+ popSeq w) :
    spawnFold spawn es <+ w.stepUntilNextTick.events := by
  obtain ⟨_, hevs, _, _, _⟩ :=
    stepUntilNextTick_general_drain w spawn logLen hfut hfire
  rw [hevs]
  exact sublist_prefix_extend (eraseEvents w.events (popSeq w))
    (spawnFold spawn es) (spawnFold spawn (popSeq w))
    (spawnFold_sublist spawn hes)

/-! ## Burst-level spawn transport -/

private theorem take_add_take_drop {α : Type} (l : List α) (a b : Nat) :
    l.take (a + b) = l.take a ++ (l.drop a).take b := by
  revert l
  induction a with
  | zero => intro l; simp
  | succ a' ih =>
    intro l
    cases l with
    | nil => simp
    | cons x xs =>
      have hidx : a' + 1 + b = (a' + b) + 1 := by omega
      rw [hidx, List.take_succ_cons, List.take_succ_cons]
      dsimp [List.drop]
      rw [ih xs]

private theorem drop_drop_add {α : Type} (l : List α) (a b : Nat) :
    (l.drop a).drop b = l.drop (a + b) := by
  revert l
  induction a with
  | zero => intro l; simp
  | succ a' ih =>
    intro l
    cases l with
    | nil => simp
    | cons x xs =>
      have hidx : a' + 1 + b = (a' + b) + 1 := by omega
      rw [hidx]
      dsimp [List.drop]
      exact ih xs

theorem spawnFold_append (spawn : ScheduledEvent → List ScheduledEvent)
    (l₁ l₂ : List ScheduledEvent) :
    spawnFold spawn (l₁ ++ l₂) =
      spawnFold spawn l₁ ++ spawnFold spawn l₂ := by
  induction l₁ with
  | nil => dsimp [spawnFold]
  | cons x xs ih =>
    change spawn x ++ spawnFold spawn (xs ++ l₂) =
      (spawn x ++ spawnFold spawn xs) ++ spawnFold spawn l₂
    rw [ih, List.append_assoc]

/-- Membership in a `spawnFold` comes from one of the spawn lists. -/
theorem mem_spawnFold (spawn : ScheduledEvent → List ScheduledEvent)
    (l : List ScheduledEvent) (e : ScheduledEvent)
    (h : e ∈ spawnFold spawn l) : ∃ x ∈ l, e ∈ spawn x := by
  induction l with
  | nil => dsimp [spawnFold] at h; cases h
  | cons x xs ih =>
    dsimp [spawnFold] at h
    rcases List.mem_append.mp h with h | h
    · exact ⟨x, List.mem_cons.mpr (Or.inl rfl), h⟩
    · obtain ⟨y, hy, hye⟩ := ih h
      exact ⟨y, List.mem_cons.mpr (Or.inr hy), hye⟩

/-- The spawns of the events a burst pops appear in pop order as a
    sublist of the burst's final events, behind any not-due carry; the
    burst's remaining pop sequence is the corresponding suffix. -/
theorem simBurst_spawn_sublist (t : Nat) (observers : List Nat)
    (pos : Nat → Nat → Nat) (w : World) (pairs : List (Nat × Nat))
    (acc : List ScheduledEvent)
    (spawn : ScheduledEvent → List ScheduledEvent)
    (hacc : acc <+ w.events)
    (haccFut : ∀ e ∈ acc, e.targetTick ≠ w.tick)
    (hfut : ∀ (v : World) (e : ScheduledEvent), e ∈ v.events →
        e.targetTick = v.tick → ∀ e' ∈ spawn e, e'.targetTick > v.tick)
    (hfire : ∀ (v : World) (e : ScheduledEvent) (wp : World),
        v.popNextEvent = some (e, wp) →
        (wp.onScheduledTick e.nodeId).events = wp.events ++ spawn e) :
    ∃ m, acc ++ spawnFold spawn ((popSeq w).take m) <+
        (simBurst t observers pos w pairs).events ∧
      popSeq (simBurst t observers pos w pairs) = (popSeq w).drop m := by
  induction pairs generalizing w acc with
  | nil =>
    refine ⟨0, ?_, ?_⟩
    · simp [simBurst, List.take, spawnFold]
      exact hacc
    · simp [simBurst]
  | cons p ps ih =>
    cases p with
    | mk i k =>
      dsimp [simBurst]
      set nProc := pos t k with hnProc
      set wP := processNEvents w nProc with hwP
      have hspawnP := processNEvents_spawn_sublist w nProc acc spawn
        hacc haccFut hfut hfire
      have htickP : wP.tick = w.tick := by
        dsimp [wP]
        rw [processNEvents_tick]
      have hfutP : ∀ e ∈ acc ++ spawnFold spawn ((popSeq w).take nProc),
          e.targetTick ≠ wP.tick := by
        intro e he
        rw [htickP]
        rcases List.mem_append.mp he with he | he
        · exact haccFut e he
        · obtain ⟨x, hx, hex⟩ := mem_spawnFold spawn _ e he
          have hdue := popSeq_mem_due w x (List.mem_of_mem_take hx)
          have := hfut w x hdue.2 hdue.1 e hex
          omega
      have hpopP : popSeq wP = (popSeq w).drop nProc := by
        dsimp [wP]
        rw [popSeq_processNEvents]
      by_cases hsome : ∃ oid, observers[i]? = some oid
      · obtain ⟨oid, hobs⟩ := hsome
        rw [hobs]
        dsimp
        set wA := activateChain wP oid with hwA
        have haccA : acc ++ spawnFold spawn ((popSeq w).take nProc) <+
            wA.events := by
          dsimp [wA]
          rw [activateChain_events]
          apply sublist_append_of_sublist_left
          exact hspawnP
        have hfutA : ∀ e ∈ acc ++ spawnFold spawn ((popSeq w).take nProc),
            e.targetTick ≠ wA.tick := by
          intro e he
          dsimp [wA]
          rw [activateChain_tick]
          exact hfutP e he
        obtain ⟨m1, hsub1, hdrop1⟩ := ih wA
          (acc ++ spawnFold spawn ((popSeq w).take nProc)) haccA hfutA
        refine ⟨nProc + m1, ?_, ?_⟩
        · change acc ++ spawnFold spawn ((popSeq w).take (nProc + m1)) <+
            (simBurst t observers pos wA ps).events
          rw [take_add_take_drop, spawnFold_append, ← List.append_assoc]
          rw [popSeq_activateChain, hpopP] at hsub1
          exact hsub1
        · change popSeq (simBurst t observers pos wA ps) =
            (popSeq w).drop (nProc + m1)
          rw [hdrop1, popSeq_activateChain, hpopP, drop_drop_add]
      · have hnone : observers[i]? = none := by
          cases h : observers[i]? with
          | none => rfl
          | some oid => exfalso; exact hsome ⟨oid, h⟩
        rw [hnone]
        dsimp
        obtain ⟨m1, hsub1, hdrop1⟩ := ih wP
          (acc ++ spawnFold spawn ((popSeq w).take nProc)) hspawnP hfutP
        refine ⟨nProc + m1, ?_, ?_⟩
        · change acc ++ spawnFold spawn ((popSeq w).take (nProc + m1)) <+
            (simBurst t observers pos wP ps).events
          rw [take_add_take_drop, spawnFold_append, ← List.append_assoc]
          rw [hpopP] at hsub1
          exact hsub1
        · change popSeq (simBurst t observers pos wP ps) =
            (popSeq w).drop (nProc + m1)
          rw [hdrop1, hpopP, drop_drop_add]

/-! ## One simBody tick -/

/-- The spawns of every event popped across a whole `simBody` tick
    (burst pops and drain pops together) appear in pop order as a
    sublist of the next tick-start world's events. -/
theorem simBody_spawn_sublist (actTick : Nat → Nat)
    (observers actOrd : List Nat) (pos : Nat → Nat → Nat) (w : World)
    (k : Nat) (spawn : ScheduledEvent → List ScheduledEvent)
    (logLen : ScheduledEvent → Nat)
    (hfut : ∀ (v : World) (e : ScheduledEvent), e ∈ v.events →
        e.targetTick = v.tick → ∀ e' ∈ spawn e, e'.targetTick > v.tick)
    (hfirePop : ∀ (v : World) (e : ScheduledEvent) (wp : World),
        v.popNextEvent = some (e, wp) →
        (wp.onScheduledTick e.nodeId).events = wp.events ++ spawn e)
    (hfireDrain : ∀ (v : World) (kk : Nat)
        (hk : kk < (popSeq v).length) (u : World),
        u.tick = v.tick →
        u.events = eraseEvents v.events ((popSeq v).take (kk + 1)) ++
            spawnFold spawn ((popSeq v).take kk) →
        (∀ id, id ∉ ((popSeq v).take kk).map (fun e => e.nodeId) →
          u.getNode id = v.getNode id) →
        ∃ msgs : List String,
          (u.onScheduledTick ((popSeq v)[kk]'hk).nodeId).events =
            u.events ++ spawn ((popSeq v)[kk]'hk) ∧
          (u.onScheduledTick ((popSeq v)[kk]'hk).nodeId).outputLog =
            u.outputLog ++ msgs ∧
          msgs.length = logLen ((popSeq v)[kk]'hk) ∧
          ∀ id, id ≠ ((popSeq v)[kk]'hk).nodeId →
            (u.onScheduledTick ((popSeq v)[kk]'hk).nodeId).getNode id =
              u.getNode id) :
    spawnFold spawn (popSeq w) <+
      (simBody actTick observers actOrd pos w k).events := by
  dsimp [simBody]
  set wL := w.logOutput s!"tick {w.tick}" with hwL
  have hpopL : popSeq wL = popSeq w := by
    apply popSeq_congr_due wL w
    · rw [hwL]
      exact World.logOutput_tick w _
    · rw [hwL]
      dsimp [wL, World.logOutput]
  set active := actOrd.filter (fun i =>
    decide (i < observers.length) && (actTick i == w.tick)) with hactive
  set wB := simBurst w.tick observers pos wL active.zipIdx with hwB
  obtain ⟨m, hsubB, hdropB⟩ := simBurst_spawn_sublist w.tick observers pos
    wL active.zipIdx [] spawn (nil_sublist_of wL.events) (by simp)
    hfut hfirePop
  have hsubB' : spawnFold spawn ((popSeq wL).take m) <+ wB.events := by
    simpa using hsubB
  have htickBL : wB.tick = wL.tick := by
    dsimp [wB]
    rw [simBurst_tick]
  have hburstFut : ∀ e ∈ spawnFold spawn ((popSeq wL).take m),
      e.targetTick ≠ wB.tick := by
    intro e he
    obtain ⟨x, hx, hex⟩ := mem_spawnFold spawn _ e he
    have hdue := popSeq_mem_due wL x (List.mem_of_mem_take hx)
    have := hfut wL x hdue.2 hdue.1 e hex
    rw [htickBL]
    omega
  have herase : spawnFold spawn ((popSeq wL).take m) <+
      eraseEvents wB.events (popSeq wB) := by
    apply eraseEvents_sublist_of_notMem (popSeq wB) hsubB'
    intro e he hm
    have hdue := popSeq_mem_due wB e he
    exact hburstFut e hm hdue.1
  have hES : (popSeq wL).drop m <+ popSeq wB := by
    rw [hdropB]
  have htail : spawnFold spawn ((popSeq wL).drop m) <+
      spawnFold spawn (popSeq wB) := by
    rw [hdropB]
  obtain ⟨_, hevs, _, _, _⟩ :=
    stepUntilNextTick_general_drain wB spawn logLen hfut hfireDrain
  have hsplit : spawnFold spawn (popSeq wL) =
      spawnFold spawn ((popSeq wL).take m) ++
        spawnFold spawn ((popSeq wL).drop m) := by
    rw [← spawnFold_append]
    congr 1
    exact (List.take_append_drop m (popSeq wL)).symm
  rw [← hpopL, hsplit, hevs]
  exact Sublist.append herase htail

/-! ## Wiring stability

Firing a node only updates its `sigLevel`; kind, inputs and outputs are
permanent. The firing obligations below are therefore stated against
kind/wiring hypotheses only. -/

/-- The wiring triple of a node. -/
def wiring (nd : NodeData) : NodeKind × List Nat × List Nat :=
  (nd.kind, nd.inputs, nd.outputs)

/-- `onNeighborUpdate` changes no node lookup. -/
theorem onNeighborUpdate_getNode (w : World) (nid id : Nat) :
    (w.onNeighborUpdate nid).getNode id = w.getNode id := by
  dsimp [World.onNeighborUpdate]
  split
  · rfl
  · split <;> dsimp [World.scheduleEvent, World.logOutput] <;> rfl

/-- A fold of `onNeighborUpdate`s changes no node lookup. -/
private theorem foldl_onNeighborUpdate_getNode (outs : List Nat)
    (w : World) (id : Nat) :
    (outs.foldl (fun w' outId => w'.onNeighborUpdate outId) w).getNode id =
      w.getNode id := by
  induction outs generalizing w with
  | nil => dsimp [List.foldl]
  | cons o os ih =>
    rw [List.foldl_cons]
    rw [ih (w.onNeighborUpdate o), onNeighborUpdate_getNode]

/-- `notifyOutputs` changes no node lookup. -/
theorem notifyOutputs_getNode (w : World) (nid id : Nat) :
    (w.notifyOutputs nid).getNode id = w.getNode id := by
  dsimp [World.notifyOutputs]
  cases hget : w.getNode nid with
  | none => rfl
  | some nd =>
    exact foldl_onNeighborUpdate_getNode nd.outputs w id

/-- Firing preserves kind, inputs and outputs of every node. -/
theorem onScheduledTick_getNode_wiring (w : World) (nid id : Nat) :
    ((w.onScheduledTick nid).getNode id).map wiring =
      (w.getNode id).map wiring := by
  dsimp [World.onScheduledTick]
  split
  · rfl
  · rename_i nd hget
    cases hkind : nd.kind
    · rfl
    · rfl
    · dsimp
      rw [notifyOutputs_getNode]
      by_cases hid : id = nid
      · subst hid
        rw [getNode_updateNode_map]
        cases hgi : w.getNode id with
        | none => dsimp [Option.map]
        | some nd' =>
          dsimp [Option.map]
          congr 1
      · rw [getNode_updateNode_ne w nid id _ hid]
    · dsimp
      rw [notifyOutputs_getNode]
      by_cases hid : id = nid
      · subst hid
        rw [getNode_updateNode_map]
        cases hgi : w.getNode id with
        | none => dsimp [Option.map]
        | some nd' =>
          dsimp [Option.map]
          congr 1
      · rw [getNode_updateNode_ne w nid id _ hid]

/-- One pop preserves wiring. -/
theorem step_getNode_wiring (w w' : World)
    (hstep : w.step = some w') (id : Nat) :
    (w'.getNode id).map wiring = (w.getNode id).map wiring := by
  dsimp [World.step] at hstep
  cases hpop : w.popNextEvent with
  | none => simp [hpop] at hstep
  | some pr =>
    rcases pr with ⟨e, wp⟩
    have hw' : w' = wp.onScheduledTick e.nodeId := by
      apply Eq.symm
      simpa [World.step, hpop] using hstep
    rw [hw', onScheduledTick_getNode_wiring]
    congr 1
    exact World.getNode_of_nodes_eq _ _ (popNextEvent_nodes w e wp hpop) id

/-- `processNEvents` preserves wiring. -/
theorem processNEvents_getNode_wiring (w : World) (n : Nat) (id : Nat) :
    ((processNEvents w n).getNode id).map wiring =
      (w.getNode id).map wiring := by
  induction n generalizing w with
  | zero => dsimp [processNEvents]
  | succ n ih =>
    dsimp [processNEvents]
    cases hstep : w.step with
    | none => rfl
    | some w' =>
      rw [ih w']
      exact step_getNode_wiring w w' hstep id

/-- `activateChain` preserves wiring. -/
theorem activateChain_getNode_wiring (w : World) (obs id : Nat) :
    ((activateChain w obs).getNode id).map wiring =
      (w.getNode id).map wiring := by
  dsimp [activateChain, World.scheduleEvent, World.getNode]

/-- `simBurst` preserves wiring. -/
theorem simBurst_getNode_wiring (t : Nat) (observers : List Nat)
    (pos : Nat → Nat → Nat) (w : World) (pairs : List (Nat × Nat))
    (id : Nat) :
    ((simBurst t observers pos w pairs).getNode id).map wiring =
      (w.getNode id).map wiring := by
  induction pairs generalizing w with
  | nil => dsimp [simBurst]
  | cons p ps ih =>
    dsimp [simBurst]
    cases p with
    | mk i k =>
      dsimp
      cases hobs : observers[i]? with
      | none =>
        dsimp
        change Option.map wiring
            ((simBurst t observers pos (processNEvents w (pos t k)) ps).getNode id) =
          Option.map wiring (w.getNode id)
        rw [ih, processNEvents_getNode_wiring]
      | some oid =>
        dsimp
        change Option.map wiring
            ((simBurst t observers pos (activateChain (processNEvents w (pos t k)) oid) ps).getNode id) =
          Option.map wiring (w.getNode id)
        rw [ih, activateChain_getNode_wiring,
          processNEvents_getNode_wiring]

/-- `stepUntilNextTick` preserves wiring. -/
theorem stepUNT_getNode_wiring (w : World) (id : Nat) :
    (w.stepUntilNextTick.getNode id).map wiring =
      (w.getNode id).map wiring := by
  induction w using World.stepUntilNextTick.induct with
  | case1 x hstep =>
    rw [stepUntilNextTick_of_step_none x hstep]
    dsimp [World.getNode]
  | case2 x w' hstep ih =>
    have hsunt : x.stepUntilNextTick = w'.stepUntilNextTick := by
      rw [World.stepUntilNextTick, hstep]
    rw [hsunt, ih]
    exact step_getNode_wiring x w' hstep id

/-- One `simBody` tick preserves wiring. -/
theorem simBody_getNode_wiring (actTick : Nat → Nat)
    (observers actOrd : List Nat) (pos : Nat → Nat → Nat) (w : World)
    (k id : Nat) :
    ((simBody actTick observers actOrd pos w k).getNode id).map wiring =
      (w.getNode id).map wiring := by
  dsimp [simBody]
  rw [stepUNT_getNode_wiring, simBurst_getNode_wiring]
  dsimp [World.logOutput, World.getNode]

/-- Wiring in a tick-start world is the built wiring. -/
theorem simWorld_getNode_wiring (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat) (t id : Nat) :
    ((simWorld T specs actOrd pos t).getNode id).map wiring =
      ((buildChains specs).1.getNode id).map wiring := by
  induction t with
  | zero => simp [simWorld, simFoldl]
  | succ t ih =>
    rw [simWorld_succ, simBody_getNode_wiring]
    exact ih

/-- A chain's stage repeater keeps its kind and output wiring in every
    tick-start world. -/
theorem simWorld_rep_wiring (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat) (t i s : Nat)
    (hi : i < specs.length) (hpri : (specAt specs i).priLenOk)
    (hs : s ≤ (specAt specs i).middleDelays.length) :
    ∃ nd, (simWorld T specs actOrd pos t).getNode (chainRepId specs i s) =
        some nd ∧
      nd.kind = NodeKind.repeater (stageDelayAt specs i s)
        (stagePriAt specs i s) ∧
      nd.outputs = [chainBaseId specs i + 3 + s] := by
  have hw := simWorld_getNode_wiring T specs actOrd pos t
    (chainRepId specs i s)
  rw [buildChains_getNode_rep specs i s hi hpri hs] at hw
  dsimp [wiring] at hw
  cases hget : (simWorld T specs actOrd pos t).getNode
      (chainRepId specs i s) with
  | none =>
    rw [hget] at hw
    dsimp [Option.map] at hw
    cases hw
  | some nd =>
    rw [hget] at hw
    dsimp [Option.map] at hw
    injection hw with htriple
    dsimp [wiring] at htriple
    have hkind : nd.kind = NodeKind.repeater (stageDelayAt specs i s)
        (stagePriAt specs i s) :=
      congrArg Prod.fst htriple
    have hout : nd.outputs = [chainBaseId specs i + 3 + s] := by
      have := congrArg Prod.snd htriple
      rw [Prod.mk.injEq] at this
      exact this.2
    exact ⟨nd, rfl, hkind, hout⟩

/-! ## Kind-form firing obligations

Stated against kind/wiring hypotheses only (sigLevel is irrelevant to
what gets appended), so the permanent wiring facts instantiate them. -/

/-- Firing chain `i`'s observer spawns its stage-0 event. -/
theorem fires_observer_stage0_kind (w : World) (T : Nat)
    (specs : List ChainSpec) (i : Nat)
    (htick : w.tick = obsTickOf T specs i)
    (hobs : ∃ nd, w.getNode (chainObserverId specs i) = some nd ∧
      nd.kind = NodeKind.observer ∧ nd.outputs = [chainRepId specs i 0])
    (hrep : ∃ nd, w.getNode (chainRepId specs i 0) = some nd ∧
      nd.kind = NodeKind.repeater (stageDelayAt specs i 0)
        (stagePriAt specs i 0)) :
    (w.onScheduledTick (chainObserverId specs i)).events =
      w.events ++ [stageEventOf T specs i 0] := by
  obtain ⟨ndObs, hgetObs, hkindObs, houtsObs⟩ := hobs
  obtain ⟨ndRep, hgetRep, hkindRep⟩ := hrep
  have hne : chainRepId specs i 0 ≠ chainObserverId specs i := by
    dsimp [chainRepId, chainObserverId]
    omega
  have heff := onScheduledTick_observer_schedules w
    (chainObserverId specs i) (chainRepId specs i 0) ndObs ndRep
    (stageDelayAt specs i 0) (stagePriAt specs i 0) hne hgetObs hkindObs
    houtsObs hgetRep hkindRep
  rw [heff]
  have htick0 : w.tick + ↑(stageDelayAt specs i 0) =
      stageTickOf T specs i 0 := by
    rw [htick]
    dsimp [obsTickOf]
    rw [stageTickOf_zero]
  rw [htick0]
  rfl

/-- Firing chain `i`'s stage-`s` repeater spawns its stage-`s+1`
    event. -/
theorem fires_rep_stage_kind (w : World) (T : Nat)
    (specs : List ChainSpec) (i s : Nat)
    (hs : s + 1 ≤ (specAt specs i).middleDelays.length)
    (htick : w.tick = stageTickOf T specs i s)
    (hrep : ∃ nd, w.getNode (chainRepId specs i s) = some nd ∧
      nd.kind = NodeKind.repeater (stageDelayAt specs i s)
        (stagePriAt specs i s) ∧
      nd.outputs = [chainRepId specs i (s + 1)])
    (hnext : ∃ nd, w.getNode (chainRepId specs i (s + 1)) = some nd ∧
      nd.kind = NodeKind.repeater (stageDelayAt specs i (s + 1))
        (stagePriAt specs i (s + 1))) :
    (w.onScheduledTick (chainRepId specs i s)).events =
      w.events ++ [stageEventOf T specs i (s + 1)] := by
  obtain ⟨ndRep, hgetRep, hkindRep, houtsRep⟩ := hrep
  obtain ⟨ndNext, hgetNext, hkindNext⟩ := hnext
  have hne : chainRepId specs i (s + 1) ≠ chainRepId specs i s := by
    dsimp [chainRepId]
    omega
  have heff := onScheduledTick_repeater_schedules_next w
    (chainRepId specs i s) (chainRepId specs i (s + 1)) ndRep ndNext
    (stageDelayAt specs i s) (stagePriAt specs i s)
    (stagePriAt specs i (s + 1)) (stageDelayAt specs i (s + 1)) hne
    hgetRep hkindRep houtsRep hgetNext hkindNext
  rw [heff]
  have htickS : w.tick + ↑(stageDelayAt specs i (s + 1)) =
      stageTickOf T specs i (s + 1) := by
    rw [htick]
    rw [← stageTickOf_succ T specs i s hs]
  rw [htickS]
  rfl

/-- Firing chain `i`'s last repeater adds no events. -/
theorem fires_lastRep_events_kind (w : World)
    (specs : List ChainSpec) (i : Nat)
    (hrep : ∃ nd, w.getNode (chainRepId specs i (repLenAt specs i)) =
        some nd ∧
      nd.kind = NodeKind.repeater (stageDelayAt specs i (repLenAt specs i))
        (stagePriAt specs i (repLenAt specs i)) ∧
      nd.outputs = [chainOutputId specs i])
    (hout : ∃ nd, w.getNode (chainOutputId specs i) = some nd ∧
      nd.kind = NodeKind.output (chainName i)) :
    (w.onScheduledTick (chainRepId specs i (repLenAt specs i))).events =
      w.events := by
  obtain ⟨ndRep, hgetRep, hkindRep, houtsRep⟩ := hrep
  obtain ⟨ndOut, hgetOut, hkindOut⟩ := hout
  have hne : chainOutputId specs i ≠ chainRepId specs i (repLenAt specs i) := by
    dsimp [chainOutputId, chainRepId, repLenAt]
    omega
  obtain ⟨_, _, hevs⟩ := onScheduledTick_lastRep_logs w
    (chainRepId specs i (repLenAt specs i)) (chainOutputId specs i)
    ndRep ndOut (stageDelayAt specs i (repLenAt specs i))
    (stagePriAt specs i (repLenAt specs i)) (chainName i) hne hgetRep
    hkindRep houtsRep hgetOut hkindOut
  exact hevs

/-- Firing chain `i`'s last repeater appends exactly one log
    entry. -/
theorem fires_lastRep_log_kind (w : World)
    (specs : List ChainSpec) (i : Nat)
    (hrep : ∃ nd, w.getNode (chainRepId specs i (repLenAt specs i)) =
        some nd ∧
      nd.kind = NodeKind.repeater (stageDelayAt specs i (repLenAt specs i))
        (stagePriAt specs i (repLenAt specs i)) ∧
      nd.outputs = [chainOutputId specs i])
    (hout : ∃ nd, w.getNode (chainOutputId specs i) = some nd ∧
      nd.kind = NodeKind.output (chainName i)) :
    ∃ msg, (w.onScheduledTick (chainRepId specs i (repLenAt specs i))).outputLog = w.outputLog ++ [msg] := by
  obtain ⟨ndRep, hgetRep, hkindRep, houtsRep⟩ := hrep
  obtain ⟨ndOut, hgetOut, hkindOut⟩ := hout
  have hne : chainOutputId specs i ≠ chainRepId specs i (repLenAt specs i) := by
    dsimp [chainOutputId, chainRepId, repLenAt]
    omega
  obtain ⟨msg, hlog, _⟩ := onScheduledTick_lastRep_logs w
    (chainRepId specs i (repLenAt specs i)) (chainOutputId specs i)
    ndRep ndOut (stageDelayAt specs i (repLenAt specs i))
    (stagePriAt specs i (repLenAt specs i)) (chainName i) hne hgetRep
    hkindRep houtsRep hgetOut hkindOut
  exact ⟨msg, hlog⟩

