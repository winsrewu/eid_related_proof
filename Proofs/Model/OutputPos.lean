import Proofs.Model.LogBridge

open BasicRedstoneSim
open World
open List

/-! # Output position = last-repeater firing order

Connect the string-based `outputPos` to the event-based pop sequence: the
output position of chain `i` is `T + 1` plus the position of chain `i`'s
last-repeater event in `popSeq (simWorld T specs actOrd pos T)`. -/

/-- The tick markers logged through tick `n - 1`. -/
def tickLog (n : Nat) : List String :=
  (List.range n).map (fun t => s!"tick {t}")

/-- Tick markers are never output entries. -/
theorem tickLog_isOutputEntry (n i : Nat) :
    ∀ a ∈ tickLog n, isOutputEntry a i = false := by
  intro a ha
  dsimp [tickLog] at ha
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ha
  exact isOutputEntry_tick t i

/-- `tickLog (T + 1)` appends the tick-`T` marker. -/
theorem tickLog_succ (T : Nat) : tickLog (T + 1) = tickLog T ++ [s!"tick {T}"] := by
  dsimp [tickLog]
  rw [List.range_succ]
  simp [List.map_append]

/-- `tickLog n` has length `n`. -/
theorem tickLog_length (n : Nat) : (tickLog n).length = n := by
  dsimp [tickLog]
  simp

/-- A valid chain's total delay is at least 4 (observer +2 plus the last
    delay ≥ 2). -/
theorem chainDelay_ge3 (specs : List ChainSpec) (i : Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (hi : i < specs.length) :
    3 ≤ chainDelay (specAt specs i) := by
  dsimp [chainDelay, ChainSpec.totalDelay]
  have hlast : 2 ≤ ((specAt specs i).lastDelay : Nat) :=
    ValidDelay.ge2 (h_valid i hi).2.2.1
  have hsum : 0 ≤ ((specAt specs i).middleDelays.map (fun d => (d : Nat))).sum :=
    Nat.zero_le _
  omega

/-- The activation tick is strictly below `T`, so nothing activates at
    tick `T` itself. -/
theorem actTickOf_lt_T (T : Nat) (specs : List ChainSpec) (i : Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_fit : ∀ i < specs.length, chainDelay (specAt specs i) ≤ T)
    (hi : i < specs.length) :
    actTickOf T specs i < T := by
  have hd : 3 ≤ chainDelay (specAt specs i) := chainDelay_ge3 specs i h_valid hi
  have hfit : chainDelay (specAt specs i) ≤ T := h_fit i hi
  dsimp [actTickOf]
  omega

/-- The final tick is just "log `tick T`, then drain": no chain activates
    at tick `T`. -/
theorem simWorld_succ_lastTick (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (h_fit : ∀ i < specs.length, chainDelay (specAt specs i) ≤ T) :
    simWorld T specs actOrd pos (T + 1) =
      ((simWorld T specs actOrd pos T).logOutput s!"tick {T}").stepUntilNextTick := by
  rw [simWorld_succ]
  dsimp [simBody]
  have htick : (simWorld T specs actOrd pos T).tick = T := by
    rw [simWorld_tick]
  rw [htick]
  have hactive : actOrd.filter (fun i =>
      decide (i < (buildChains specs).2.length) && (actTickOf T specs i == T)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro i hi
    have hiLen : i < specs.length :=
      List.mem_range.mp ((List.Perm.mem_iff h_perm).mp hi)
    have hlt : actTickOf T specs i < T := actTickOf_lt_T T specs i h_valid h_fit hiLen
    have hne : (actTickOf T specs i == T) = false := by
      rw [beq_eq_false_iff_ne]
      exact ne_of_lt hlt
    simp [hne]
  rw [hactive]
  simp [simBurst]

/-! ## The drain ignores the output log -/

/-- Two worlds agree on everything except the output log. -/
def LogIrrel (v w : World) : Prop :=
  v.nodes = w.nodes ∧ v.events = w.events ∧ v.tick = w.tick

/-- `logOutput` changes only the output log. -/
theorem logOutput_LogIrrel (w : World) (msg : String) :
    LogIrrel (w.logOutput msg) w := by
  dsimp [LogIrrel, World.logOutput]
  simp

/-- `getNode` depends only on `nodes`. -/
theorem getNode_congr {v w : World} (h : v.nodes = w.nodes) (id : Nat) :
    v.getNode id = w.getNode id := by
  simp [World.getNode, h]

/-- `getInputSignal` depends only on `nodes`. -/
theorem getInputSignal_congr {v w : World} (h : v.nodes = w.nodes) (id : Nat) :
    v.getInputSignal id = w.getInputSignal id := by
  dsimp [World.getInputSignal]
  rw [getNode_congr h id]
  cases hg : w.getNode id with
  | none => rfl
  | some nd =>
      have hfold : ∀ maxSig, nd.inputs.foldl
          (fun maxSig inputId => match v.getNode inputId with
            | none => maxSig | some inputNd => max maxSig inputNd.sigLevel) maxSig =
          nd.inputs.foldl
          (fun maxSig inputId => match w.getNode inputId with
            | none => maxSig | some inputNd => max maxSig inputNd.sigLevel) maxSig := by
        intro maxSig
        induction nd.inputs generalizing maxSig with
        | nil => rfl
        | cons inp is ih =>
            dsimp [List.foldl]
            rw [getNode_congr h inp]
            exact ih _
      exact (hfold 0)

/-- `scheduleEvent` preserves `LogIrrel`. -/
theorem scheduleEvent_LogIrrel (v w : World) (h : LogIrrel v w) (ev : ScheduledEvent) :
    LogIrrel (v.scheduleEvent ev) (w.scheduleEvent ev) := by
  rcases h with ⟨hnodes, hevents, htick⟩
  dsimp [LogIrrel, World.scheduleEvent]
  simp [hnodes, hevents, htick]

/-- `onNeighborUpdate` preserves `LogIrrel`. -/
theorem onNeighborUpdate_LogIrrel (v w : World) (h : LogIrrel v w) (id : Nat) :
    LogIrrel (v.onNeighborUpdate id) (w.onNeighborUpdate id) := by
  rcases h with ⟨hnodes, hevents, htick⟩
  have hget : v.getNode id = w.getNode id := getNode_congr hnodes id
  dsimp [World.onNeighborUpdate]
  rw [hget]
  cases hg : w.getNode id with
  | none => simp; exact ⟨hnodes, hevents, htick⟩
  | some nd =>
      simp
      cases hk : nd.kind with
      | repeater d p => simp [LogIrrel, World.scheduleEvent, hevents, htick, hnodes]
      | observer => simp [LogIrrel, World.scheduleEvent, hevents, htick, hnodes]
      | output name => simp [LogIrrel, World.logOutput, hnodes, hevents, htick]
      | input => simp; exact ⟨hnodes, hevents, htick⟩

/-- `notifyOutputs` preserves `LogIrrel`. -/
theorem notifyOutputs_LogIrrel (v w : World) (h : LogIrrel v w) (id : Nat) :
    LogIrrel (v.notifyOutputs id) (w.notifyOutputs id) := by
  rcases h with ⟨hnodes, hevents, htick⟩
  have hget : v.getNode id = w.getNode id := getNode_congr hnodes id
  dsimp [World.notifyOutputs]
  rw [hget]
  cases hg : w.getNode id with
  | none => simp; exact ⟨hnodes, hevents, htick⟩
  | some nd =>
      simp
      have hfold : ∀ (v' w' : World), LogIrrel v' w' →
          LogIrrel (nd.outputs.foldl (fun w'' outId => w''.onNeighborUpdate outId) v')
            (nd.outputs.foldl (fun w'' outId => w''.onNeighborUpdate outId) w') := by
        intro v' w' h'
        induction nd.outputs generalizing v' w' with
        | nil => exact h'
        | cons o os ih =>
            dsimp [List.foldl]
            exact ih (v'.onNeighborUpdate o) (w'.onNeighborUpdate o)
              (onNeighborUpdate_LogIrrel v' w' h' o)
      exact hfold v w ⟨hnodes, hevents, htick⟩

/-- `onScheduledTick` preserves `LogIrrel`. -/
theorem onScheduledTick_LogIrrel (v w : World) (h : LogIrrel v w) (nid : Nat) :
    LogIrrel (v.onScheduledTick nid) (w.onScheduledTick nid) := by
  rcases h with ⟨hnodes, hevents, htick⟩
  have hsig : v.getInputSignal nid = w.getInputSignal nid := getInputSignal_congr hnodes nid
  have hget : v.getNode nid = w.getNode nid := getNode_congr hnodes nid
  dsimp [World.onScheduledTick]
  rw [hget]
  cases hg : w.getNode nid with
  | none => simp; exact ⟨hnodes, hevents, htick⟩
  | some nd =>
      simp
      cases hk : nd.kind with
      | repeater d p =>
          have hu : LogIrrel (v.updateNode nid (fun nd' =>
                { nd' with sigLevel := if v.getInputSignal nid > 0 then 15 else 0 }))
              (w.updateNode nid (fun nd' =>
                { nd' with sigLevel := if w.getInputSignal nid > 0 then 15 else 0 })) := by
            simp [LogIrrel, World.updateNode, hnodes, hevents, htick, hsig]
          simp
          exact notifyOutputs_LogIrrel _ _ hu nid
      | observer =>
          have hu : LogIrrel (v.updateNode nid (fun nd' => { nd' with sigLevel := 15 }))
              (w.updateNode nid (fun nd' => { nd' with sigLevel := 15 })) := by
            simp [LogIrrel, World.updateNode, hnodes, hevents, htick]
          simp
          exact notifyOutputs_LogIrrel _ _ hu nid
      | _ => simp; exact ⟨hnodes, hevents, htick⟩

/-- `popNextEvent` preserves `LogIrrel`: the two popped worlds agree on
    everything but the output log (and the popped events coincide). -/
theorem popNextEvent_LogIrrel (v w : World) (h : LogIrrel v w) :
    match v.popNextEvent with
    | none => w.popNextEvent = none
    | some (e, v') => ∃ w', w.popNextEvent = some (e, w') ∧ LogIrrel v' w' := by
  rcases h with ⟨hnodes, hevents, htick⟩
  have hmap : (v.popNextEvent).map (fun p => (p.1, p.2.nodes, p.2.events, p.2.tick)) =
      (w.popNextEvent).map (fun p => (p.1, p.2.nodes, p.2.events, p.2.tick)) := by
    dsimp [World.popNextEvent]
    rw [htick, hevents, hnodes]
    by_cases hC : (filter (fun x => x.2.targetTick == w.tick)
        ((range w.events.length).zip w.events)).isEmpty
    · simp [hC]
    · simp [hC]
      split <;> simp
  cases hvp : v.popNextEvent with
  | none =>
      have hwn : w.popNextEvent = none := by
        simpa [hvp] using hmap
      exact hwn
  | some pv =>
      rcases pv with ⟨ev, v₂⟩
      cases hwp : w.popNextEvent with
      | none =>
          rw [hvp, hwp] at hmap
          cases hmap
      | some pw =>
          rcases pw with ⟨ew, w₂⟩
          have htuple : (ev, v₂.nodes, v₂.events, v₂.tick) =
              (ew, w₂.nodes, w₂.events, w₂.tick) := by
            simpa [hvp, hwp] using hmap
          have hev : ev = ew := congrArg (fun q => q.1) htuple
          have hnodes₂ : v₂.nodes = w₂.nodes := congrArg (fun q => q.2.1) htuple
          have hevents₂ : v₂.events = w₂.events := congrArg (fun q => q.2.2.1) htuple
          have htick₂ : v₂.tick = w₂.tick := congrArg (fun q => q.2.2.2) htuple
          refine ⟨w₂, by rw [← hev], ⟨hnodes₂, hevents₂, htick₂⟩⟩

/-- `popSeqFuel` ignores the output log. -/
theorem popSeqFuel_LogIrrel : ∀ (n : Nat) (v w : World), LogIrrel v w →
    popSeqFuel v n = popSeqFuel w n := by
  intro n
  induction n with
  | zero => intro v w h; rfl
  | succ m ih =>
      intro v w h
      dsimp [popSeqFuel]
      have hpop := popNextEvent_LogIrrel v w h
      cases hvp : v.popNextEvent with
      | none =>
          have hwn : w.popNextEvent = none := by
            simpa [hvp] using hpop
          simp [hwn]
      | some pv =>
          rcases pv with ⟨ev, v₂⟩
          rw [hvp] at hpop
          rcases hpop with ⟨w₂, hwp, h₂⟩
          have htail := ih (v₂.onScheduledTick ev.nodeId) (w₂.onScheduledTick ev.nodeId)
            (onScheduledTick_LogIrrel v₂ w₂ h₂ ev.nodeId)
          simp [hwp, htail]

/-- `popSeq` ignores the output log. -/
theorem popSeq_logOutput (w : World) (msg : String) :
    popSeq (w.logOutput msg) = popSeq w := by
  dsimp [popSeq]
  exact popSeqFuel_LogIrrel w.events.length (w.logOutput msg) w (logOutput_LogIrrel w msg)


/-- A due event at a tick strictly before `T` is never a last-repeater. -/
theorem not_lastRepOf_of_tick_lt (T : Nat) (specs : List ChainSpec)
    (h_fit : ∀ i < specs.length, chainDelay (specAt specs i) ≤ T)
    (t : Nat) (ht : t < T) (e : ScheduledEvent) (hetick : e.targetTick = t) :
    ¬ lastRepOf T specs e := by
  rintro ⟨i, hi, heq⟩
  rw [heq] at hetick
  dsimp [stageEventOf] at hetick
  rw [stageTickOf_last T specs i (h_fit i hi)] at hetick
  omega

/-- Firing a single popped event at a pre-`T` tick appends no log entry. -/
theorem fire_pop_noOutput (w : World) (T : Nat) (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_fit : ∀ i < specs.length, chainDelay (specAt specs i) ≤ T)
    (t : Nat) (q₀ acts : List ScheduledEvent) (e : ScheduledEvent)
    (wp : World) (hpop : w.popNextEvent = some (e, wp))
    (htick : w.tick = t) (hinv : TickInv T specs t q₀ acts w)
    (hlt : t < T) :
    (wp.onScheduledTick e.nodeId).outputLog = wp.outputLog := by
  obtain ⟨idx, hidx, herase, hget, htickE, _, hfirst⟩ :=
    popNextEvent_first_occ w e wp hpop
  have hseq : popSeq w = e :: popSeq (wp.onScheduledTick e.nodeId) := by
    rw [popSeq_of_popNextEvent_some w e wp hpop]
  have hwpEv : wp.events = eraseEvents w.events ((popSeq w).take 1) := by
    rw [hseq]
    change wp.events = eraseEvents w.events [e]
    rw [herase, eraseIdx_eq_eraseEv w.events idx hidx e hget hfirst]
    dsimp [eraseEvents]
  have hframe0 : ∀ id, id ∉ ((popSeq w).take 0).map (fun e => e.nodeId) →
      wp.getNode id = w.getNode id := by
    intro id _
    dsimp [World.getNode]
    rw [popNextEvent_nodes w e wp hpop]
  have htick0 := World.popNextEvent_tick w e wp hpop
  obtain ⟨msgs, _hev, hlog, hlen, _hloc⟩ :=
    drain_fire_eq T specs h_valid t q₀ acts w htick hinv 0
      (by rw [hseq]; exact Nat.zero_lt_succ _) wp htick0
      (by rw [hwpEv]; dsimp [spawnFold]; rw [List.append_nil]) hframe0
  have hdue := popSeq_mem_due w e (by rw [hseq]; exact List.mem_cons.mpr (Or.inl rfl))
  have hnotlast : ¬ lastRepOf T specs e :=
    not_lastRepOf_of_tick_lt T specs h_fit t hlt e (hdue.1.trans htick)
  have hzero : cascadeLogLen T specs e = 0 := by
    dsimp [cascadeLogLen]
    simp [hnotlast]
  have hmsgs : msgs = [] := by
    have hlen0 : msgs.length = 0 := by simpa [hseq, hzero] using hlen
    cases msgs with
    | nil => rfl
    | cons m ms => simp at hlen0
  have hlog' : (wp.onScheduledTick e.nodeId).outputLog = wp.outputLog ++ msgs := by
    simpa [hseq] using hlog
  rw [hlog', hmsgs, List.append_nil]

/-- One `step` at a pre-`T` tick appends no log entry. -/
theorem step_noOutput (w w' : World) (T : Nat) (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_fit : ∀ i < specs.length, chainDelay (specAt specs i) ≤ T)
    (t : Nat) (q₀ acts : List ScheduledEvent)
    (htick : w.tick = t) (hstep : w.step = some w')
    (hinv : TickInv T specs t q₀ acts w) (hlt : t < T) :
    w'.outputLog = w.outputLog := by
  dsimp [World.step] at hstep
  cases hpop : w.popNextEvent with
  | none => simp [hpop] at hstep
  | some pr =>
      rcases pr with ⟨e, wp⟩
      have hw' : w' = wp.onScheduledTick e.nodeId := by
        apply Eq.symm
        simpa [World.step, hpop] using hstep
      rw [hw', fire_pop_noOutput w T specs h_valid h_fit t q₀ acts e wp hpop
        htick hinv hlt, popNextEvent_outputLog w e wp hpop]

/-- `processNEvents` at a pre-`T` tick appends no log entry. -/
theorem processNEvents_noOutput (w : World) (n : Nat) (T : Nat)
    (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_fit : ∀ i < specs.length, chainDelay (specAt specs i) ≤ T)
    (t : Nat) (q₀ acts : List ScheduledEvent)
    (htick : w.tick = t) (hinv : TickInv T specs t q₀ acts w) (hlt : t < T) :
    (processNEvents w n).outputLog = w.outputLog := by
  induction n generalizing w with
  | zero => dsimp [processNEvents]
  | succ n' ih =>
      dsimp [processNEvents]
      cases hstep : w.step with
      | none => dsimp
      | some w' =>
          have hstepO := step_noOutput w w' T specs h_valid h_fit t q₀ acts
            htick hstep hinv hlt
          have hinv' := tickInv_pop_fire T specs h_valid t q₀ acts w w'
            htick hstep hinv
          have htick' : w'.tick = t := by rw [World.step_tick w w' hstep, htick]
          rw [ih w' htick' hinv', hstepO]

/-- The full drain at a pre-`T` tick appends no log entry. -/
theorem stepUntilNextTick_noOutput (w : World) (T : Nat)
    (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_fit : ∀ i < specs.length, chainDelay (specAt specs i) ≤ T)
    (t : Nat) (q₀ acts : List ScheduledEvent)
    (htick : w.tick = t) (hinv : TickInv T specs t q₀ acts w) (hlt : t < T) :
    w.stepUntilNextTick.outputLog = w.outputLog := by
  induction w using World.stepUntilNextTick.induct with
  | case1 x hstep =>
      have hnone : x.popNextEvent = none := by
        dsimp [World.step] at hstep
        cases hp : x.popNextEvent <;> simp_all
      simp [stepUntilNextTick_of_step_none x hstep]
  | case2 x w' hstep ih =>
      dsimp [World.step] at hstep
      cases hpop : x.popNextEvent with
      | none => simp [hpop] at hstep
      | some pr =>
          rcases pr with ⟨e0, wp⟩
          have hw' : w' = wp.onScheduledTick e0.nodeId := by
            apply Eq.symm
            simpa [World.step, hpop] using hstep
          subst hw'
          have hstepUNT : x.stepUntilNextTick =
              (wp.onScheduledTick e0.nodeId).stepUntilNextTick := by
            rw [World.stepUntilNextTick]
            dsimp [World.step]
            rw [hpop]
          have htick0 := World.popNextEvent_tick x e0 wp hpop
          have hlog0' : (wp.onScheduledTick e0.nodeId).outputLog = wp.outputLog :=
            fire_pop_noOutput x T specs h_valid h_fit t q₀ acts e0 wp hpop
              htick hinv hlt
          have htick' : (wp.onScheduledTick e0.nodeId).tick = t := by
            rw [World.onScheduledTick_tick, htick0, htick]
          have hinv' : TickInv T specs t q₀ acts (wp.onScheduledTick e0.nodeId) := by
            exact tickInv_pop_fire T specs h_valid t q₀ acts x
              (wp.onScheduledTick e0.nodeId) htick
              (by dsimp [World.step]; rw [hpop]) hinv
          have hih := ih htick' hinv'
          rw [hstepUNT, hih, hlog0', popNextEvent_outputLog x e0 wp hpop]

/-- A burst at a pre-`T` tick appends no log entry. -/
theorem simBurst_noOutput (t : Nat) (observers : List Nat)
    (pos : Nat → Nat → Nat) (w : World) (pairs : List (Nat × Nat))
    (T : Nat) (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_fit : ∀ i < specs.length, chainDelay (specAt specs i) ≤ T)
    (q₀ acts : List ScheduledEvent)
    (htick : w.tick = t) (hinv : TickInv T specs t q₀ acts w) (hlt : t < T)
    (hact : ∀ p ∈ pairs, ∀ oid, observers[p.1]? = some oid →
      ∃ c < specs.length, obsActEvt t oid = obsEventOf T specs c ∧
        actTickOf T specs c = t)
    (hne : ∀ a ∈ acts, ∀ p ∈ pairs, ∀ oid,
      observers[p.1]? = some oid → a ≠ obsActEvt t oid)
    (hfresh : ∀ p ∈ pairs, ∀ oid, observers[p.1]? = some oid →
      ∀ q ∈ pairs, ∀ oid', observers[q.1]? = some oid' →
        obsActEvt t oid = obsActEvt t oid' → p = q)
    (hnp : pairs.Nodup) :
    (simBurst t observers pos w pairs).outputLog = w.outputLog := by
  induction pairs generalizing w acts with
  | nil => dsimp [simBurst]
  | cons p ps ih =>
      rcases p with ⟨i, k⟩
      dsimp [simBurst, List.foldl]
      cases hobs : observers[i]? with
      | none =>
          dsimp
          have hprocOut : (processNEvents w (pos t k)).outputLog = w.outputLog :=
            processNEvents_noOutput w (pos t k) T specs h_valid h_fit t q₀ acts
              htick hinv hlt
          have htickP : (processNEvents w (pos t k)).tick = t := by
            rw [processNEvents_tick, htick]
          have hinvP : TickInv T specs t q₀ acts (processNEvents w (pos t k)) :=
            tickInv_processN T specs h_valid t q₀ acts w (pos t k) htick hinv
          have hrest := ih (processNEvents w (pos t k)) acts htickP hinvP
            (fun q hq oid' hobsq => hact q (List.mem_cons.mpr (Or.inr hq)) oid' hobsq)
            (fun a ha q hq oid' hobsq => hne a ha q (List.mem_cons.mpr (Or.inr hq)) oid' hobsq)
            (fun q hq oid' hobsq q' hq' oid'' hobsq' heq =>
              hfresh q (List.mem_cons.mpr (Or.inr hq)) oid' hobsq q'
                (List.mem_cons.mpr (Or.inr hq')) oid'' hobsq' heq)
            (List.nodup_cons.mp hnp).2
          exact hrest.trans hprocOut
      | some oid =>
          dsimp
          have hprocOut : (processNEvents w (pos t k)).outputLog = w.outputLog :=
            processNEvents_noOutput w (pos t k) T specs h_valid h_fit t q₀ acts
              htick hinv hlt
          have hA : (activateChain (processNEvents w (pos t k)) oid).outputLog =
              (processNEvents w (pos t k)).outputLog := by
            simp [activateChain]
          have htickP : (processNEvents w (pos t k)).tick = t := by
            rw [processNEvents_tick, htick]
          have hinvP : TickInv T specs t q₀ acts (processNEvents w (pos t k)) :=
            tickInv_processN T specs h_valid t q₀ acts w (pos t k) htick hinv
          have hinvA : TickInv T specs t q₀ (acts ++ [obsActEvt t oid])
              (activateChain (processNEvents w (pos t k)) oid) :=
            tickInv_activate T specs h_valid t q₀ acts
              (processNEvents w (pos t k)) oid htickP hinvP
              (hact (i, k) (List.mem_cons.mpr (Or.inl rfl)) oid hobs)
              (fun a ha => hne a ha (i, k) (List.mem_cons.mpr (Or.inl rfl)) oid hobs)
          have htickA : (activateChain (processNEvents w (pos t k)) oid).tick = t := by
            rw [activateChain_tick, htickP]
          have hact' : ∀ q ∈ ps, ∀ oid', observers[q.1]? = some oid' →
              ∃ c < specs.length, obsActEvt t oid' = obsEventOf T specs c ∧
                actTickOf T specs c = t := by
            intro q hq oid' hobsq
            exact hact q (List.mem_cons.mpr (Or.inr hq)) oid' hobsq
          have hne' : ∀ a ∈ acts ++ [obsActEvt t oid], ∀ q ∈ ps, ∀ oid',
              observers[q.1]? = some oid' → a ≠ obsActEvt t oid' := by
            intro a ha q hq oid' hobsq
            rcases List.mem_append.mp ha with ha | ha
            · exact hne a ha q (List.mem_cons.mpr (Or.inr hq)) oid' hobsq
            · rcases List.mem_singleton.mp ha with rfl
              intro heq
              have hpq := hfresh (i, k) (List.mem_cons.mpr (Or.inl rfl)) oid hobs
                q (List.mem_cons.mpr (Or.inr hq)) oid' hobsq heq
              have hqIn : (i, k) ∈ ps := by rw [hpq]; exact hq
              exact (List.nodup_cons.mp hnp).1 hqIn
          have hfresh' : ∀ q ∈ ps, ∀ oid', observers[q.1]? = some oid' →
              ∀ q' ∈ ps, ∀ oid'', observers[q'.1]? = some oid'' →
                obsActEvt t oid' = obsActEvt t oid'' → q = q' := by
            intro q hq oid' hobsq q' hq' oid'' hobsq' heq
            exact hfresh q (List.mem_cons.mpr (Or.inr hq)) oid' hobsq q'
              (List.mem_cons.mpr (Or.inr hq')) oid'' hobsq' heq
          have hrest := ih (activateChain (processNEvents w (pos t k)) oid)
            (acts ++ [obsActEvt t oid]) htickA hinvA
            hact' hne' hfresh' (List.nodup_cons.mp hnp).2
          exact hrest.trans (hA.trans hprocOut)

/-- One `simBody` tick before `T` appends exactly the tick marker. -/
theorem simBody_outputLog_before_T (T t : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (h_fit : ∀ i < specs.length, chainDelay (specAt specs i) ≤ T)
    (ht : t < T) :
    (simWorld T specs actOrd pos (t + 1)).outputLog =
      (simWorld T specs actOrd pos t).outputLog ++ [s!"tick {t}"] := by
  rw [simWorld_succ]
  set wT := simWorld T specs actOrd pos t with hwT
  set observers := (buildChains specs).2 with hob
  dsimp only [simBody]
  set wLog := wT.logOutput s!"tick {wT.tick}" with hwL
  have htickT : wT.tick = t := by dsimp only [wT]; rw [simWorld_tick]
  have htickLog : wLog.tick = t := by
    dsimp only [wLog]; rw [World.logOutput_tick, htickT]
  rw [htickLog]
  set F := actOrd.filter (fun i =>
    decide (i < observers.length) && (actTickOf T specs i == t)) with hF
  set wB := simBurst t observers pos wLog F.zipIdx with hwB
  -- activation shape / freshness / nodup of `F.zipIdx`
  have hactF : ∀ p ∈ F.zipIdx, ∀ oid, observers[p.1]? = some oid →
      ∃ c < specs.length, obsActEvt t oid = obsEventOf T specs c ∧
        actTickOf T specs c = t := by
    intro p hp oid hobs
    obtain ⟨k, hkPos, hpk⟩ := List.exists_mem_zipIdx'.mp ⟨p, hp, rfl⟩
    have hp1 : p.1 = F[k] := congrArg Prod.fst hpk
    have hiF : p.1 ∈ F := by rw [hp1]; exact List.getElem_mem hkPos
    have hcond := (List.mem_filter.mp hiF).2
    rw [Bool.and_eq_true, decide_eq_true_eq] at hcond
    have hiLen : p.1 < observers.length := hcond.1
    have hactP : actTickOf T specs p.1 = t := LawfulBEq.eq_of_beq hcond.2
    have hget : observers[p.1]? = some (chainObserverId specs p.1) := by
      rw [List.getElem?_eq_getElem hiLen,
        observers_getElem_eq_chainObserverId specs p.1 hiLen]
    have hoid : oid = chainObserverId specs p.1 :=
      (Option.some_inj.mp (by rwa [hget] at hobs)).symm
    subst hoid
    have hiLenS : p.1 < specs.length := by
      rw [← buildChains_observers_length]
      exact hiLen
    refine ⟨p.1, hiLenS, ?_, ?_⟩
    · dsimp [obsActEvt, obsEventOf, obsTickOf]
      rw [hactP]
    · exact hactP
  have hneF : ∀ a ∈ ([] : List ScheduledEvent), ∀ p ∈ F.zipIdx, ∀ oid,
      observers[p.1]? = some oid → a ≠ obsActEvt t oid := by
    intro a ha
    cases ha
  have hfreshF : ∀ p ∈ F.zipIdx, ∀ oid, observers[p.1]? = some oid →
      ∀ q ∈ F.zipIdx, ∀ oid', observers[q.1]? = some oid' →
        obsActEvt t oid = obsActEvt t oid' → p = q := by
    intro p hp oid hobs q hq oid' hobsq heq
    obtain ⟨k, hkPos, hpk⟩ := List.exists_mem_zipIdx'.mp ⟨p, hp, rfl⟩
    obtain ⟨k', hk'Pos, hqk⟩ := List.exists_mem_zipIdx'.mp ⟨q, hq, rfl⟩
    have hp1 : p.1 = F[k] := congrArg Prod.fst hpk
    have hq1 : q.1 = F[k'] := congrArg Prod.fst hqk
    have hiF : p.1 ∈ F := by rw [hp1]; exact List.getElem_mem hkPos
    have hjF : q.1 ∈ F := by rw [hq1]; exact List.getElem_mem hk'Pos
    have hpLen : p.1 < observers.length := by
      have := (List.mem_filter.mp hiF).2
      rw [Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.1
    have hqLen : q.1 < observers.length := by
      have := (List.mem_filter.mp hjF).2
      rw [Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.1
    have hpLenS : p.1 < specs.length := by
      rw [← buildChains_observers_length]; exact hpLen
    have hqLenS : q.1 < specs.length := by
      rw [← buildChains_observers_length]; exact hqLen
    have hgetP : observers[p.1]? = some (chainObserverId specs p.1) := by
      rw [List.getElem?_eq_getElem hpLen,
        observers_getElem_eq_chainObserverId specs p.1 hpLen]
    have hgetQ : observers[q.1]? = some (chainObserverId specs q.1) := by
      rw [List.getElem?_eq_getElem hqLen,
        observers_getElem_eq_chainObserverId specs q.1 hqLen]
    have hoid : oid = chainObserverId specs p.1 :=
      (Option.some_inj.mp (by rwa [hgetP] at hobs)).symm
    have hoid' : oid' = chainObserverId specs q.1 :=
      (Option.some_inj.mp (by rwa [hgetQ] at hobsq)).symm
    have hnode : chainObserverId specs p.1 = chainObserverId specs q.1 := by
      have := congrArg (fun ev => ev.nodeId) heq
      dsimp [obsActEvt] at this
      rwa [hoid, hoid'] at this
    have hiEq : p.1 = q.1 := chainObserverId_inj specs p.1 q.1 hpLenS hqLenS hnode
    have hFEq : F[k] = F[k'] := by rw [← hp1, ← hq1, hiEq]
    have hFnd : F.Nodup := by
      have hactNd : actOrd.Nodup := h_perm.nodup_iff.mpr List.nodup_range
      exact hactNd.filter (fun i =>
        decide (i < observers.length) && (actTickOf T specs i == t))
    have hkk' : k = k' :=
      (hFnd.getElem_inj_iff (i := k) (hi := hkPos) (j := k')
        (hj := hk'Pos)).mp hFEq
    subst hkk'
    rw [hpk, hqk]
  -- burst and drain append nothing
  have hinvLog : TickInv T specs t wT.events [] wLog := by
    dsimp [wLog]
    exact tickInv_logOutput T specs t wT.events [] wT s!"tick {wT.tick}"
      (simWorld_tickInv T specs actOrd pos h_valid h_perm t)
  have hburstOut : wB.outputLog = wLog.outputLog := by
    dsimp [wB]
    exact simBurst_noOutput t observers pos wLog F.zipIdx T specs
      h_valid h_fit wT.events [] htickLog hinvLog ht hactF hneF hfreshF
      (nodup_zipIdx F (n := 0))
  have hinvB : TickInv T specs t wT.events
      (obsActEvts t observers F.zipIdx) wB := by
    dsimp [wB, wLog, wT, observers, F]
    exact simBurst_tickInv T specs actOrd pos t h_valid h_perm
  have htickB : wB.tick = t := by
    dsimp [wB]; rw [simBurst_tick, htickLog]
  have hdrainOut : wB.stepUntilNextTick.outputLog = wB.outputLog :=
    stepUntilNextTick_noOutput wB T specs h_valid h_fit t wT.events
      (obsActEvts t observers F.zipIdx) htickB hinvB ht
  rw [hdrainOut, hburstOut]
  dsimp [wLog, World.logOutput]
  rw [htickT]

/-- `addNode` preserves the output log. -/
private theorem addNode_outputLog (w : World) (nd : NodeData) :
    (w.addNode nd).2.outputLog = w.outputLog := by
  dsimp [World.addNode]

/-- `updateNode` preserves the output log. -/
private theorem updateNode_outputLog (w : World) (id : Nat)
    (f : NodeData → NodeData) :
    (w.updateNode id f).outputLog = w.outputLog := by
  dsimp [World.updateNode]

/-- `connectChain` preserves the output log. -/
private theorem connectChain_outputLog (w : World) (ids : List Nat) :
    (connectChain w ids).outputLog = w.outputLog := by
  dsimp [connectChain]
  generalize hp : ids.zip (ids.drop 1) = pairs
  clear hp
  induction pairs generalizing w with
  | nil => rfl
  | cons p ps ih =>
      rw [List.foldl_cons]
      cases p with
      | mk prev curr => dsimp; rw [ih, updateNode_outputLog, updateNode_outputLog]

/-- The repeater-adding fold preserves the output log. -/
private theorem repFoldl_outputLog (l : List (PNat × Int))
    (acc : List Nat × World) :
    (l.foldl repFoldlStep acc).2.outputLog = acc.2.outputLog := by
  induction l generalizing acc with
  | nil => dsimp [List.foldl]
  | cons dp rest ih =>
      rw [List.foldl_cons, ih (repFoldlStep acc dp)]
      dsimp [repFoldlStep]
      rw [addNode_outputLog]

/-- `buildChain` preserves the output log. -/
private theorem buildChain_outputLog (w : World) (name : String)
    (c : ChainSpec) : (buildChain w name c).2.outputLog = w.outputLog := by
  dsimp [buildChain, buildChainPre, World.addNode]
  rw [connectChain_outputLog, repFoldl_outputLog]

/-- `buildChainsFrom` preserves the output log. -/
private theorem buildChainsFrom_outputLog (start : Nat) (w : World)
    (specs : List ChainSpec) :
    (buildChainsFrom start w specs).1.outputLog = w.outputLog := by
  induction specs generalizing start w with
  | nil => dsimp [buildChainsFrom]
  | cons c cs ih =>
      dsimp only [buildChainsFrom]
      rw [ih (start + 1) ((buildChain w (chainName start) c).2)]
      exact buildChain_outputLog w (chainName start) c

/-- The built world has an empty output log. -/
theorem buildChains_outputLog (specs : List ChainSpec) :
    (buildChains specs).1.outputLog = [] := by
  dsimp [buildChains]
  rw [buildChainsFrom_outputLog]
  dsimp [World.empty]

/-- Before tick `T` the log holds exactly the tick markers (no output entry
    is produced by a non-last repeater). -/
theorem simWorld_outputLog_ticks (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (h_fit : ∀ i < specs.length, chainDelay (specAt specs i) ≤ T) :
    (simWorld T specs actOrd pos T).outputLog = tickLog T := by
  have hgeneral : ∀ t, t ≤ T →
      (simWorld T specs actOrd pos t).outputLog = tickLog t := by
    intro t
    induction t with
    | zero =>
        intro _
        rw [simWorld_zero, buildChains_outputLog]
        dsimp [tickLog]
    | succ t' ih =>
        intro htle
        have ht' : t' < T := Nat.lt_of_succ_le htle
        have hstep := simBody_outputLog_before_T T t' specs actOrd pos
          h_valid h_perm h_fit ht'
        rw [hstep, ih (Nat.le_of_lt ht'), tickLog_succ]
  exact hgeneral T le_rfl

/-- Two `isOutputEntry` truths force the same chain. -/
theorem isOutputEntry_true_of_true {i j : Nat} {s : String}
    (hi : isOutputEntry s i = true) (hj : isOutputEntry s j = true) : i = j := by
  dsimp [isOutputEntry] at hj
  cases hb : s == s!"{chainName j}: 0" with
  | true =>
      have hs : s = s!"{chainName j}: 0" := LawfulBEq.eq_of_beq hb
      rw [hs] at hi
      rw [← chainMsg_lit_zero j] at hi
      exact isOutputEntry_of_msg i j 0 hi
  | false =>
      rw [hb] at hj
      simp at hj
      rw [hj] at hi
      rw [← chainMsg_lit_fifteen j] at hi
      exact isOutputEntry_of_msg i j 15 hi

/-- An output entry of chain `j` is not chain `i`'s entry when `i ≠ j`. -/
theorem isOutputEntry_true_of_ne {i j : Nat} {s : String} (hij : i ≠ j)
    (hj : isOutputEntry s j = true) : isOutputEntry s i = false := by
  dsimp [isOutputEntry] at hj ⊢
  cases hb : s == s!"{chainName j}: 0" with
  | true =>
      have hs : s = s!"{chainName j}: 0" := LawfulBEq.eq_of_beq hb
      rw [hs]
      rw [← chainMsg_lit_zero j]
      exact isOutputEntry_of_ne i j 0 hij
  | false =>
      rw [hb] at hj
      simp at hj
      rw [hj]
      rw [← chainMsg_lit_fifteen j]
      exact isOutputEntry_of_ne i j 15 hij

/-- `findIdx?` agrees on two same-length lists whose elements are
    pointwise related by the predicates. -/
theorem findIdx?_congr_pointwise {α β : Type} (p : β → Bool) (q : α → Bool)
    (l₁ : List α) (l₂ : List β)
    (h : l₁.length = l₂.length)
    (hp : ∀ (k : Nat) (hk : k < l₁.length),
      p (l₂[k]'(by simpa [h] using hk)) = q (l₁[k]'hk)) :
    _root_.findIdx? p l₂ = _root_.findIdx? q l₁ := by
  induction l₁ generalizing l₂ with
  | nil =>
      cases l₂ with
      | nil => rfl
      | cons y ys => dsimp [List.length] at h; omega
  | cons x xs ih =>
      cases l₂ with
      | nil => dsimp [List.length] at h; omega
      | cons y ys =>
        dsimp [_root_.findIdx?]
        have h0 : p y = q x := by
          simpa using (hp 0 (Nat.zero_lt_succ _))
        have hlen : xs.length = ys.length := by
          dsimp [List.length] at h ⊢
          omega
        have hptail : ∀ (k : Nat) (hk : k < xs.length),
            p (ys[k]'(by simpa [hlen] using hk)) = q (xs[k]'hk) := by
          intro k hk
          have hk' : k + 1 < (x :: xs).length := by
            dsimp [List.length]
            omega
          simpa using (hp (k + 1) hk')
        rw [h0]
        by_cases hq : q x
        · simp [hq]
        · simp [hq, ih ys hlen hptail]

/-- The k-th drain message is chain `i`'s output entry iff the k-th pop is
    chain `i`'s last-repeater event. -/
theorem msgs_isOutputEntry_iff_popSeq (w : World) (T : Nat)
    (specs : List ChainSpec) (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (msgs : List String) (i : Nat) (hi : i < specs.length)
    (hlen : msgs.length = (popSeq w).length)
    (hcont : ∀ (k : Nat) (hk : k < (popSeq w).length),
      ∃ j < specs.length,
        (popSeq w)[k]'hk = stageEventOf T specs j (repLenAt specs j) ∧
        isOutputEntry (msgs[k]'(by simpa [hlen] using hk)) j = true) :
    ∀ (k : Nat) (hk : k < (popSeq w).length),
      isOutputEntry (msgs[k]'(by simpa [hlen] using hk)) i =
        decide ((popSeq w)[k]'hk = stageEventOf T specs i (repLenAt specs i)) := by
  intro k hk
  obtain ⟨j, hj, hpop, hmsg⟩ := hcont k hk
  by_cases heq : (popSeq w)[k]'hk = stageEventOf T specs i (repLenAt specs i)
  · -- the pop is chain i's last repeater, so the message is chain i's entry
    have hstage : stageEventOf T specs j (repLenAt specs j) =
        stageEventOf T specs i (repLenAt specs i) := by
      rw [← hpop]
      exact heq
    have hnode : chainRepId specs j (repLenAt specs j) =
        chainRepId specs i (repLenAt specs i) := by
      simpa [stageEventOf] using (congrArg ScheduledEvent.nodeId hstage)
    have hpair := chainRepId_inj specs j i (repLenAt specs j)
      (repLenAt specs i) hj hi
      (by dsimp [repLenAt]; exact le_rfl)
      (by dsimp [repLenAt]; exact le_rfl)
      (h_valid j hj).1 (h_valid i hi).1 hnode
    have hij : j = i := hpair.1
    rw [hij] at hmsg
    simpa [heq] using hmsg
  · -- the pop is not chain i's last repeater, so the message is not chain i's
    have hstage_ne : stageEventOf T specs j (repLenAt specs j) ≠
        stageEventOf T specs i (repLenAt specs i) := by
      intro hst
      exact heq (by rw [hpop]; exact hst)
    have hij : i ≠ j := by
      intro hji
      apply hstage_ne
      rw [hji]
    have hfalse : isOutputEntry (msgs[k]'(by simpa [hlen] using hk)) i = false :=
      isOutputEntry_true_of_ne hij hmsg
    have hdec : decide ((popSeq w)[k]'hk = stageEventOf T specs i (repLenAt specs i)) = false := by
      simp [heq]
    rw [hfalse, hdec]

/-- The messages of the final drain, indexed by the pop sequence: the k-th
    message is an output entry of chain `i` iff the k-th pop is chain `i`'s
    last-repeater event. -/
theorem findIdx?_msgs_of_popSeq (w : World) (T : Nat)
    (specs : List ChainSpec) (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (msgs : List String) (i : Nat) (hi : i < specs.length)
    (hlen : msgs.length = (popSeq w).length)
    (hcont : ∀ (k : Nat) (hk : k < (popSeq w).length),
      ∃ j < specs.length,
        (popSeq w)[k]'hk = stageEventOf T specs j (repLenAt specs j) ∧
        isOutputEntry (msgs[k]'(by simpa [hlen] using hk)) j = true) :
    _root_.findIdx? (fun s => isOutputEntry s i) msgs =
      _root_.findIdx? (fun e => decide (e = stageEventOf T specs i (repLenAt specs i)))
        (popSeq w) := by
  exact findIdx?_congr_pointwise (fun s => isOutputEntry s i)
    (fun e => decide (e = stageEventOf T specs i (repLenAt specs i)))
    (popSeq w) msgs hlen.symm
    (msgs_isOutputEntry_iff_popSeq w T specs h_valid msgs i hi hlen hcont)

/-- The full tick-marker prefix never matches an output entry. -/
theorem findIdx?_tickLog_none (T i : Nat) :
    _root_.findIdx? (fun s => isOutputEntry s i) (tickLog (T + 1)) = none := by
  rw [_root_.findIdx?_eq_none_iff]
  intro a ha
  dsimp [tickLog] at ha
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ha
  exact isOutputEntry_tick t i

/-- The capstone bridge: chain `i`'s output position is `T + 1` plus the
    position of its last-repeater event in the tick-`T` pop sequence. -/
theorem outputPos_simulate (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat) (i : Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (h_fit : ∀ i < specs.length, chainDelay (specAt specs i) ≤ T)
    (hi : i < specs.length) :
    outputPos (simulate T specs actOrd pos) i =
      (_root_.findIdx? (fun e => decide (e = stageEventOf T specs i (repLenAt specs i)))
        (popSeq (simWorld T specs actOrd pos T))).map (fun r => T + 1 + r) := by
  set wT := simWorld T specs actOrd pos T with hwT
  set wLog := wT.logOutput s!"tick {T}" with hwL
  -- the tick-`T` drain appends one output entry per last-repeater pop
  have htickLog : wLog.tick = T := by
    dsimp only [wLog]
    rw [World.logOutput_tick, simWorld_tick]
  have hinvLog : TickInv T specs T wT.events [] wLog := by
    dsimp [wLog]
    exact tickInv_logOutput T specs T wT.events [] wT s!"tick {T}"
      (simWorld_tickInv T specs actOrd pos h_valid h_perm T)
  have hpopLog : popSeq wLog = popSeq wT := by
    dsimp [wLog]
    exact popSeq_logOutput wT (s!"tick {T}")
  have hall : ∀ e ∈ popSeq wLog, lastRepOf T specs e := by
    intro e he
    rw [hpopLog] at he
    dsimp [wT] at he
    exact popSeq_simWorld_lastRep T specs actOrd pos h_valid h_perm h_fit e he
  obtain ⟨msgs, hdrain, hlen, hcont⟩ :=
    stepUntilNextTick_lastRep_messages wLog T specs h_valid T wT.events []
      htickLog hinvLog hall
  -- the pre-`T` log is exactly the tick markers
  have hwLogOut : wLog.outputLog = tickLog (T + 1) := by
    dsimp [wLog, wT, World.logOutput]
    rw [simWorld_outputLog_ticks T specs actOrd pos h_valid h_perm h_fit]
    exact (tickLog_succ T).symm
  have hsim : simulate T specs actOrd pos = tickLog (T + 1) ++ msgs := by
    rw [simulate_eq_simWorld_log,
      simWorld_succ_lastTick T specs actOrd pos h_valid h_perm h_fit]
    rw [← hwT, ← hwL]
    rw [hdrain, hwLogOut]
  -- convert `hcont` to the getElem form used by `findIdx?_msgs_of_popSeq`
  have hcont' : ∀ (k : Nat) (hk : k < (popSeq wLog).length),
      ∃ j < specs.length,
        (popSeq wLog)[k]'hk = stageEventOf T specs j (repLenAt specs j) ∧
        isOutputEntry (msgs[k]'(by simpa [hlen] using hk)) j = true := by
    intro k hk
    obtain ⟨j, hj, heq, hmsg⟩ := hcont k hk
    have hk' : k < msgs.length := by simpa [hlen] using hk
    have hmsg' : isOutputEntry (msgs[k]'hk') j = true := by
      simpa [List.getElem?_eq_getElem hk'] using hmsg
    refine ⟨j, hj, heq, ?_⟩
    exact hmsg'
  have hidx : _root_.findIdx? (fun s => isOutputEntry s i) msgs =
      _root_.findIdx? (fun e => decide (e = stageEventOf T specs i (repLenAt specs i)))
        (popSeq wLog) :=
    findIdx?_msgs_of_popSeq wLog T specs h_valid msgs i hi hlen hcont'
  dsimp [outputPos]
  rw [hsim, _root_.findIdx?_append]
  simp [findIdx?_tickLog_none T i, tickLog_length (T + 1)]
  rw [hidx, hpopLog]
