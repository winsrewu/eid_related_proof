import Proofs.Model.SpawnMembership

open BasicRedstoneSim
open World
open List

/-! # The tick invariant and its preservation at every tick boundary. -/

/-! ## The tick invariant -/

/-- The invariant carried through the burst and drain of tick `t`,
    starting from queue `q₀` with activation list `acts`: nodup,
    buildChains wiring, cascade classification, source classification
    (survived / activation / spawn) and spawn freshness. -/
def TickInv (T : Nat) (specs : List ChainSpec) (t : Nat)
    (q₀ : List ScheduledEvent) (acts : List ScheduledEvent)
    (w : World) : Prop :=
  List.Nodup w.events ∧
  (∀ id, (w.getNode id).map wiring =
    ((buildChains specs).1.getNode id).map wiring) ∧
  CascadeGood T specs w ∧
  (∀ e ∈ w.events,
    (e ∈ q₀ ∧ EventHistory T specs t e) ∨
    e ∈ acts ∨
    ∃ x, e ∈ cascadeSpawn T specs x ∧ x.targetTick = t ∧
      IsCascadeEv T specs x) ∧
  ∀ e₀ ∈ w.events, e₀.targetTick = t →
    ∀ s ∈ cascadeSpawn T specs e₀, s ∉ w.events

/-! ## TickInv preservation -/

/-- Erasing an index preserves nodup. -/
theorem nodup_eraseIdx_of_nodup {α : Type} (l : List α)
    (i : Nat) (hnd : l.Nodup) : (l.eraseIdx i).Nodup := by
  revert i hnd
  induction l with
  | nil => intro i hnd; dsimp [List.eraseIdx]; exact nodup_nil
  | cons a l ih =>
    intro i hnd
    rcases List.nodup_cons.mp hnd with ⟨hna, hnd'⟩
    cases i with
    | zero => dsimp [List.eraseIdx]; exact hnd'
    | succ i' =>
      dsimp [List.eraseIdx]
      exact List.nodup_cons.mpr
        ⟨fun h => hna (List.mem_of_mem_eraseIdx h), ih i' hnd'⟩

/-- The erased element (unique under nodup) is gone after erasure. -/
theorem not_mem_eraseIdx_of_nodup {α : Type} [DecidableEq α]
    (l : List α) (i : Nat) (hi : i < l.length) (hnd : l.Nodup) :
    l[i]'hi ∉ l.eraseIdx i := by
  revert i hi hnd
  induction l with
  | nil => intro i hi; dsimp [List.length] at hi; omega
  | cons a l ih =>
    intro i hi hnd
    rcases List.nodup_cons.mp hnd with ⟨hna, hnd'⟩
    cases i with
    | zero => change a ∉ l; exact hna
    | succ i' =>
      have hi' : i' < l.length := by dsimp [List.length] at hi; omega
      change l[i']'hi' ∉ a :: l.eraseIdx i'
      intro h
      rcases List.mem_cons.mp h with heq | hm
      · exfalso
        exact hna (by rw [← heq]; exact List.getElem_mem hi')
      · exact ih i' hi' hnd' hm

/-- The cascade spawn of a cascade event is nodup. -/
private theorem cascadeSpawn_nodup (T : Nat) (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (e : ScheduledEvent) (hcl : IsCascadeEv T specs e) :
    (cascadeSpawn T specs e).Nodup := by
  rcases hcl with ⟨i, hi, rfl⟩ | hstage
  · rw [cascadeSpawn_obs T specs i hi]
    exact nodup_singleton _
  · rcases hstage with ⟨i, hi, s, hs, rfl⟩
    by_cases hlt : s < (specAt specs i).middleDelays.length
    · rw [cascadeSpawn_stage T specs h_valid i s hi hlt]
      exact nodup_singleton _
    · have heqLen : s = (specAt specs i).middleDelays.length := by
        omega
      subst heqLen
      change (cascadeSpawn T specs
        (stageEventOf T specs i (repLenAt specs i))).Nodup
      rw [cascadeSpawn_lastRep T specs h_valid i hi]
      exact nodup_nil

/-- One pop-fire step of the drain preserves the tick invariant. -/
theorem tickInv_pop_fire (T : Nat) (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (t : Nat) (q₀ acts : List ScheduledEvent) (w w' : World)
    (htick : w.tick = t) (hstep : w.step = some w')
    (hinv : TickInv T specs t q₀ acts w) :
    TickInv T specs t q₀ acts w' := by
  rcases hinv with ⟨hnd, hwir, hgood, hsrc, hfresh⟩
  dsimp [World.step] at hstep
  cases hpop : w.popNextEvent with
  | none => simp [hpop] at hstep
  | some pr =>
    rcases pr with ⟨e, wp⟩
    have hw' : w' = wp.onScheduledTick e.nodeId := by
      apply Eq.symm
      simpa [World.step, hpop] using hstep
    obtain ⟨idx, hidx, herase, htickE, hget⟩ :=
      popNextEvent_eraseIdx w e wp hpop
    have hmem : e ∈ w.events := by
      rw [← hget]; exact List.getElem_mem hidx
    have hfire := firing_cascadeSpawn_eq T specs h_valid w e wp hpop
      hgood hwir
    have hdue : e.targetTick = t := by rw [htickE, htick]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hw', hfire, List.nodup_append]
      refine ⟨?_, ?_, ?_⟩
      · rw [herase]
        exact nodup_eraseIdx_of_nodup w.events idx hnd
      · exact cascadeSpawn_nodup T specs h_valid e (hgood e hmem)
      · intro a ha b hb heq
        rw [heq] at ha
        have hfw : b ∈ w.events := by
          rw [herase] at ha
          exact List.mem_of_mem_eraseIdx ha
        exact hfresh e hmem hdue b hb hfw
    · intro id
      rw [step_getNode_wiring w w' hstep id, hwir]
    · intro f hf
      rw [hw', hfire] at hf
      rcases List.mem_append.mp hf with hf | hf
      · rw [herase] at hf
        exact hgood f (List.mem_of_mem_eraseIdx hf)
      · exact cascadeSpawn_mem_good T specs h_valid e f hf
          (hgood e hmem)
    · intro f hf
      rw [hw', hfire] at hf
      rcases List.mem_append.mp hf with hf | hf
      · rw [herase] at hf
        exact hsrc f (List.mem_of_mem_eraseIdx hf)
      · exact Or.inr (Or.inr ⟨e, hf, hdue, hgood e hmem⟩)
    · intro e₀ he₀ ht₀ s hs
      rw [hw', hfire] at he₀
      rcases List.mem_append.mp he₀ with he₀ | he₀
      · have he₀er : e₀ ∈ w.events.eraseIdx idx := by rwa [← herase]
        have he₀w : e₀ ∈ w.events := List.mem_of_mem_eraseIdx he₀er
        intro hsm
        rw [hw', hfire] at hsm
        rcases List.mem_append.mp hsm with hsm | hsm
        · exact hfresh e₀ he₀w ht₀ s hs
            (by rw [herase] at hsm; exact List.mem_of_mem_eraseIdx hsm)
        · have heq := cascadeSpawn_inj T specs h_valid e₀ e s hs hsm
            (hgood e₀ he₀w) (hgood e hmem)
          rw [heq] at he₀
          have := not_mem_eraseIdx_of_nodup w.events idx hidx hnd
          rw [hget, ← herase] at this
          exact this he₀
      · exfalso
        have hgt := cascadeSpawn_target_gt T specs h_valid e e₀ t he₀
          (hgood e hmem) hdue
        omega

/-- `processNEvents` at the same tick preserves the tick invariant. -/
theorem tickInv_processN (T : Nat) (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (t : Nat) (q₀ acts : List ScheduledEvent) (w : World) (n : Nat)
    (htick : w.tick = t)
    (hinv : TickInv T specs t q₀ acts w) :
    TickInv T specs t q₀ acts (processNEvents w n) := by
  induction n generalizing w with
  | zero => dsimp [processNEvents]; exact hinv
  | succ n ih =>
    dsimp [processNEvents]
    cases hstep : w.step with
    | none => exact hinv
    | some w' =>
      apply ih
      · exact (World.step_tick w w' hstep).trans htick
      · exact tickInv_pop_fire T specs h_valid t q₀ acts w w' htick
          hstep hinv

/-- Appending one activation event preserves the tick invariant. -/
theorem tickInv_activate (T : Nat) (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (t : Nat) (q₀ acts : List ScheduledEvent) (w : World) (oid : Nat)
    (htick : w.tick = t)
    (hinv : TickInv T specs t q₀ acts w)
    (hact : ∃ c < specs.length, obsActEvt t oid = obsEventOf T specs c ∧
      actTickOf T specs c = t)
    (hne : ∀ a ∈ acts, a ≠ obsActEvt t oid) :
    TickInv T specs t q₀ (acts ++ [obsActEvt t oid])
      (activateChain w oid) := by
  rcases hinv with ⟨hnd, hwir, hgood, hsrc, hfresh⟩
  rcases hact with ⟨c, hc, hevt, hactT⟩
  have hevEvts : (activateChain w oid).events =
      w.events ++ [obsActEvt t oid] := by
    dsimp [activateChain, obsActEvt]
    rw [htick]
  have hnotEv : obsActEvt t oid ∉ w.events := by
    intro hev
    rcases hsrc (obsActEvt t oid) hev with
        ⟨hq, hhist⟩ | hactm | ⟨x, hx, hxt, hcx⟩
    · have := hhist.1 c hc hevt
      rw [hactT] at this
      omega
    · exact hne (obsActEvt t oid) hactm rfl
    · rcases cascadeSpawn_shape T specs h_valid x
        (obsActEvt t oid) hx hcx with
          ⟨j, hj, _, hej⟩ | ⟨j, hj, s', hs', _, hej⟩
      · exact obsEventOf_ne_stageEventOf T specs h_valid c j 0 hc hj
          (by omega) (hevt.symm.trans hej)
      · exact obsEventOf_ne_stageEventOf T specs h_valid c j (s' + 1)
          hc hj (by omega) (hevt.symm.trans hej)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hevEvts, List.nodup_append]
    refine ⟨hnd, nodup_singleton _, ?_⟩
    intro a ha b hb heq
    rcases List.mem_singleton.mp hb with rfl
    rw [heq] at ha
    exact hnotEv ha
  · intro id
    rw [activateChain_getNode_wiring w oid id, hwir]
  · intro f hf
    rw [hevEvts] at hf
    rcases List.mem_append.mp hf with hf | hf
    · exact hgood f hf
    · rcases List.mem_singleton.mp hf with rfl
      rw [hevt]
      exact Or.inl ⟨c, hc, rfl⟩
  · intro f hf
    rw [hevEvts] at hf
    rcases List.mem_append.mp hf with hf | hf
    · rcases hsrc f hf with hq | hact | hsp
      · exact Or.inl hq
      · exact Or.inr (Or.inl (List.mem_append.mpr (Or.inl hact)))
      · exact Or.inr (Or.inr hsp)
    · rcases List.mem_singleton.mp hf with rfl
      exact Or.inr (Or.inl (List.mem_append.mpr
        (Or.inr (List.mem_singleton.mpr rfl))))
  · intro e₀ he₀ ht₀ s hs
    rw [hevEvts] at he₀
    rcases List.mem_append.mp he₀ with he₀ | he₀
    · intro hsm
      rw [hevEvts] at hsm
      rcases List.mem_append.mp hsm with hsm | hsm
      · exact hfresh e₀ he₀ ht₀ s hs hsm
      · rcases List.mem_singleton.mp hsm with heqS
        rcases cascadeSpawn_shape T specs h_valid e₀ s hs
            (hgood e₀ he₀) with
            ⟨j, hj, _, hej⟩ | ⟨j, hj, s', hs', _, hej⟩
        · exact obsEventOf_ne_stageEventOf T specs h_valid c j 0 hc hj
            (by omega) (hevt.symm.trans (heqS.symm.trans hej))
        · exact obsEventOf_ne_stageEventOf T specs h_valid c j (s' + 1)
            hc hj (by omega) (hevt.symm.trans (heqS.symm.trans hej))
    · rcases List.mem_singleton.mp he₀ with rfl
      exfalso
      dsimp [obsActEvt] at ht₀
      omega

/-- A burst preserves the tick invariant, growing the activation
    list. -/
private theorem tickInv_simBurst (T : Nat) (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (t : Nat) (q₀ acts : List ScheduledEvent) (observers : List Nat)
    (pos : Nat → Nat → Nat) (w : World)
    (pairs : List (Nat × Nat))
    (htick : w.tick = t)
    (hinv : TickInv T specs t q₀ acts w)
    (hact : ∀ p ∈ pairs, ∀ oid, observers[p.1]? = some oid →
      ∃ c < specs.length, obsActEvt t oid = obsEventOf T specs c ∧
        actTickOf T specs c = t)
    (hne₀ : ∀ a ∈ acts, ∀ p ∈ pairs, ∀ oid,
      observers[p.1]? = some oid → a ≠ obsActEvt t oid)
    (hfresh : ∀ p ∈ pairs, ∀ oid, observers[p.1]? = some oid →
      ∀ q ∈ pairs, ∀ oid', observers[q.1]? = some oid' →
        obsActEvt t oid = obsActEvt t oid' → p = q)
    (hnp : pairs.Nodup) :
    TickInv T specs t q₀ (acts ++ obsActEvts t observers pairs)
      (simBurst t observers pos w pairs) := by
  induction pairs generalizing w acts with
  | nil =>
    dsimp [simBurst, obsActEvts]
    rw [List.append_nil]
    exact hinv
  | cons p ps ih =>
    rcases p with ⟨i, k⟩
    dsimp [simBurst, obsActEvts, List.foldl, List.filterMap]
    cases hobs : observers[i]? with
    | none =>
      dsimp
      apply ih
      · rw [processNEvents_tick]; exact htick
      · exact tickInv_processN T specs h_valid t q₀ acts w
          (pos t k) htick hinv
      · intro q hq
        exact hact q (List.mem_cons.mpr (Or.inr hq))
      · intro a ha q hq
        exact hne₀ a ha q (List.mem_cons.mpr (Or.inr hq))
      · intro q hq oid hobsq q' hq' oid' hobsq' heq
        exact hfresh q (List.mem_cons.mpr (Or.inr hq)) oid hobsq q'
          (List.mem_cons.mpr (Or.inr hq')) oid' hobsq' heq
      · exact (List.nodup_cons.mp hnp).2
    | some oid =>
      dsimp
      change TickInv T specs t q₀
        (acts ++ ([obsActEvt t oid] ++ obsActEvts t observers ps))
        (simBurst t observers pos
          (activateChain (processNEvents w (pos t k)) oid) ps)
      rw [← List.append_assoc]
      apply ih
      · rw [activateChain_tick, processNEvents_tick]
        exact htick
      · exact tickInv_activate T specs h_valid t q₀ acts
          (processNEvents w (pos t k)) oid
          (by rw [processNEvents_tick]; exact htick)
          (tickInv_processN T specs h_valid t q₀ acts w (pos t k)
            htick hinv)
          (hact (i, k) (List.mem_cons.mpr (Or.inl rfl)) oid hobs)
          (fun a ha => hne₀ a ha (i, k)
            (List.mem_cons.mpr (Or.inl rfl)) oid hobs)
      · intro q hq
        exact hact q (List.mem_cons.mpr (Or.inr hq))
      · intro a ha q hq oid' hobsq
        rcases List.mem_append.mp ha with ha | ha
        · exact hne₀ a ha q (List.mem_cons.mpr (Or.inr hq)) oid'
            hobsq
        · rcases List.mem_singleton.mp ha with rfl
          intro heq
          have hpq := hfresh (i, k) (List.mem_cons.mpr (Or.inl rfl))
            oid hobs q (List.mem_cons.mpr (Or.inr hq)) oid' hobsq
            heq
          have hqIn : (i, k) ∈ ps := by rw [hpq]; exact hq
          exact (List.nodup_cons.mp hnp).1 hqIn
      · intro q hq oid hobsq q' hq' oid' hobsq' heq
        exact hfresh q (List.mem_cons.mpr (Or.inr hq)) oid hobsq q'
          (List.mem_cons.mpr (Or.inr hq')) oid' hobsq' heq
      · exact (List.nodup_cons.mp hnp).2

/-- The full drain preserves the tick invariant. -/
private theorem tickInv_stepUNT (T : Nat) (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (t : Nat) (q₀ acts : List ScheduledEvent) (w : World)
    (htick : w.tick = t)
    (hinv : TickInv T specs t q₀ acts w) :
    TickInv T specs t q₀ acts w.stepUntilNextTick := by
  induction w using World.stepUntilNextTick.induct with
  | case1 x hstep =>
    rw [stepUntilNextTick_of_step_none x hstep]
    exact hinv
  | case2 x w' hstep ih =>
    have hsunt : x.stepUntilNextTick = w'.stepUntilNextTick := by
      rw [World.stepUntilNextTick, hstep]
    rw [hsunt]
    apply ih
    · exact (World.step_tick x w' hstep).trans htick
    · exact tickInv_pop_fire T specs h_valid t q₀ acts x w' htick
        hstep hinv

/-! ## History across tick boundaries -/

/-- `EventHistory` weakens when the tick advances. -/
theorem eventHistory_mono (T : Nat) (specs : List ChainSpec) (t : Nat)
    (e : ScheduledEvent) (hh : EventHistory T specs t e) :
    EventHistory T specs (t + 1) e := by
  dsimp [EventHistory] at hh ⊢
  refine ⟨fun i hi heq => by have := hh.1 i hi heq; omega,
    fun i hi heq => by have := hh.2.1 i hi heq; omega,
    fun i hi s hs heq => by have := hh.2.2 i hi s hs heq; omega⟩

/-- A chain's output id sits strictly before the next chain's base
    id. -/
private theorem chainOutputId_lt_nextBase (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (j : Nat) (hj : j < specs.length) :
    chainOutputId specs j < chainBaseId specs (j + 1) := by
  rw [chainBaseId_succ specs j hj]
  dsimp [chainOutputId, chainNodeCount]
  have hzip : ((specAt specs j).middleDelays.zip
      (specAt specs j).middlePriorities).length =
      (specAt specs j).middleDelays.length := by
    rw [List.length_zip, (h_valid j hj).1, min_self]
  dsimp [repLenAt]
  omega

/-- An output node id is never an in-range repeater node id. -/
theorem chainOutputId_ne_chainRepId_of_le_repLen
    (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (i j s' : Nat) (hi : i < specs.length) (hj : j < specs.length)
    (hs' : s' ≤ repLenAt specs i) :
    chainOutputId specs j ≠ chainRepId specs i s' := by
  intro h
  dsimp [chainOutputId, chainRepId] at h
  by_cases hij : i ≤ j
  · by_cases hij' : i < j
    · have hle : chainBaseId specs i + 2 + s' ≤
          chainBaseId specs i + 2 + repLenAt specs i := by omega
      have hlt : chainBaseId specs i + 2 + repLenAt specs i <
          chainBaseId specs (i + 1) := by
        rw [chainBaseId_succ specs i hi]
        dsimp [chainNodeCount]
        have hzip : ((specAt specs i).middleDelays.zip
            (specAt specs i).middlePriorities).length =
            (specAt specs i).middleDelays.length := by
          rw [List.length_zip, (h_valid i hi).1, min_self]
        dsimp [repLenAt]
        omega
      have hmono := chainBaseId_mono specs (i + 1) j (by omega)
      omega
    · have hij_eq : i = j := by omega
      subst hij_eq
      omega
  · have hlt := chainOutputId_lt_nextBase specs h_valid j hj
    dsimp [chainOutputId] at hlt
    have hmono := chainBaseId_mono specs (j + 1) i (by omega)
    omega

/-- An output node id is never an observer node id. -/
theorem chainOutputId_ne_chainObserverId
    (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (i j : Nat) (_ : i < specs.length) (hj : j < specs.length) :
    chainOutputId specs j ≠ chainObserverId specs i := by
  intro h
  dsimp [chainOutputId, chainObserverId] at h
  by_cases hij : i ≤ j
  · have hmono := chainBaseId_mono specs i j hij
    omega
  · have hlt := chainOutputId_lt_nextBase specs h_valid j hj
    dsimp [chainOutputId] at hlt
    have hmono := chainBaseId_mono specs (j + 1) i (by omega)
    omega

/-- An activation event fired at tick `t` carries history for tick
    `t + 1`. -/
theorem obsActEvt_EventHistory (T : Nat) (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (t oid c : Nat) (hc : c < specs.length)
    (hevt : obsActEvt t oid = obsEventOf T specs c)
    (hactT : actTickOf T specs c = t) :
    EventHistory T specs (t + 1) (obsActEvt t oid) := by
  dsimp [EventHistory]
  refine ⟨?_, ?_, ?_⟩
  · intro i hi heq
    have hic : c = i := obsEventOf_inj T specs c i hc hi
      (hevt.symm.trans heq)
    rw [← hic, hactT]
    omega
  · intro i hi heq
    exfalso
    exact obsEventOf_ne_stageEventOf T specs h_valid c i 0 hc hi
      (by omega) (hevt.symm.trans heq)
  · intro i hi s hs heq
    by_cases hle : s + 1 ≤ repLenAt specs i
    · exfalso
      exact obsEventOf_ne_stageEventOf T specs h_valid c i (s + 1) hc
        hi hle (hevt.symm.trans heq)
    · exfalso
      have hgt : s + 1 = repLenAt specs i + 1 := by omega
      have hnode := congrArg (fun ev => ev.nodeId)
        (hevt.symm.trans heq)
      dsimp [obsEventOf, stageEventOf] at hnode
      rw [hgt] at hnode
      have hfld : chainRepId specs i (repLenAt specs i + 1) =
          chainOutputId specs i := by
        dsimp [chainRepId, chainOutputId]
        omega
      rw [hfld] at hnode
      exact chainOutputId_ne_chainObserverId specs h_valid c i hc hi
        hnode.symm

/-- A cascade spawn of an event due at tick `t` carries history for
    tick `t + 1`. -/
theorem spawn_EventHistory (T : Nat) (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (t : Nat) (x : ScheduledEvent) (hx : IsCascadeEv T specs x)
    (htick : x.targetTick = t) (s : ScheduledEvent)
    (hs : s ∈ cascadeSpawn T specs x) :
    EventHistory T specs (t + 1) s := by
  rcases cascadeSpawn_shape T specs h_valid x s hs hx with
      ⟨i, hi, hxobs, heq⟩ | ⟨i, hi, s₀, hs₀, hxst, heq⟩
  · subst heq
    rw [hxobs] at htick
    dsimp [obsEventOf] at htick
    dsimp [EventHistory]
    refine ⟨?_, ?_, ?_⟩
    · intro j hj heqj
      exfalso
      exact obsEventOf_ne_stageEventOf T specs h_valid j i 0 hj hi
        (by omega) heqj.symm
    · intro j hj heqj
      have hpair := stageEventOf_inj T specs h_valid i j 0 0 hi hj
        (by omega) (by omega) heqj
      rw [← hpair.1, htick]
      omega
    · intro j hj u hu heqj
      by_cases hle : u + 1 ≤ repLenAt specs j
      · have hpair := stageEventOf_inj T specs h_valid i j 0 (u + 1)
          hi hj (by omega) hle heqj
        omega
      · exfalso
        have hgt : u + 1 = repLenAt specs j + 1 := by omega
        have hnode := congrArg (fun ev => ev.nodeId) heqj
        dsimp [stageEventOf] at hnode
        rw [hgt] at hnode
        have hfld : chainRepId specs j (repLenAt specs j + 1) =
            chainOutputId specs j := by
          dsimp [chainRepId, chainOutputId]
          omega
        rw [hfld] at hnode
        exact chainOutputId_ne_chainRepId_of_le_repLen specs h_valid
          i j 0 hi hj (by omega) hnode.symm
  · subst heq
    rw [hxst] at htick
    dsimp [stageEventOf] at htick
    dsimp [EventHistory]
    refine ⟨?_, ?_, ?_⟩
    · intro j hj heqj
      exfalso
      exact obsEventOf_ne_stageEventOf T specs h_valid j i (s₀ + 1) hj
        hi (by omega) heqj.symm
    · intro j hj heqj
      have hpair := stageEventOf_inj T specs h_valid i j (s₀ + 1) 0 hi
        hj (by omega) (by omega) heqj
      omega
    · intro j hj u hu heqj
      by_cases hle : u + 1 ≤ repLenAt specs j
      · have hpair := stageEventOf_inj T specs h_valid i j (s₀ + 1)
          (u + 1) hi hj (by omega) hle heqj
        rw [← hpair.1]
        have hus : u = s₀ := by omega
        rw [hus, htick]
        omega
      · exfalso
        have hgt : u + 1 = repLenAt specs j + 1 := by omega
        have hnode := congrArg (fun ev => ev.nodeId) heqj
        dsimp [stageEventOf] at hnode
        rw [hgt] at hnode
        have hfld : chainRepId specs j (repLenAt specs j + 1) =
            chainOutputId specs j := by
          dsimp [chainRepId, chainOutputId]
          omega
        rw [hfld] at hnode
        exact chainOutputId_ne_chainRepId_of_le_repLen specs h_valid
          i j (s₀ + 1) hi hj (by omega) hnode.symm

/-- At a tick boundary, reclassify every queued event as a survivor
    with history for the new tick. -/
theorem tickInv_next_history (T : Nat) (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (t : Nat) (q₀ acts : List ScheduledEvent) (w : World)
    (hinv : TickInv T specs t q₀ acts w)
    (hactH : ∀ a ∈ acts, EventHistory T specs (t + 1) a)
    (hactShape : ∀ a ∈ acts, ∃ c < specs.length,
      a = obsEventOf T specs c) :
    TickInv T specs (t + 1) w.events [] w := by
  rcases hinv with ⟨hnd, hwir, hgood, hsrc, hfresh⟩
  refine ⟨hnd, hwir, hgood, ?_, ?_⟩
  · intro e he
    refine Or.inl ⟨he, ?_⟩
    rcases hsrc e he with ⟨hq, hh⟩ | hact | ⟨x, hx, hxt, hcx⟩
    · exact eventHistory_mono T specs t e hh
    · exact hactH e hact
    · exact spawn_EventHistory T specs h_valid t x hcx hxt e hx
  · intro e₀ he₀ ht₀ s hs hsm
    have hc₀ : IsCascadeEv T specs e₀ := hgood e₀ he₀
    rcases hsrc s hsm with ⟨hq, hh⟩ | hact | ⟨y, hy, hyt, hcy⟩
    · rcases cascadeSpawn_shape T specs h_valid e₀ s hs hc₀ with
          ⟨i, hi, hx₀, heq⟩ | ⟨i, hi, s₀, hs₀, hx₀, heq⟩
      · have hlt := hh.2.1 i hi heq
        have htickI : obsTickOf T specs i = t + 1 := by
          have := congrArg ScheduledEvent.targetTick hx₀
          dsimp [obsEventOf] at this
          rw [ht₀] at this
          exact this.symm
        omega
      · have hlt := hh.2.2 i hi s₀ (by omega) heq
        have htickI : stageTickOf T specs i s₀ = t + 1 := by
          have := congrArg ScheduledEvent.targetTick hx₀
          dsimp [stageEventOf] at this
          rw [ht₀] at this
          exact this.symm
        omega
    · rcases hactShape s hact with ⟨c, hc, hsc⟩
      rcases cascadeSpawn_shape T specs h_valid e₀ s hs hc₀ with
          ⟨i, hi, _, heq⟩ | ⟨i, hi, s₀, hs₀, _, heq⟩
      · exfalso
        exact obsEventOf_ne_stageEventOf T specs h_valid c i 0 hc hi
          (by omega) (hsc.symm.trans heq)
      · exfalso
        exact obsEventOf_ne_stageEventOf T specs h_valid c i (s₀ + 1)
          hc hi (by omega) (hsc.symm.trans heq)
    · have heq₀ := cascadeSpawn_inj T specs h_valid e₀ y s hs hy hc₀
        hcy
      rw [heq₀] at ht₀
      rw [hyt] at ht₀
      omega

/-- `logOutput` preserves the tick invariant. -/
theorem tickInv_logOutput (T : Nat) (specs : List ChainSpec)
    (t : Nat) (q₀ acts : List ScheduledEvent) (w : World)
    (msg : String) (hinv : TickInv T specs t q₀ acts w) :
    TickInv T specs t q₀ acts (w.logOutput msg) := by
  rcases hinv with ⟨hnd, hwir, hgood, hsrc, hfresh⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · dsimp [World.logOutput]; exact hnd
  · intro id
    dsimp [World.logOutput, World.getNode]
    exact hwir id
  · intro e he
    dsimp [World.logOutput] at he
    exact hgood e he
  · intro e he
    dsimp [World.logOutput] at he
    exact hsrc e he
  · intro e₀ he₀ ht₀ s hs
    dsimp [World.logOutput] at he₀
    intro hsm
    dsimp [World.logOutput] at hsm
    exact hfresh e₀ he₀ ht₀ s hs hsm

/-- Membership in `obsActEvts` comes from one pair. -/
private theorem mem_obsActEvts (t : Nat) (observers : List Nat)
    (pairs : List (Nat × Nat)) (a : ScheduledEvent)
    (ha : a ∈ obsActEvts t observers pairs) :
    ∃ p ∈ pairs, ∃ oid, observers[p.1]? = some oid ∧
      a = obsActEvt t oid := by
  induction pairs with
  | nil => dsimp [obsActEvts] at ha; cases ha
  | cons p ps ih =>
    dsimp [obsActEvts, List.filterMap] at ha
    cases hp : observers[p.1]? with
    | none =>
      rw [hp] at ha
      dsimp at ha
      obtain ⟨q, hq, oid, hq', heq⟩ := ih ha
      exact ⟨q, List.mem_cons.mpr (Or.inr hq), oid, hq', heq⟩
    | some oid =>
      rw [hp] at ha
      dsimp at ha
      rcases List.mem_cons.mp ha with heq | h
      · exact ⟨p, List.mem_cons.mpr (Or.inl rfl), oid, hp, heq⟩
      · obtain ⟨q, hq, oid', hq', heq⟩ := ih h
        exact ⟨q, List.mem_cons.mpr (Or.inr hq), oid', hq', heq⟩

/-! ## Nodup of `zipIdx` -/

/-- Second components of `zipIdx` start at the offset. -/
private theorem zipIdx_snd_ge {α : Type} (l : List α) (m : Nat) :
    ∀ p ∈ l.zipIdx m, p.2 ≥ m := by
  induction l generalizing m with
  | nil => intro p h; dsimp [List.zipIdx] at h; cases h
  | cons a l ih =>
    intro p h
    have hcons : (a :: l).zipIdx m = (a, m) :: l.zipIdx (m + 1) := by
      dsimp [List.zipIdx]
    rw [hcons] at h
    rcases List.mem_cons.mp h with heq | h
    · have := congrArg Prod.snd heq
      dsimp at this
      omega
    · have := ih (m + 1) p h
      omega

/-- `zipIdx` never duplicates a pair. -/
theorem nodup_zipIdx {α : Type} (l : List α) (n : Nat) :
    (l.zipIdx n).Nodup := by
  induction l generalizing n with
  | nil => dsimp [List.zipIdx]; exact nodup_nil
  | cons a l ih =>
    have hcons : (a :: l).zipIdx n = (a, n) :: l.zipIdx (n + 1) := by
      dsimp [List.zipIdx]
    rw [hcons]
    apply List.nodup_cons.mpr
    refine ⟨?_, ih (n + 1)⟩
    intro h
    exact Nat.lt_irrefl n ((zipIdx_snd_ge l (n + 1) (a, n) h).trans
      (by omega))

/-! ## The tick invariant at every tick boundary -/

/-- At every tick boundary the simulated world satisfies the tick
    invariant, with every queued event carrying history. -/
theorem simWorld_tickInv (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length)) (t : Nat) :
    TickInv T specs t (simWorld T specs actOrd pos t).events []
      (simWorld T specs actOrd pos t) := by
  induction t with
  | zero =>
    rw [simWorld_zero]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [buildChains_events]; exact nodup_nil
    · intro id; rfl
    · intro e he
      rw [buildChains_events] at he
      cases he
    · intro e he
      rw [buildChains_events] at he
      cases he
    · intro e₀ he₀
      rw [buildChains_events] at he₀
      cases he₀
  | succ t ih =>
    rw [simWorld_succ]
    set wT := simWorld T specs actOrd pos t
    set observers := (buildChains specs).2
    dsimp only [simBody]
    set wLog := wT.logOutput s!"tick {wT.tick}"
    set F := actOrd.filter (fun i =>
      decide (i < observers.length) &&
        (actTickOf T specs i == wLog.tick))
    have htickT : wT.tick = t := by dsimp only [wT]; rw [simWorld_tick]
    have htickLog : wLog.tick = t := by
      dsimp only [wLog]; rw [World.logOutput_tick, htickT]
    rw [htickLog]
    have hinvLog := tickInv_logOutput T specs t wT.events [] wT
      s!"tick {wT.tick}" ih
    -- activation shape for pairs of this burst
    have hactF : ∀ p ∈ F.zipIdx, ∀ oid, observers[p.1]? = some oid →
        ∃ c < specs.length, obsActEvt t oid = obsEventOf T specs c ∧
          actTickOf T specs c = t := by
      intro p hp oid hobs
      obtain ⟨k, hkPos, hpk⟩ := List.exists_mem_zipIdx'.mp ⟨p, hp, rfl⟩
      have hp1 : p.1 = F[k] := congrArg Prod.fst hpk
      have hiF : p.1 ∈ F := by rw [hp1]; exact List.getElem_mem hkPos
      have hiLen : p.1 < observers.length := by
        have := (List.mem_filter.mp hiF).2
        rw [Bool.and_eq_true, decide_eq_true_eq] at this
        exact this.1
      have hactP : actTickOf T specs p.1 = wLog.tick := by
        have := (List.mem_filter.mp hiF).2
        rw [Bool.and_eq_true, decide_eq_true_eq] at this
        exact LawfulBEq.eq_of_beq this.2
      have hget : observers[p.1]? =
          some (chainObserverId specs p.1) := by
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
        rw [hactP, htickLog]
      · rw [hactP, htickLog]
    have hfreshB : ∀ p ∈ F.zipIdx, ∀ oid,
        observers[p.1]? = some oid → ∀ q ∈ F.zipIdx, ∀ oid',
          observers[q.1]? = some oid' →
            obsActEvt t oid = obsActEvt t oid' → p = q := by
      intro p hp oid hobs q hq oid' hobsq heq
      obtain ⟨k, hkPos, hpk⟩ := List.exists_mem_zipIdx'.mp ⟨p, hp, rfl⟩
      obtain ⟨k', hk'Pos, hqk⟩ :=
        List.exists_mem_zipIdx'.mp ⟨q, hq, rfl⟩
      have hp1 : p.1 = F[k] := congrArg Prod.fst hpk
      have hq1 : q.1 = F[k'] := congrArg Prod.fst hqk
      have hiF : p.1 ∈ F := by rw [hp1]; exact List.getElem_mem hkPos
      have hjF : q.1 ∈ F := by rw [hq1]; exact List.getElem_mem hk'Pos
      have hpLen : p.1 < specs.length := by
        have := (List.mem_filter.mp hiF).2
        rw [Bool.and_eq_true, decide_eq_true_eq] at this
        rw [← buildChains_observers_length]
        exact this.1
      have hqLen : q.1 < specs.length := by
        have := (List.mem_filter.mp hjF).2
        rw [Bool.and_eq_true, decide_eq_true_eq] at this
        rw [← buildChains_observers_length]
        exact this.1
      have hpLenO : p.1 < observers.length := by
        rw [buildChains_observers_length]; exact hpLen
      have hqLenO : q.1 < observers.length := by
        rw [buildChains_observers_length]; exact hqLen
      have hoid : oid = chainObserverId specs p.1 :=
        (Option.some_inj.mp (by
          rwa [List.getElem?_eq_getElem hpLenO,
            observers_getElem_eq_chainObserverId specs p.1 hpLenO]
            at hobs)).symm
      have hoid' : oid' = chainObserverId specs q.1 :=
        (Option.some_inj.mp (by
          rwa [List.getElem?_eq_getElem hqLenO,
            observers_getElem_eq_chainObserverId specs q.1 hqLenO]
            at hobsq)).symm
      have hnode : chainObserverId specs p.1 =
          chainObserverId specs q.1 := by
        have := congrArg (fun ev => ev.nodeId) heq
        dsimp [obsActEvt] at this
        rwa [hoid, hoid'] at this
      have hiEq : p.1 = q.1 :=
        chainObserverId_inj specs p.1 q.1 hpLen hqLen hnode
      have hFEq : F[k] = F[k'] := by rw [← hp1, ← hq1, hiEq]
      have hFnd : F.Nodup := by
        have hactNd : actOrd.Nodup :=
          h_perm.nodup_iff.mpr List.nodup_range
        exact hactNd.filter (fun i =>
          decide (i < observers.length) &&
            (actTickOf T specs i == wLog.tick))
      have hkk' : k = k' :=
        (hFnd.getElem_inj_iff (i := k) (hi := hkPos) (j := k')
          (hj := hk'Pos)).mp hFEq
      subst hkk'
      rw [hpk, hqk]
    have hBurst := tickInv_simBurst T specs h_valid t wT.events []
      observers pos wLog (F.zipIdx) htickLog hinvLog hactF
      (by intro a ha; cases ha) hfreshB (nodup_zipIdx F (n := 0))
    have hDrain := tickInv_stepUNT T specs h_valid t wT.events
      (obsActEvts t observers (F.zipIdx))
      (simBurst t observers pos wLog (F.zipIdx))
      (by rw [simBurst_tick, htickLog]) hBurst
    apply tickInv_next_history T specs h_valid t wT.events
      (obsActEvts t observers (F.zipIdx))
      (simBurst t observers pos wLog (F.zipIdx)).stepUntilNextTick
      hDrain ?_ ?_
    · intro a ha
      obtain ⟨p, hp, oid, hobs, rfl⟩ := mem_obsActEvts t observers
        (F.zipIdx) a ha
      obtain ⟨c, hc, hevt, hactT⟩ := hactF p hp oid hobs
      exact obsActEvt_EventHistory T specs h_valid t oid c hc hevt
        hactT
    · intro a ha
      obtain ⟨p, hp, oid, hobs, rfl⟩ := mem_obsActEvts t observers
        (F.zipIdx) a ha
      obtain ⟨c, hc, hevt, _⟩ := hactF p hp oid hobs
      exact ⟨c, hc, hevt⟩


/-! ## The burst world at a tick boundary -/

/-- The burst world of a tick (log + activations, before the drain)
    satisfies the tick invariant with the freshly fired observer
    events as the activation list. -/
theorem simBurst_tickInv (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat) (t : Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length)) :
    TickInv T specs t (simWorld T specs actOrd pos t).events
      (obsActEvts t (buildChains specs).2
        ((actOrd.filter (fun i =>
          decide (i < (buildChains specs).2.length) &&
            (actTickOf T specs i == t))).zipIdx))
      (simBurst t (buildChains specs).2 pos
        ((simWorld T specs actOrd pos t).logOutput
          s!"tick {(simWorld T specs actOrd pos t).tick}")
        ((actOrd.filter (fun i =>
          decide (i < (buildChains specs).2.length) &&
            (actTickOf T specs i == t))).zipIdx)) := by
  set wT := simWorld T specs actOrd pos t
  set observers := (buildChains specs).2
  set wLog := wT.logOutput s!"tick {wT.tick}"
  set F := actOrd.filter (fun i =>
    decide (i < observers.length) && (actTickOf T specs i == t))
  have htickT : wT.tick = t := by dsimp only [wT]; rw [simWorld_tick]
  have htickLog : wLog.tick = t := by
    dsimp only [wLog]; rw [World.logOutput_tick, htickT]
  have hinvLog := tickInv_logOutput T specs t wT.events [] wT
    s!"tick {wT.tick}" (simWorld_tickInv T specs actOrd pos h_valid h_perm t)
  have hactF : ∀ p ∈ F.zipIdx, ∀ oid, observers[p.1]? = some oid →
      ∃ c < specs.length, obsActEvt t oid = obsEventOf T specs c ∧
        actTickOf T specs c = t := by
    intro p hp oid hobs
    obtain ⟨k, hkPos, hpk⟩ := List.exists_mem_zipIdx'.mp ⟨p, hp, rfl⟩
    have hp1 : p.1 = F[k] := congrArg Prod.fst hpk
    have hiF : p.1 ∈ F := by rw [hp1]; exact List.getElem_mem hkPos
    have hiLen : p.1 < observers.length := by
      have := (List.mem_filter.mp hiF).2
      rw [Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.1
    have hactP : actTickOf T specs p.1 = t := by
      have := (List.mem_filter.mp hiF).2
      rw [Bool.and_eq_true, decide_eq_true_eq] at this
      exact LawfulBEq.eq_of_beq this.2
    have hget : observers[p.1]? =
        some (chainObserverId specs p.1) := by
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
  have hfreshB : ∀ p ∈ F.zipIdx, ∀ oid,
      observers[p.1]? = some oid → ∀ q ∈ F.zipIdx, ∀ oid',
        observers[q.1]? = some oid' →
          obsActEvt t oid = obsActEvt t oid' → p = q := by
    intro p hp oid hobs q hq oid' hobsq heq
    obtain ⟨k, hkPos, hpk⟩ := List.exists_mem_zipIdx'.mp ⟨p, hp, rfl⟩
    obtain ⟨k', hk'Pos, hqk⟩ :=
      List.exists_mem_zipIdx'.mp ⟨q, hq, rfl⟩
    have hp1 : p.1 = F[k] := congrArg Prod.fst hpk
    have hq1 : q.1 = F[k'] := congrArg Prod.fst hqk
    have hiF : p.1 ∈ F := by rw [hp1]; exact List.getElem_mem hkPos
    have hjF : q.1 ∈ F := by rw [hq1]; exact List.getElem_mem hk'Pos
    have hpLen : p.1 < specs.length := by
      have := (List.mem_filter.mp hiF).2
      rw [Bool.and_eq_true, decide_eq_true_eq] at this
      rw [← buildChains_observers_length]
      exact this.1
    have hqLen : q.1 < specs.length := by
      have := (List.mem_filter.mp hjF).2
      rw [Bool.and_eq_true, decide_eq_true_eq] at this
      rw [← buildChains_observers_length]
      exact this.1
    have hpLenO : p.1 < observers.length := by
      rw [buildChains_observers_length]; exact hpLen
    have hqLenO : q.1 < observers.length := by
      rw [buildChains_observers_length]; exact hqLen
    have hoid : oid = chainObserverId specs p.1 :=
      (Option.some_inj.mp (by
        rwa [List.getElem?_eq_getElem hpLenO,
          observers_getElem_eq_chainObserverId specs p.1 hpLenO]
          at hobs)).symm
    have hoid' : oid' = chainObserverId specs q.1 :=
      (Option.some_inj.mp (by
        rwa [List.getElem?_eq_getElem hqLenO,
          observers_getElem_eq_chainObserverId specs q.1 hqLenO]
          at hobsq)).symm
    have hnode : chainObserverId specs p.1 =
        chainObserverId specs q.1 := by
      have := congrArg (fun ev => ev.nodeId) heq
      dsimp [obsActEvt] at this
      rwa [hoid, hoid'] at this
    have hiEq : p.1 = q.1 :=
      chainObserverId_inj specs p.1 q.1 hpLen hqLen hnode
    have hFEq : F[k] = F[k'] := by rw [← hp1, ← hq1, hiEq]
    have hFnd : F.Nodup := by
      have hactNd : actOrd.Nodup :=
        h_perm.nodup_iff.mpr List.nodup_range
      exact hactNd.filter (fun i =>
        decide (i < observers.length) && (actTickOf T specs i == t))
    have hkk' : k = k' :=
      (hFnd.getElem_inj_iff (i := k) (hi := hkPos) (j := k')
        (hj := hk'Pos)).mp hFEq
    subst hkk'
    rw [hpk, hqk]
  exact tickInv_simBurst T specs h_valid t wT.events []
    observers pos wLog (F.zipIdx) htickLog hinvLog hactF
    (by intro a ha; cases ha) hfreshB (nodup_zipIdx F (n := 0))
