import Proofs.Model.DescentDrain

open BasicRedstoneSim
open World
open List

/-! # The descent step: stage `s` to stage `s + 1`

A same-spec class's stage-`s` events, due at their common firing tick,
fire and spawn the stage-`(s + 1)` events, which reach their own firing
tick in the same activation order. The transport below is `TickInv`-aware:
firing appends the cascade spawn only because the world is tick-invariant
(`CascadeGood` + wiring). -/

/-- A sublist stays a sublist when the host gains a prefix. -/
private theorem sublist_prefix_extend {α : Type} (v t u : List α)
    (h : t <+ u) : t <+ v ++ u := by
  induction v generalizing t u with
  | nil => simpa using h
  | cons x xs ih => exact Sublist.cons x (ih t u h)

/-! ## `processNEvents` spawn transport, invariant-carrying -/

/-- Spawns of the pops made by `processNEvents` accumulate as a sublist
    behind a not-due carry, while the tick invariant is preserved. -/
theorem tickInv_processNEvents_spawn_sublist (T : Nat)
    (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (t : Nat) (q₀ acts : List ScheduledEvent) (w : World) (n : Nat)
    (acc : List ScheduledEvent)
    (htick : w.tick = t) (hinv : TickInv T specs t q₀ acts w)
    (hacc : acc <+ w.events) (haccFut : ∀ e ∈ acc, e.targetTick ≠ t) :
    acc ++ spawnFold (cascadeSpawn T specs) ((popSeq w).take n) <+
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
        have hgood : CascadeGood T specs w := hinv.2.2.1
        have hwiring : ∀ id, (w.getNode id).map wiring =
            ((buildChains specs).1.getNode id).map wiring := hinv.2.1
        have haccWp : acc <+ wp.events := by
          obtain ⟨idx, hidx, herase, htickE, hget⟩ :=
            popNextEvent_eraseIdx w e wp hpop
          rw [herase]
          apply sublist_eraseIdx_of_notMem_nth hacc idx hidx
          rw [hget]
          intro he
          exact haccFut e he (by rw [htickE, htick])
        have htickW1 : w1'.tick = t := by
          dsimp [w1']
          rw [World.onScheduledTick_tick,
            World.popNextEvent_tick w e wp hpop, htick]
        have hacc' : acc ++ cascadeSpawn T specs e <+ w1'.events := by
          have hfireE := firing_cascadeSpawn_eq T specs h_valid w e wp hpop
            hgood hwiring
          dsimp [w1'] at hfireE ⊢
          rw [hfireE]
          exact Sublist.append haccWp (Sublist.refl (cascadeSpawn T specs e))
        have haccFut' : ∀ e' ∈ acc ++ cascadeSpawn T specs e,
            e'.targetTick ≠ t := by
          intro e' he'
          rcases List.mem_append.mp he' with he' | he'
          · exact haccFut e' he'
          · have hcl : IsCascadeEv T specs e := hgood e hdue.2
            have hgt := cascadeSpawn_target_gt T specs h_valid e e' t
              he' hcl (by rw [hdue.1, htick])
            omega
        have hinv1 := tickInv_pop_fire T specs h_valid t q₀ acts w w1'
          htick (by dsimp [World.step, w1']; rw [hpop]) hinv
        exact ih w1' (acc ++ cascadeSpawn T specs e) htickW1 hinv1 hacc'
          haccFut'

/-! ## Drain transport, invariant-carrying -/

/-- The drain fires the whole pop sequence, appending the cascade spawn
    at each step; the tick invariant is preserved throughout. -/
theorem stepUntilNextTick_drain_tickInv (T : Nat) (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (t : Nat) (q₀ acts : List ScheduledEvent) (w : World)
    (htick : w.tick = t) (hinv : TickInv T specs t q₀ acts w) :
    w.stepUntilNextTick.tick = w.tick + 1 ∧
    w.stepUntilNextTick.events =
      eraseEvents w.events (popSeq w) ++
        spawnFold (cascadeSpawn T specs) (popSeq w) := by
  induction w using World.stepUntilNextTick.induct with
  | case1 x hstep =>
    have hnone : x.popNextEvent = none := by
      dsimp [World.step] at hstep
      cases hp : x.popNextEvent <;> simp_all
    have hseq : popSeq x = [] := popSeq_of_popNextEvent_none x hnone
    rw [stepUntilNextTick_of_step_none x hstep]
    refine ⟨rfl, ?_⟩
    rw [hseq]
    dsimp [eraseEvents, spawnFold]
    rw [List.append_nil]
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
      set es := popSeq (wp.onScheduledTick e0.nodeId) with hesdef
      have hseq : popSeq x = e0 :: es := by
        rw [popSeq_of_popNextEvent_some x e0 wp hpop, hesdef]
      have hstepUNT : x.stepUntilNextTick =
          (wp.onScheduledTick e0.nodeId).stepUntilNextTick := by
        rw [World.stepUntilNextTick]
        dsimp [World.step]
        rw [hpop]
      obtain ⟨idx, hidx, herase, hget, htickE, _, hfirst⟩ :=
        popNextEvent_first_occ x e0 wp hpop
      have hwpEv : wp.events = eraseEvents x.events ((popSeq x).take 1) := by
        rw [hseq]
        change wp.events = eraseEvents x.events [e0]
        rw [herase, eraseIdx_eq_eraseEv x.events idx hidx e0 hget hfirst]
        dsimp [eraseEvents]
      have hframe0 : ∀ id, id ∉ ((popSeq x).take 0).map (fun e => e.nodeId) →
          wp.getNode id = x.getNode id := by
        intro id hid
        dsimp [World.getNode]
        rw [popNextEvent_nodes x e0 wp hpop]
      obtain ⟨_, hev0, _, _, _⟩ := drain_fire_eq T specs h_valid t q₀ acts x
        htick hinv
        0 (by rw [hseq]; exact Nat.zero_lt_succ _) wp
        (World.popNextEvent_tick x e0 wp hpop)
        (by rw [hwpEv]; dsimp [spawnFold]; rw [List.append_nil])
        hframe0
      have hev0' : (wp.onScheduledTick e0.nodeId).events =
          wp.events ++ cascadeSpawn T specs e0 := by
        simpa [hseq] using hev0
      have hinv' := tickInv_pop_fire T specs h_valid t q₀ acts x
        (wp.onScheduledTick e0.nodeId) htick
        (by dsimp [World.step]; rw [hpop]) hinv
      have htick' : (wp.onScheduledTick e0.nodeId).tick = t := by
        rw [World.onScheduledTick_tick, World.popNextEvent_tick x e0 wp hpop,
          htick]
      obtain ⟨htik', hevs'⟩ := ih htick' hinv'
      refine ⟨?_, ?_⟩
      · rw [hstepUNT, htik', World.onScheduledTick_tick,
          World.popNextEvent_tick x e0 wp hpop]
      · rw [hstepUNT, hevs', hesdef, hev0']
        have havoid : ∀ e ∈ es, e ∉ cascadeSpawn T specs e0 := by
          intro e he
          have hdue : e.targetTick = x.tick := by
            have := popSeq_mem_due (wp.onScheduledTick e0.nodeId) e
              (by rwa [← hesdef])
            rw [this.1, World.onScheduledTick_tick,
              World.popNextEvent_tick x e0 wp hpop]
          intro hm
          have hgt := cascadeSpawn_target_gt T specs h_valid e0 e x.tick hm
            (hinv.2.2.1 e0 (by rw [← hget]; exact List.getElem_mem hidx))
            htickE
          omega
        rw [eraseEvents_append_right wp.events (cascadeSpawn T specs e0) es
          havoid]
        have htake : (popSeq x).take 1 = [e0] := by rw [hseq]; rfl
        rw [hwpEv, htake]
        rw [← eraseEvents_append x.events [e0] es]
        dsimp [spawnFold]
        rw [hseq]
        exact List.append_assoc _ _ _

/-- The drain's spawns, over any sublist of the pop sequence, embed into
    the drained world's events. -/
theorem tickInv_stepUNT_spawn_sublist (T : Nat) (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (t : Nat) (q₀ acts : List ScheduledEvent) (w : World)
    (htick : w.tick = t) (hinv : TickInv T specs t q₀ acts w)
    (es : List ScheduledEvent) (hes : es <+ popSeq w) :
    spawnFold (cascadeSpawn T specs) es <+ w.stepUntilNextTick.events := by
  obtain ⟨_, hevs⟩ := stepUntilNextTick_drain_tickInv T specs h_valid t
    q₀ acts w htick hinv
  rw [hevs]
  exact sublist_prefix_extend (eraseEvents w.events (popSeq w))
    (spawnFold (cascadeSpawn T specs) es)
    (spawnFold (cascadeSpawn T specs) (popSeq w))
    (spawnFold_sublist (cascadeSpawn T specs) hes)

/-! ## Burst transport, invariant-carrying -/

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

/-- The spawns of the events a burst pops appear in pop order as a
    sublist of the burst's final events, while the tick invariant is
    preserved (with the activation list grown). -/
theorem tickInv_simBurst_spawn_sublist (T : Nat) (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (t : Nat) (q₀ acts : List ScheduledEvent) (observers : List Nat)
    (pos : Nat → Nat → Nat) (w : World) (pairs : List (Nat × Nat))
    (acc : List ScheduledEvent)
    (htick : w.tick = t) (hinv : TickInv T specs t q₀ acts w)
    (hact : ∀ p ∈ pairs, ∀ oid, observers[p.1]? = some oid →
      ∃ c < specs.length, obsActEvt t oid = obsEventOf T specs c ∧
        actTickOf T specs c = t)
    (hne₀ : ∀ a ∈ acts, ∀ p ∈ pairs, ∀ oid,
      observers[p.1]? = some oid → a ≠ obsActEvt t oid)
    (hfresh : ∀ p ∈ pairs, ∀ oid, observers[p.1]? = some oid →
      ∀ q ∈ pairs, ∀ oid', observers[q.1]? = some oid' →
        obsActEvt t oid = obsActEvt t oid' → p = q)
    (hnp : pairs.Nodup)
    (hacc : acc <+ w.events) (haccFut : ∀ e ∈ acc, e.targetTick ≠ t) :
    ∃ m, acc ++ spawnFold (cascadeSpawn T specs) ((popSeq w).take m) <+
        (simBurst t observers pos w pairs).events ∧
      popSeq (simBurst t observers pos w pairs) = (popSeq w).drop m ∧
      TickInv T specs t q₀ (acts ++ obsActEvts t observers pairs)
        (simBurst t observers pos w pairs) := by
  induction pairs generalizing w acc acts with
  | nil =>
    refine ⟨0, ?_, ?_, ?_⟩
    · simp [simBurst, List.take, spawnFold]
      exact hacc
    · simp [simBurst]
    · dsimp [simBurst, obsActEvts]
      rw [List.append_nil]
      exact hinv
  | cons p ps ih =>
    rcases p with ⟨i, k⟩
    dsimp [simBurst, obsActEvts, List.foldl, List.filterMap]
    set nProc := pos t k with hnProc
    set wP := processNEvents w nProc with hwP
    have hspawnP := tickInv_processNEvents_spawn_sublist T specs h_valid t
      q₀ acts w nProc acc htick hinv hacc haccFut
    have htickP : wP.tick = t := by
      dsimp [wP]; rw [processNEvents_tick, htick]
    have hinvP : TickInv T specs t q₀ acts wP := by
      dsimp [wP]
      exact tickInv_processN T specs h_valid t q₀ acts w nProc htick hinv
    have hfutP : ∀ e ∈ acc ++ spawnFold (cascadeSpawn T specs)
        ((popSeq w).take nProc), e.targetTick ≠ t := by
      intro e he
      rcases List.mem_append.mp he with he | he
      · exact haccFut e he
      · obtain ⟨x, hx, hex⟩ :=
          mem_spawnFold (cascadeSpawn T specs) _ e he
        have hdue := popSeq_mem_due w x (List.mem_of_mem_take hx)
        have hgt := cascadeSpawn_target_gt T specs h_valid x e t hex
          (hinv.2.2.1 x hdue.2) (by rw [hdue.1, htick])
        omega
    have hpopP : popSeq wP = (popSeq w).drop nProc := by
      dsimp [wP]; rw [popSeq_processNEvents]
    cases hobs : observers[i]? with
    | none =>
      dsimp
      have hact' : ∀ p ∈ ps, ∀ oid', observers[p.1]? = some oid' →
          ∃ c < specs.length, obsActEvt t oid' = obsEventOf T specs c ∧
            actTickOf T specs c = t := by
        intro q hq oid' hobsq
        exact hact q (List.mem_cons.mpr (Or.inr hq)) oid' hobsq
      have hne' : ∀ a ∈ acts, ∀ p ∈ ps, ∀ oid',
          observers[p.1]? = some oid' → a ≠ obsActEvt t oid' := by
        intro a ha q hq oid' hobsq
        exact hne₀ a ha q (List.mem_cons.mpr (Or.inr hq)) oid' hobsq
      have hfresh' : ∀ p ∈ ps, ∀ oid', observers[p.1]? = some oid' →
          ∀ q ∈ ps, ∀ oid'', observers[q.1]? = some oid'' →
            obsActEvt t oid' = obsActEvt t oid'' → p = q := by
        intro q hq oid' hobsq q' hq' oid'' hobsq' heq
        exact hfresh q (List.mem_cons.mpr (Or.inr hq)) oid' hobsq q'
          (List.mem_cons.mpr (Or.inr hq')) oid'' hobsq' heq
      have hnp' : ps.Nodup := (List.nodup_cons.mp hnp).2
      obtain ⟨m1, hsub1, hdrop1, hinv1⟩ := ih acts wP
        (acc ++ spawnFold (cascadeSpawn T specs) ((popSeq w).take nProc))
        htickP hinvP hact' hne' hfresh' hnp' hspawnP hfutP
      refine ⟨nProc + m1, ?_, ?_, ?_⟩
      · change acc ++ spawnFold (cascadeSpawn T specs)
            ((popSeq w).take (nProc + m1)) <+
          (simBurst t observers pos wP ps).events
        rw [take_add_take_drop, spawnFold_append, ← List.append_assoc]
        rw [hpopP] at hsub1
        exact hsub1
      · change popSeq (simBurst t observers pos wP ps) =
          (popSeq w).drop (nProc + m1)
        rw [hdrop1, hpopP, drop_drop_add]
      · exact hinv1
    | some oid =>
      dsimp
      set wA := activateChain wP oid with hwA
      have haccA : acc ++ spawnFold (cascadeSpawn T specs)
          ((popSeq w).take nProc) <+ wA.events := by
        dsimp [wA]
        rw [activateChain_events]
        apply sublist_append_of_sublist_left
        exact hspawnP
      have htickA : wA.tick = t := by
        dsimp [wA]; rw [activateChain_tick, processNEvents_tick, htick]
      have hinvA : TickInv T specs t q₀ (acts ++ [obsActEvt t oid]) wA := by
        dsimp [wA]
        exact tickInv_activate T specs h_valid t q₀ acts wP oid htickP
          hinvP
          (hact (i, k) (List.mem_cons.mpr (Or.inl rfl)) oid hobs)
          (fun a ha => hne₀ a ha (i, k)
            (List.mem_cons.mpr (Or.inl rfl)) oid hobs)
      have hact' : ∀ p ∈ ps, ∀ oid', observers[p.1]? = some oid' →
          ∃ c < specs.length, obsActEvt t oid' = obsEventOf T specs c ∧
            actTickOf T specs c = t := by
        intro q hq oid' hobsq
        exact hact q (List.mem_cons.mpr (Or.inr hq)) oid' hobsq
      have hne' : ∀ a ∈ acts ++ [obsActEvt t oid], ∀ p ∈ ps, ∀ oid',
          observers[p.1]? = some oid' → a ≠ obsActEvt t oid' := by
        intro a ha q hq oid' hobsq
        rcases List.mem_append.mp ha with ha | ha
        · exact hne₀ a ha q (List.mem_cons.mpr (Or.inr hq)) oid' hobsq
        · rcases List.mem_singleton.mp ha with rfl
          intro heq
          have hpq := hfresh (i, k) (List.mem_cons.mpr (Or.inl rfl))
            oid hobs q (List.mem_cons.mpr (Or.inr hq)) oid' hobsq heq
          have hqIn : (i, k) ∈ ps := by rw [hpq]; exact hq
          exact (List.nodup_cons.mp hnp).1 hqIn
      have hfresh' : ∀ p ∈ ps, ∀ oid', observers[p.1]? = some oid' →
          ∀ q ∈ ps, ∀ oid'', observers[q.1]? = some oid'' →
            obsActEvt t oid' = obsActEvt t oid'' → p = q := by
        intro q hq oid' hobsq q' hq' oid'' hobsq' heq
        exact hfresh q (List.mem_cons.mpr (Or.inr hq)) oid' hobsq q'
          (List.mem_cons.mpr (Or.inr hq')) oid'' hobsq' heq
      have hnp' : ps.Nodup := (List.nodup_cons.mp hnp).2
      obtain ⟨m1, hsub1, hdrop1, hinv1⟩ := ih (acts ++ [obsActEvt t oid])
        wA
        (acc ++ spawnFold (cascadeSpawn T specs) ((popSeq w).take nProc))
        htickA hinvA hact' hne' hfresh' hnp' haccA hfutP
      refine ⟨nProc + m1, ?_, ?_, ?_⟩
      · change acc ++ spawnFold (cascadeSpawn T specs)
            ((popSeq w).take (nProc + m1)) <+
          (simBurst t observers pos wA ps).events
        rw [take_add_take_drop, spawnFold_append, ← List.append_assoc]
        rw [popSeq_activateChain, hpopP] at hsub1
        exact hsub1
      · change popSeq (simBurst t observers pos wA ps) =
          (popSeq w).drop (nProc + m1)
        rw [hdrop1, popSeq_activateChain, hpopP, drop_drop_add]
      · change TickInv T specs t q₀
          (acts ++ ([obsActEvt t oid] ++ obsActEvts t observers ps))
          (simBurst t observers pos wA ps)
        rw [← List.append_assoc]
        exact hinv1

/-! ## The full tick transport -/

private theorem nil_sublist_of (l : List ScheduledEvent) : [] <+ l := by
  induction l with
  | nil => exact Sublist.slnil
  | cons x xs ih => exact Sublist.cons x ih

/-- The spawns of every event popped across a whole tick (burst and drain
    together) appear in pop order in the next tick-start world's events. -/
theorem simWorld_popSeq_spawn_sublist (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat) (t : Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length)) :
    spawnFold (cascadeSpawn T specs) (popSeq (simWorld T specs actOrd pos t)) <+
      (simWorld T specs actOrd pos (t + 1)).events := by
  rw [simWorld_succ]
  set wT := simWorld T specs actOrd pos t
  set observers := (buildChains specs).2
  have htickT : wT.tick = t := by dsimp [wT]; rw [simWorld_tick]
  dsimp only [simBody]
  rw [World.logOutput_tick, htickT]
  set wL := wT.logOutput s!"tick {t}" with hwL
  set F := actOrd.filter (fun i =>
    decide (i < observers.length) && (actTickOf T specs i == t))
  set wB := simBurst t observers pos wL F.zipIdx with hwB
  have htickL : wL.tick = t := by
    dsimp [wL]; exact htickT
  have hinvL : TickInv T specs t wT.events [] wL := by
    dsimp [wL]
    simpa [htickT] using tickInv_logOutput T specs t wT.events [] wT
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
  have hfreshB : ∀ p ∈ F.zipIdx, ∀ oid, observers[p.1]? = some oid →
      ∀ q ∈ F.zipIdx, ∀ oid', observers[q.1]? = some oid' →
        obsActEvt t oid = obsActEvt t oid' → p = q := by
    intro p hp oid hobs q hq oid' hobsq heq
    obtain ⟨k, hkPos, hpk⟩ := List.exists_mem_zipIdx'.mp ⟨p, hp, rfl⟩
    obtain ⟨k', hk'Pos, hqk⟩ := List.exists_mem_zipIdx'.mp ⟨q, hq, rfl⟩
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
    have hnode : chainObserverId specs p.1 = chainObserverId specs q.1 := by
      have := congrArg (fun ev => ev.nodeId) heq
      dsimp [obsActEvt] at this
      rwa [hoid, hoid'] at this
    have hiEq : p.1 = q.1 := chainObserverId_inj specs p.1 q.1 hpLen hqLen
      hnode
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
  obtain ⟨m, hsubB, hdropB, hinvB⟩ :=
    tickInv_simBurst_spawn_sublist T specs h_valid t wT.events []
      observers pos wL F.zipIdx [] htickL hinvL hactF
      (by intro a ha; cases ha) hfreshB (nodup_zipIdx F (n := 0))
      (nil_sublist_of wL.events) (by simp)
  have hsubB' : spawnFold (cascadeSpawn T specs) ((popSeq wL).take m) <+
      wB.events := by simpa using hsubB
  have htickB : wB.tick = t := by dsimp [wB]; rw [simBurst_tick, htickL]
  have hburstFut : ∀ e ∈ spawnFold (cascadeSpawn T specs)
      ((popSeq wL).take m), e.targetTick ≠ wB.tick := by
    intro e he
    obtain ⟨x, hx, hex⟩ := mem_spawnFold (cascadeSpawn T specs) _ e he
    have hdue := popSeq_mem_due wL x (List.mem_of_mem_take hx)
    have hgt := cascadeSpawn_target_gt T specs h_valid x e t hex
      (hinvL.2.2.1 x hdue.2) (by rw [hdue.1, htickL])
    rw [htickB]
    omega
  have herase : spawnFold (cascadeSpawn T specs) ((popSeq wL).take m) <+
      eraseEvents wB.events (popSeq wB) := by
    apply eraseEvents_sublist_of_notMem (popSeq wB) hsubB'
    intro e he hm
    exact hburstFut e hm (popSeq_mem_due wB e he).1
  have htail : spawnFold (cascadeSpawn T specs) ((popSeq wL).drop m) <+
      spawnFold (cascadeSpawn T specs) (popSeq wB) := by
    rw [hdropB]
  have hdrain := tickInv_stepUNT_spawn_sublist T specs h_valid t wT.events
    (obsActEvts t observers F.zipIdx) wB htickB hinvB (popSeq wB)
    (Sublist.refl (popSeq wB))
  have hpopL : popSeq wL = popSeq wT := by
    apply popSeq_congr_due wL wT
    · rw [hwL]; exact World.logOutput_tick wT _
    · rw [hwL]; dsimp [wL, World.logOutput]
  have hsplit : spawnFold (cascadeSpawn T specs) (popSeq wL) =
      spawnFold (cascadeSpawn T specs) ((popSeq wL).take m) ++
        spawnFold (cascadeSpawn T specs) ((popSeq wL).drop m) := by
    rw [← spawnFold_append]
    congr 1
    exact (List.take_append_drop m (popSeq wL)).symm
  change spawnFold (cascadeSpawn T specs) (popSeq wT) <+
    wB.stepUntilNextTick.events
  obtain ⟨_, hevsB⟩ := stepUntilNextTick_drain_tickInv T specs h_valid t
    wT.events (obsActEvts t observers F.zipIdx) wB htickB hinvB
  rw [← hpopL, hsplit, hevsB]
  exact Sublist.append herase htail

/-! ## Surviving many ticks -/

/-- A sublist whose events all fire at or after tick `t + n` survives `n`
    ticks unchanged. -/
theorem simWorld_sublist_survive_delta (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat) (t n : Nat)
    (evts : List ScheduledEvent)
    (hs : evts <+ (simWorld T specs actOrd pos t).events)
    (hgt : ∀ e ∈ evts, t + n ≤ e.targetTick) :
    evts <+ (simWorld T specs actOrd pos (t + n)).events := by
  induction n generalizing t with
  | zero =>
    simpa using hs
  | succ n ih =>
    have hsurv := simWorld_sublist_survive T specs actOrd pos t evts hs
      (by intro e he; have := hgt e he; omega)
    have hgt' : ∀ e ∈ evts, (t + 1) + n ≤ e.targetTick := by
      intro e he
      have := hgt e he
      omega
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ih (t + 1) hsurv hgt'

/-! ## Stage spawns equal the successor class -/

private theorem spawnFold_cascade_map_stage (T : Nat) (specs : List ChainSpec)
    (s : Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (l : List Nat) (hi_class : ∀ i ∈ l, i < specs.length)
    (hs : ∀ i ∈ l, s < repLenAt specs i) :
    spawnFold (cascadeSpawn T specs) (l.map (stageEventOf T specs · s)) =
      l.map (stageEventOf T specs · (s + 1)) := by
  induction l with
  | nil => dsimp [spawnFold, List.map]
  | cons i rest ih =>
    dsimp [spawnFold, List.map]
    rw [cascadeSpawn_stage T specs h_valid i s (hi_class i
      (List.mem_cons.mpr (Or.inl rfl)))
      (hs i (List.mem_cons.mpr (Or.inl rfl)))]
    have ih' := ih (fun j hj => hi_class j (List.mem_cons.mpr (Or.inr hj)))
      (fun j hj => hs j (List.mem_cons.mpr (Or.inr hj)))
    dsimp [spawnFold] at ih'
    rw [ih']
    rfl

/-- The cascade spawns of a class's stage-`s` events are exactly its
    stage-`(s + 1)` events. -/
theorem spawnFold_classStageEvts_succ (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (c : ChainSpec) (s : Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (hi_class : ∀ i ∈ classActOrder specs actOrd c, i < specs.length)
    (hs : ∀ i ∈ classActOrder specs actOrd c, s < repLenAt specs i) :
    spawnFold (cascadeSpawn T specs) (classStageEvts T specs actOrd c s) =
      classStageEvts T specs actOrd c (s + 1) := by
  dsimp [classStageEvts]
  exact spawnFold_cascade_map_stage T specs s h_valid
    (classActOrder specs actOrd c) hi_class hs

/-! ## The descent step -/

/-- Stage `s` events due at their firing tick spawn the stage `s + 1`
    events, which reach their own firing tick in the same activation
    order. -/
theorem classStageEvts_next_due (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat) (c : ChainSpec)
    (s i₀ : Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (hi₀ : i₀ ∈ classActOrder specs actOrd c)
    (hi_class : ∀ i ∈ classActOrder specs actOrd c, i < specs.length)
    (hs : ∀ i ∈ classActOrder specs actOrd c, s < repLenAt specs i)
    (h_ind : classStageEvts T specs actOrd c s <+
      (simWorld T specs actOrd pos (stageTickOf T specs i₀ s)).events.filter
        (fun e => e.targetTick == stageTickOf T specs i₀ s &&
          e.priority == stagePriAt specs i₀ s)) :
    classStageEvts T specs actOrd c (s + 1) <+
      (simWorld T specs actOrd pos
        (stageTickOf T specs i₀ (s + 1))).events.filter
        (fun e => e.targetTick == stageTickOf T specs i₀ (s + 1) &&
          e.priority == stagePriAt specs i₀ (s + 1)) := by
  set τ := stageTickOf T specs i₀ s
  set p := stagePriAt specs i₀ s
  set τ' := stageTickOf T specs i₀ (s + 1)
  set p' := stagePriAt specs i₀ (s + 1)
  set d := (stageDelayAt specs i₀ (s + 1) : Nat)
  have hspec : ∀ i ∈ classActOrder specs actOrd c, specAt specs i = c := by
    intro i hi
    dsimp [classActOrder] at hi
    exact of_decide_eq_true (List.mem_filter.mp hi).2
  have h_ind_pop : classStageEvts T specs actOrd c s <+
      (popSeq (simWorld T specs actOrd pos τ)).filter
        (fun e => e.priority == p) := by
    have hpp := filter_popSeq_priority (simWorld T specs actOrd pos τ) p
    rw [simWorld_tick] at hpp
    rw [hpp]
    exact h_ind
  have h_ind_pseq : classStageEvts T specs actOrd c s <+
      popSeq (simWorld T specs actOrd pos τ) :=
    Sublist.trans h_ind_pop
      (List.filter_sublist (l := popSeq (simWorld T specs actOrd pos τ))
        (p := fun e => e.priority == p))
  have hspawn : spawnFold (cascadeSpawn T specs)
      (classStageEvts T specs actOrd c s) <+
      spawnFold (cascadeSpawn T specs) (popSeq (simWorld T specs actOrd pos τ)) :=
    spawnFold_sublist (cascadeSpawn T specs) h_ind_pseq
  have htrans : spawnFold (cascadeSpawn T specs)
      (popSeq (simWorld T specs actOrd pos τ)) <+
      (simWorld T specs actOrd pos (τ + 1)).events :=
    simWorld_popSeq_spawn_sublist T specs actOrd pos τ h_valid h_perm
  have heq : spawnFold (cascadeSpawn T specs)
      (classStageEvts T specs actOrd c s) =
      classStageEvts T specs actOrd c (s + 1) :=
    spawnFold_classStageEvts_succ T specs actOrd c s h_valid hi_class hs
  have hnext : classStageEvts T specs actOrd c (s + 1) <+
      (simWorld T specs actOrd pos (τ + 1)).events := by
    rw [← heq]
    exact Sublist.trans hspawn htrans
  have hd : 1 ≤ d := by
    dsimp [d]
    have h2 : 2 ≤ (stageDelayAt specs i₀ (s + 1) : Nat) :=
      ValidDelay.ge2 (stageDelayAt_valid specs h_valid i₀ (s + 1)
        (hi_class i₀ hi₀))
    omega
  have hτd : τ' = τ + d := by
    dsimp [τ', τ, d]
    rw [stageTickOf_succ T specs i₀ s (by
      have hsi := hs i₀ hi₀
      dsimp [repLenAt] at hsi
      omega)]
  have hgt : ∀ e ∈ classStageEvts T specs actOrd c (s + 1),
      (τ + 1) + (d - 1) ≤ e.targetTick := by
    intro e he
    obtain ⟨i, hi, heq⟩ := List.mem_map.mp he
    rw [← heq]
    dsimp [stageEventOf]
    rw [stageTickOf_spec T specs i i₀ (s + 1)
      (by rw [hspec i hi, hspec i₀ hi₀])]
    rw [stageTickOf_succ T specs i₀ s (by
      have hsi := hs i₀ hi₀
      dsimp [repLenAt] at hsi
      omega)]
    dsimp [τ, d]
    omega
  have hsurv := simWorld_sublist_survive_delta T specs actOrd pos (τ + 1)
    (d - 1) (classStageEvts T specs actOrd c (s + 1)) hnext hgt
  have hsurv' : classStageEvts T specs actOrd c (s + 1) <+
      (simWorld T specs actOrd pos τ').events := by
    have harg : (τ + 1) + (d - 1) = τ' := by omega
    simpa [harg] using hsurv
  apply sublist_filter_of_forall
    (fun e => e.targetTick == τ' && e.priority == p') hsurv'
  intro e he
  obtain ⟨i, hi, heq⟩ := List.mem_map.mp he
  rw [← heq]
  dsimp [stageEventOf]
  rw [Bool.and_eq_true]
  constructor
  · change decide (stageTickOf T specs i (s + 1) = τ') = true
    rw [decide_eq_true_eq]
    rw [stageTickOf_spec T specs i i₀ (s + 1)
      (by rw [hspec i hi, hspec i₀ hi₀])]
  · change decide (stagePriAt specs i (s + 1) = p') = true
    rw [decide_eq_true_eq]
    rw [stagePriAt_spec specs i i₀ (s + 1)
      (by rw [hspec i hi, hspec i₀ hi₀])]



