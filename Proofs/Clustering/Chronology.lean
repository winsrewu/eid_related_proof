import Proofs.Model.Basic
import Proofs.Model.ListOrder
import Proofs.Model.OutputPos
import Proofs.Model.DescentConclusion
import Proofs.Model.ChainIds
import Proofs.Model.DrainOrder
import Proofs.Model.LogBridge
import Proofs.Model.DescentDrain
import Mathlib.Data.List.Perm.Basic


open BasicRedstoneSim
open List

/-! # Chronological transport for the clustering descent

The FIFO tiebreak, per-tick order transport, survivor-before-spawn ordering,
enqueue-tick realization, and the `lastRep_index_gt_of_delay_lt` chronological
half of the descent. -/

/-- Among equal-priority events in the pop sequence, the pop order is the
    queue order: an earlier pop has a smaller first-occurrence index in the
    world's event queue. This is the FIFO tiebreak that grounds the descent
    below. -/
theorem popSeq_same_priority_findIdx_order (w : World) {x y : ScheduledEvent}
    (hx : x ∈ popSeq w) (hy : y ∈ popSeq w)
    (hnodup : w.events.Nodup) (hpopNd : (popSeq w).Nodup)
    (hpri : x.priority = y.priority)
    (hb : (_root_.findIdx? (fun e => decide (e = x)) (popSeq w)).getD 0 <
          (_root_.findIdx? (fun e => decide (e = y)) (popSeq w)).getD 0) :
    (_root_.findIdx? (fun e => decide (e = x)) w.events).getD 0 <
      (_root_.findIdx? (fun e => decide (e = y)) w.events).getD 0 := by
  have hxfil : x ∈ (popSeq w).filter (fun e => e.priority == x.priority) := by
    rw [List.mem_filter]
    exact ⟨hx, beq_self_eq_true x.priority⟩
  have hyfil : y ∈ (popSeq w).filter (fun e => e.priority == x.priority) := by
    rw [List.mem_filter]
    exact ⟨hy, by rw [hpri]; exact beq_self_eq_true y.priority⟩
  have hfp := filter_popSeq_priority w x.priority
  have hsub1 : (popSeq w).filter (fun e => e.priority == x.priority) <+ popSeq w :=
    List.filter_sublist (l := popSeq w) (p := fun e => e.priority == x.priority)
  have hsub2 : (popSeq w).filter (fun e => e.priority == x.priority) <+ w.events := by
    rw [hfp]
    exact List.filter_sublist (l := w.events)
      (p := fun e => e.targetTick == w.tick && e.priority == x.priority)
  have hb_fil : (_root_.findIdx? (fun e => decide (e = x))
      ((popSeq w).filter (fun e => e.priority == x.priority))).getD 0 <
        (_root_.findIdx? (fun e => decide (e = y))
          ((popSeq w).filter (fun e => e.priority == x.priority))).getD 0 :=
    (findIdx?_getD_lt_sublist (l₁ := (popSeq w).filter (fun e => e.priority == x.priority))
      (l₂ := popSeq w) hsub1 hpopNd hxfil hyfil).mp hb
  exact (findIdx?_getD_lt_sublist (l₁ := (popSeq w).filter (fun e => e.priority == x.priority))
    (l₂ := w.events) hsub2 hnodup hxfil hyfil).mpr hb_fil

/-- The converse of `popSeq_same_priority_findIdx_order`: among equal-priority
    events due at the current tick, the queue (events-list) order implies the
    pop order. -/
theorem events_same_priority_findIdx_order (w : World) {x y : ScheduledEvent}
    (hx : x ∈ popSeq w) (hy : y ∈ popSeq w)
    (hnodup : w.events.Nodup) (hpopNd : (popSeq w).Nodup)
    (hpri : x.priority = y.priority)
    (hb : (_root_.findIdx? (fun e => decide (e = x)) w.events).getD 0 <
          (_root_.findIdx? (fun e => decide (e = y)) w.events).getD 0) :
    (_root_.findIdx? (fun e => decide (e = x)) (popSeq w)).getD 0 <
      (_root_.findIdx? (fun e => decide (e = y)) (popSeq w)).getD 0 := by
  have hxfil : x ∈ (popSeq w).filter (fun e => e.priority == x.priority) := by
    rw [List.mem_filter]
    exact ⟨hx, beq_self_eq_true x.priority⟩
  have hyfil : y ∈ (popSeq w).filter (fun e => e.priority == x.priority) := by
    rw [List.mem_filter]
    exact ⟨hy, by rw [hpri]; exact beq_self_eq_true y.priority⟩
  have hfp := filter_popSeq_priority w x.priority
  have hsub1 : (popSeq w).filter (fun e => e.priority == x.priority) <+ popSeq w :=
    List.filter_sublist (l := popSeq w) (p := fun e => e.priority == x.priority)
  have hsub2 : (popSeq w).filter (fun e => e.priority == x.priority) <+ w.events := by
    rw [hfp]
    exact List.filter_sublist (l := w.events)
      (p := fun e => e.targetTick == w.tick && e.priority == x.priority)
  have hb_fil : (_root_.findIdx? (fun e => decide (e = x))
      ((popSeq w).filter (fun e => e.priority == x.priority))).getD 0 <
        (_root_.findIdx? (fun e => decide (e = y))
          ((popSeq w).filter (fun e => e.priority == x.priority))).getD 0 :=
    (findIdx?_getD_lt_sublist (l₁ := (popSeq w).filter (fun e => e.priority == x.priority))
      (l₂ := w.events) hsub2 hnodup hxfil hyfil).mp hb
  exact (findIdx?_getD_lt_sublist (l₁ := (popSeq w).filter (fun e => e.priority == x.priority))
    (l₂ := popSeq w) hsub1 hpopNd hxfil hyfil).mpr hb_fil

/-- A pair of events that both survive a tick boundary (not due at the
    current tick) keeps its queue order across `simWorld`'s one-tick step. -/
theorem simWorld_succ_order_preserved
    (T : Nat) (specs : List ChainSpec) (actOrd : List Nat) (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (t : Nat) {e₁ e₂ : ScheduledEvent}
    (he₁ : e₁ ∈ (simWorld T specs actOrd pos t).events)
    (he₂ : e₂ ∈ (simWorld T specs actOrd pos t).events)
    (htgt₁ : e₁.targetTick > t) (htgt₂ : e₂.targetTick > t)
    (hb : (_root_.findIdx? (fun a => decide (a = e₁))
            (simWorld T specs actOrd pos t).events).getD 0 <
          (_root_.findIdx? (fun a => decide (a = e₂))
            (simWorld T specs actOrd pos t).events).getD 0) :
    (_root_.findIdx? (fun a => decide (a = e₁))
        (simWorld T specs actOrd pos (t + 1)).events).getD 0 <
      (_root_.findIdx? (fun a => decide (a = e₂))
        (simWorld T specs actOrd pos (t + 1)).events).getD 0 := by
  set wT := simWorld T specs actOrd pos t
  set observers := (buildChains specs).2
  have htickT : wT.tick = t := by dsimp only [wT]; rw [simWorld_tick]
  set carry := wT.events.filter (fun e => e.targetTick > t)
  have hc : carry <+ wT.events := by
    dsimp only [carry]
    exact List.filter_sublist (l := wT.events) (p := fun e => e.targetTick > t)
  have hcarryfut : ∀ e ∈ carry, e.targetTick ≠ t := by
    intro e he
    exact ne_of_gt (of_decide_eq_true (List.mem_filter.mp he).2)
  have he₁c : e₁ ∈ carry := by
    dsimp only [carry]
    rw [List.mem_filter]
    exact ⟨he₁, decide_eq_true_eq.mpr htgt₁⟩
  have he₂c : e₂ ∈ carry := by
    dsimp only [carry]
    rw [List.mem_filter]
    exact ⟨he₂, decide_eq_true_eq.mpr htgt₂⟩
  have hsubNext : carry <+ (simWorld T specs actOrd pos (t + 1)).events := by
    rw [simWorld_succ]
    dsimp only [simBody]
    rw [World.logOutput_tick, htickT]
    set wL := wT.logOutput s!"tick {t}"
    set F := actOrd.filter (fun i =>
      decide (i < observers.length) && (actTickOf T specs i == t))
    set wB := simBurst t observers pos wL F.zipIdx
    have htickL : wL.tick = t := by dsimp only [wL]; rw [World.logOutput_tick, htickT]
    have htickB : wB.tick = t := by dsimp only [wB]; rw [simBurst_tick, htickL]
    have hburst := simBurst_sublist_carry t observers pos wL F.zipIdx
      carry (by simpa [wL] using hc) (by intro e he; rw [htickL]; exact hcarryfut e he) htickL
    have hcarryB : carry <+ wB.events := by
      dsimp only [wB]
      exact Sublist.trans
        (by simp)
        hburst
    have hdrain := stepUntilNextTick_sublist_carry wB carry hcarryB
      (by intro e he; rw [htickB]; exact hcarryfut e he)
    simpa [wB] using hdrain
  have hnodup_t : wT.events.Nodup :=
    (simWorld_tickInv T specs actOrd pos h_valid h_perm t).1
  have hnodup_next : (simWorld T specs actOrd pos (t + 1)).events.Nodup :=
    (simWorld_tickInv T specs actOrd pos h_valid h_perm (t + 1)).1
  have hb_carry : (_root_.findIdx? (fun a => decide (a = e₁)) carry).getD 0 <
      (_root_.findIdx? (fun a => decide (a = e₂)) carry).getD 0 :=
    (findIdx?_getD_lt_sublist (l₁ := carry) (l₂ := wT.events) hc hnodup_t he₁c he₂c).mp hb
  exact (findIdx?_getD_lt_sublist (l₁ := carry)
    (l₂ := (simWorld T specs actOrd pos (t + 1)).events)
    hsubNext hnodup_next he₁c he₂c).mpr hb_carry

/-- A survivor of the current tick precedes an event spawned by the tick's
    drain in the next tick-start queue: the drain keeps surviving events as a
    prefix and appends the cascade spawns after it. -/
theorem simWorld_succ_survivor_before_spawn
    (T : Nat) (specs : List ChainSpec) (actOrd : List Nat) (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (t : Nat) {e₁ e₂ : ScheduledEvent}
    (he₁ : e₁ ∈ (simWorld T specs actOrd pos t).events)
    (htgt₁ : e₁.targetTick > t)
    (he₂spawn : e₂ ∈ spawnFold (cascadeSpawn T specs)
        (popSeq (simBurst t (buildChains specs).2 pos
          ((simWorld T specs actOrd pos t).logOutput s!"tick {t}")
          ((actOrd.filter (fun i =>
            decide (i < (buildChains specs).2.length) &&
              (actTickOf T specs i == t))).zipIdx)))) :
    (_root_.findIdx? (fun a => decide (a = e₁))
        (simWorld T specs actOrd pos (t + 1)).events).getD 0 <
      (_root_.findIdx? (fun a => decide (a = e₂))
        (simWorld T specs actOrd pos (t + 1)).events).getD 0 := by
  set wT := simWorld T specs actOrd pos t
  set observers := (buildChains specs).2
  have htickT : wT.tick = t := by dsimp only [wT]; rw [simWorld_tick]
  set wL := wT.logOutput s!"tick {t}"
  set F := actOrd.filter (fun i =>
    decide (i < observers.length) && (actTickOf T specs i == t))
  set wB := simBurst t observers pos wL F.zipIdx
  have htickB : wB.tick = t := by
    dsimp only [wB]; rw [simBurst_tick]
    dsimp only [wL]; rw [World.logOutput_tick, htickT]
  have hinvB : TickInv T specs t wT.events (obsActEvts t observers F.zipIdx) wB := by
    simpa [wB, wL, F, observers, wT, htickT] using
      (simBurst_tickInv T specs actOrd pos t h_valid h_perm)
  have hdrain := stepUntilNextTick_drain_tickInv T specs h_valid t wT.events
    (obsActEvts t observers F.zipIdx) wB htickB hinvB
  have hevNext : (simWorld T specs actOrd pos (t + 1)).events =
      eraseEvents wB.events (popSeq wB) ++
        spawnFold (cascadeSpawn T specs) (popSeq wB) := by
    rw [simWorld_succ]
    dsimp only [simBody]
    rw [World.logOutput_tick, htickT]
    exact hdrain.2
  have htickL : wL.tick = t := by dsimp only [wL]; rw [World.logOutput_tick, htickT]
  -- e₁ survives the burst (not due at tick t)
  have hburst := simBurst_sublist_carry t observers pos wL F.zipIdx
    [e₁] (by
      dsimp only [wL]
      rw [World.logOutput_events]
      exact List.singleton_sublist.mpr he₁)
    (by intro e he; rw [List.mem_singleton] at he; subst he; rw [htickL]; exact ne_of_gt htgt₁)
    htickL
  have he₁B : e₁ ∈ wB.events := by
    dsimp only [wB]
    have : [e₁] <+ wB.events := Sublist.trans
      (by simp)
      hburst
    exact (List.singleton_sublist.mp this)
  have he₁_not_due : e₁ ∉ popSeq wB := by
    intro h
    have hdue := (popSeq_mem_due wB e₁ h).1
    rw [htickB] at hdue
    omega
  have he₁erase : e₁ ∈ eraseEvents wB.events (popSeq wB) := by
    have hsub₁ : [e₁] <+ wB.events := List.singleton_sublist.mpr he₁B
    have hx : ∀ e ∈ popSeq wB, e ∉ [e₁] := by
      intro e he hmem
      rw [List.mem_singleton] at hmem
      subst e
      exact he₁_not_due he
    exact List.singleton_sublist.mp
      (eraseEvents_sublist_of_notMem (popSeq wB) hsub₁ hx)
  have he₂spawn' : e₂ ∈ spawnFold (cascadeSpawn T specs) (popSeq wB) := by
    simpa [wB, wL, F, observers] using he₂spawn
  -- The final queue is nodup; a spawn lives in the suffix, so it cannot also
  -- be a survivor (in the prefix).
  have hnodup_next : (simWorld T specs actOrd pos (t + 1)).events.Nodup :=
    (simWorld_tickInv T specs actOrd pos h_valid h_perm (t + 1)).1
  have hdisj : ∀ a ∈ eraseEvents wB.events (popSeq wB),
      ∀ b ∈ spawnFold (cascadeSpawn T specs) (popSeq wB), a ≠ b := by
    have hnd : (eraseEvents wB.events (popSeq wB) ++
        spawnFold (cascadeSpawn T specs) (popSeq wB)).Nodup := by
      simpa [hevNext] using hnodup_next
    exact (List.nodup_append.mp hnd).2.2
  have he₂_not_surv : e₂ ∉ eraseEvents wB.events (popSeq wB) := by
    intro h
    exact hdisj e₂ h e₂ he₂spawn' rfl
  rw [hevNext]
  exact findIdx?_lt_of_prefix_mem (eraseEvents wB.events (popSeq wB))
    (spawnFold (cascadeSpawn T specs) (popSeq wB)) he₁erase
    (by rw [List.mem_append]; exact Or.inr he₂spawn') he₂_not_surv

/-- Across one tick, the surviving events (not due at the current tick) form a
    prefix of the next tick-start queue, and every cascade spawn of the tick
    (whether fired by the burst's `processNEvents` or by the drain) appears
    after them. -/
theorem simWorld_succ_survivors_before_spawns
    (T : Nat) (specs : List ChainSpec) (actOrd : List Nat) (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length)) (t : Nat) :
    (simWorld T specs actOrd pos t).events.filter (fun e => e.targetTick > t) ++
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
  set carry := wT.events.filter (fun e => e.targetTick > t)
  have htickL : wL.tick = t := by
    dsimp [wL]; exact htickT
  have hinvL : TickInv T specs t wT.events [] wL := by
    dsimp [wL]
    simpa [htickT] using tickInv_logOutput T specs t wT.events [] wT
      s!"tick {wT.tick}" (simWorld_tickInv T specs actOrd pos h_valid h_perm t)
  have hacc : carry <+ wL.events := by
    dsimp only [carry]
    have : wT.events.filter (fun e => e.targetTick > t) <+ wT.events :=
      List.filter_sublist (l := wT.events) (p := fun e => e.targetTick > t)
    simp [wL]
  have haccFut : ∀ e ∈ carry, e.targetTick ≠ t := by
    intro e he
    exact ne_of_gt (of_decide_eq_true (List.mem_filter.mp he).2)
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
    have hiEq : p.1 = q.1 := chainObserverId_inj specs p.1 q.1 hpLen hqLen hnode
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
      observers pos wL F.zipIdx carry htickL hinvL hactF
      (by intro a ha; cases ha) hfreshB (nodup_zipIdx F (n := 0)) hacc haccFut
  have htickB : wB.tick = t := by dsimp [wB]; rw [simBurst_tick, htickL]
  have hnot_due : ∀ e ∈ carry ++ spawnFold (cascadeSpawn T specs)
      ((popSeq wL).take m), e.targetTick ≠ wB.tick := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · rw [htickB]
      exact haccFut e he
    · obtain ⟨x, hx, hex⟩ := mem_spawnFold (cascadeSpawn T specs) _ e he
      have hdue := popSeq_mem_due wL x (List.mem_of_mem_take hx)
      have hgt := cascadeSpawn_target_gt T specs h_valid x e t hex
        (hinvL.2.2.1 x hdue.2) (by rw [hdue.1, htickL])
      rw [htickB]
      omega
  have herase : carry ++ spawnFold (cascadeSpawn T specs) ((popSeq wL).take m) <+
      eraseEvents wB.events (popSeq wB) := by
    apply eraseEvents_sublist_of_notMem (popSeq wB) hsubB
    intro e he hm
    exact hnot_due e hm (popSeq_mem_due wB e he).1
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
  change carry ++ spawnFold (cascadeSpawn T specs) (popSeq wT) <+
    wB.stepUntilNextTick.events
  obtain ⟨_, hevsB⟩ := stepUntilNextTick_drain_tickInv T specs h_valid t
    wT.events (obsActEvts t observers F.zipIdx) wB htickB hinvB
  rw [← hpopL, hsplit, hevsB]
  rw [← List.append_assoc]
  exact Sublist.append herase htail

/-- A due event is popped within its due count worth of fuel. -/
private theorem mem_popSeqFuel_count (w : World) (e : ScheduledEvent)
    (he : e ∈ w.events) (hdue : e.targetTick = w.tick) :
    e ∈ popSeqFuel w (World.countEventAtThisTick w w.tick) := by
  induction hc : World.countEventAtThisTick w w.tick using Nat.strong_induction_on
    generalizing w e with
  | h n ih =>
    have hcpos : 0 < World.countEventAtThisTick w w.tick := by
      dsimp [World.countEventAtThisTick]
      have hmem : e ∈ w.events.filter (fun ev => ev.targetTick == w.tick) := by
        rw [List.mem_filter]
        exact ⟨he, by simpa [beq_iff_eq] using hdue⟩
      have hne : w.events.filter (fun ev => ev.targetTick == w.tick) ≠ [] := by
        intro hnil; rw [hnil] at hmem; cases hmem
      exact List.length_pos_iff_ne_nil.mpr hne
    cases hpop : w.popNextEvent with
    | none =>
      have hc0 : World.countEventAtThisTick w w.tick = 0 := popNextEvent_none_count_zero w hpop
      omega
    | some pr =>
      rcases pr with ⟨e₀, wp⟩
      rw [← hc]
      have hcsucc : World.countEventAtThisTick w w.tick =
          Nat.succ (World.countEventAtThisTick w w.tick - 1) := by omega
      rw [hcsucc]
      dsimp [popSeqFuel]
      rw [hpop]
      dsimp
      by_cases heq : e = e₀
      · subst e
        exact List.mem_cons.mpr (Or.inl rfl)
      · have herase := World.popNextEvent_eraseIdx w e₀ wp hpop
        rcases herase with ⟨idx, hidx, hwpEv, htickE₀, hget⟩
        have he_wp : e ∈ wp.events := by
          rw [hwpEv]
          have hsub₁ : [e] <+ w.events := List.singleton_sublist.mpr he
          have hnth : w.events[idx] ∉ [e] := by
            intro h
            rw [List.mem_singleton] at h
            exact heq (hget.symm.trans h).symm
          have hsub : [e] <+ w.events.eraseIdx idx :=
            sublist_eraseIdx_of_notMem_nth hsub₁ idx hidx hnth
          exact List.singleton_sublist.mp hsub
        have he_fire : e ∈ (wp.onScheduledTick e₀.nodeId).events := by
          obtain ⟨news, happ, _⟩ := World.onScheduledTick_events_append wp e₀.nodeId
          rw [happ]
          exact List.mem_append.mpr (Or.inl he_wp)
        have hdue_fire : e.targetTick = (wp.onScheduledTick e₀.nodeId).tick := by
          rw [World.onScheduledTick_tick, World.popNextEvent_tick w e₀ wp hpop]
          exact hdue
        have hcount_fire : World.countEventAtThisTick (wp.onScheduledTick e₀.nodeId)
            (wp.onScheduledTick e₀.nodeId).tick =
              World.countEventAtThisTick w w.tick - 1 := by
          rw [World.onScheduledTick_tick, World.onScheduledTick_countEventAtThisTick wp e₀.nodeId,
            World.popNextEvent_tick w e₀ wp hpop]
          exact (World.popNextEvent_remove_one_current_tick_event_if_some w e₀ wp hpop).2
        have hsmall : World.countEventAtThisTick (wp.onScheduledTick e₀.nodeId)
            (wp.onScheduledTick e₀.nodeId).tick < n := by
          rw [hcount_fire, ← hc]
          omega
        have hmem := ih (World.countEventAtThisTick (wp.onScheduledTick e₀.nodeId)
          (wp.onScheduledTick e₀.nodeId).tick) hsmall
          (wp.onScheduledTick e₀.nodeId) e he_fire hdue_fire
        have hmem' : e ∈ popSeqFuel (wp.onScheduledTick e₀.nodeId)
            (World.countEventAtThisTick w w.tick - 1) := by
          simpa [hcount_fire] using hmem
        exact List.mem_cons.mpr (Or.inr hmem')

/-- A due event of a world is always popped by the tick's drain. -/
theorem mem_popSeq_of_due (w : World) (e : ScheduledEvent)
    (he : e ∈ w.events) (hdue : e.targetTick = w.tick) :
    e ∈ popSeq w := by
  dsimp [popSeq]
  have hle : World.countEventAtThisTick w w.tick ≤ w.events.length := by
    dsimp [World.countEventAtThisTick]
    exact List.length_filter_le (fun ev => ev.targetTick == w.tick) w.events
  have hext := popSeqFuel_extend w (World.countEventAtThisTick w w.tick)
    (w.events.length - World.countEventAtThisTick w w.tick) (Nat.le_refl _)
  have hlen : World.countEventAtThisTick w w.tick +
      (w.events.length - World.countEventAtThisTick w w.tick) = w.events.length := by omega
  rw [← hlen, hext]
  exact mem_popSeqFuel_count w e he hdue

/-- A single chain's stage-`s` repeater event is present in the queue at its
    firing tick. -/
theorem stageEvent_present (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (c : Nat) (hc : c < specs.length)
    (_h_fit : chainDelay (specAt specs c) ≤ T)
    (s : Nat) (hs : s ≤ repLenAt specs c) :
    stageEventOf T specs c s ∈
      (simWorld T specs actOrd pos (stageTickOf T specs c s)).events := by
  have hi₀ : c ∈ classActOrder specs actOrd (specAt specs c) := by
    dsimp [classActOrder]
    rw [List.mem_filter]
    exact ⟨h_perm.mem_iff.mpr (List.mem_range.mpr hc), by simp⟩
  have hi_class : ∀ i ∈ classActOrder specs actOrd (specAt specs c), i < specs.length := by
    intro i hi
    exact List.mem_range.mp ((h_perm.mem_iff).mp (List.mem_filter.mp hi).1)
  have hstage : classStageEvts T specs actOrd (specAt specs c) s <+
      (simWorld T specs actOrd pos (stageTickOf T specs c s)).events.filter
        (fun e => e.targetTick == stageTickOf T specs c s &&
          e.priority == stagePriAt specs c s) := by
    induction s with
    | zero =>
      exact classStageEvts_zero_due T specs actOrd pos (specAt specs c) c
        h_valid h_perm hi₀ hi_class
    | succ s' ih =>
      have hs' : s' < repLenAt specs c := Nat.lt_of_succ_le hs
      exact classStageEvts_next_due T specs actOrd pos (specAt specs c) s' c
        h_valid h_perm hi₀ hi_class
        (fun i hi => by
          rw [repLenAt_spec specs i c (by
            have hspec_i : specAt specs i = specAt specs c := by
              dsimp [classActOrder] at hi
              exact of_decide_eq_true (List.mem_filter.mp hi).2
            exact hspec_i)]
          exact hs')
        (ih (Nat.le_of_lt hs'))
  have hmem : stageEventOf T specs c s ∈ classStageEvts T specs actOrd (specAt specs c) s := by
    dsimp [classStageEvts]
    exact List.mem_map.mpr ⟨c, hi₀, rfl⟩
  have hmem' : stageEventOf T specs c s ∈
      (simWorld T specs actOrd pos (stageTickOf T specs c s)).events.filter
        (fun e => e.targetTick == stageTickOf T specs c s &&
          e.priority == stagePriAt specs c s) :=
    List.Sublist.mem hmem hstage
  exact (List.mem_filter.mp hmem').1

/-- The last-repeater of a chain with at least one middle repeater is enqueued
    when its predecessor (the last middle repeater) fires, at tick
    `T - lastDelay`. -/
theorem lastRep_pred_tick (T : Nat) (specs : List ChainSpec) (i : Nat)
    (h_fit : chainDelay (specAt specs i) ≤ T)
    (hn : 0 < repLenAt specs i) :
    stageTickOf T specs i (repLenAt specs i - 1) =
      T - (specAt specs i).lastDelay := by
  have hrep : repLenAt specs i = (specAt specs i).middleDelays.length := rfl
  have hs : (repLenAt specs i - 1) + 1 ≤ (specAt specs i).middleDelays.length := by
    rw [hrep]
    omega
  have hpre : (repLenAt specs i - 1) + 1 = repLenAt specs i := by omega
  have hsucc := stageTickOf_succ T specs i (repLenAt specs i - 1) hs
  have hsucc' : stageTickOf T specs i (repLenAt specs i) =
      stageTickOf T specs i (repLenAt specs i - 1) +
        (stageDelayAt specs i (repLenAt specs i) : Nat) := by
    simpa [hpre] using hsucc
  have hdelay : stageDelayAt specs i (repLenAt specs i) = (specAt specs i).lastDelay :=
    stageDelayAt_of_eq specs i (by simp [repLenAt])
  have hlast := stageTickOf_last T specs i h_fit
  have hle : ((specAt specs i).lastDelay : Nat) ≤ T := by
    have hfit' : 2 + ((specAt specs i).middleDelays.map (fun d => (d : Nat))).sum +
        ((specAt specs i).lastDelay : Nat) ≤ T := by
      simpa [chainDelay, ChainSpec.totalDelay] using h_fit
    omega
  rw [hdelay] at hsucc'
  rw [hlast] at hsucc'
  omega

/-- A chain with no middle repeaters enqueues its last-repeater when its
    observer fires, at tick `T - lastDelay`. -/
theorem obsTickOf_zero (T : Nat) (specs : List ChainSpec) (i : Nat)
    (h_fit : chainDelay (specAt specs i) ≤ T)
    (hz : repLenAt specs i = 0) :
    obsTickOf T specs i = T - (specAt specs i).lastDelay := by
  have hmid : (specAt specs i).middleDelays = [] := by
    cases h : (specAt specs i).middleDelays with
    | nil => rfl
    | cons d rest =>
      have hlen : rest.length + 1 = 0 := by
        have : (d :: rest).length = 0 := by
          rw [← h]
          simpa [repLenAt] using hz
        simp at this
      omega
  have hcd : chainDelay (specAt specs i) = 2 + ((specAt specs i).lastDelay : Nat) := by
    dsimp [chainDelay, ChainSpec.totalDelay]
    rw [hmid]
    simp
  dsimp [obsTickOf, actTickOf]
  rw [hcd]
  have hle2 : ((specAt specs i).lastDelay : Nat) ≤ T := by
    have := h_fit
    rw [hcd] at this
    omega
  omega

/-- Forward membership for the spawn fold. -/
theorem mem_spawnFold_of_mem (spawn : ScheduledEvent → List ScheduledEvent)
    (l : List ScheduledEvent) (e : ScheduledEvent) (x : ScheduledEvent)
    (hx : x ∈ l) (he : e ∈ spawn x) :
    e ∈ spawnFold spawn l := by
  induction l with
  | nil => cases hx
  | cons a rest ih =>
    simp [spawnFold]
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact Or.inl he
    · exact Or.inr ⟨x, hx', he⟩

/-- The last-repeater of a chain with at least one middle repeater is spawned
    by its predecessor at tick `T - lastDelay`. -/
theorem lastRep_mem_spawn_pos (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (c : Nat) (hc : c < specs.length)
    (h_fit : chainDelay (specAt specs c) ≤ T)
    (hpos : 0 < repLenAt specs c) :
    stageEventOf T specs c (repLenAt specs c) ∈
      spawnFold (cascadeSpawn T specs)
        (popSeq (simWorld T specs actOrd pos (T - (specAt specs c).lastDelay))) := by
  have hticks : stageTickOf T specs c (repLenAt specs c - 1) =
      T - (specAt specs c).lastDelay :=
    lastRep_pred_tick T specs c h_fit hpos
  have hpresent : stageEventOf T specs c (repLenAt specs c - 1) ∈
      (simWorld T specs actOrd pos (T - (specAt specs c).lastDelay)).events := by
    have hp := stageEvent_present T specs actOrd pos h_valid h_perm c hc h_fit
      (repLenAt specs c - 1) (by omega)
    simpa [hticks] using hp
  have hdue : (stageEventOf T specs c (repLenAt specs c - 1)).targetTick =
      T - (specAt specs c).lastDelay := by
    dsimp [stageEventOf]
    rw [hticks]
  have hpop : stageEventOf T specs c (repLenAt specs c - 1) ∈
      popSeq (simWorld T specs actOrd pos (T - (specAt specs c).lastDelay)) := by
    have htick := simWorld_tick T specs actOrd pos (T - (specAt specs c).lastDelay)
    exact mem_popSeq_of_due
      (simWorld T specs actOrd pos (T - (specAt specs c).lastDelay))
      (stageEventOf T specs c (repLenAt specs c - 1)) hpresent (by simpa [htick] using hdue)
  have hspawn : cascadeSpawn T specs (stageEventOf T specs c (repLenAt specs c - 1)) =
      [stageEventOf T specs c (repLenAt specs c)] := by
    have hsucc : repLenAt specs c - 1 + 1 = repLenAt specs c := by omega
    simpa [hsucc] using (cascadeSpawn_stage T specs h_valid c
      (repLenAt specs c - 1) hc (by omega))
  exact mem_spawnFold_of_mem (cascadeSpawn T specs)
    (popSeq (simWorld T specs actOrd pos (T - (specAt specs c).lastDelay)))
    (stageEventOf T specs c (repLenAt specs c))
    (stageEventOf T specs c (repLenAt specs c - 1)) hpop (by rw [hspawn]; simp)

/-- A chain's observer event is present at its firing tick. -/
theorem obsEvent_present (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat)
    (_h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (c : Nat) (hc : c < specs.length) :
    obsEventOf T specs c ∈
      (simWorld T specs actOrd pos (obsTickOf T specs c)).events := by
  have hi₀ : c ∈ classActOrder specs actOrd (specAt specs c) := by
    dsimp [classActOrder]
    rw [List.mem_filter]
    exact ⟨h_perm.mem_iff.mpr (List.mem_range.mpr hc), by simp⟩
  have hact : ∀ i ∈ classActOrder specs actOrd (specAt specs c),
      actTickOf T specs i = actTickOf T specs c := by
    intro i hi
    have hspec : specAt specs i = specAt specs c := by
      dsimp [classActOrder] at hi
      exact of_decide_eq_true (List.mem_filter.mp hi).2
    exact actTickOf_spec T specs i c hspec
  have hdue := classObsEvts_due_sublist T specs actOrd pos (specAt specs c)
    h_perm (actTickOf T specs c) hact
  have hmem : obsEventOf T specs c ∈ classObsEvts T specs actOrd (specAt specs c) := by
    dsimp [classObsEvts]
    exact List.mem_map.mpr ⟨c, hi₀, rfl⟩
  have hmem' : obsEventOf T specs c ∈
      (simWorld T specs actOrd pos (actTickOf T specs c + 2)).events.filter
        (fun e => e.targetTick == actTickOf T specs c + 2 && e.priority == 0) :=
    List.Sublist.mem hmem hdue
  have htick : obsTickOf T specs c = actTickOf T specs c + 2 := by
    dsimp [obsTickOf]
  simpa [htick] using (List.mem_filter.mp hmem').1

/-- A chain with no middle repeaters enqueues its last-repeater when its
    observer fires, at tick `T - lastDelay`. -/
theorem lastRep_mem_spawn_zero (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (c : Nat) (hc : c < specs.length)
    (h_fit : chainDelay (specAt specs c) ≤ T)
    (hz : repLenAt specs c = 0) :
    stageEventOf T specs c (repLenAt specs c) ∈
      spawnFold (cascadeSpawn T specs)
        (popSeq (simWorld T specs actOrd pos (T - (specAt specs c).lastDelay))) := by
  have htick : obsTickOf T specs c = T - (specAt specs c).lastDelay :=
    obsTickOf_zero T specs c h_fit hz
  have hpresent : obsEventOf T specs c ∈
      (simWorld T specs actOrd pos (T - (specAt specs c).lastDelay)).events := by
    simpa [htick] using (obsEvent_present T specs actOrd pos h_valid h_perm c hc)
  have hdue : (obsEventOf T specs c).targetTick =
      T - (specAt specs c).lastDelay := by
    dsimp [obsEventOf]
    rw [htick]
  have hpop : obsEventOf T specs c ∈
      popSeq (simWorld T specs actOrd pos (T - (specAt specs c).lastDelay)) := by
    have htick' := simWorld_tick T specs actOrd pos (T - (specAt specs c).lastDelay)
    exact mem_popSeq_of_due
      (simWorld T specs actOrd pos (T - (specAt specs c).lastDelay))
      (obsEventOf T specs c) hpresent (by simpa [htick'] using hdue)
  have hspawn : cascadeSpawn T specs (obsEventOf T specs c) =
      [stageEventOf T specs c 0] := by
    rw [cascadeSpawn_obs T specs c hc]
  rw [hz]
  exact mem_spawnFold_of_mem (cascadeSpawn T specs)
    (popSeq (simWorld T specs actOrd pos (T - (specAt specs c).lastDelay)))
    (stageEventOf T specs c 0)
    (obsEventOf T specs c) hpop (by rw [hspawn]; simp)

/-- A chain's last-repeater is spawned at tick `T - lastDelay` (its enqueue
    tick), regardless of whether it has middle repeaters. -/
theorem lastRep_mem_spawn (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (c : Nat) (hc : c < specs.length)
    (h_fit : chainDelay (specAt specs c) ≤ T) :
    stageEventOf T specs c (repLenAt specs c) ∈
      spawnFold (cascadeSpawn T specs)
        (popSeq (simWorld T specs actOrd pos (T - (specAt specs c).lastDelay))) := by
  by_cases hz : repLenAt specs c = 0
  · simpa [hz] using lastRep_mem_spawn_zero T specs actOrd pos h_valid h_perm c hc h_fit hz
  · have hpos : 0 < repLenAt specs c := Nat.pos_of_ne_zero hz
    exact lastRep_mem_spawn_pos T specs actOrd pos h_valid h_perm c hc h_fit hpos

/-- A pair of events that survive through every tick up to `t + n` (inclusive,
    i.e. their target tick is at least `t + n`) keeps its queue order across
    those `n` ticks. -/
theorem simWorld_findIdx_order_survive (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (t n : Nat) {e₁ e₂ : ScheduledEvent}
    (hpres₁ : e₁ ∈ (simWorld T specs actOrd pos t).events)
    (hpres₂ : e₂ ∈ (simWorld T specs actOrd pos t).events)
    (htgtN₁ : t + n ≤ e₁.targetTick) (htgtN₂ : t + n ≤ e₂.targetTick)
    (hb : (_root_.findIdx? (fun a => decide (a = e₁))
            (simWorld T specs actOrd pos t).events).getD 0 <
          (_root_.findIdx? (fun a => decide (a = e₂))
            (simWorld T specs actOrd pos t).events).getD 0) :
    (_root_.findIdx? (fun a => decide (a = e₁))
        (simWorld T specs actOrd pos (t + n)).events).getD 0 <
      (_root_.findIdx? (fun a => decide (a = e₂))
        (simWorld T specs actOrd pos (t + n)).events).getD 0 := by
  induction n generalizing t with
  | zero => simpa using hb
  | succ n' ih =>
      have htgt₁ : e₁.targetTick > t := by omega
      have htgt₂ : e₂.targetTick > t := by omega
      have hsurv₁ : [e₁] <+ (simWorld T specs actOrd pos (t + 1)).events :=
        simWorld_sublist_survive T specs actOrd pos t [e₁]
          (List.singleton_sublist.mpr hpres₁)
          (by intro e he; rw [List.mem_singleton] at he; subst e; exact ne_of_gt htgt₁)
      have hsurv₂ : [e₂] <+ (simWorld T specs actOrd pos (t + 1)).events :=
        simWorld_sublist_survive T specs actOrd pos t [e₂]
          (List.singleton_sublist.mpr hpres₂)
          (by intro e he; rw [List.mem_singleton] at he; subst e; exact ne_of_gt htgt₂)
      have hpres₁' : e₁ ∈ (simWorld T specs actOrd pos (t + 1)).events :=
        List.singleton_sublist.mp hsurv₁
      have hpres₂' : e₂ ∈ (simWorld T specs actOrd pos (t + 1)).events :=
        List.singleton_sublist.mp hsurv₂
      have hord := simWorld_succ_order_preserved T specs actOrd pos h_valid h_perm t
        hpres₁ hpres₂ htgt₁ htgt₂ hb
      have htgt₁' : (t + 1) + n' ≤ e₁.targetTick := by omega
      have htgt₂' : (t + 1) + n' ≤ e₂.targetTick := by omega
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (t + 1) hpres₁' hpres₂' htgt₁' htgt₂' hord

/-- The last-repeater of a chain with strictly smaller `lastDelay` is enqueued
    at a later tick, hence sits later in the queue (larger first-occurrence
    index) at tick `T`. This is the chronological half of the descent. -/
theorem lastRep_index_gt_of_delay_lt
    (T : Nat) (specs : List ChainSpec) (actOrd : List Nat) (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (h_fit : ∀ i < specs.length, chainDelay (specAt specs i) ≤ T)
    (x y : Nat) (hx : x < specs.length) (hy : y < specs.length)
    (hlt : (specAt specs x).lastDelay < (specAt specs y).lastDelay) :
    (_root_.findIdx? (fun e => decide (e = stageEventOf T specs x (repLenAt specs x)))
        ((simWorld T specs actOrd pos T).events)).getD 0 >
      (_root_.findIdx? (fun e => decide (e = stageEventOf T specs y (repLenAt specs y)))
        ((simWorld T specs actOrd pos T).events)).getD 0 := by
  set ex := stageEventOf T specs x (repLenAt specs x)
  set ey := stageEventOf T specs y (repLenAt specs y)
  set tx := T - (specAt specs x).lastDelay
  set ty := T - (specAt specs y).lastDelay
  have hltN : ((specAt specs x).lastDelay : Nat) < ((specAt specs y).lastDelay : Nat) := by
    exact_mod_cast hlt
  have hposx : 1 ≤ ((specAt specs x).lastDelay : Nat) := by
    have h := PNat.pos (specAt specs x).lastDelay
    omega
  have hlex : ((specAt specs x).lastDelay : Nat) ≤ T := by
    have hle : ((specAt specs x).lastDelay : Nat) ≤ chainDelay (specAt specs x) := by
      dsimp [chainDelay, ChainSpec.totalDelay]
      omega
    exact Nat.le_trans hle (h_fit x hx)
  have hley : ((specAt specs y).lastDelay : Nat) ≤ T := by
    have hle : ((specAt specs y).lastDelay : Nat) ≤ chainDelay (specAt specs y) := by
      dsimp [chainDelay, ChainSpec.totalDelay]
      omega
    exact Nat.le_trans hle (h_fit y hy)
  have htick_ex : ex.targetTick = T := by
    dsimp [ex, stageEventOf]
    exact stageTickOf_last T specs x (h_fit x hx)
  have htick_ey : ey.targetTick = T := by
    dsimp [ey, stageEventOf]
    exact stageTickOf_last T specs y (h_fit y hy)
  -- y's last-repeater is enqueued at tick ty and present at ty + 1
  have hespawn_y := lastRep_mem_spawn T specs actOrd pos h_valid h_perm y hy (h_fit y hy)
  have hsub_ty := simWorld_succ_survivors_before_spawns T specs actOrd pos h_valid h_perm ty
  have hey_ty1 : ey ∈ (simWorld T specs actOrd pos (ty + 1)).events := by
    have hm : ey ∈
        (simWorld T specs actOrd pos ty).events.filter (fun e => e.targetTick > ty) ++
          spawnFold (cascadeSpawn T specs) (popSeq (simWorld T specs actOrd pos ty)) := by
      rw [List.mem_append]
      exact Or.inr (by simpa [ey] using hespawn_y)
    exact List.Sublist.mem hm hsub_ty
  -- ey survives from ty + 1 to tx (its target tick is T ≥ tx)
  have htx_ge : ty + 1 ≤ tx := by
    dsimp [tx, ty]
    omega
  have hsurv_delta : [ey] <+ (simWorld T specs actOrd pos tx).events := by
    have h := simWorld_sublist_survive_delta T specs actOrd pos (ty + 1) (tx - (ty + 1)) [ey]
      (List.singleton_sublist.mpr hey_ty1)
      (by
        intro e he
        rw [List.mem_singleton] at he
        subst e
        rw [htick_ey]
        omega)
    have harg : (ty + 1) + (tx - (ty + 1)) = tx := by omega
    simpa [harg] using h
  have hey_tx : ey ∈ (simWorld T specs actOrd pos tx).events :=
    List.singleton_sublist.mp hsurv_delta
  -- x's last-repeater spawns at tick tx
  have hespawn_x := lastRep_mem_spawn T specs actOrd pos h_valid h_perm x hx (h_fit x hx)
  -- at tick tx, the survivor ey precedes the fresh spawn ex
  have hsub_tx := simWorld_succ_survivors_before_spawns T specs actOrd pos h_valid h_perm tx
  set pre := (simWorld T specs actOrd pos tx).events.filter (fun e => e.targetTick > tx)
  set rest := spawnFold (cascadeSpawn T specs) (popSeq (simWorld T specs actOrd pos tx))
  have hsub_tx' : pre ++ rest <+ (simWorld T specs actOrd pos (tx + 1)).events := by
    simpa [pre, rest] using hsub_tx
  have hey_pre : ey ∈ pre := by
    dsimp [pre]
    rw [List.mem_filter]
    exact ⟨hey_tx, decide_eq_true_eq.mpr (by rw [htick_ey]; dsimp [tx]; omega)⟩
  have hex_rest : ex ∈ rest := by
    dsimp [rest, ex]
    simpa [tx] using hespawn_x
  have hex_in_concat : ex ∈ pre ++ rest := by
    rw [List.mem_append]
    exact Or.inr hex_rest
  have hey_in_concat : ey ∈ pre ++ rest := by
    rw [List.mem_append]
    exact Or.inl hey_pre
  have hnodup_next : (simWorld T specs actOrd pos (tx + 1)).events.Nodup :=
    (simWorld_tickInv T specs actOrd pos h_valid h_perm (tx + 1)).1
  have hnd_concat : (pre ++ rest).Nodup := List.Sublist.nodup hsub_tx' hnodup_next
  have hdisj := (List.nodup_append.mp hnd_concat).2.2
  have hex_not_pre : ex ∉ pre := by
    intro h
    exact hdisj ex h ex hex_rest rfl
  have hlt_concat : (_root_.findIdx? (fun e => decide (e = ey)) (pre ++ rest)).getD 0 <
      (_root_.findIdx? (fun e => decide (e = ex)) (pre ++ rest)).getD 0 :=
    findIdx?_lt_of_prefix_mem pre rest (x := ey) (y := ex)
      hey_pre hex_in_concat hex_not_pre
  have hlt_next : (_root_.findIdx? (fun e => decide (e = ey))
      (simWorld T specs actOrd pos (tx + 1)).events).getD 0 <
        (_root_.findIdx? (fun e => decide (e = ex))
          (simWorld T specs actOrd pos (tx + 1)).events).getD 0 :=
    (findIdx?_getD_lt_sublist (l₁ := pre ++ rest)
      (l₂ := (simWorld T specs actOrd pos (tx + 1)).events)
      hsub_tx' hnodup_next (x := ey) (y := ex) hey_in_concat hex_in_concat).mpr hlt_concat
  -- order preserved from tx + 1 to T
  have hex_next : ex ∈ (simWorld T specs actOrd pos (tx + 1)).events :=
    List.Sublist.mem hex_in_concat hsub_tx'
  have hey_next : ey ∈ (simWorld T specs actOrd pos (tx + 1)).events :=
    List.Sublist.mem hey_in_concat hsub_tx'
  have hargT : (tx + 1) + (T - (tx + 1)) = T := by
    dsimp [tx]
    omega
  have htgt_exN : (tx + 1) + (T - (tx + 1)) ≤ ex.targetTick := by
    simp [htick_ex, hargT]
  have htgt_eyN : (tx + 1) + (T - (tx + 1)) ≤ ey.targetTick := by
    simp [htick_ey, hargT]
  have horder := simWorld_findIdx_order_survive T specs actOrd pos h_valid h_perm
    (tx + 1) (T - (tx + 1)) (e₁ := ey) (e₂ := ex)
    hey_next hex_next htgt_eyN htgt_exN hlt_next
  change (_root_.findIdx? (fun e => decide (e = ex))
      (simWorld T specs actOrd pos T).events).getD 0 >
        (_root_.findIdx? (fun e => decide (e = ey))
          (simWorld T specs actOrd pos T).events).getD 0
  simpa [hargT] using horder
