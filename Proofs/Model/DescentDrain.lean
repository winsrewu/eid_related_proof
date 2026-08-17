import Proofs.Model.TickInvariant

open BasicRedstoneSim
open World
open List

/-! # The drain-fire discharge. -/

/-! ## Drain fire discharge

Frame and node-id facts needed to instantiate `stepUNT_spawn_sublist`
for the no-group cascade spawn. -/

/-- An observer id is never an in-range stage repeater id. -/
theorem chainObserverId_ne_chainRepId (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (i j s : Nat) (_ : i < specs.length) (hj : j < specs.length)
    (hs : s ≤ repLenAt specs j) :
    chainObserverId specs i ≠ chainRepId specs j s := by
  intro h
  dsimp [chainObserverId, chainRepId] at h
  by_cases hij : i ≤ j
  · have hmono := chainBaseId_mono specs i j hij
    omega
  · have hltNext := chainRepId_lt_nextBase specs j s
      (by simpa [repLenAt] using hs) (h_valid j hj).1
    dsimp [chainRepId] at hltNext
    have hsucc := chainBaseId_succ specs j hj
    have hmono := chainBaseId_mono specs (j + 1) i (by omega)
    omega

/-- No cascade event's node id is a chain output id. -/
theorem chainOutputId_not_cascade_nodeId (T : Nat)
    (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (i : Nat) (hi : i < specs.length) (p : ScheduledEvent)
    (hpc : IsCascadeEv T specs p) : p.nodeId ≠ chainOutputId specs i := by
  rcases hpc with ⟨j, hj, rfl⟩ | hst
  · dsimp [obsEventOf]
    intro h
    exact chainOutputId_ne_chainObserverId specs h_valid j i hj hi h.symm
  · rcases hst with ⟨j, hj, s, hs, rfl⟩
    dsimp [stageEventOf]
    intro h
    exact chainOutputId_ne_chainRepId_of_le_repLen specs h_valid j i s
      hj hi (by simpa [repLenAt] using hs) h.symm

/-- Cascade events with the same node id are equal. -/
theorem cascade_nodeId_inj (T : Nat) (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (x y : ScheduledEvent) (hx : IsCascadeEv T specs x)
    (hy : IsCascadeEv T specs y) (h : x.nodeId = y.nodeId) :
    x = y := by
  rcases hx with ⟨i, hi, rfl⟩ | hxst
  · rcases hy with ⟨j, hj, rfl⟩ | hyst
    · change chainObserverId specs i = chainObserverId specs j at h
      have hij := chainObserverId_inj specs i j hi hj h
      rw [hij]
    · rcases hyst with ⟨j, hj, s, hs, rfl⟩
      change chainObserverId specs i = chainRepId specs j s at h
      exfalso
      exact chainObserverId_ne_chainRepId specs h_valid i j s hi hj
        (by simpa [repLenAt] using hs) h
  · rcases hxst with ⟨i, hi, s, hs, rfl⟩
    rcases hy with ⟨j, hj, rfl⟩ | hyst
    · change chainRepId specs i s = chainObserverId specs j at h
      exfalso
      exact chainObserverId_ne_chainRepId specs h_valid j i s hj hi
        (by simpa [repLenAt] using hs) h.symm
    · rcases hyst with ⟨j, hj, t, ht, rfl⟩
      change chainRepId specs i s = chainRepId specs j t at h
      have hpair := chainRepId_inj specs i j s t hi hj
        (by simpa [repLenAt] using hs) (by simpa [repLenAt] using ht)
        (h_valid i hi).1 (h_valid j hj).1 h
      rw [hpair.1, hpair.2]

/-- Membership in a `take` follows from membership in the list. -/
theorem mem_of_take {α : Type} (l : List α) (k : Nat) (x : α)
    (h : x ∈ l.take k) : x ∈ l := by
  induction l generalizing k with
  | nil => rw [List.take_nil] at h; cases h
  | cons a l ih =>
    cases k with
    | zero => rw [List.take_zero] at h; cases h
    | succ k' =>
      rw [List.take_succ_cons] at h
      rcases List.mem_cons.mp h with heq | h
      · rw [heq]; exact List.mem_cons.mpr (Or.inl rfl)
      · exact List.mem_cons.mpr (Or.inr (ih k' h))

/-- Membership in a `take` yields a position before the cut. -/
private theorem mem_take_getElem' {α : Type} (l : List α) (n : Nat)
    (a : α) (h : a ∈ l.take n) :
    ∃ (j : Nat) (hj : j < l.length), j < n ∧ l[j]'hj = a := by
  revert n h
  induction l with
  | nil => intro n h; cases n <;> dsimp [List.take] at h <;> cases h
  | cons x xs ih =>
    intro n h
    cases n with
    | zero => rw [List.take_zero] at h; cases h
    | succ n' =>
      rw [List.take_succ_cons] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨0, Nat.zero_lt_succ _, Nat.zero_lt_succ _, by simp⟩
      · obtain ⟨j, hj, hjn, hjE⟩ := ih n' h
        refine ⟨j + 1, Nat.succ_lt_succ hj, Nat.succ_lt_succ hjn, ?_⟩
        simpa using hjE

/-- In a nodup list the k-th element is not among the first k. -/
theorem getElem_not_mem_take_of_nodup {α : Type} (l : List α)
    (k : Nat) (hk : k < l.length) (hnd : l.Nodup) :
    l[k]'hk ∉ l.take k := by
  intro h
  obtain ⟨j, hj, hjk, hjp⟩ := mem_take_getElem' l k (l[k]'hk) h
  have hneq : j ≠ k := by omega
  exact hneq ((hnd.getElem_inj_iff (i := j) (hi := hj) (j := k)
    (hj := hk)).mp hjp)

/-- `popSeq` of a tick-invariant world is duplicate-free. -/
private theorem popSeqFuel_nodup (T : Nat) (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (t : Nat) (q₀ acts : List ScheduledEvent) (w : World) (n : Nat)
    (htick : w.tick = t) (hinv : TickInv T specs t q₀ acts w) :
    (popSeqFuel w n).Nodup := by
  induction n generalizing w with
  | zero => dsimp [popSeqFuel]; exact nodup_nil
  | succ n ih =>
    cases hpop : w.popNextEvent with
    | none => dsimp [popSeqFuel]; rw [hpop]; exact nodup_nil
    | some pr =>
      rcases pr with ⟨e, wp⟩
      dsimp [popSeqFuel]
      rw [hpop]
      apply List.nodup_cons.mpr
      refine ⟨?_, ?_⟩
      · intro he
        have hdue := popSeqFuel_mem_due (wp.onScheduledTick e.nodeId) n e he
        obtain ⟨news, hnews, hfut⟩ := onScheduledTick_events_append wp e.nodeId
        rw [hnews] at hdue
        rcases List.mem_append.mp hdue.2 with hwp | hnews'
        · obtain ⟨idx, hidx, herase, _, hget⟩ :=
            popNextEvent_eraseIdx w e wp hpop
          have hnot := not_mem_eraseIdx_of_nodup w.events idx hidx hinv.1
          rw [hget] at hnot
          rw [herase] at hwp
          exact hnot hwp
        · have hgt := hfut e hnews'
          rw [World.popNextEvent_tick w e wp hpop] at hgt
          rw [World.onScheduledTick_tick,
            World.popNextEvent_tick w e wp hpop] at hdue
          omega
      · have hw₁ : (wp.onScheduledTick e.nodeId).tick = t := by
          rw [World.onScheduledTick_tick,
            World.popNextEvent_tick w e wp hpop, htick]
        have hinv₁ := tickInv_pop_fire T specs h_valid t q₀ acts w
          (wp.onScheduledTick e.nodeId) htick
          (by dsimp [World.step]; rw [hpop]) hinv
        exact ih (wp.onScheduledTick e.nodeId) hw₁ hinv₁

/-- `popSeq` of a tick-invariant world is duplicate-free. -/
theorem popSeq_nodup_of_tickInv (T : Nat) (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (t : Nat) (q₀ acts : List ScheduledEvent) (w : World)
    (htick : w.tick = t) (hinv : TickInv T specs t q₀ acts w) :
    (popSeq w).Nodup := by
  dsimp [popSeq]
  exact popSeqFuel_nodup T specs h_valid t q₀ acts w w.events.length
    htick hinv

/-- Firing an observer appends no log entries. -/
private theorem fires_observer_log_kind (w : World) (_T : Nat)
    (specs : List ChainSpec) (i : Nat)
    (hobs : ∃ nd, w.getNode (chainObserverId specs i) = some nd ∧
      nd.kind = NodeKind.observer ∧ nd.outputs = [chainRepId specs i 0])
    (hrep : ∃ nd, w.getNode (chainRepId specs i 0) = some nd ∧
      nd.kind = NodeKind.repeater (stageDelayAt specs i 0)
        (stagePriAt specs i 0)) :
    (w.onScheduledTick (chainObserverId specs i)).outputLog = w.outputLog := by
  obtain ⟨ndObs, hgetObs, hkindObs, houtsObs⟩ := hobs
  obtain ⟨ndRep, hgetRep, hkindRep⟩ := hrep
  have hne : chainRepId specs i 0 ≠ chainObserverId specs i := by
    dsimp [chainRepId, chainObserverId]
    omega
  set w1 := w.updateNode (chainObserverId specs i) (fun nd =>
    { nd with sigLevel := 15 }) with hw1
  have h1 : w.onScheduledTick (chainObserverId specs i) =
      w1.notifyOutputs (chainObserverId specs i) := by
    dsimp [onScheduledTick, w1]
    simp [hgetObs, hkindObs]
  rw [h1]
  have hgetObs1 : w1.getNode (chainObserverId specs i) =
      some { ndObs with sigLevel := 15 } := by
    dsimp [w1]
    rw [getNode_updateNode_map, hgetObs]
    simp
  have hnotify : w1.notifyOutputs (chainObserverId specs i) =
      w1.onNeighborUpdate (chainRepId specs i 0) := by
    dsimp [notifyOutputs]
    rw [hgetObs1]
    simp [houtsObs]
  rw [hnotify]
  have hgetRep1 : w1.getNode (chainRepId specs i 0) = some ndRep := by
    dsimp [w1]
    rw [getNode_updateNode_ne w (chainObserverId specs i)
      (chainRepId specs i 0) (fun nd => { nd with sigLevel := 15 }) hne]
    exact hgetRep
  dsimp [onNeighborUpdate]
  simp [hgetRep1, hkindRep]
  rfl

/-- `lastRepOf` is a last-repeater event. -/
def lastRepOf (T : Nat) (specs : List ChainSpec) (e : ScheduledEvent) : Prop :=
  ∃ i < specs.length, e = stageEventOf T specs i (repLenAt specs i)

/-- The drain log-length: only last-repeater firings log one entry. -/
noncomputable def cascadeLogLen (T : Nat) (specs : List ChainSpec)
    (e : ScheduledEvent) : Nat := by
  classical
  exact if lastRepOf T specs e then 1 else 0

/-- An observer event is never a last-repeater event. -/
private theorem not_lastRepOf_obs (T : Nat) (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (i : Nat) (hi : i < specs.length) :
    ¬ lastRepOf T specs (obsEventOf T specs i) := by
  dsimp [lastRepOf]
  rintro ⟨j, hj, heqj⟩
  exact obsEventOf_ne_stageEventOf T specs h_valid i j (repLenAt specs j)
    hi hj (by dsimp [repLenAt]; omega) heqj

/-- A middle stage event is never a last-repeater event. -/
private theorem not_lastRepOf_middle (T : Nat) (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (i s : Nat) (hi : i < specs.length) (hs : s < repLenAt specs i) :
    ¬ lastRepOf T specs (stageEventOf T specs i s) := by
  dsimp [lastRepOf]
  rintro ⟨j, hj, heqj⟩
  have hpair := stageEventOf_inj T specs h_valid i j s (repLenAt specs j)
    hi hj (by omega) (by dsimp [repLenAt]; omega) heqj
  have : s = repLenAt specs i := by rw [hpair.1, hpair.2]
  omega


/-! ## The drain-fire discharge -/

/-- Firing the k-th pop of a tick-invariant world appends exactly its
    cascade spawn; the log gains exactly the last-repeater entry. This
    discharges the `hfire` obligation of `stepUNT_spawn_sublist`. -/
theorem drain_fire_eq (T : Nat) (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (t : Nat) (q₀ acts : List ScheduledEvent) (v : World)
    (htick : v.tick = t)
    (hinv : TickInv T specs t q₀ acts v) :
    ∀ (k : Nat) (hk : k < (popSeq v).length) (u : World),
      u.tick = v.tick →
      u.events = eraseEvents v.events ((popSeq v).take (k + 1)) ++
        spawnFold (cascadeSpawn T specs) ((popSeq v).take k) →
      (∀ id, id ∉ ((popSeq v).take k).map (fun e => e.nodeId) →
        u.getNode id = v.getNode id) →
      ∃ msgs : List String,
        (u.onScheduledTick ((popSeq v)[k]'hk).nodeId).events =
          u.events ++ cascadeSpawn T specs ((popSeq v)[k]'hk) ∧
        (u.onScheduledTick ((popSeq v)[k]'hk).nodeId).outputLog =
          u.outputLog ++ msgs ∧
        msgs.length = cascadeLogLen T specs ((popSeq v)[k]'hk) ∧
        ∀ id, id ≠ ((popSeq v)[k]'hk).nodeId →
          (u.onScheduledTick ((popSeq v)[k]'hk).nodeId).getNode id =
            u.getNode id := by
  rcases hinv with ⟨hnd, hwir, hgood, hsrc, hfresh⟩
  intro k hk u hutik hevs hframe
  have hmem : (popSeq v)[k]'hk ∈ popSeq v := List.getElem_mem hk
  have hdue := popSeq_mem_due v ((popSeq v)[k]'hk) hmem
  have hcl : IsCascadeEv T specs ((popSeq v)[k]'hk) := hgood _ hdue.2
  have hcl' : IsCascadeEv T specs ((popSeq v)[k]'hk) := hcl
  have hnp : (popSeq v).Nodup := popSeq_nodup_of_tickInv T specs h_valid
    t q₀ acts v htick ⟨hnd, hwir, hgood, hsrc, hfresh⟩
  have hnotTake : (popSeq v)[k]'hk ∉ (popSeq v).take k :=
    getElem_not_mem_take_of_nodup (popSeq v) k hk hnp
  have hwU : ∀ id, id ∉ ((popSeq v).take k).map (fun ev => ev.nodeId) →
      (u.getNode id).map wiring =
        ((buildChains specs).1.getNode id).map wiring := by
    intro id hid
    rw [hframe id hid, hwir id]
  rcases hcl with ⟨i, hi, heqO⟩ | hst
  · -- observer event
    rw [heqO]
    have htickI : obsTickOf T specs i = v.tick := by
      rw [heqO] at hdue
      dsimp [obsEventOf] at hdue
      exact hdue.1
    have htickU : u.tick = obsTickOf T specs i := by rw [hutik, htickI]
    have hfObs : chainObserverId specs i ∉
        ((popSeq v).take k).map (fun ev => ev.nodeId) := by
      intro hm
      obtain ⟨p, hp, hpN⟩ := List.mem_map.mp hm
      have hpPop : p ∈ popSeq v := mem_of_take (popSeq v) k p hp
      have hpdue := popSeq_mem_due v p hpPop
      have hpc : IsCascadeEv T specs p := hgood p hpdue.2
      have hpe : p = (popSeq v)[k]'hk := by
        apply cascade_nodeId_inj T specs h_valid p ((popSeq v)[k]'hk) hpc
          hcl'
        rw [hpN, heqO]
        simp [obsEventOf]
      exact hnotTake (by rw [← hpe]; exact hp)
    have hfRep : chainRepId specs i 0 ∉
        ((popSeq v).take k).map (fun ev => ev.nodeId) := by
      intro hm
      obtain ⟨p, hp, hpN⟩ := List.mem_map.mp hm
      have hpPop : p ∈ popSeq v := mem_of_take (popSeq v) k p hp
      have hpdue := popSeq_mem_due v p hpPop
      have hpc : IsCascadeEv T specs p := hgood p hpdue.2
      have hpe : p = stageEventOf T specs i 0 := by
        apply cascade_nodeId_inj T specs h_valid p
          (stageEventOf T specs i 0) hpc (Or.inr ⟨i, hi, 0, by omega, rfl⟩)
        rw [hpN]
        simp [stageEventOf]
      have hpTick : p.targetTick = stageTickOf T specs i 0 := by
        rw [hpe]
        rfl
      have hgt : stageTickOf T specs i 0 > obsTickOf T specs i := by
        rw [stageTickOf_zero]
        dsimp [obsTickOf]
        have hd := ValidDelay.ge2 (stageDelayAt_valid specs h_valid i 0 hi)
        omega
      rw [hpTick] at hpdue
      have hcontr : stageTickOf T specs i 0 = obsTickOf T specs i := by
        rw [hpdue.1, ← htickI]
      omega
    have hobsU : ∃ nd, u.getNode (chainObserverId specs i) = some nd ∧
        nd.kind = NodeKind.observer ∧ nd.outputs = [chainRepId specs i 0] := by
      have hb := buildChains_getNode_observer' specs i hi
      have houts : [chainBaseId specs i + 2] = [chainRepId specs i 0] := by
        dsimp [chainRepId]
      rw [houts] at hb
      exact wiring_kind_exists u (buildChains specs).1
        (chainObserverId specs i) NodeKind.observer [chainRepId specs i 0]
        (hwU (chainObserverId specs i) hfObs)
        ⟨{ kind := NodeKind.observer, sigLevel := 0, inputs := [chainBaseId specs i], outputs := [chainRepId specs i 0] }, hb, rfl, rfl⟩
    have hrepU : ∃ nd, u.getNode (chainRepId specs i 0) = some nd ∧
        nd.kind = NodeKind.repeater (stageDelayAt specs i 0)
          (stagePriAt specs i 0) := by
      have hb := buildChains_getNode_rep specs i 0 hi
        ((h_valid i hi).1) (by omega)
      obtain ⟨nd, hgetN, hkindN, _⟩ := wiring_kind_exists u
        (buildChains specs).1 (chainRepId specs i 0)
        (NodeKind.repeater (stageDelayAt specs i 0) (stagePriAt specs i 0))
        [chainBaseId specs i + 3]
        (hwU (chainRepId specs i 0) hfRep)
        ⟨{ kind := NodeKind.repeater (stageDelayAt specs i 0) (stagePriAt specs i 0), sigLevel := 0, inputs := [chainBaseId specs i + 1], outputs := [chainBaseId specs i + 3] }, hb, rfl, rfl⟩
      exact ⟨nd, hgetN, hkindN⟩
    have hevt := fires_observer_stage0_kind u T specs i htickU hobsU hrepU
    have hlog := fires_observer_log_kind u T specs i hobsU hrepU
    rw [cascadeSpawn_obs T specs i hi]
    refine ⟨[], ?_, ?_, ?_, ?_⟩
    · simpa [obsEventOf] using hevt
    · simpa [obsEventOf] using hlog
    · simp [cascadeLogLen, not_lastRepOf_obs T specs h_valid i hi]
    · intro id hid
      exact onScheduledTick_getNode_of_ne u (chainObserverId specs i) id hid
  · -- stage event
    rcases hst with ⟨i, hi, s, hs, heqS⟩
    rw [heqS]
    have htickI : stageTickOf T specs i s = v.tick := by
      rw [heqS] at hdue
      dsimp [stageEventOf] at hdue
      exact hdue.1
    have htickU : u.tick = stageTickOf T specs i s := by rw [hutik, htickI]
    by_cases hlt : s < repLenAt specs i
    · -- middle stage
      have hfRep : chainRepId specs i s ∉
          ((popSeq v).take k).map (fun ev => ev.nodeId) := by
        intro hm
        obtain ⟨p, hp, hpN⟩ := List.mem_map.mp hm
        have hpPop : p ∈ popSeq v := mem_of_take (popSeq v) k p hp
        have hpdue := popSeq_mem_due v p hpPop
        have hpc : IsCascadeEv T specs p := hgood p hpdue.2
        have hpe : p = (popSeq v)[k]'hk := by
          apply cascade_nodeId_inj T specs h_valid p ((popSeq v)[k]'hk)
            hpc hcl'
          rw [hpN, heqS]
          simp [stageEventOf]
        exact hnotTake (by rw [← hpe]; exact hp)
      have hfNext : chainRepId specs i (s + 1) ∉
          ((popSeq v).take k).map (fun ev => ev.nodeId) := by
        intro hm
        obtain ⟨p, hp, hpN⟩ := List.mem_map.mp hm
        have hpPop : p ∈ popSeq v := mem_of_take (popSeq v) k p hp
        have hpdue := popSeq_mem_due v p hpPop
        have hpc : IsCascadeEv T specs p := hgood p hpdue.2
        have hpe : p = stageEventOf T specs i (s + 1) := by
          apply cascade_nodeId_inj T specs h_valid p
            (stageEventOf T specs i (s + 1)) hpc
            (Or.inr ⟨i, hi, s + 1, by dsimp [repLenAt] at hlt; omega, rfl⟩)
          rw [hpN]
          simp [stageEventOf]
        have hpTick : p.targetTick = stageTickOf T specs i (s + 1) := by
          rw [hpe]
          rfl
        have hgt : stageTickOf T specs i (s + 1) >
            stageTickOf T specs i s := by
          rw [stageTickOf_succ T specs i s (by dsimp [repLenAt] at hlt; omega)]
          have hd := ValidDelay.ge2
            (stageDelayAt_valid specs h_valid i (s + 1) hi)
          omega
        rw [hpTick] at hpdue
        have hcontr : stageTickOf T specs i (s + 1) =
            stageTickOf T specs i s := by
          rw [hpdue.1, ← htickI]
        omega
      have hrepU : ∃ nd, u.getNode (chainRepId specs i s) = some nd ∧
          nd.kind = NodeKind.repeater (stageDelayAt specs i s)
            (stagePriAt specs i s) ∧
          nd.outputs = [chainRepId specs i (s + 1)] := by
        have hb := buildChains_getNode_rep specs i s hi
          ((h_valid i hi).1) (by dsimp [repLenAt] at hlt; omega)
        have houts : [chainBaseId specs i + 3 + s] =
            [chainRepId specs i (s + 1)] := by
          congr 1
          dsimp [chainRepId]
          omega
        rw [houts] at hb
        exact wiring_kind_exists u (buildChains specs).1 (chainRepId specs i s)
          (NodeKind.repeater (stageDelayAt specs i s) (stagePriAt specs i s))
          [chainRepId specs i (s + 1)]
          (hwU (chainRepId specs i s) hfRep)
          ⟨{ kind := NodeKind.repeater (stageDelayAt specs i s) (stagePriAt specs i s), sigLevel := 0, inputs := [chainBaseId specs i + 1 + s], outputs := [chainRepId specs i (s + 1)] }, hb, rfl, rfl⟩
      have hnextU : ∃ nd, u.getNode (chainRepId specs i (s + 1)) =
          some nd ∧
        nd.kind = NodeKind.repeater (stageDelayAt specs i (s + 1))
          (stagePriAt specs i (s + 1)) := by
        have hb := buildChains_getNode_rep specs i (s + 1) hi
          ((h_valid i hi).1) (by dsimp [repLenAt] at hlt; omega)
        obtain ⟨nd, hgetN, hkindN, _⟩ := wiring_kind_exists u
          (buildChains specs).1 (chainRepId specs i (s + 1))
          (NodeKind.repeater (stageDelayAt specs i (s + 1))
            (stagePriAt specs i (s + 1)))
          [chainBaseId specs i + 3 + (s + 1)]
          (hwU (chainRepId specs i (s + 1)) hfNext)
          ⟨{ kind := NodeKind.repeater (stageDelayAt specs i (s + 1)) (stagePriAt specs i (s + 1)), sigLevel := 0, inputs := [chainBaseId specs i + 1 + (s + 1)], outputs := [chainBaseId specs i + 3 + (s + 1)] }, hb, rfl, rfl⟩
        exact ⟨nd, hgetN, hkindN⟩
      have hevt := fires_rep_stage_kind u T specs i s
        (by dsimp [repLenAt] at hlt; omega) htickU hrepU hnextU
      obtain ⟨ndRep, hgetRepU, hkindRepU, houtsRepU⟩ := hrepU
      obtain ⟨ndNext, hgetNextU, hkindNextU⟩ := hnextU
      have hne : chainRepId specs i (s + 1) ≠ chainRepId specs i s := by
        dsimp [chainRepId]
        omega
      have hlog := onScheduledTick_repeater_outputLog u (chainRepId specs i s)
        (chainRepId specs i (s + 1)) ndRep ndNext
        (stageDelayAt specs i s) (stagePriAt specs i s)
        (stagePriAt specs i (s + 1)) (stageDelayAt specs i (s + 1)) hne
        hgetRepU hkindRepU houtsRepU hgetNextU hkindNextU
      rw [cascadeSpawn_stage T specs h_valid i s hi hlt]
      refine ⟨[], ?_, ?_, ?_, ?_⟩
      · simpa [stageEventOf] using hevt
      · simpa [stageEventOf] using hlog
      · simp [cascadeLogLen, not_lastRepOf_middle T specs h_valid i s hi hlt]
      · intro id hid
        exact onScheduledTick_getNode_of_ne u (chainRepId specs i s) id hid
    · -- last repeater: s = repLenAt
      have heqLen : s = repLenAt specs i := by
        dsimp [repLenAt] at hlt
        dsimp [repLenAt]
        omega
      rw [heqLen]
      rw [heqLen] at htickI htickU
      have hfRep : chainRepId specs i (repLenAt specs i) ∉
          ((popSeq v).take k).map (fun ev => ev.nodeId) := by
        intro hm
        obtain ⟨p, hp, hpN⟩ := List.mem_map.mp hm
        have hpPop : p ∈ popSeq v := mem_of_take (popSeq v) k p hp
        have hpdue := popSeq_mem_due v p hpPop
        have hpc : IsCascadeEv T specs p := hgood p hpdue.2
        have hpe : p = (popSeq v)[k]'hk := by
          apply cascade_nodeId_inj T specs h_valid p ((popSeq v)[k]'hk)
            hpc hcl'
          rw [hpN, heqS, heqLen]
          simp [stageEventOf]
        exact hnotTake (by rw [← hpe]; exact hp)
      have hfOut : chainOutputId specs i ∉
          ((popSeq v).take k).map (fun ev => ev.nodeId) := by
        intro hm
        obtain ⟨p, hp, hpN⟩ := List.mem_map.mp hm
        have hpPop : p ∈ popSeq v := mem_of_take (popSeq v) k p hp
        have hpdue := popSeq_mem_due v p hpPop
        have hpc : IsCascadeEv T specs p := hgood p hpdue.2
        exact chainOutputId_not_cascade_nodeId T specs h_valid i hi p hpc
          hpN
      have hrepU : ∃ nd, u.getNode (chainRepId specs i (repLenAt specs i)) =
          some nd ∧
        nd.kind = NodeKind.repeater (stageDelayAt specs i (repLenAt specs i))
          (stagePriAt specs i (repLenAt specs i)) ∧
        nd.outputs = [chainOutputId specs i] := by
        have hb := buildChains_getNode_rep specs i (repLenAt specs i) hi
          ((h_valid i hi).1) (by dsimp [repLenAt]; omega)
        obtain ⟨nd, hgetN, hkindN, houtsN⟩ := wiring_kind_exists u
          (buildChains specs).1 (chainRepId specs i (repLenAt specs i))
          (NodeKind.repeater (stageDelayAt specs i (repLenAt specs i))
            (stagePriAt specs i (repLenAt specs i)))
          [chainBaseId specs i + 3 + repLenAt specs i]
          (hwU (chainRepId specs i (repLenAt specs i)) hfRep)
          ⟨{ kind := NodeKind.repeater (stageDelayAt specs i (repLenAt specs i)) (stagePriAt specs i (repLenAt specs i)), sigLevel := 0, inputs := [chainBaseId specs i + 1 + repLenAt specs i], outputs := [chainBaseId specs i + 3 + repLenAt specs i] }, hb, rfl, rfl⟩
        exact ⟨nd, hgetN, hkindN, by rw [houtsN]; dsimp [chainOutputId]⟩
      have houtU : ∃ nd, u.getNode (chainOutputId specs i) = some nd ∧
          nd.kind = NodeKind.output (chainName i) := by
        have hb := buildChains_getNode_output' specs i hi ((h_valid i hi).1)
        obtain ⟨nd, hgetN, hkindN, _⟩ := wiring_kind_exists u
          (buildChains specs).1 (chainOutputId specs i)
          (NodeKind.output (chainName i)) []
          (hwU (chainOutputId specs i) hfOut)
          ⟨{ kind := NodeKind.output (chainName i), sigLevel := 0, inputs := [chainBaseId specs i + 2 + repLenAt specs i], outputs := [] }, hb, rfl, rfl⟩
        exact ⟨nd, hgetN, hkindN⟩
      have hevt := fires_lastRep_events_kind u specs i hrepU houtU
      obtain ⟨msg, hlog⟩ := fires_lastRep_log_kind u specs i hrepU houtU
      rw [cascadeSpawn_lastRep T specs h_valid i hi]
      refine ⟨[msg], ?_, ?_, ?_, ?_⟩
      · simpa [stageEventOf, List.append_nil] using hevt
      · simpa [stageEventOf] using hlog
      · simp [cascadeLogLen]
        exact ⟨i, hi, rfl⟩
      · intro id hid
        exact onScheduledTick_getNode_of_ne u
          (chainRepId specs i (repLenAt specs i)) id hid

