import Proofs.Clustering.DescentTrace
import Mathlib.Data.List.Perm.Basic


open BasicRedstoneSim
open List

/-! # Clustering theorem (no-group model)

All chains output on a common tick `T`. Chains with identical specs output in
a contiguous block: no different-spec chain's output can lie strictly between
two same-spec outputs. -/

/-! ## Spec equality from matching stages -/

/-- If two valid specs have the same number of middle repeaters, the same
    middle delays and priorities at every stage, and the same last delay and
    priority, then they are equal. -/
theorem spec_eq_of_all_stage_eq (specs : List ChainSpec) (i j : Nat)
    (hpri_i : (specAt specs i).priLenOk) (hpri_j : (specAt specs j).priLenOk)
    (hlen : repLenAt specs i = repLenAt specs j)
    (hstage : ∀ s < repLenAt specs i,
       stageDelayAt specs i s = stageDelayAt specs j s ∧
       stagePriAt specs i s = stagePriAt specs j s)
    (hlastDelay : (specAt specs i).lastDelay = (specAt specs j).lastDelay)
    (hlastPri : (specAt specs i).lastPriority = (specAt specs j).lastPriority) :
    specAt specs i = specAt specs j := by
  have hlenD : (specAt specs i).middleDelays.length =
      (specAt specs j).middleDelays.length := by
    dsimp [repLenAt] at hlen
    exact hlen
  have hlenP : (specAt specs i).middlePriorities.length =
      (specAt specs j).middlePriorities.length := by
    dsimp [ChainSpec.priLenOk] at hpri_i hpri_j
    rw [hpri_i, hpri_j, hlenD]
  have hmid : (specAt specs i).middleDelays = (specAt specs j).middleDelays := by
    apply List.ext_getElem?
    intro s
    by_cases hs : s < (specAt specs i).middleDelays.length
    · have hlt : s < repLenAt specs i := by
        dsimp [repLenAt]
        exact hs
      have hd := (hstage s hlt).1
      rw [stageDelayAt_of_lt specs i s hs,
        stageDelayAt_of_lt specs j s (by rwa [hlenD] at hs)] at hd
      rw [List.getElem?_eq_getElem hs,
        List.getElem?_eq_getElem (by rwa [hlenD] at hs)]
      exact congrArg some hd
    · rw [List.getElem?_eq_none (l := (specAt specs i).middleDelays) (by omega),
        List.getElem?_eq_none (l := (specAt specs j).middleDelays) (by omega)]
  have hmidP : (specAt specs i).middlePriorities =
      (specAt specs j).middlePriorities := by
    apply List.ext_getElem?
    intro s
    by_cases hs : s < (specAt specs i).middlePriorities.length
    · have hlt : s < repLenAt specs i := by
        dsimp [repLenAt]
        dsimp [ChainSpec.priLenOk] at hpri_i
        rw [← hpri_i]
        exact hs
      have hltj : s < (specAt specs j).middlePriorities.length := by
        rw [hlenP] at hs
        exact hs
      have hltjD : s < (specAt specs j).middleDelays.length := by
        dsimp [ChainSpec.priLenOk] at hpri_j
        rw [← hpri_j]
        rw [hlenP] at hs
        exact hs
      have hltiD : s < (specAt specs i).middleDelays.length := by
        dsimp [ChainSpec.priLenOk] at hpri_i
        rw [hpri_i] at hs
        exact hs
      have hp := (hstage s hlt).2
      rw [stagePriAt_of_lt specs i s hpri_i hltiD,
          stagePriAt_of_lt specs j s hpri_j hltjD] at hp
      rw [List.getElem?_eq_getElem hs, List.getElem?_eq_getElem hltj]
      exact congrArg some hp
    · rw [List.getElem?_eq_none (l := (specAt specs i).middlePriorities) (by omega),
        List.getElem?_eq_none (l := (specAt specs j).middlePriorities) (by omega)]
  cases h1 : specAt specs i with
  | mk a b c d =>
    cases h2 : specAt specs j with
    | mk a' b' c' d' =>
      rw [h1, h2] at hmid hmidP hlastDelay hlastPri
      have ha : a = a' := by simpa using hmid
      have hb : b = b' := by simpa using hmidP
      have hc : c = c' := by simpa using hlastDelay
      have hd : d = d' := by simpa using hlastPri
      subst ha
      subst hb
      subst hc
      subst hd
      rfl

/-! ## Output-position bridge -/

/-- `outputPos` being `some px` pins the pop-sequence position of the
    last-repeater event. -/
private theorem outputPos_findIdx_some (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (h_fit : ∀ i < specs.length, chainDelay (specAt specs i) ≤ T)
    (x : Nat) (hx : x < specs.length) (px : Nat)
    (hp : outputPos (simulate T specs actOrd pos) x = some px) :
    ∃ r, _root_.findIdx?
        (fun e => decide (e = stageEventOf T specs x (repLenAt specs x)))
        (popSeq (simWorld T specs actOrd pos T)) = some r ∧
      px = T + 1 + r := by
  have hs := outputPos_simulate T specs actOrd pos x h_valid h_perm h_fit hx
  rw [hs] at hp
  cases hf : _root_.findIdx?
      (fun e => decide (e = stageEventOf T specs x (repLenAt specs x)))
      (popSeq (simWorld T specs actOrd pos T)) with
  | none => simp [hf] at hp
  | some r =>
      refine ⟨r, ?_⟩
      constructor
      · rfl
      · simp [hf] at hp
        exact hp.symm

/-! ## The recursive descent

The remaining argument descends from the last repeater to the observer,
matching one (delay, priority) pair per step. Each step needs two facts
about the pop sequence's FIFO tiebreak (among equal priority, events pop in
enqueue order; the last-repeater of chain `x` is enqueued at tick
`T - lastDelay (specAt specs x)`, when its predecessor fires):

1. **Delay monotonicity** (`lastRep_delay_eq_of_between`): if `x`'s
   last-repeater pops before `y`'s with equal priority, then
   `lastDelay x ≥ lastDelay y`. Hence a last-repeater sandwiched between
   two same-spec last-repeaters shares their `lastDelay`.

2. **Parent bridge** (`lastRep_parent_between_of_between`): with equal
   `lastDelay`, the enqueue order of last-repeaters equals the pop order of
   their predecessor events one tick earlier, so the sandwiched chain's
   predecessor is sandwiched between the two reference predecessors.

3. **Short-chain separation**: a chain whose repeater list is a proper
   trailing part of the reference spec has an observer predecessor
   (priority `0`), while the reference predecessor is a repeater
   (priority `≤ -1` by `ValidPriority.neg`), so it can never land between.

The base case (`repLenAt = 0`) then closes via `hlastPri_eq` plus the
matching `lastDelay`; the step recurses on `repLenAt - 1` and finishes via
`spec_eq_of_all_stage_eq`. -/

/-- **Delay monotonicity.** In the tick-`T` pop sequence, a same-priority
    last-repeater that pops before another has `lastDelay` at least as large.
    Combined with the symmetric inequality this forces equality for a
    sandwiched chain. -/
theorem lastRep_delay_ge_of_before
    (T : Nat) (specs : List ChainSpec) (actOrd : List Nat) (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (h_fit : ∀ i < specs.length, chainDelay (specAt specs i) ≤ T)
    (x y : Nat) (hx : x < specs.length) (hy : y < specs.length)
    (hx_mem : stageEventOf T specs x (repLenAt specs x) ∈
        popSeq (simWorld T specs actOrd pos T))
    (hy_mem : stageEventOf T specs y (repLenAt specs y) ∈
        popSeq (simWorld T specs actOrd pos T))
    (hpri : (specAt specs x).lastPriority = (specAt specs y).lastPriority)
    (hb : (_root_.findIdx? (fun e => decide (e = stageEventOf T specs x (repLenAt specs x)))
            (popSeq (simWorld T specs actOrd pos T))).getD 0 <
          (_root_.findIdx? (fun e => decide (e = stageEventOf T specs y (repLenAt specs y)))
            (popSeq (simWorld T specs actOrd pos T))).getD 0) :
    (specAt specs x).lastDelay ≥ (specAt specs y).lastDelay := by
  set wT := simWorld T specs actOrd pos T
  have hpri_x : (specAt specs x).priLenOk := (h_valid x hx).1
  have hpri_y : (specAt specs y).priLenOk := (h_valid y hy).1
  have hpri_ev : (stageEventOf T specs x (repLenAt specs x)).priority =
      (stageEventOf T specs y (repLenAt specs y)).priority := by
    dsimp [stageEventOf]
    have hle_x : (specAt specs x).middleDelays.length ≤ repLenAt specs x := by
      simp [repLenAt]
    have hle_y : (specAt specs y).middleDelays.length ≤ repLenAt specs y := by
      simp [repLenAt]
    rw [stagePriAt_of_eq specs x hpri_x hle_x, stagePriAt_of_eq specs y hpri_y hle_y]
    exact hpri
  have hnodup : wT.events.Nodup :=
    (simWorld_tickInv T specs actOrd pos h_valid h_perm T).1
  have hpopNd : (popSeq wT).Nodup :=
    popSeq_nodup_of_tickInv T specs h_valid T wT.events [] wT
      (by dsimp [wT]; rw [simWorld_tick])
      (simWorld_tickInv T specs actOrd pos h_valid h_perm T)
  have hindex : (_root_.findIdx? (fun e => decide (e = stageEventOf T specs x (repLenAt specs x)))
      wT.events).getD 0 <
        (_root_.findIdx? (fun e => decide (e = stageEventOf T specs y (repLenAt specs y)))
        wT.events).getD 0 :=
    popSeq_same_priority_findIdx_order wT hx_mem hy_mem hnodup hpopNd hpri_ev hb
  by_contra hnotge
  have hlt : (specAt specs x).lastDelay < (specAt specs y).lastDelay :=
    Nat.lt_of_not_ge hnotge
  have hgt := lastRep_index_gt_of_delay_lt T specs actOrd pos h_valid h_perm h_fit
    x y hx hy hlt
  have hgt' : (_root_.findIdx? (fun e => decide (e = stageEventOf T specs x (repLenAt specs x)))
      wT.events).getD 0 >
        (_root_.findIdx? (fun e => decide (e = stageEventOf T specs y (repLenAt specs y)))
        wT.events).getD 0 := by
    simpa [wT] using hgt
  omega


/-- The descent: from the last-repeater sandwich, descending one stage at a
    time gives `repLenAt` equality and stage-by-stage delay/priority match. -/
theorem sandwich_descent (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (h_fit : ∀ i < specs.length, chainDelay (specAt specs i) ≤ T)
    (i j k : Nat) (hi : i < specs.length) (hj : j < specs.length) (hk : k < specs.length)
    (hij : (_root_.findIdx? (fun e => decide (e = stageEventOf T specs i (repLenAt specs i)))
            (popSeq (simWorld T specs actOrd pos T))).getD 0 <
          (_root_.findIdx? (fun e => decide (e = stageEventOf T specs j (repLenAt specs j)))
            (popSeq (simWorld T specs actOrd pos T))).getD 0)
    (hjk : (_root_.findIdx? (fun e => decide (e = stageEventOf T specs j (repLenAt specs j)))
            (popSeq (simWorld T specs actOrd pos T))).getD 0 <
          (_root_.findIdx? (fun e => decide (e = stageEventOf T specs k (repLenAt specs k)))
            (popSeq (simWorld T specs actOrd pos T))).getD 0)
    (hspec : specAt specs i = specAt specs k)
    (hlastPri : (specAt specs j).lastPriority = (specAt specs i).lastPriority)
    (hlastDelay : (specAt specs j).lastDelay = (specAt specs i).lastDelay) :
    repLenAt specs j = repLenAt specs i ∧
    (∀ s < repLenAt specs i, stageDelayAt specs i s = stageDelayAt specs j s ∧
      stagePriAt specs i s = stagePriAt specs j s) := by
  have hmem_stage : ∀ c < specs.length, ∀ s ≤ repLenAt specs c,
      stageEventOf T specs c s ∈
        popSeq (simWorld T specs actOrd pos (stageTickOf T specs c s)) := by
    intro c hc s hs
    have hpresent := stageEvent_present T specs actOrd pos h_valid h_perm c hc
      (h_fit c hc) s hs
    have hdue : (stageEventOf T specs c s).targetTick = stageTickOf T specs c s := by
      dsimp [stageEventOf]
    have htick := simWorld_tick T specs actOrd pos (stageTickOf T specs c s)
    exact mem_popSeq_of_due
      (simWorld T specs actOrd pos (stageTickOf T specs c s))
      (stageEventOf T specs c s) hpresent (by simpa [htick] using hdue)
  let ei : Nat → ScheduledEvent := evI T specs i
  let ej : Nat → ScheduledEvent := evJ T specs j
  let ek : Nat → ScheduledEvent := evK T specs k i
  let wi : Nat → World := wI T specs actOrd pos i
  have hdesc := descent_trace T specs actOrd pos h_valid h_perm h_fit i j k hi hj hk
    hij hjk hspec hlastPri hlastDelay
  -- short-chain: repLenAt j = repLenAt i
  have hlen_eq : repLenAt specs j = repLenAt specs i := by
    by_cases hle : repLenAt specs j ≤ repLenAt specs i
    · by_contra hne
      have hlt : repLenAt specs j < repLenAt specs i := Nat.lt_of_le_of_ne hle hne
      set si := repLenAt specs i - repLenAt specs j
      have hsi_pos : 0 < si := by dsimp [si]; omega
      have hsi_le_k : si ≤ repLenAt specs k := by
        dsimp [si]
        rw [← repLenAt_spec specs i k hspec]
        omega
      obtain ⟨htick, hpri, hij_s, hjk_s, hdel_cond⟩ :=
        hdesc (repLenAt specs j) hle (Nat.le_refl (repLenAt specs j))
      have hz_j : repLenAt specs j - repLenAt specs j = 0 := by omega
      have htick_ij : stageTickOf T specs i si = stageTickOf T specs j 0 := by
        simpa [si, hz_j] using htick
      have hpri_ij : stagePriAt specs i si = stagePriAt specs j 0 := by
        simpa [si, hz_j] using hpri
      have htick_jk : stageTickOf T specs j 0 = stageTickOf T specs k si := by
        have hk : stageTickOf T specs i si = stageTickOf T specs k si :=
          stageTickOf_spec T specs i k si hspec
        exact htick_ij.symm.trans hk
      have hpri_jk : stagePriAt specs j 0 = stagePriAt specs k si := by
        have hk : stagePriAt specs i si = stagePriAt specs k si :=
          stagePriAt_spec specs i k si hspec
        exact hpri_ij.symm.trans hk
      have hij_raw : (_root_.findIdx? (fun e => decide (e = stageEventOf T specs i si))
          (popSeq (simWorld T specs actOrd pos (stageTickOf T specs i si)))).getD 0 <
        (_root_.findIdx? (fun e => decide (e = stageEventOf T specs j 0))
          (popSeq (simWorld T specs actOrd pos (stageTickOf T specs i si)))).getD 0 := by
        dsimp [eventIdx, ei, ej, wi, wI, evI, evJ] at hij_s
        simpa [si, hz_j] using hij_s
      have hjk_raw : (_root_.findIdx? (fun e => decide (e = stageEventOf T specs j 0))
          (popSeq (simWorld T specs actOrd pos (stageTickOf T specs i si)))).getD 0 <
        (_root_.findIdx? (fun e => decide (e = stageEventOf T specs k si))
          (popSeq (simWorld T specs actOrd pos (stageTickOf T specs i si)))).getD 0 := by
        dsimp [eventIdx, ej, ek, wi, wI, evJ, evK] at hjk_s
        simpa [si, hz_j] using hjk_s
      have hdelay_ge_ij : stageDelayAt specs i si ≥ stageDelayAt specs j 0 :=
        rep_delay_ge_of_before_mid0 T specs actOrd pos h_valid h_perm h_fit
          i j si hi hj hsi_pos (by dsimp [si]; omega)
          htick_ij hpri_ij
          (hmem_stage i hi si (by dsimp [si]; omega))
          (by simpa [htick_ij] using (hmem_stage j hj 0 (by omega)))
          hij_raw
      have hdelay_ge_jk : stageDelayAt specs j 0 ≥ stageDelayAt specs k si :=
        rep_delay_ge_of_before_0mid T specs actOrd pos h_valid h_perm h_fit
          j k si hj hk hsi_pos hsi_le_k
          htick_jk hpri_jk
          (hmem_stage j hj 0 (by omega))
          (by simpa [htick_jk] using (hmem_stage k hk si hsi_le_k))
          (by simpa [htick_ij] using hjk_raw)
      have hdelay_ki : stageDelayAt specs k si = stageDelayAt specs i si :=
        (stageDelayAt_spec specs i k si hspec).symm
      have hdelay_jk_eq : stageDelayAt specs j 0 = stageDelayAt specs k si := by
        have hge_j_i : stageDelayAt specs j 0 ≥ stageDelayAt specs i si := by
          rw [hdelay_ki] at hdelay_ge_jk
          exact hdelay_ge_jk
        have hdelay_ij_eq : stageDelayAt specs i si = stageDelayAt specs j 0 :=
          le_antisymm hge_j_i hdelay_ge_ij
        exact hdelay_ij_eq.symm.trans hdelay_ki.symm
      have hb_jk : (_root_.findIdx? (fun e => decide (e = stageEventOf T specs j 0))
          (popSeq (simWorld T specs actOrd pos (stageTickOf T specs j 0)))).getD 0 <
        (_root_.findIdx? (fun e => decide (e = stageEventOf T specs k si))
          (popSeq (simWorld T specs actOrd pos (stageTickOf T specs j 0)))).getD 0 := by
        simpa [htick_ij] using hjk_raw
      exact obs_middle_contradiction T specs actOrd pos h_valid h_perm h_fit
        j k si hj hk hsi_le_k hsi_pos htick_jk hdelay_jk_eq hpri_jk hb_jk
    · have hlt : repLenAt specs i < repLenAt specs j := Nat.lt_of_not_ge hle
      set sj := repLenAt specs j - repLenAt specs i
      have hsj_pos : 0 < sj := by dsimp [sj]; omega
      have hsj_le_j : sj ≤ repLenAt specs j := by dsimp [sj]; omega
      obtain ⟨htick, hpri, hij_s, hjk_s, hdel_cond⟩ :=
        hdesc (repLenAt specs i) (Nat.le_refl (repLenAt specs i)) (Nat.le_of_lt hlt)
      have hz_i : repLenAt specs i - repLenAt specs i = 0 := by omega
      have htick_ij : stageTickOf T specs i 0 = stageTickOf T specs j sj := by
        simpa [sj, hz_i] using htick
      have hpri_ij : stagePriAt specs i 0 = stagePriAt specs j sj := by
        simpa [sj, hz_i] using hpri
      have htick_jk : stageTickOf T specs j sj = stageTickOf T specs k 0 := by
        have hk : stageTickOf T specs i 0 = stageTickOf T specs k 0 :=
          stageTickOf_spec T specs i k 0 hspec
        exact htick_ij.symm.trans hk
      have hpri_jk : stagePriAt specs j sj = stagePriAt specs k 0 := by
        have hk : stagePriAt specs i 0 = stagePriAt specs k 0 :=
          stagePriAt_spec specs i k 0 hspec
        exact hpri_ij.symm.trans hk
      have hij_raw : (_root_.findIdx? (fun e => decide (e = stageEventOf T specs i 0))
          (popSeq (simWorld T specs actOrd pos (stageTickOf T specs i 0)))).getD 0 <
        (_root_.findIdx? (fun e => decide (e = stageEventOf T specs j sj))
          (popSeq (simWorld T specs actOrd pos (stageTickOf T specs i 0)))).getD 0 := by
        dsimp [eventIdx, ei, ej, wi, wI, evI, evJ] at hij_s
        simpa [sj, hz_i] using hij_s
      have hjk_raw : (_root_.findIdx? (fun e => decide (e = stageEventOf T specs j sj))
          (popSeq (simWorld T specs actOrd pos (stageTickOf T specs i 0)))).getD 0 <
        (_root_.findIdx? (fun e => decide (e = stageEventOf T specs k 0))
          (popSeq (simWorld T specs actOrd pos (stageTickOf T specs i 0)))).getD 0 := by
        dsimp [eventIdx, ej, ek, wi, wI, evJ, evK] at hjk_s
        simpa [sj, hz_i, repLenAt_spec specs i k hspec] using hjk_s
      have hdelay_ge_ij : stageDelayAt specs i 0 ≥ stageDelayAt specs j sj :=
        rep_delay_ge_of_before_0mid T specs actOrd pos h_valid h_perm h_fit
          i j sj hi hj hsj_pos hsj_le_j
          htick_ij hpri_ij
          (hmem_stage i hi 0 (by omega))
          (by simpa [htick_ij] using (hmem_stage j hj sj hsj_le_j))
          hij_raw
      have hdelay_ge_jk : stageDelayAt specs j sj ≥ stageDelayAt specs k 0 :=
        rep_delay_ge_of_before_mid0 T specs actOrd pos h_valid h_perm h_fit
          j k sj hj hk hsj_pos hsj_le_j
          htick_jk hpri_jk
          (hmem_stage j hj sj hsj_le_j)
          (by simpa [htick_jk] using (hmem_stage k hk 0 (by omega)))
          (by simpa [htick_ij] using hjk_raw)
      have hdelay_ki : stageDelayAt specs k 0 = stageDelayAt specs i 0 :=
        (stageDelayAt_spec specs i k 0 hspec).symm
      have hdelay_ij_eq : stageDelayAt specs i 0 = stageDelayAt specs j sj := by
        have hge_j_i : stageDelayAt specs j sj ≥ stageDelayAt specs i 0 := by
          rw [hdelay_ki] at hdelay_ge_jk
          exact hdelay_ge_jk
        exact le_antisymm hge_j_i hdelay_ge_ij
      have hb_ij : (_root_.findIdx? (fun e => decide (e = stageEventOf T specs i 0))
          (popSeq (simWorld T specs actOrd pos (stageTickOf T specs i 0)))).getD 0 <
        (_root_.findIdx? (fun e => decide (e = stageEventOf T specs j sj))
          (popSeq (simWorld T specs actOrd pos (stageTickOf T specs i 0)))).getD 0 :=
        hij_raw
      exfalso
      exact obs_middle_contradiction T specs actOrd pos h_valid h_perm h_fit
        i j sj hi hj hsj_le_j hsj_pos htick_ij hdelay_ij_eq hpri_ij hb_ij
  -- extract stage equality
  have hstage : ∀ s < repLenAt specs i,
      stageDelayAt specs i s = stageDelayAt specs j s ∧
      stagePriAt specs i s = stagePriAt specs j s := by
    intro s hs
    have hr_le_i : repLenAt specs i - s ≤ repLenAt specs i := by omega
    have hr_le_j : repLenAt specs i - s ≤ repLenAt specs j := by
      rw [hlen_eq]
      omega
    obtain ⟨htick_s, hpri_s, hij_s, hjk_s, hdel_cond⟩ :=
      hdesc (repLenAt specs i - s) hr_le_i hr_le_j
    have harg : repLenAt specs i - (repLenAt specs i - s) = s := by omega
    have hargj : repLenAt specs j - (repLenAt specs i - s) = s := by
      rw [hlen_eq]
      omega
    have hpri' : stagePriAt specs i s = stagePriAt specs j s := by
      simpa [harg, hargj] using hpri_s
    have hdel' : stageDelayAt specs i s = stageDelayAt specs j s := by
      by_cases hs0 : s = 0
      · subst s
        have hz_i : repLenAt specs i - repLenAt specs i = 0 := by omega
        have hz_j : repLenAt specs j - repLenAt specs i = 0 := by
          rw [hlen_eq]
          omega
        have htick0 : stageTickOf T specs i 0 = stageTickOf T specs j 0 := by
          have htick_s' : stageTickOf T specs i (repLenAt specs i - repLenAt specs i) =
              stageTickOf T specs j (repLenAt specs j - repLenAt specs i) := by
            simpa [Nat.sub_zero] using htick_s
          simpa [hz_i, hz_j] using htick_s'
        have hge_ij := obsRep_delay_ge_of_before_ev T specs actOrd pos h_valid h_perm h_fit
          i j hi hj htick0
          (evI T specs i (repLenAt specs i)) (evJ T specs j (repLenAt specs i)) (wi (repLenAt specs i))
          (by dsimp [evI]; rw [hz_i]) (by dsimp [evJ]; rw [hz_j])
          (by dsimp [wi, wI]; rw [hz_i])
          (by simpa [evI, wi, wI, hz_i] using (hmem_stage i hi 0 (by omega)))
          (by simpa [evJ, wi, wI, hz_i, hz_j, htick0] using (hmem_stage j hj 0 (by omega)))
          hpri' (by simpa using hij_s)
        have hge_jk := obsRep_delay_ge_of_before_ev T specs actOrd pos h_valid h_perm h_fit
          j k hj hk (by rw [stageTickOf_spec T specs k i 0 hspec.symm]; exact htick0.symm)
          (evJ T specs j (repLenAt specs i)) (evK T specs k i (repLenAt specs i)) (wi (repLenAt specs i))
          (by dsimp [evJ]; rw [hz_j]) (by dsimp [evK]; rw [hz_i])
          (by dsimp [wi, wI]; rw [hz_i, htick0])
          (by simpa [evJ, wi, wI, hz_i, hz_j, htick0] using (hmem_stage j hj 0 (by omega)))
          (by simpa [evK, wi, wI, hz_i, stageTickOf_spec T specs k i 0 hspec.symm] using (hmem_stage k hk 0 (by omega)))
          (by rw [← hpri']; exact stagePriAt_spec specs i k 0 hspec)
          (by simpa using hjk_s)
        have hdelay_ki : stageDelayAt specs k 0 = stageDelayAt specs i 0 := by
          rw [stageDelayAt_spec specs k i 0 hspec.symm]
        have hge_j_i : stageDelayAt specs j 0 ≥ stageDelayAt specs i 0 := by
          rw [hdelay_ki] at hge_jk
          exact hge_jk
        exact le_antisymm hge_j_i hge_ij
      · have hpos : 0 < s := Nat.pos_of_ne_zero hs0
        simpa [harg, hargj] using (hdel_cond (by omega) (by omega))
    exact ⟨hdel', hpri'⟩
  exact ⟨hlen_eq, hstage⟩

/-- **Clustering.** For any valid no-group system whose chains all output on
    tick `T`, if two same-spec chains output with a third chain's output
    strictly between them, then that third chain has the same spec too. -/
theorem clustering
    (T : Nat) (specs : List ChainSpec) (actOrd : List Nat)
    (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (h_fit : ∀ i < specs.length, chainDelay (specAt specs i) ≤ T) :
    let log := simulate T specs actOrd pos
    ∀ i j k p_i p_j p_k,
      i < specs.length → j < specs.length → k < specs.length →
      outputPos log i = some p_i → outputPos log j = some p_j →
      outputPos log k = some p_k →
      p_i < p_j → p_j < p_k →
      specAt specs i = specAt specs k →
      specAt specs j = specAt specs i := by
  intro log i j k p_i p_j p_k hi hj hk hpi hpj hpk hpij hpjk hspec
  set wT := simWorld T specs actOrd pos T
  have hpri_i : (specAt specs i).priLenOk := (h_valid i hi).1
  have hpri_j : (specAt specs j).priLenOk := (h_valid j hj).1
  -- pin the three pop-sequence positions
  obtain ⟨ri, hfi, hpi_eq⟩ := outputPos_findIdx_some T specs actOrd pos
    h_valid h_perm h_fit i hi p_i hpi
  obtain ⟨rj, hfj, hpj_eq⟩ := outputPos_findIdx_some T specs actOrd pos
    h_valid h_perm h_fit j hj p_j hpj
  obtain ⟨rk, hfk, hpk_eq⟩ := outputPos_findIdx_some T specs actOrd pos
    h_valid h_perm h_fit k hk p_k hpk
  have hpos_i : (_root_.findIdx?
      (fun e => decide (e = stageEventOf T specs i (repLenAt specs i)))
      (popSeq wT)).getD 0 = ri :=
    findIdx?_getD_eq_of_some (popSeq wT) (stageEventOf T specs i (repLenAt specs i)) ri hfi
  have hpos_j : (_root_.findIdx?
      (fun e => decide (e = stageEventOf T specs j (repLenAt specs j)))
      (popSeq wT)).getD 0 = rj :=
    findIdx?_getD_eq_of_some (popSeq wT) (stageEventOf T specs j (repLenAt specs j)) rj hfj
  have hpos_k : (_root_.findIdx?
      (fun e => decide (e = stageEventOf T specs k (repLenAt specs k)))
      (popSeq wT)).getD 0 = rk :=
    findIdx?_getD_eq_of_some (popSeq wT) (stageEventOf T specs k (repLenAt specs k)) rk hfk
  have hrij : ri < rj := by
    rw [hpi_eq, hpj_eq] at hpij
    omega
  have hrjk : rj < rk := by
    rw [hpj_eq, hpk_eq] at hpjk
    omega
  have hfindij : (_root_.findIdx?
      (fun e => decide (e = stageEventOf T specs i (repLenAt specs i)))
      (popSeq wT)).getD 0 <
        (_root_.findIdx?
          (fun e => decide (e = stageEventOf T specs j (repLenAt specs j)))
          (popSeq wT)).getD 0 := by
    rw [hpos_i, hpos_j]
    exact hrij
  have hfindjk : (_root_.findIdx?
      (fun e => decide (e = stageEventOf T specs j (repLenAt specs j)))
      (popSeq wT)).getD 0 <
        (_root_.findIdx?
          (fun e => decide (e = stageEventOf T specs k (repLenAt specs k)))
          (popSeq wT)).getD 0 := by
    rw [hpos_j, hpos_k]
    exact hrjk
  -- membership of the three last-repeater events
  have hev_i_mem : stageEventOf T specs i (repLenAt specs i) ∈ popSeq wT :=
    findIdx?_mem_of_some (popSeq wT) (stageEventOf T specs i (repLenAt specs i)) ri hfi
  have hev_j_mem : stageEventOf T specs j (repLenAt specs j) ∈ popSeq wT :=
    findIdx?_mem_of_some (popSeq wT) (stageEventOf T specs j (repLenAt specs j)) rj hfj
  have hev_k_mem : stageEventOf T specs k (repLenAt specs k) ∈ popSeq wT :=
    findIdx?_mem_of_some (popSeq wT) (stageEventOf T specs k (repLenAt specs k)) rk hfk
  -- the pop sequence is priority-sorted
  have hsorted : (popSeq wT).Pairwise (fun a b => a.priority ≤ b.priority) :=
    popSeq_sorted_priority wT
  -- priority sandwich: last priorities agree
  have hxz : (stageEventOf T specs i (repLenAt specs i)).priority =
      (stageEventOf T specs k (repLenAt specs k)).priority := by
    dsimp [stageEventOf]
    rw [stagePriAt_spec specs i k (repLenAt specs i) hspec,
      repLenAt_spec specs i k hspec]
  have hpri_eq : stagePriAt specs j (repLenAt specs j) =
      stagePriAt specs i (repLenAt specs i) :=
    pairwise_le_sandwich (popSeq wT) (fun e => e.priority) hsorted
      hev_i_mem hev_j_mem hev_k_mem hfindij hfindjk hxz
  have hlastPri_eq : (specAt specs j).lastPriority =
      (specAt specs i).lastPriority := by
    have hle_i : (specAt specs i).middleDelays.length ≤ repLenAt specs i := by
      simp [repLenAt]
    have hle_j : (specAt specs j).middleDelays.length ≤ repLenAt specs j := by
      simp [repLenAt]
    rw [stagePriAt_of_eq specs i hpri_i hle_i,
      stagePriAt_of_eq specs j hpri_j hle_j] at hpri_eq
    exact hpri_eq
  -- delay equality: the sandwiched chain shares the reference lastDelay
  have hlastPri_ik : (specAt specs i).lastPriority = (specAt specs k).lastPriority := by
    rw [hspec]
  have hlastPri_jk : (specAt specs j).lastPriority = (specAt specs k).lastPriority := by
    rw [hlastPri_eq, hlastPri_ik]
  have hdelay_ij := lastRep_delay_ge_of_before T specs actOrd pos h_valid h_perm h_fit
    i j hi hj hev_i_mem hev_j_mem hlastPri_eq.symm hfindij
  have hdelay_jk := lastRep_delay_ge_of_before T specs actOrd pos h_valid h_perm h_fit
    j k hj hk hev_j_mem hev_k_mem hlastPri_jk hfindjk
  have hdelay_ki : (specAt specs k).lastDelay = (specAt specs i).lastDelay := by
    rw [hspec]
  have hdelay_jge_i : (specAt specs j).lastDelay ≥ (specAt specs i).lastDelay := by
    rw [hdelay_ki] at hdelay_jk
    exact hdelay_jk
  have hlastDelay_eq : (specAt specs j).lastDelay = (specAt specs i).lastDelay :=
    le_antisymm hdelay_ij hdelay_jge_i
  -- the recursive descent: delay equality and the parent bridge
  obtain ⟨hlen_eq, hstage⟩ := sandwich_descent T specs actOrd pos h_valid h_perm h_fit
    i j k hi hj hk hfindij hfindjk hspec hlastPri_eq hlastDelay_eq
  exact (spec_eq_of_all_stage_eq specs i j hpri_i hpri_j hlen_eq.symm hstage
    hlastDelay_eq.symm hlastPri_eq.symm).symm
