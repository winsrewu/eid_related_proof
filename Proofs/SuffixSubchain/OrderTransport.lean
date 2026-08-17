import Proofs.SuffixSubchain.Descent

open BasicRedstoneSim
open List

/-! # Suffix order transport (pair-wise)

Within a suffix family the cascade from the first suffix repeater down to the
last repeater preserves the relative pop order of any two chains, because the
two chains fire every repeater at the same tick and with the same priority. -/

/-- One step of the pair-wise transport: if two same-suffix chains are
    ordered at distance `r + 1`, they stay ordered at distance `r`. -/
theorem suffix_pair_step_forward
    (n T : Nat) (specs : List ChainSpec) (actOrd : List Nat)
    (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (h_fit : ∀ i < specs.length, chainDelay (specAt specs i) ≤ T)
    (i j : Nat) (hi : i < specs.length) (hj : j < specs.length)
    (s : List (PNat × Int))
    (hi_spec : (specAt specs i).suffixSpec n = some s)
    (hj_spec : (specAt specs j).suffixSpec n = some s)
    (r : Nat) (hr : r + 1 < n) :
    eventIdx (wI T specs actOrd pos i (r + 1)) (evI T specs i (r + 1)) <
      eventIdx (wI T specs actOrd pos i (r + 1)) (evJ T specs j (r + 1)) →
    eventIdx (wI T specs actOrd pos i r) (evI T specs i r) <
      eventIdx (wI T specs actOrd pos i r) (evJ T specs j r) := by
  intro hb
  have hpri_i : (specAt specs i).priLenOk := (h_valid i hi).1
  have hpri_j : (specAt specs j).priLenOk := (h_valid j hj).1
  have hi_ge : n ≤ repLenAt specs i + 1 := suffixSpec_repLen_ge specs i n s hpri_i hi_spec
  have hj_ge : n ≤ repLenAt specs j + 1 := suffixSpec_repLen_ge specs j n s hpri_j hj_spec
  have hr_lt : r < n := by omega
  have hmem_stage : ∀ c < specs.length, ∀ st ≤ repLenAt specs c,
      stageEventOf T specs c st ∈
        popSeq (simWorld T specs actOrd pos (stageTickOf T specs c st)) := by
    intro c hc st hs
    have hpresent := stageEvent_present T specs actOrd pos h_valid h_perm c hc
      (h_fit c hc) st hs
    have hdue : (stageEventOf T specs c st).targetTick = stageTickOf T specs c st := by
      dsimp [stageEventOf]
    exact mem_popSeq_of_due
      (simWorld T specs actOrd pos (stageTickOf T specs c st))
      (stageEventOf T specs c st) hpresent (by simpa [simWorld_tick] using hdue)
  let sx := repLenAt specs i - (r + 1)
  let sy := repLenAt specs j - (r + 1)
  have hsx_lt : sx < repLenAt specs i := by
    dsimp [sx]
    exact Nat.sub_lt (by omega) (by omega)
  have hsy_lt : sy < repLenAt specs j := by
    dsimp [sy]
    exact Nat.sub_lt (by omega) (by omega)
  have htick : stageTickOf T specs i sx = stageTickOf T specs j sy := by
    dsimp [sx, sy]
    exact suffixStageTick_eq T specs i j n (r + 1) s hpri_i hpri_j (h_fit i hi) (h_fit j hj)
      hi_spec hj_spec hr
  have htick_succ : stageTickOf T specs i (sx + 1) = stageTickOf T specs j (sy + 1) := by
    dsimp [sx, sy]
    have hsx_succ : repLenAt specs i - (r + 1) + 1 = repLenAt specs i - r := by omega
    have hsy_succ : repLenAt specs j - (r + 1) + 1 = repLenAt specs j - r := by omega
    simpa [hsx_succ, hsy_succ] using
      (suffixStageTick_eq T specs i j n r s hpri_i hpri_j (h_fit i hi) (h_fit j hj)
        hi_spec hj_spec hr_lt)
  have hx_mem : evI T specs i (r + 1) ∈ popSeq (wI T specs actOrd pos i (r + 1)) := by
    change stageEventOf T specs i (repLenAt specs i - (r + 1)) ∈
      popSeq (simWorld T specs actOrd pos
        (stageTickOf T specs i (repLenAt specs i - (r + 1))))
    exact hmem_stage i hi (repLenAt specs i - (r + 1)) (by omega)
  have hy_mem : evJ T specs j (r + 1) ∈ popSeq (wI T specs actOrd pos i (r + 1)) := by
    change stageEventOf T specs j (repLenAt specs j - (r + 1)) ∈
      popSeq (simWorld T specs actOrd pos
        (stageTickOf T specs i (repLenAt specs i - (r + 1))))
    rw [htick]
    exact hmem_stage j hj (repLenAt specs j - (r + 1)) (by omega)
  have hb' : eventIdx (wI T specs actOrd pos i (r + 1)) (evI T specs i (r + 1)) <
      eventIdx (wI T specs actOrd pos i (r + 1)) (evJ T specs j (r + 1)) := hb
  have hsucc_ev := stageRep_succ_order_ev T specs actOrd pos h_valid h_perm h_fit
    i j sx sy hi hj hsx_lt hsy_lt htick htick_succ
    (evI T specs i (r + 1)) (evJ T specs j (r + 1)) (wI T specs actOrd pos i (r + 1))
    (by dsimp [evI, sx]) (by dsimp [evJ, sy])
    (by dsimp [wI, sx])
    hx_mem hy_mem hb'
  have hsucc_ev' : eventIdxEvents (wI T specs actOrd pos i r) (evI T specs i r) <
      eventIdxEvents (wI T specs actOrd pos i r) (evJ T specs j r) := by
    dsimp [eventIdxEvents, evI, evJ, wI] at hsucc_ev ⊢
    have hsx_succ : repLenAt specs i - (r + 1) + 1 = repLenAt specs i - r := by omega
    have hsy_succ : repLenAt specs j - (r + 1) + 1 = repLenAt specs j - r := by omega
    rw [hsx_succ, hsy_succ] at hsucc_ev
    have htick_r : stageTickOf T specs i (repLenAt specs i - r) =
        stageTickOf T specs j (repLenAt specs j - r) := by
      dsimp [sx, sy] at htick_succ
      simpa [hsx_succ, hsy_succ] using htick_succ
    simpa [htick_r] using hsucc_ev
  have hx_mem_r : evI T specs i r ∈ popSeq (wI T specs actOrd pos i r) := by
    change stageEventOf T specs i (repLenAt specs i - r) ∈
      popSeq (simWorld T specs actOrd pos (stageTickOf T specs i (repLenAt specs i - r)))
    exact hmem_stage i hi (repLenAt specs i - r) (by omega)
  have hy_mem_r : evJ T specs j r ∈ popSeq (wI T specs actOrd pos i r) := by
    change stageEventOf T specs j (repLenAt specs j - r) ∈
      popSeq (simWorld T specs actOrd pos (stageTickOf T specs i (repLenAt specs i - r)))
    have htick_r : stageTickOf T specs i (repLenAt specs i - r) =
        stageTickOf T specs j (repLenAt specs j - r) := by
      have hsx_succ : repLenAt specs i - (r + 1) + 1 = repLenAt specs i - r := by omega
      have hsy_succ : repLenAt specs j - (r + 1) + 1 = repLenAt specs j - r := by omega
      dsimp [sx, sy] at htick_succ
      simpa [hsx_succ, hsy_succ] using htick_succ
    rw [htick_r]
    exact hmem_stage j hj (repLenAt specs j - r) (by omega)
  have hpri_r : (evI T specs i r).priority = (evJ T specs j r).priority := by
    dsimp [evI, evJ, stageEventOf]
    exact (suffixStage_eq specs i j n r s hpri_i hpri_j hi_spec hj_spec hr_lt).2
  have hnodup_r : (wI T specs actOrd pos i r).events.Nodup :=
    (simWorld_tickInv T specs actOrd pos h_valid h_perm
      (stageTickOf T specs i (repLenAt specs i - r))).1
  have hpopNd_r : (popSeq (wI T specs actOrd pos i r)).Nodup :=
    popSeq_nodup_of_tickInv T specs h_valid
      (stageTickOf T specs i (repLenAt specs i - r)) (wI T specs actOrd pos i r).events []
      (wI T specs actOrd pos i r)
      (by dsimp [wI]; rw [simWorld_tick])
      (simWorld_tickInv T specs actOrd pos h_valid h_perm
        (stageTickOf T specs i (repLenAt specs i - r)))
  have hres := events_same_priority_findIdx_order (wI T specs actOrd pos i r)
    hx_mem_r hy_mem_r hnodup_r hpopNd_r hpri_r
    (by dsimp [eventIdxEvents] at hsucc_ev'; exact hsucc_ev')
  dsimp [eventIdx] at hres ⊢
  exact hres

/-- The forward direction of the pair-wise transport: order at the first
    suffix repeater implies order at the last repeater. -/
theorem suffix_pair_fwd
    (n T : Nat) (specs : List ChainSpec) (actOrd : List Nat)
    (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (h_fit : ∀ i < specs.length, chainDelay (specAt specs i) ≤ T)
    (i j : Nat) (hi : i < specs.length) (hj : j < specs.length)
    (s : List (PNat × Int))
    (hi_spec : (specAt specs i).suffixSpec n = some s)
    (hj_spec : (specAt specs j).suffixSpec n = some s)
    (hn : 1 ≤ n) :
    eventIdx (wI T specs actOrd pos i (n - 1)) (evI T specs i (n - 1)) <
      eventIdx (wI T specs actOrd pos i (n - 1)) (evJ T specs j (n - 1)) →
    eventIdx (wI T specs actOrd pos i 0) (evI T specs i 0) <
      eventIdx (wI T specs actOrd pos i 0) (evJ T specs j 0) := by
  intro h
  have hgeneral : ∀ r, r < n →
      eventIdx (wI T specs actOrd pos i r) (evI T specs i r) <
        eventIdx (wI T specs actOrd pos i r) (evJ T specs j r) →
      eventIdx (wI T specs actOrd pos i 0) (evI T specs i 0) <
        eventIdx (wI T specs actOrd pos i 0) (evJ T specs j 0) := by
    intro r
    induction r with
    | zero => intro _ h; exact h
    | succ r' ih =>
        intro hr_succ h'
        have hr'_lt : r' < n := by omega
        have hstep := suffix_pair_step_forward n T specs actOrd pos h_valid h_perm h_fit
          i j hi hj s hi_spec hj_spec r' hr_succ h'
        exact ih hr'_lt hstep
  exact hgeneral (n - 1) (by omega) h

/-- Within a suffix family the pop order of the first suffix repeaters equals
    the pop order of the last repeaters. -/
theorem suffix_pair_order_forward
    (n T : Nat) (specs : List ChainSpec) (actOrd : List Nat)
    (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (h_fit : ∀ i < specs.length, chainDelay (specAt specs i) ≤ T)
    (i j : Nat) (hi : i < specs.length) (hj : j < specs.length)
    (s : List (PNat × Int))
    (hi_spec : (specAt specs i).suffixSpec n = some s)
    (hj_spec : (specAt specs j).suffixSpec n = some s)
    (hn : 1 ≤ n) :
    (eventIdx (wI T specs actOrd pos i 0) (evI T specs i 0) <
       eventIdx (wI T specs actOrd pos i 0) (evJ T specs j 0)) ↔
    (eventIdx (wI T specs actOrd pos i (n - 1)) (evI T specs i (n - 1)) <
       eventIdx (wI T specs actOrd pos i (n - 1)) (evJ T specs j (n - 1))) := by
  have hpri_i : (specAt specs i).priLenOk := (h_valid i hi).1
  have hpri_j : (specAt specs j).priLenOk := (h_valid j hj).1
  constructor
  · intro h0
    by_cases hij : i = j
    · subst j
      dsimp [evI, evJ, wI] at h0 ⊢
      rw [stageTickOf_last T specs i (h_fit i hi)] at h0
      omega
    · have hfwd_swap := suffix_pair_fwd n T specs actOrd pos h_valid h_perm h_fit
        j i hj hi s hj_spec hi_spec hn
      by_contra hnot
      have hne : evI T specs i (n - 1) ≠ evJ T specs j (n - 1) := by
        intro he
        have hnode := congrArg ScheduledEvent.nodeId he
        dsimp [evI, evJ, stageEventOf] at hnode
        have hxy' := chainRepId_inj specs i j (repLenAt specs i - (n - 1))
          (repLenAt specs j - (n - 1)) hi hj
          (by dsimp [repLenAt]; omega) (by dsimp [repLenAt]; omega)
          hpri_i hpri_j hnode
        exact hij hxy'.1
      have hrev : eventIdx (wI T specs actOrd pos i (n - 1)) (evJ T specs j (n - 1)) <
          eventIdx (wI T specs actOrd pos i (n - 1)) (evI T specs i (n - 1)) := by
        have hle := Nat.le_of_not_gt hnot
        have hne_idx := findIdx?_ne_of_ne (popSeq (wI T specs actOrd pos i (n - 1)))
          (by
            change stageEventOf T specs i (repLenAt specs i - (n - 1)) ∈
              popSeq (simWorld T specs actOrd pos
                (stageTickOf T specs i (repLenAt specs i - (n - 1))))
            have hpresent := stageEvent_present T specs actOrd pos h_valid h_perm i hi
              (h_fit i hi) (repLenAt specs i - (n - 1)) (by omega)
            exact mem_popSeq_of_due
              (simWorld T specs actOrd pos (stageTickOf T specs i (repLenAt specs i - (n - 1))))
              (stageEventOf T specs i (repLenAt specs i - (n - 1))) hpresent
              (by dsimp [stageEventOf]; simp [simWorld_tick]))
          (by
            change stageEventOf T specs j (repLenAt specs j - (n - 1)) ∈
              popSeq (simWorld T specs actOrd pos
                (stageTickOf T specs i (repLenAt specs i - (n - 1))))
            have htick_n := suffixStageTick_eq T specs i j n (n - 1) s hpri_i hpri_j
              (h_fit i hi) (h_fit j hj) hi_spec hj_spec (by omega)
            rw [htick_n]
            have hpresent := stageEvent_present T specs actOrd pos h_valid h_perm j hj
              (h_fit j hj) (repLenAt specs j - (n - 1)) (by omega)
            exact mem_popSeq_of_due
              (simWorld T specs actOrd pos (stageTickOf T specs j (repLenAt specs j - (n - 1))))
              (stageEventOf T specs j (repLenAt specs j - (n - 1))) hpresent
              (by dsimp [stageEventOf]; simp [simWorld_tick]))
          hne
        exact Nat.lt_of_le_of_ne hle hne_idx.symm
      have hrev_j : eventIdx (wI T specs actOrd pos j (n - 1)) (evI T specs j (n - 1)) <
          eventIdx (wI T specs actOrd pos j (n - 1)) (evJ T specs i (n - 1)) := by
        have htick_n : stageTickOf T specs i (repLenAt specs i - (n - 1)) =
            stageTickOf T specs j (repLenAt specs j - (n - 1)) :=
          suffixStageTick_eq T specs i j n (n - 1) s hpri_i hpri_j
            (h_fit i hi) (h_fit j hj) hi_spec hj_spec (by omega)
        dsimp [eventIdx, evI, evJ, wI] at hrev ⊢
        simpa [htick_n] using hrev
      have hrev0 := hfwd_swap hrev_j
      have hcontra : eventIdx (wI T specs actOrd pos i 0) (evJ T specs j 0) <
          eventIdx (wI T specs actOrd pos i 0) (evI T specs i 0) := by
        have htick0 : stageTickOf T specs i (repLenAt specs i) =
            stageTickOf T specs j (repLenAt specs j) := by
          rw [stageTickOf_last T specs i (h_fit i hi), stageTickOf_last T specs j (h_fit j hj)]
        dsimp [eventIdx, evI, evJ, wI] at hrev0 ⊢
        simpa [htick0] using hrev0
      omega
  · intro hn1
    exact suffix_pair_fwd n T specs actOrd pos h_valid h_perm h_fit
      i j hi hj s hi_spec hj_spec hn hn1
