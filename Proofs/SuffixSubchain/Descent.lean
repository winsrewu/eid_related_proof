import Proofs.SuffixSubchain.Algebra
import Proofs.Clustering.Descent

open BasicRedstoneSim
open List

/-! # The suffix descent (no-group suffix clustering)

`descent_trace` in `Proofs.Clustering.DescentTrace` marches a sandwiched
triple down one stage at a time, but it assumes the two reference chains
share a full spec, so `repLenAt i = repLenAt k` and the `_spec` lemmas
connect `i` and `k` at equal stage indices. Here the two reference chains
only share their last `n` repeaters, so `repLenAt i` and `repLenAt k` may
differ. The descent below tracks the three stage indices
`repLenAt i - r`, `repLenAt j - r`, `repLenAt k - r` separately and connects
`i` and `k` through the suffix-matching lemmas of
`Proofs.SuffixSubchain.Algebra`. -/

/-- The stage-by-stage suffix descent, from the last repeater (`r = 0`)
    down to the first suffix repeater (`r = n - 1`). At every distance `r`
    the two sandwiched chains and the interloper agree on firing tick and
    priority, keep the pop order, and (for strict stages) agree on delay. -/
theorem suffix_descent_trace
    (n : Nat) (T : Nat) (specs : List ChainSpec) (actOrd : List Nat)
    (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (h_fit : ∀ i < specs.length, chainDelay (specAt specs i) ≤ T)
    (i j k : Nat) (hi : i < specs.length) (hj : j < specs.length) (hk : k < specs.length)
    (s : List (PNat × Int))
    (hi_spec : (specAt specs i).suffixSpec n = some s)
    (hk_spec : (specAt specs k).suffixSpec n = some s)
    (hij : (_root_.findIdx? (fun e => decide (e = stageEventOf T specs i (repLenAt specs i)))
            (popSeq (simWorld T specs actOrd pos T))).getD 0 <
          (_root_.findIdx? (fun e => decide (e = stageEventOf T specs j (repLenAt specs j)))
            (popSeq (simWorld T specs actOrd pos T))).getD 0)
    (hjk : (_root_.findIdx? (fun e => decide (e = stageEventOf T specs j (repLenAt specs j)))
            (popSeq (simWorld T specs actOrd pos T))).getD 0 <
          (_root_.findIdx? (fun e => decide (e = stageEventOf T specs k (repLenAt specs k)))
            (popSeq (simWorld T specs actOrd pos T))).getD 0)
    (hlastPri : (specAt specs j).lastPriority = (specAt specs i).lastPriority)
    (hlastDelay : (specAt specs j).lastDelay = (specAt specs i).lastDelay) :
    ∀ r, r < n → r ≤ repLenAt specs j →
      stageTickOf T specs i (repLenAt specs i - r) =
        stageTickOf T specs j (repLenAt specs j - r) ∧
      stagePriAt specs i (repLenAt specs i - r) =
        stagePriAt specs j (repLenAt specs j - r) ∧
      eventIdx (wI T specs actOrd pos i r) (evI T specs i r) <
        eventIdx (wI T specs actOrd pos i r) (evJ T specs j r) ∧
      eventIdx (wI T specs actOrd pos i r) (evJ T specs j r) <
        eventIdx (wI T specs actOrd pos i r)
          (stageEventOf T specs k (repLenAt specs k - r)) ∧
      (0 < repLenAt specs i - r → 0 < repLenAt specs j - r →
        stageDelayAt specs i (repLenAt specs i - r) =
          stageDelayAt specs j (repLenAt specs j - r)) := by
  have hpri_i : (specAt specs i).priLenOk := (h_valid i hi).1
  have hpri_j : (specAt specs j).priLenOk := (h_valid j hj).1
  have hpri_k : (specAt specs k).priLenOk := (h_valid k hk).1
  have hine : i ≠ j := by
    intro h
    subst h
    have hself : (_root_.findIdx? (fun e => decide (e = stageEventOf T specs i (repLenAt specs i)))
        (popSeq (simWorld T specs actOrd pos T))).getD 0 <
        (_root_.findIdx? (fun e => decide (e = stageEventOf T specs i (repLenAt specs i)))
          (popSeq (simWorld T specs actOrd pos T))).getD 0 := by
      exact hij
    omega
  have hkne : j ≠ k := by
    intro h
    subst h
    have hself : (_root_.findIdx? (fun e => decide (e = stageEventOf T specs j (repLenAt specs j)))
        (popSeq (simWorld T specs actOrd pos T))).getD 0 <
        (_root_.findIdx? (fun e => decide (e = stageEventOf T specs j (repLenAt specs j)))
          (popSeq (simWorld T specs actOrd pos T))).getD 0 := by
      exact hjk
    omega
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
  let wi : Nat → World := wI T specs actOrd pos i
  intro r
  induction r with
  | zero =>
      intro _ _
      have htick0 : stageTickOf T specs i (repLenAt specs i) =
          stageTickOf T specs j (repLenAt specs j) := by
        rw [stageTickOf_last T specs i (h_fit i hi),
          stageTickOf_last T specs j (h_fit j hj)]
      have hpri0 : stagePriAt specs i (repLenAt specs i) =
          stagePriAt specs j (repLenAt specs j) := by
        have hle_i : (specAt specs i).middleDelays.length ≤ repLenAt specs i := by
          simp [repLenAt]
        have hle_j : (specAt specs j).middleDelays.length ≤ repLenAt specs j := by
          simp [repLenAt]
        rw [stagePriAt_of_eq specs i hpri_i hle_i,
          stagePriAt_of_eq specs j hpri_j hle_j]
        exact hlastPri.symm
      have hij0 : eventIdx (wi 0) (evI T specs i 0) < eventIdx (wi 0) (evJ T specs j 0) := by
        dsimp [eventIdx, evI, evJ, wi, wI]
        rw [stageTickOf_last T specs i (h_fit i hi)]
        exact hij
      have hjk0 : eventIdx (wi 0) (evJ T specs j 0) <
          eventIdx (wi 0) (stageEventOf T specs k (repLenAt specs k)) := by
        dsimp [eventIdx, evJ, wi, wI]
        rw [stageTickOf_last T specs i (h_fit i hi)]
        exact hjk
      have hdel0 : 0 < repLenAt specs i - 0 → 0 < repLenAt specs j - 0 →
          stageDelayAt specs i (repLenAt specs i) =
            stageDelayAt specs j (repLenAt specs j) := by
        intro _ _
        have hle_i : (specAt specs i).middleDelays.length ≤ repLenAt specs i := by
          simp [repLenAt]
        have hle_j : (specAt specs j).middleDelays.length ≤ repLenAt specs j := by
          simp [repLenAt]
        rw [stageDelayAt_of_eq specs i hle_i, stageDelayAt_of_eq specs j hle_j]
        exact hlastDelay.symm
      exact ⟨htick0, hpri0, hij0, hjk0, hdel0⟩
  | succ r' ih =>
      intro hr_succ hrj
      have hr'_lt : r' < n := by omega
      have hi_ge : n ≤ repLenAt specs i + 1 := suffixSpec_repLen_ge specs i n s hpri_i hi_spec
      have hk_ge : n ≤ repLenAt specs k + 1 := suffixSpec_repLen_ge specs k n s hpri_k hk_spec
      obtain ⟨htick', hpri', hij', hjk', hdel'_cond⟩ := ih hr'_lt (by omega)
      let sx := repLenAt specs i - (r' + 1)
      let sy := repLenAt specs j - (r' + 1)
      let sz := repLenAt specs k - (r' + 1)
      have hsx_succ : sx + 1 = repLenAt specs i - r' := by
        dsimp [sx]
        omega
      have hsy_succ : sy + 1 = repLenAt specs j - r' := by
        dsimp [sy]
        omega
      have hsz_succ : sz + 1 = repLenAt specs k - r' := by
        dsimp [sz]
        omega
      have hsx_lt : sx < repLenAt specs i := by
        dsimp [sx]
        exact Nat.sub_lt (by omega) (by omega)
      have hsy_lt : sy < repLenAt specs j := by
        dsimp [sy]
        exact Nat.sub_lt (by omega) (by omega)
      have hsz_lt : sz < repLenAt specs k := by
        dsimp [sz]
        exact Nat.sub_lt (by omega) (by omega)
      have hdel_U : stageDelayAt specs i (repLenAt specs i - r') =
          stageDelayAt specs j (repLenAt specs j - r') :=
        hdel'_cond (by omega) (by omega)
      -- (a) tick equality at r'+1
      have htick_r : stageTickOf T specs i sx = stageTickOf T specs j sy := by
        have hi_eq : stageTickOf T specs i (sx + 1) = stageTickOf T specs j (sy + 1) := by
          simpa [hsx_succ, hsy_succ] using htick'
        have hdel_eq : stageDelayAt specs i (sx + 1) = stageDelayAt specs j (sy + 1) := by
          simpa [hsx_succ, hsy_succ] using hdel_U
        have hi_succ := stageTickOf_succ T specs i sx (by
          rw [hsx_succ]
          dsimp [repLenAt]
          omega)
        have hj_succ := stageTickOf_succ T specs j sy (by
          rw [hsy_succ]
          dsimp [repLenAt]
          omega)
        have hdel_eqN : (stageDelayAt specs i (sx + 1) : Nat) =
            (stageDelayAt specs j (sy + 1) : Nat) := by
          exact_mod_cast hdel_eq
        omega
      -- suffix i↔k connections at distance r'+1 and r'
      have htick_ik : stageTickOf T specs i sx = stageTickOf T specs k sz :=
        suffixStageTick_eq T specs i k n (r' + 1) s hpri_i hpri_k (h_fit i hi) (h_fit k hk)
          hi_spec hk_spec hr_succ
      have hpri_ik : stagePriAt specs i sx = stagePriAt specs k sz :=
        (suffixStage_eq specs i k n (r' + 1) s hpri_i hpri_k hi_spec hk_spec hr_succ).2
      have hdelay_ik : stageDelayAt specs i sx = stageDelayAt specs k sz :=
        (suffixStage_eq specs i k n (r' + 1) s hpri_i hpri_k hi_spec hk_spec hr_succ).1
      have htick_ik' : stageTickOf T specs i (repLenAt specs i - r') =
          stageTickOf T specs k (repLenAt specs k - r') :=
        suffixStageTick_eq T specs i k n r' s hpri_i hpri_k (h_fit i hi) (h_fit k hk)
          hi_spec hk_spec hr'_lt
      -- (b) sandwich i < j at r'+1
      have hij_r : eventIdx (wi (r' + 1)) (evI T specs i (r' + 1)) <
          eventIdx (wi (r' + 1)) (evJ T specs j (r' + 1)) := by
        by_contra hnot
        have hmem_i_sx : stageEventOf T specs i sx ∈ popSeq (wi (r' + 1)) := by
          change stageEventOf T specs i sx ∈ popSeq (simWorld T specs actOrd pos (stageTickOf T specs i sx))
          exact hmem_stage i hi sx (Nat.le_of_lt hsx_lt)
        have hmem_j_sy : stageEventOf T specs j sy ∈ popSeq (wi (r' + 1)) := by
          change stageEventOf T specs j sy ∈ popSeq (simWorld T specs actOrd pos (stageTickOf T specs i sx))
          rw [htick_r]
          exact hmem_stage j hj sy (Nat.le_of_lt hsy_lt)
        have hne_ij : stageEventOf T specs i sx ≠ stageEventOf T specs j sy := by
          intro h
          have hnode := congrArg ScheduledEvent.nodeId h
          dsimp [stageEventOf] at hnode
          have hxy' := chainRepId_inj specs i j sx sy hi hj
            (by dsimp [sx, repLenAt]; omega) (by dsimp [sy, repLenAt]; omega)
            hpri_i hpri_j hnode
          exact hine hxy'.1
        have hne_idx := findIdx?_ne_of_ne (popSeq (wi (r' + 1)))
          hmem_i_sx hmem_j_sy hne_ij
        have hle := Nat.le_of_not_gt hnot
        have hrev : eventIdx (wi (r' + 1)) (evJ T specs j (r' + 1)) <
            eventIdx (wi (r' + 1)) (evI T specs i (r' + 1)) :=
          Nat.lt_of_le_of_ne hle hne_idx.symm
        have hrev_r := stageRep_succ_order_ev T specs actOrd pos h_valid h_perm h_fit
          j i sy sx hj hi hsy_lt hsx_lt htick_r.symm
          (by simpa [hsy_succ, hsx_succ] using htick'.symm)
          (evJ T specs j (r' + 1)) (evI T specs i (r' + 1)) (wi (r' + 1))
          (by dsimp [evJ, sy]) (by dsimp [evI, sx])
          (by dsimp [wi, wI, sx]; rw [htick_r])
          (by dsimp [evJ, sy]; exact hmem_j_sy)
          (by dsimp [evI, sx]; exact hmem_i_sx)
          hrev
        have hcontra : eventIdxEvents (wi r') (evJ T specs j r') <
            eventIdxEvents (wi r') (evI T specs i r') := by
          dsimp [eventIdxEvents, evJ, evI, wi, wI] at hrev_r ⊢
          simpa [hsy_succ, hsx_succ, htick'] using hrev_r
        have hij'_ev : eventIdxEvents (wi r') (evI T specs i r') <
            eventIdxEvents (wi r') (evJ T specs j r') := by
          have hmem_i_U : evI T specs i r' ∈ popSeq (wi r') := by
            change stageEventOf T specs i (repLenAt specs i - r') ∈ popSeq (simWorld T specs actOrd pos (stageTickOf T specs i (repLenAt specs i - r')))
            exact hmem_stage i hi (repLenAt specs i - r') (by omega)
          have hmem_j_U : evJ T specs j r' ∈ popSeq (wi r') := by
            change stageEventOf T specs j (repLenAt specs j - r') ∈ popSeq (simWorld T specs actOrd pos (stageTickOf T specs i (repLenAt specs i - r')))
            rw [htick']
            exact hmem_stage j hj (repLenAt specs j - r') (by omega)
          have hpri_ev : (evI T specs i r').priority = (evJ T specs j r').priority := by
            dsimp [evI, evJ, stageEventOf]
            exact hpri'
          have hnodup : (wi r').events.Nodup :=
            (simWorld_tickInv T specs actOrd pos h_valid h_perm
              (stageTickOf T specs i (repLenAt specs i - r'))).1
          have hpopNd : (popSeq (wi r')).Nodup :=
            popSeq_nodup_of_tickInv T specs h_valid
              (stageTickOf T specs i (repLenAt specs i - r')) (wi r').events [] (wi r')
              (by dsimp [wi, wI]; rw [simWorld_tick])
              (simWorld_tickInv T specs actOrd pos h_valid h_perm
                (stageTickOf T specs i (repLenAt specs i - r')))
          have hb_ev := popSeq_same_priority_findIdx_order (wi r') hmem_i_U hmem_j_U
            hnodup hpopNd hpri_ev (by dsimp [eventIdx] at hij'; exact hij')
          dsimp [eventIdxEvents] at hb_ev ⊢
          exact hb_ev
        exact Nat.lt_asymm hij'_ev hcontra
      -- (c) sandwich j < k at r'+1 (k's own repLenAt)
      have hjk_r : eventIdx (wi (r' + 1)) (evJ T specs j (r' + 1)) <
          eventIdx (wi (r' + 1)) (stageEventOf T specs k sz) := by
        by_contra hnot
        have hmem_j_sy : stageEventOf T specs j sy ∈ popSeq (wi (r' + 1)) := by
          change stageEventOf T specs j sy ∈ popSeq (simWorld T specs actOrd pos (stageTickOf T specs i sx))
          rw [htick_r]
          exact hmem_stage j hj sy (Nat.le_of_lt hsy_lt)
        have hmem_k_sz : stageEventOf T specs k sz ∈ popSeq (wi (r' + 1)) := by
          change stageEventOf T specs k sz ∈ popSeq (simWorld T specs actOrd pos (stageTickOf T specs i sx))
          rw [htick_ik]
          exact hmem_stage k hk sz (Nat.le_of_lt hsz_lt)
        have hne_jk : stageEventOf T specs j sy ≠ stageEventOf T specs k sz := by
          intro h
          have hnode := congrArg ScheduledEvent.nodeId h
          dsimp [stageEventOf] at hnode
          have hxy' := chainRepId_inj specs j k sy sz hj hk
            (by dsimp [sy, repLenAt]; omega) (by dsimp [sz, repLenAt]; omega)
            hpri_j hpri_k hnode
          exact hkne hxy'.1
        have hne_idx := findIdx?_ne_of_ne (popSeq (wi (r' + 1)))
          hmem_j_sy hmem_k_sz hne_jk
        have hle := Nat.le_of_not_gt hnot
        have hrev : eventIdx (wi (r' + 1)) (stageEventOf T specs k sz) <
            eventIdx (wi (r' + 1)) (evJ T specs j (r' + 1)) :=
          Nat.lt_of_le_of_ne hle hne_idx.symm
        have hrev_r := stageRep_succ_order_ev T specs actOrd pos h_valid h_perm h_fit
          k j sz sy hk hj hsz_lt hsy_lt
          (by simpa [sz, sy] using htick_ik.symm.trans htick_r)
          (by simpa [hsx_succ, hsy_succ, hsz_succ] using (htick_ik'.symm.trans htick'))
          (stageEventOf T specs k sz) (evJ T specs j (r' + 1)) (wi (r' + 1))
          (by dsimp [sz]) (by dsimp [evJ, sy])
          (by dsimp [wi, wI, sx]; rw [htick_ik])
          (by dsimp [sz]; exact hmem_k_sz)
          (by dsimp [evJ, sy]; exact hmem_j_sy)
          hrev
        have hcontra : eventIdxEvents (wi r') (stageEventOf T specs k (repLenAt specs k - r')) <
            eventIdxEvents (wi r') (evJ T specs j r') := by
          dsimp [eventIdxEvents, evJ, wi, wI] at hrev_r ⊢
          simpa [hsx_succ, hsy_succ, hsz_succ, htick_ik'.symm, htick'] using hrev_r
        have hjk'_ev : eventIdxEvents (wi r') (evJ T specs j r') <
            eventIdxEvents (wi r') (stageEventOf T specs k (repLenAt specs k - r')) := by
          have hmem_j_U : evJ T specs j r' ∈ popSeq (wi r') := by
            change stageEventOf T specs j (repLenAt specs j - r') ∈ popSeq (simWorld T specs actOrd pos (stageTickOf T specs i (repLenAt specs i - r')))
            rw [htick']
            exact hmem_stage j hj (repLenAt specs j - r') (by omega)
          have hmem_k_U : stageEventOf T specs k (repLenAt specs k - r') ∈ popSeq (wi r') := by
            change stageEventOf T specs k (repLenAt specs k - r') ∈ popSeq (simWorld T specs actOrd pos (stageTickOf T specs i (repLenAt specs i - r')))
            rw [htick_ik']
            exact hmem_stage k hk (repLenAt specs k - r') (by omega)
          have hpri_ev : (evJ T specs j r').priority =
              (stageEventOf T specs k (repLenAt specs k - r')).priority := by
            dsimp [evJ, stageEventOf]
            have hpri_jk : stagePriAt specs j (repLenAt specs j - r') =
                stagePriAt specs k (repLenAt specs k - r') := by
              have hpri_ik'' : stagePriAt specs i (repLenAt specs i - r') =
                  stagePriAt specs k (repLenAt specs k - r') :=
                (suffixStage_eq specs i k n r' s hpri_i hpri_k hi_spec hk_spec hr'_lt).2
              exact hpri'.symm.trans hpri_ik''
            exact hpri_jk
          have hnodup : (wi r').events.Nodup :=
            (simWorld_tickInv T specs actOrd pos h_valid h_perm
              (stageTickOf T specs i (repLenAt specs i - r'))).1
          have hpopNd : (popSeq (wi r')).Nodup :=
            popSeq_nodup_of_tickInv T specs h_valid
              (stageTickOf T specs i (repLenAt specs i - r')) (wi r').events [] (wi r')
              (by dsimp [wi, wI]; rw [simWorld_tick])
              (simWorld_tickInv T specs actOrd pos h_valid h_perm
                (stageTickOf T specs i (repLenAt specs i - r')))
          have hb_ev := popSeq_same_priority_findIdx_order (wi r') hmem_j_U hmem_k_U
            hnodup hpopNd hpri_ev (by dsimp [eventIdx] at hjk'; exact hjk')
          dsimp [eventIdxEvents] at hb_ev ⊢
          exact hb_ev
        exact Nat.lt_asymm hjk'_ev hcontra
      -- (d) priority equality at r'+1
      have hpri_r : stagePriAt specs i sx = stagePriAt specs j sy := by
        have hsorted := popSeq_sorted_priority (wi (r' + 1))
        have hmem_i : evI T specs i (r' + 1) ∈ popSeq (wi (r' + 1)) := by
          change stageEventOf T specs i sx ∈ popSeq (simWorld T specs actOrd pos (stageTickOf T specs i sx))
          exact hmem_stage i hi sx (Nat.le_of_lt hsx_lt)
        have hmem_j : evJ T specs j (r' + 1) ∈ popSeq (wi (r' + 1)) := by
          change stageEventOf T specs j sy ∈ popSeq (simWorld T specs actOrd pos (stageTickOf T specs i sx))
          rw [htick_r]
          exact hmem_stage j hj sy (Nat.le_of_lt hsy_lt)
        have hmem_k : stageEventOf T specs k sz ∈ popSeq (wi (r' + 1)) := by
          change stageEventOf T specs k sz ∈ popSeq (simWorld T specs actOrd pos (stageTickOf T specs i sx))
          rw [htick_ik]
          exact hmem_stage k hk sz (Nat.le_of_lt hsz_lt)
        have hxz : (evI T specs i (r' + 1)).priority =
            (stageEventOf T specs k sz).priority := by
          dsimp [evI, stageEventOf, sx]
          exact hpri_ik
        have hpri := pairwise_le_sandwich (popSeq (wi (r' + 1))) (fun e => e.priority) hsorted
          hmem_i hmem_j hmem_k hij_r hjk_r hxz
        dsimp [evI, evJ, sx, sy, stageEventOf] at hpri
        exact hpri.symm
      -- (e) delay equality at r'+1 (conditional on strict stages)
      have hdel_r : 0 < repLenAt specs i - (r' + 1) → 0 < repLenAt specs j - (r' + 1) →
          stageDelayAt specs i sx = stageDelayAt specs j sy := by
        intro hposx hposy
        have hge_ij := stageRep_delay_ge_of_before_sep_ev T specs actOrd pos h_valid h_perm h_fit
          i j sx sy hi hj hsx_lt hsy_lt (by dsimp [sx]; exact hposx) (by dsimp [sy]; exact hposy)
          htick_r (evI T specs i (r' + 1)) (evJ T specs j (r' + 1)) (wi (r' + 1))
          (by dsimp [evI, sx]) (by dsimp [evJ, sy])
          (by dsimp [wi, wI, sx])
          (by change stageEventOf T specs i sx ∈ popSeq (simWorld T specs actOrd pos (stageTickOf T specs i sx)); exact hmem_stage i hi sx (Nat.le_of_lt hsx_lt))
          (by change stageEventOf T specs j sy ∈ popSeq (simWorld T specs actOrd pos (stageTickOf T specs i sx)); rw [htick_r]; exact hmem_stage j hj sy (Nat.le_of_lt hsy_lt))
          hpri_r hij_r
        have htick_jk : stageTickOf T specs j sy = stageTickOf T specs k sz :=
          htick_r.symm.trans htick_ik
        have hpri_jk : stagePriAt specs j sy = stagePriAt specs k sz :=
          hpri_r.symm.trans hpri_ik
        have hge_jk : stageDelayAt specs j sy ≥ stageDelayAt specs k sz := by
          by_cases hsz0 : sz = 0
          · have hsz0' : repLenAt specs k - (r' + 1) = 0 := by
              dsimp [sz] at hsz0
              exact hsz0
            dsimp [sz] at htick_jk hpri_jk hjk_r ⊢
            rw [hsz0'] at htick_jk hpri_jk hjk_r ⊢
            have hjk_r0 : (_root_.findIdx? (fun e => decide (e = stageEventOf T specs j sy))
                (popSeq (simWorld T specs actOrd pos (stageTickOf T specs j sy)))).getD 0 <
              (_root_.findIdx? (fun e => decide (e = stageEventOf T specs k 0))
                (popSeq (simWorld T specs actOrd pos (stageTickOf T specs j sy)))).getD 0 := by
              dsimp [eventIdx, evJ, wi, wI] at hjk_r
              simpa [sy, sx, htick_r] using hjk_r
            have hmem_j : stageEventOf T specs j sy ∈
                popSeq (simWorld T specs actOrd pos (stageTickOf T specs j sy)) :=
              hmem_stage j hj sy (Nat.le_of_lt hsy_lt)
            have hmem_k : stageEventOf T specs k 0 ∈
                popSeq (simWorld T specs actOrd pos (stageTickOf T specs j sy)) := by
              have hm := hmem_stage k hk 0 (by simp [repLenAt])
              simpa [htick_jk.symm] using hm
            exact rep_delay_ge_of_before_mid0 T specs actOrd pos h_valid h_perm h_fit
              j k sy hj hk (by dsimp [sy]; exact hposy) (by dsimp [sy]; omega)
              htick_jk hpri_jk hmem_j hmem_k hjk_r0
          · have hsz_pos : 0 < sz := by omega
            exact stageRep_delay_ge_of_before_sep_ev T specs actOrd pos h_valid h_perm h_fit
              j k sy sz hj hk hsy_lt hsz_lt (by dsimp [sy]; exact hposy) (by dsimp [sz]; exact hsz_pos)
              htick_jk (evJ T specs j (r' + 1)) (stageEventOf T specs k sz) (wi (r' + 1))
              (by dsimp [evJ, sy]) (by dsimp [sz])
              (by dsimp [wi, wI, sx]; rw [htick_r])
              (by change stageEventOf T specs j sy ∈ popSeq (simWorld T specs actOrd pos (stageTickOf T specs i sx)); rw [htick_r]; exact hmem_stage j hj sy (Nat.le_of_lt hsy_lt))
              (by change stageEventOf T specs k sz ∈ popSeq (simWorld T specs actOrd pos (stageTickOf T specs i sx)); rw [htick_ik]; exact hmem_stage k hk sz (Nat.le_of_lt hsz_lt))
              hpri_jk hjk_r
        have hge_j_i : stageDelayAt specs j sy ≥ stageDelayAt specs i sx := by
          rw [hdelay_ik.symm] at hge_jk
          exact hge_jk
        exact le_antisymm hge_j_i hge_ij
      exact ⟨htick_r, hpri_r, hij_r, hjk_r, hdel_r⟩

/-- Delay monotonicity for arbitrary stages (stage 0 or a middle stage):
    among equal-priority events in a common firing tick, an earlier pop has
    delay at least as large. Subsumes the `mid0` / `0mid` / `sep` / observer
    wrappers by splitting on whether each stage is stage 0. -/
theorem stage_delay_ge_of_before_any
    (T : Nat) (specs : List ChainSpec) (actOrd : List Nat) (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (h_fit : ∀ i < specs.length, chainDelay (specAt specs i) ≤ T)
    (x y sx sy : Nat) (hx : x < specs.length) (hy : y < specs.length)
    (hsx_le : sx ≤ repLenAt specs x) (hsy_le : sy ≤ repLenAt specs y)
    (htick : stageTickOf T specs x sx = stageTickOf T specs y sy)
    (hpri : stagePriAt specs x sx = stagePriAt specs y sy)
    (hx_mem : stageEventOf T specs x sx ∈
        popSeq (simWorld T specs actOrd pos (stageTickOf T specs x sx)))
    (hy_mem : stageEventOf T specs y sy ∈
        popSeq (simWorld T specs actOrd pos (stageTickOf T specs x sx)))
    (hb : (_root_.findIdx? (fun e => decide (e = stageEventOf T specs x sx))
            (popSeq (simWorld T specs actOrd pos (stageTickOf T specs x sx)))).getD 0 <
          (_root_.findIdx? (fun e => decide (e = stageEventOf T specs y sy))
            (popSeq (simWorld T specs actOrd pos (stageTickOf T specs x sx)))).getD 0) :
    stageDelayAt specs x sx ≥ stageDelayAt specs y sy := by
  have hdx_pos : 1 ≤ (stageDelayAt specs x sx : Nat) := by
    have h := PNat.pos (stageDelayAt specs x sx)
    omega
  by_cases hsx0 : sx = 0
  · subst sx
    have hspawn_x : stageEventOf T specs x 0 ∈ spawnFold (cascadeSpawn T specs)
        (popSeq (simWorld T specs actOrd pos (obsTickOf T specs x))) :=
      stageRep_mem_spawn_zero T specs actOrd pos h_valid h_perm x hx
    have hsucc_x : stageTickOf T specs x 0 =
        obsTickOf T specs x + (stageDelayAt specs x 0 : Nat) := by
      dsimp [obsTickOf]
      rw [stageTickOf_zero T specs x]
    by_cases hsy0 : sy = 0
    · subst sy
      have hspawn_y : stageEventOf T specs y 0 ∈ spawnFold (cascadeSpawn T specs)
          (popSeq (simWorld T specs actOrd pos (obsTickOf T specs y))) :=
        stageRep_mem_spawn_zero T specs actOrd pos h_valid h_perm y hy
      have hsucc_y : stageTickOf T specs x 0 =
          obsTickOf T specs y + (stageDelayAt specs y 0 : Nat) := by
        dsimp [obsTickOf]
        simpa [htick] using (stageTickOf_zero T specs y)
      exact rep_delay_ge_of_before T specs actOrd pos h_valid h_perm
        (stageEventOf T specs x 0) (stageEventOf T specs y 0)
        (obsTickOf T specs x) (obsTickOf T specs y)
        (stageDelayAt specs x 0 : Nat) (stageDelayAt specs y 0 : Nat)
        (stageTickOf T specs x 0)
        (by dsimp [stageEventOf]) (by dsimp [stageEventOf]; exact htick.symm)
        hsucc_x hsucc_y hdx_pos hspawn_x hspawn_y
        (by dsimp [stageEventOf]; exact hpri) hx_mem hy_mem hb
    · have hsy_pos : 0 < sy := by omega
      have hsy_pred : sy - 1 < repLenAt specs y := by omega
      have hspawn_y : stageEventOf T specs y sy ∈ spawnFold (cascadeSpawn T specs)
          (popSeq (simWorld T specs actOrd pos (stageTickOf T specs y (sy - 1)))) := by
        have hsp := stageRep_mem_spawn T specs actOrd pos h_valid h_perm y hy (h_fit y hy) (sy - 1) hsy_pred
        have hpred : sy - 1 + 1 = sy := by omega
        simpa [hpred] using hsp
      have hsucc_y : stageTickOf T specs x 0 =
          stageTickOf T specs y (sy - 1) + (stageDelayAt specs y sy : Nat) := by
        have hle : (sy - 1) + 1 ≤ (specAt specs y).middleDelays.length := by
          dsimp [repLenAt] at hsy_le
          omega
        have hsucc := stageTickOf_succ T specs y (sy - 1) hle
        have hpred : sy - 1 + 1 = sy := by omega
        simpa [hpred, htick] using hsucc
      exact rep_delay_ge_of_before T specs actOrd pos h_valid h_perm
        (stageEventOf T specs x 0) (stageEventOf T specs y sy)
        (obsTickOf T specs x) (stageTickOf T specs y (sy - 1))
        (stageDelayAt specs x 0 : Nat) (stageDelayAt specs y sy : Nat)
        (stageTickOf T specs x 0)
        (by dsimp [stageEventOf]) (by dsimp [stageEventOf]; exact htick.symm)
        hsucc_x hsucc_y hdx_pos hspawn_x hspawn_y
        (by dsimp [stageEventOf]; exact hpri) hx_mem hy_mem hb
  · have hsx_pos : 0 < sx := by omega
    have hsx_pred : sx - 1 < repLenAt specs x := by omega
    have hspawn_x : stageEventOf T specs x sx ∈ spawnFold (cascadeSpawn T specs)
        (popSeq (simWorld T specs actOrd pos (stageTickOf T specs x (sx - 1)))) := by
      have hsp := stageRep_mem_spawn T specs actOrd pos h_valid h_perm x hx (h_fit x hx) (sx - 1) hsx_pred
      have hpred : sx - 1 + 1 = sx := by omega
      simpa [hpred] using hsp
    have hsucc_x : stageTickOf T specs x sx =
        stageTickOf T specs x (sx - 1) + (stageDelayAt specs x sx : Nat) := by
      have hle : (sx - 1) + 1 ≤ (specAt specs x).middleDelays.length := by
        dsimp [repLenAt] at hsx_le
        omega
      have hsucc := stageTickOf_succ T specs x (sx - 1) hle
      have hpred : sx - 1 + 1 = sx := by omega
      simpa [hpred] using hsucc
    by_cases hsy0 : sy = 0
    · subst sy
      have hspawn_y : stageEventOf T specs y 0 ∈ spawnFold (cascadeSpawn T specs)
          (popSeq (simWorld T specs actOrd pos (obsTickOf T specs y))) :=
        stageRep_mem_spawn_zero T specs actOrd pos h_valid h_perm y hy
      have hsucc_y : stageTickOf T specs x sx =
          obsTickOf T specs y + (stageDelayAt specs y 0 : Nat) := by
        dsimp [obsTickOf]
        simpa [htick] using (stageTickOf_zero T specs y)
      exact rep_delay_ge_of_before T specs actOrd pos h_valid h_perm
        (stageEventOf T specs x sx) (stageEventOf T specs y 0)
        (stageTickOf T specs x (sx - 1)) (obsTickOf T specs y)
        (stageDelayAt specs x sx : Nat) (stageDelayAt specs y 0 : Nat)
        (stageTickOf T specs x sx)
        (by dsimp [stageEventOf]) (by dsimp [stageEventOf]; exact htick.symm)
        hsucc_x hsucc_y hdx_pos hspawn_x hspawn_y
        (by dsimp [stageEventOf]; exact hpri) hx_mem hy_mem hb
    · have hsy_pos : 0 < sy := by omega
      have hsy_pred : sy - 1 < repLenAt specs y := by omega
      have hspawn_y : stageEventOf T specs y sy ∈ spawnFold (cascadeSpawn T specs)
          (popSeq (simWorld T specs actOrd pos (stageTickOf T specs y (sy - 1)))) := by
        have hsp := stageRep_mem_spawn T specs actOrd pos h_valid h_perm y hy (h_fit y hy) (sy - 1) hsy_pred
        have hpred : sy - 1 + 1 = sy := by omega
        simpa [hpred] using hsp
      have hsucc_y : stageTickOf T specs x sx =
          stageTickOf T specs y (sy - 1) + (stageDelayAt specs y sy : Nat) := by
        have hle : (sy - 1) + 1 ≤ (specAt specs y).middleDelays.length := by
          dsimp [repLenAt] at hsy_le
          omega
        have hsucc := stageTickOf_succ T specs y (sy - 1) hle
        have hpred : sy - 1 + 1 = sy := by omega
        simpa [hpred, htick] using hsucc
      exact rep_delay_ge_of_before T specs actOrd pos h_valid h_perm
        (stageEventOf T specs x sx) (stageEventOf T specs y sy)
        (stageTickOf T specs x (sx - 1)) (stageTickOf T specs y (sy - 1))
        (stageDelayAt specs x sx : Nat) (stageDelayAt specs y sy : Nat)
        (stageTickOf T specs x sx)
        (by dsimp [stageEventOf]) (by dsimp [stageEventOf]; exact htick.symm)
        hsucc_x hsucc_y hdx_pos hspawn_x hspawn_y
        (by dsimp [stageEventOf]; exact hpri) hx_mem hy_mem hb

/-- The suffix sandwich descent: under the sandwich hypotheses, chain `j`
    has at least `n` repeaters and agrees with chain `i` on the delay and
    priority of every repeater `r < n` steps from the end. -/
theorem suffix_sandwich_descent
    (n : Nat) (T : Nat) (specs : List ChainSpec) (actOrd : List Nat)
    (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (h_fit : ∀ i < specs.length, chainDelay (specAt specs i) ≤ T)
    (i j k : Nat) (hi : i < specs.length) (hj : j < specs.length) (hk : k < specs.length)
    (s : List (PNat × Int))
    (hi_spec : (specAt specs i).suffixSpec n = some s)
    (hk_spec : (specAt specs k).suffixSpec n = some s)
    (hij : (_root_.findIdx? (fun e => decide (e = stageEventOf T specs i (repLenAt specs i)))
            (popSeq (simWorld T specs actOrd pos T))).getD 0 <
          (_root_.findIdx? (fun e => decide (e = stageEventOf T specs j (repLenAt specs j)))
            (popSeq (simWorld T specs actOrd pos T))).getD 0)
    (hjk : (_root_.findIdx? (fun e => decide (e = stageEventOf T specs j (repLenAt specs j)))
            (popSeq (simWorld T specs actOrd pos T))).getD 0 <
          (_root_.findIdx? (fun e => decide (e = stageEventOf T specs k (repLenAt specs k)))
            (popSeq (simWorld T specs actOrd pos T))).getD 0)
    (hlastPri : (specAt specs j).lastPriority = (specAt specs i).lastPriority)
    (hlastDelay : (specAt specs j).lastDelay = (specAt specs i).lastDelay) :
    n ≤ repLenAt specs j + 1 ∧
    (∀ r < n, stageDelayAt specs j (repLenAt specs j - r) =
        stageDelayAt specs i (repLenAt specs i - r) ∧
      stagePriAt specs j (repLenAt specs j - r) =
        stagePriAt specs i (repLenAt specs i - r)) := by
  have hpri_i : (specAt specs i).priLenOk := (h_valid i hi).1
  have hpri_j : (specAt specs j).priLenOk := (h_valid j hj).1
  have hpri_k : (specAt specs k).priLenOk := (h_valid k hk).1
  have hi_ge : n ≤ repLenAt specs i + 1 := suffixSpec_repLen_ge specs i n s hpri_i hi_spec
  have hk_ge : n ≤ repLenAt specs k + 1 := suffixSpec_repLen_ge specs k n s hpri_k hk_spec
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
  -- short-chain: chain j has at least n repeaters
  have hj_ge : n ≤ repLenAt specs j + 1 := by
    by_contra hnot
    have hj_short : repLenAt specs j + 1 < n := Nat.lt_of_not_ge hnot
    have hrj_lt : repLenAt specs j < n := by omega
    obtain ⟨htick, hpri, hij_s, hjk_s, hdel⟩ :=
      suffix_descent_trace n T specs actOrd pos h_valid h_perm h_fit i j k hi hj hk
        s hi_spec hk_spec hij hjk hlastPri hlastDelay (repLenAt specs j) hrj_lt (le_refl _)
    have hz_j : repLenAt specs j - repLenAt specs j = 0 := by omega
    have htick_ij : stageTickOf T specs i (repLenAt specs i - repLenAt specs j) =
        stageTickOf T specs j 0 := by
      simpa [hz_j] using htick
    have hpri_ij : stagePriAt specs i (repLenAt specs i - repLenAt specs j) =
        stagePriAt specs j 0 := by
      simpa [hz_j] using hpri
    have htick_ik : stageTickOf T specs i (repLenAt specs i - repLenAt specs j) =
        stageTickOf T specs k (repLenAt specs k - repLenAt specs j) :=
      suffixStageTick_eq T specs i k n (repLenAt specs j) s hpri_i hpri_k
        (h_fit i hi) (h_fit k hk) hi_spec hk_spec hrj_lt
    have htick_jk : stageTickOf T specs j 0 =
        stageTickOf T specs k (repLenAt specs k - repLenAt specs j) :=
      htick_ij.symm.trans htick_ik
    have hpri_ik : stagePriAt specs i (repLenAt specs i - repLenAt specs j) =
        stagePriAt specs k (repLenAt specs k - repLenAt specs j) :=
      (suffixStage_eq specs i k n (repLenAt specs j) s hpri_i hpri_k hi_spec hk_spec hrj_lt).2
    have hpri_jk : stagePriAt specs j 0 =
        stagePriAt specs k (repLenAt specs k - repLenAt specs j) :=
      hpri_ij.symm.trans hpri_ik
    have hmem_i : stageEventOf T specs i (repLenAt specs i - repLenAt specs j) ∈
        popSeq (simWorld T specs actOrd pos
          (stageTickOf T specs i (repLenAt specs i - repLenAt specs j))) :=
      hmem_stage i hi (repLenAt specs i - repLenAt specs j) (by omega)
    have hmem_j : stageEventOf T specs j 0 ∈
        popSeq (simWorld T specs actOrd pos
          (stageTickOf T specs i (repLenAt specs i - repLenAt specs j))) := by
      simpa [htick_ij.symm] using (hmem_stage j hj 0 (by simp [repLenAt]))
    have hmem_k : stageEventOf T specs k (repLenAt specs k - repLenAt specs j) ∈
        popSeq (simWorld T specs actOrd pos
          (stageTickOf T specs i (repLenAt specs i - repLenAt specs j))) := by
      simpa [htick_ik.symm] using (hmem_stage k hk (repLenAt specs k - repLenAt specs j) (by omega))
    have hb_ij : (_root_.findIdx?
          (fun e => decide (e = stageEventOf T specs i (repLenAt specs i - repLenAt specs j)))
          (popSeq (simWorld T specs actOrd pos
            (stageTickOf T specs i (repLenAt specs i - repLenAt specs j))))).getD 0 <
        (_root_.findIdx?
          (fun e => decide (e = stageEventOf T specs j 0))
          (popSeq (simWorld T specs actOrd pos
            (stageTickOf T specs i (repLenAt specs i - repLenAt specs j))))).getD 0 := by
      dsimp [eventIdx, evI, evJ, wI] at hij_s
      rw [hz_j] at hij_s
      exact hij_s
    have hb_jk : (_root_.findIdx?
          (fun e => decide (e = stageEventOf T specs j 0))
          (popSeq (simWorld T specs actOrd pos
            (stageTickOf T specs i (repLenAt specs i - repLenAt specs j))))).getD 0 <
        (_root_.findIdx?
          (fun e => decide (e = stageEventOf T specs k (repLenAt specs k - repLenAt specs j)))
          (popSeq (simWorld T specs actOrd pos
            (stageTickOf T specs i (repLenAt specs i - repLenAt specs j))))).getD 0 := by
      dsimp [eventIdx, evJ, wI] at hjk_s
      rw [hz_j] at hjk_s
      exact hjk_s
    have hb_jk_at_j : (_root_.findIdx? (fun e => decide (e = stageEventOf T specs j 0))
          (popSeq (simWorld T specs actOrd pos (stageTickOf T specs j 0)))).getD 0 <
        (_root_.findIdx?
          (fun e => decide (e = stageEventOf T specs k (repLenAt specs k - repLenAt specs j)))
          (popSeq (simWorld T specs actOrd pos (stageTickOf T specs j 0)))).getD 0 := by
      simpa [htick_ij] using hb_jk
    have hge_ij : stageDelayAt specs i (repLenAt specs i - repLenAt specs j) ≥
        stageDelayAt specs j 0 :=
      stage_delay_ge_of_before_any T specs actOrd pos h_valid h_perm h_fit
        i j (repLenAt specs i - repLenAt specs j) 0 hi hj (by omega) (by simp [repLenAt])
        htick_ij hpri_ij hmem_i hmem_j hb_ij
    have hmem_j0 : stageEventOf T specs j 0 ∈
        popSeq (simWorld T specs actOrd pos (stageTickOf T specs j 0)) :=
      hmem_stage j hj 0 (by simp [repLenAt])
    have hmem_k_j : stageEventOf T specs k (repLenAt specs k - repLenAt specs j) ∈
        popSeq (simWorld T specs actOrd pos (stageTickOf T specs j 0)) := by
      simpa [htick_jk.symm] using (hmem_stage k hk (repLenAt specs k - repLenAt specs j) (by omega))
    have hge_jk : stageDelayAt specs j 0 ≥
        stageDelayAt specs k (repLenAt specs k - repLenAt specs j) :=
      stage_delay_ge_of_before_any T specs actOrd pos h_valid h_perm h_fit
        j k 0 (repLenAt specs k - repLenAt specs j) hj hk (by simp [repLenAt]) (by omega)
        htick_jk hpri_jk hmem_j0 hmem_k_j hb_jk_at_j
    have hdelay_ki : stageDelayAt specs k (repLenAt specs k - repLenAt specs j) =
        stageDelayAt specs i (repLenAt specs i - repLenAt specs j) :=
      ((suffixStage_eq specs i k n (repLenAt specs j) s hpri_i hpri_k hi_spec hk_spec hrj_lt).1).symm
    have hdelay_jk : stageDelayAt specs j 0 =
        stageDelayAt specs k (repLenAt specs k - repLenAt specs j) := by
      have hge_j_i : stageDelayAt specs j 0 ≥
          stageDelayAt specs i (repLenAt specs i - repLenAt specs j) := by
        rw [hdelay_ki] at hge_jk
        exact hge_jk
      have hdelay_ij : stageDelayAt specs i (repLenAt specs i - repLenAt specs j) =
          stageDelayAt specs j 0 := le_antisymm hge_j_i hge_ij
      exact hdelay_ij.symm.trans hdelay_ki.symm
    have hsk_pos : 0 < repLenAt specs k - repLenAt specs j := by omega
    have hsk_le : repLenAt specs k - repLenAt specs j ≤ repLenAt specs k := by omega
    exact obs_middle_contradiction T specs actOrd pos h_valid h_perm h_fit
      j k (repLenAt specs k - repLenAt specs j) hj hk hsk_le hsk_pos
      htick_jk hdelay_jk hpri_jk hb_jk_at_j
  -- stage-by-stage equality
  have hstage : ∀ r < n,
      stageDelayAt specs j (repLenAt specs j - r) =
        stageDelayAt specs i (repLenAt specs i - r) ∧
      stagePriAt specs j (repLenAt specs j - r) =
        stagePriAt specs i (repLenAt specs i - r) := by
    intro r hr
    have hrj : r ≤ repLenAt specs j := by omega
    obtain ⟨htick, hpri, hij_r, hjk_r, hdel⟩ :=
      suffix_descent_trace n T specs actOrd pos h_valid h_perm h_fit i j k hi hj hk
        s hi_spec hk_spec hij hjk hlastPri hlastDelay r hr hrj
    have hpri' : stagePriAt specs j (repLenAt specs j - r) =
        stagePriAt specs i (repLenAt specs i - r) := hpri.symm
    have hdel' : stageDelayAt specs j (repLenAt specs j - r) =
        stageDelayAt specs i (repLenAt specs i - r) := by
      have hmem_i : stageEventOf T specs i (repLenAt specs i - r) ∈
          popSeq (simWorld T specs actOrd pos (stageTickOf T specs i (repLenAt specs i - r))) :=
        hmem_stage i hi (repLenAt specs i - r) (by omega)
      have hmem_j : stageEventOf T specs j (repLenAt specs j - r) ∈
          popSeq (simWorld T specs actOrd pos (stageTickOf T specs i (repLenAt specs i - r))) := by
        simpa [htick.symm] using (hmem_stage j hj (repLenAt specs j - r) (by omega))
      have htick_ik : stageTickOf T specs i (repLenAt specs i - r) =
          stageTickOf T specs k (repLenAt specs k - r) :=
        suffixStageTick_eq T specs i k n r s hpri_i hpri_k (h_fit i hi) (h_fit k hk)
          hi_spec hk_spec hr
      have hmem_k : stageEventOf T specs k (repLenAt specs k - r) ∈
          popSeq (simWorld T specs actOrd pos (stageTickOf T specs i (repLenAt specs i - r))) := by
        simpa [htick_ik.symm] using (hmem_stage k hk (repLenAt specs k - r) (by omega))
      have hb_ij : (_root_.findIdx?
            (fun e => decide (e = stageEventOf T specs i (repLenAt specs i - r)))
            (popSeq (simWorld T specs actOrd pos (stageTickOf T specs i (repLenAt specs i - r))))).getD 0 <
          (_root_.findIdx?
            (fun e => decide (e = stageEventOf T specs j (repLenAt specs j - r)))
            (popSeq (simWorld T specs actOrd pos (stageTickOf T specs i (repLenAt specs i - r))))).getD 0 := by
        dsimp [eventIdx, evI, evJ, wI] at hij_r
        exact hij_r
      have hb_jk : (_root_.findIdx?
            (fun e => decide (e = stageEventOf T specs j (repLenAt specs j - r)))
            (popSeq (simWorld T specs actOrd pos (stageTickOf T specs i (repLenAt specs i - r))))).getD 0 <
          (_root_.findIdx?
            (fun e => decide (e = stageEventOf T specs k (repLenAt specs k - r)))
            (popSeq (simWorld T specs actOrd pos (stageTickOf T specs i (repLenAt specs i - r))))).getD 0 := by
        dsimp [eventIdx, evJ, wI] at hjk_r
        exact hjk_r
      have hge_ij : stageDelayAt specs i (repLenAt specs i - r) ≥
          stageDelayAt specs j (repLenAt specs j - r) :=
        stage_delay_ge_of_before_any T specs actOrd pos h_valid h_perm h_fit
          i j (repLenAt specs i - r) (repLenAt specs j - r) hi hj (by omega) (by omega)
          htick hpri hmem_i hmem_j hb_ij
      have htick_jk : stageTickOf T specs j (repLenAt specs j - r) =
          stageTickOf T specs k (repLenAt specs k - r) := htick.symm.trans htick_ik
      have hpri_jk : stagePriAt specs j (repLenAt specs j - r) =
          stagePriAt specs k (repLenAt specs k - r) :=
        hpri.symm.trans ((suffixStage_eq specs i k n r s hpri_i hpri_k hi_spec hk_spec hr).2)
      have hmem_j_at_j : stageEventOf T specs j (repLenAt specs j - r) ∈
          popSeq (simWorld T specs actOrd pos (stageTickOf T specs j (repLenAt specs j - r))) :=
        hmem_stage j hj (repLenAt specs j - r) (by omega)
      have hmem_k_at_j : stageEventOf T specs k (repLenAt specs k - r) ∈
          popSeq (simWorld T specs actOrd pos (stageTickOf T specs j (repLenAt specs j - r))) := by
        simpa [htick_jk.symm] using (hmem_stage k hk (repLenAt specs k - r) (by omega))
      have hb_jk_at_j : (_root_.findIdx?
            (fun e => decide (e = stageEventOf T specs j (repLenAt specs j - r)))
            (popSeq (simWorld T specs actOrd pos (stageTickOf T specs j (repLenAt specs j - r))))).getD 0 <
          (_root_.findIdx?
            (fun e => decide (e = stageEventOf T specs k (repLenAt specs k - r)))
            (popSeq (simWorld T specs actOrd pos (stageTickOf T specs j (repLenAt specs j - r))))).getD 0 := by
        simpa [htick] using hb_jk
      have hge_jk : stageDelayAt specs j (repLenAt specs j - r) ≥
          stageDelayAt specs k (repLenAt specs k - r) :=
        stage_delay_ge_of_before_any T specs actOrd pos h_valid h_perm h_fit
          j k (repLenAt specs j - r) (repLenAt specs k - r) hj hk (by omega) (by omega)
          htick_jk hpri_jk hmem_j_at_j hmem_k_at_j hb_jk_at_j
      have hdelay_ki : stageDelayAt specs k (repLenAt specs k - r) =
          stageDelayAt specs i (repLenAt specs i - r) :=
        ((suffixStage_eq specs i k n r s hpri_i hpri_k hi_spec hk_spec hr).1).symm
      have hge_j_i : stageDelayAt specs j (repLenAt specs j - r) ≥
          stageDelayAt specs i (repLenAt specs i - r) := by
        rw [hdelay_ki] at hge_jk
        exact hge_jk
      exact le_antisymm hge_ij hge_j_i
    exact ⟨hdel', hpri'⟩
  exact ⟨hj_ge, hstage⟩
