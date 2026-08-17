import Proofs.Clustering.Descent


open BasicRedstoneSim
open List

/-! # The descent induction (no-group clustering)

`descent_trace`: marching a sandwiched triple down one stage at a time,
from the last repeaters to stage 0. -/

/-- The stage-by-stage descent invariant, maintained from the last repeater
    down to stage 0: common firing tick, common priority, the sandwiched pop
    order, and (for strict stages) common delay. -/
theorem descent_trace (T : Nat) (specs : List ChainSpec)
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
    ∀ r, r ≤ repLenAt specs i → r ≤ repLenAt specs j →
      stageTickOf T specs i (repLenAt specs i - r) =
        stageTickOf T specs j (repLenAt specs j - r) ∧
      stagePriAt specs i (repLenAt specs i - r) =
        stagePriAt specs j (repLenAt specs j - r) ∧
      eventIdx (wI T specs actOrd pos i r) (evI T specs i r) <
        eventIdx (wI T specs actOrd pos i r) (evJ T specs j r) ∧
      eventIdx (wI T specs actOrd pos i r) (evJ T specs j r) <
        eventIdx (wI T specs actOrd pos i r) (evK T specs k i r) ∧
      (0 < repLenAt specs i - r → 0 < repLenAt specs j - r →
        stageDelayAt specs i (repLenAt specs i - r) =
          stageDelayAt specs j (repLenAt specs j - r)) := by
  have hine : i ≠ j := by
    intro h
    subst h
    have hself : (_root_.findIdx? (fun e => decide (e = stageEventOf T specs i (repLenAt specs i)))
        (popSeq (simWorld T specs actOrd pos T))).getD 0 <
        (_root_.findIdx? (fun e => decide (e = stageEventOf T specs i (repLenAt specs i)))
          (popSeq (simWorld T specs actOrd pos T))).getD 0 := by
      simp at hij
    omega
  have hkne : j ≠ k := by
    intro h
    subst h
    have hself : (_root_.findIdx? (fun e => decide (e = stageEventOf T specs j (repLenAt specs j)))
        (popSeq (simWorld T specs actOrd pos T))).getD 0 <
        (_root_.findIdx? (fun e => decide (e = stageEventOf T specs j (repLenAt specs j)))
          (popSeq (simWorld T specs actOrd pos T))).getD 0 := by
      simp at hjk
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
  let ei : Nat → ScheduledEvent := evI T specs i
  let ej : Nat → ScheduledEvent := evJ T specs j
  let ek : Nat → ScheduledEvent := evK T specs k i
  let wi : Nat → World := wI T specs actOrd pos i
  have hdesc : ∀ r, r ≤ repLenAt specs i → r ≤ repLenAt specs j →
      stageTickOf T specs i (repLenAt specs i - r) =
        stageTickOf T specs j (repLenAt specs j - r) ∧
      stagePriAt specs i (repLenAt specs i - r) =
        stagePriAt specs j (repLenAt specs j - r) ∧
      eventIdx (wi r) (ei r) < eventIdx (wi r) (ej r) ∧
      eventIdx (wi r) (ej r) < eventIdx (wi r) (ek r) ∧
      (0 < repLenAt specs i - r → 0 < repLenAt specs j - r →
        stageDelayAt specs i (repLenAt specs i - r) =
          stageDelayAt specs j (repLenAt specs j - r)) := by
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
          rw [stagePriAt_of_eq specs i (h_valid i hi).1 hle_i,
            stagePriAt_of_eq specs j (h_valid j hj).1 hle_j]
          exact hlastPri.symm
        have hij0 : eventIdx (wi 0) (ei 0) < eventIdx (wi 0) (ej 0) := by
          dsimp [eventIdx, ei, ej, wi, evI, evJ, wI]
          rw [stageTickOf_last T specs i (h_fit i hi)]
          exact hij
        have hjk0 : eventIdx (wi 0) (ej 0) < eventIdx (wi 0) (ek 0) := by
          dsimp [eventIdx, ei, ej, ek, wi, evJ, evK, wI]
          rw [stageTickOf_last T specs i (h_fit i hi)]
          simpa [← repLenAt_spec specs i k hspec] using hjk
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
        intro hr_i hr_j
        obtain ⟨htick', hpri', hij', hjk', hdel'_cond⟩ := ih (by omega) (by omega)
        let sx := repLenAt specs i - (r' + 1)
        let sy := repLenAt specs j - (r' + 1)
        have hsx_succ : sx + 1 = repLenAt specs i - r' := by
          dsimp [sx]
          have h₁ : repLenAt specs i - (r' + 1) + (r' + 1) = repLenAt specs i :=
            Nat.sub_add_cancel hr_i
          have h₂ : repLenAt specs i - r' + r' = repLenAt specs i :=
            Nat.sub_add_cancel (by omega : r' ≤ repLenAt specs i)
          exact Nat.add_right_cancel (by
            rw [h₂]
            omega)
        have hsy_succ : sy + 1 = repLenAt specs j - r' := by
          dsimp [sy]
          have h₁ : repLenAt specs j - (r' + 1) + (r' + 1) = repLenAt specs j :=
            Nat.sub_add_cancel hr_j
          have h₂ : repLenAt specs j - r' + r' = repLenAt specs j :=
            Nat.sub_add_cancel (by omega : r' ≤ repLenAt specs j)
          exact Nat.add_right_cancel (by
            rw [h₂]
            omega)
        have hsx_lt : sx < repLenAt specs i := by
          dsimp [sx]
          exact Nat.sub_lt (by omega : 0 < repLenAt specs i) (by omega : 0 < r' + 1)
        have hsy_lt : sy < repLenAt specs j := by
          dsimp [sy]
          exact Nat.sub_lt (by omega : 0 < repLenAt specs j) (by omega : 0 < r' + 1)
        have hsxk : sx ≤ repLenAt specs k := by
          rw [← repLenAt_spec specs i k hspec]
          exact Nat.le_of_lt hsx_lt
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
          have hdel_eqN : (stageDelayAt specs i (sx + 1) : Nat) = (stageDelayAt specs j (sy + 1) : Nat) := by
            exact_mod_cast hdel_eq
          omega
        -- (b) sandwich at r'+1 (contrapositive of the parent bridge)
        have hij_r : eventIdx (wi (r' + 1)) (ei (r' + 1)) <
            eventIdx (wi (r' + 1)) (ej (r' + 1)) := by
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
              (h_valid i hi).1 (h_valid j hj).1 hnode
            exact hine hxy'.1
          have hne_idx := findIdx?_ne_of_ne (popSeq (wi (r' + 1)))
            hmem_i_sx hmem_j_sy hne_ij
          have hle := Nat.le_of_not_gt hnot
          have hrev : eventIdx (wi (r' + 1)) (ej (r' + 1)) <
              eventIdx (wi (r' + 1)) (ei (r' + 1)) :=
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
        -- similar for j < k
        have hjk_r : eventIdx (wi (r' + 1)) (ej (r' + 1)) <
            eventIdx (wi (r' + 1)) (ek (r' + 1)) := by
          by_contra hnot
          have hmem_j_sy : stageEventOf T specs j sy ∈ popSeq (wi (r' + 1)) := by
            change stageEventOf T specs j sy ∈ popSeq (simWorld T specs actOrd pos (stageTickOf T specs i sx))
            rw [htick_r]
            exact hmem_stage j hj sy (Nat.le_of_lt hsy_lt)
          have hmem_k_sx : stageEventOf T specs k sx ∈ popSeq (wi (r' + 1)) := by
            change stageEventOf T specs k sx ∈ popSeq (simWorld T specs actOrd pos (stageTickOf T specs i sx))
            simpa [stageTickOf_spec T specs k i sx hspec.symm] using (hmem_stage k hk sx hsxk)
          have hne_jk : stageEventOf T specs j sy ≠ stageEventOf T specs k sx := by
            intro h
            have hnode := congrArg ScheduledEvent.nodeId h
            dsimp [stageEventOf] at hnode
            have hxy' := chainRepId_inj specs j k sy sx hj hk
              (by dsimp [sy, repLenAt]; omega) hsxk
              (h_valid j hj).1 (h_valid k hk).1 hnode
            exact hkne hxy'.1
          have hne_idx := findIdx?_ne_of_ne (popSeq (wi (r' + 1)))
            hmem_j_sy hmem_k_sx hne_jk
          have hle := Nat.le_of_not_gt hnot
          have hrev : eventIdx (wi (r' + 1)) (ek (r' + 1)) <
              eventIdx (wi (r' + 1)) (ej (r' + 1)) :=
            Nat.lt_of_le_of_ne hle hne_idx.symm
          have hrev_r := stageRep_succ_order_ev T specs actOrd pos h_valid h_perm h_fit
            k j sx sy hk hj
            (by rw [← repLenAt_spec specs i k hspec]; exact hsx_lt)
            hsy_lt
            (by rw [stageTickOf_spec T specs k i sx hspec.symm]; exact htick_r)
            (by
              rw [stageTickOf_spec T specs k i (sx + 1) hspec.symm]
              simpa [hsx_succ, hsy_succ] using htick')
            (evK T specs k i (r' + 1)) (evJ T specs j (r' + 1)) (wi (r' + 1))
            (by dsimp [evK, sx]) (by dsimp [evJ, sy])
            (by dsimp [wi, wI, sx]; rw [stageTickOf_spec T specs k i sx hspec.symm])
            (by dsimp [evK, sx]; exact hmem_k_sx)
            (by dsimp [evJ, sy]; exact hmem_j_sy)
            hrev
          have hcontra : eventIdxEvents (wi r') (evK T specs k i r') <
              eventIdxEvents (wi r') (evJ T specs j r') := by
            dsimp [eventIdxEvents, evK, evJ, wi, wI] at hrev_r ⊢
            simpa [hsx_succ, hsy_succ, stageTickOf_spec T specs k i (repLenAt specs i - r') hspec.symm, htick'] using hrev_r
          have hjk'_ev : eventIdxEvents (wi r') (evJ T specs j r') <
              eventIdxEvents (wi r') (evK T specs k i r') := by
            have hmem_j_U : evJ T specs j r' ∈ popSeq (wi r') := by
              change stageEventOf T specs j (repLenAt specs j - r') ∈ popSeq (simWorld T specs actOrd pos (stageTickOf T specs i (repLenAt specs i - r')))
              rw [htick']
              exact hmem_stage j hj (repLenAt specs j - r') (by omega)
            have hmem_k_U : evK T specs k i r' ∈ popSeq (wi r') := by
              change stageEventOf T specs k (repLenAt specs i - r') ∈ popSeq (simWorld T specs actOrd pos (stageTickOf T specs i (repLenAt specs i - r')))
              simpa [stageTickOf_spec T specs k i (repLenAt specs i - r') hspec.symm] using (hmem_stage k hk (repLenAt specs i - r') (by rw [repLenAt_spec specs i k hspec]; omega))
            have hpri_ev : (evJ T specs j r').priority = (evK T specs k i r').priority := by
              dsimp [evJ, evK, stageEventOf]
              have hpri'_jk : stagePriAt specs j (repLenAt specs j - r') =
                  stagePriAt specs k (repLenAt specs i - r') :=
                hpri'.symm.trans (stagePriAt_spec specs i k (repLenAt specs i - r') hspec)
              exact hpri'_jk
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
        -- (c) priority equality at r'+1
        have hpri_r : stagePriAt specs i sx = stagePriAt specs j sy := by
          have hsorted := popSeq_sorted_priority (wi (r' + 1))
          have hmem_i : evI T specs i (r' + 1) ∈ popSeq (wi (r' + 1)) := by
            change stageEventOf T specs i sx ∈ popSeq (simWorld T specs actOrd pos (stageTickOf T specs i sx))
            exact hmem_stage i hi sx (Nat.le_of_lt hsx_lt)
          have hmem_j : evJ T specs j (r' + 1) ∈ popSeq (wi (r' + 1)) := by
            change stageEventOf T specs j sy ∈ popSeq (simWorld T specs actOrd pos (stageTickOf T specs i sx))
            rw [htick_r]
            exact hmem_stage j hj sy (Nat.le_of_lt hsy_lt)
          have hmem_k : evK T specs k i (r' + 1) ∈ popSeq (wi (r' + 1)) := by
            change stageEventOf T specs k sx ∈ popSeq (simWorld T specs actOrd pos (stageTickOf T specs i sx))
            simpa [stageTickOf_spec T specs k i sx hspec.symm] using (hmem_stage k hk sx hsxk)
          have hxz : (evI T specs i (r' + 1)).priority = (evK T specs k i (r' + 1)).priority := by
            dsimp [evI, evK, stageEventOf, sx]
            exact stagePriAt_spec specs i k sx hspec
          have hpri := pairwise_le_sandwich (popSeq (wi (r' + 1))) (fun e => e.priority) hsorted
            hmem_i hmem_j hmem_k hij_r hjk_r hxz
          dsimp [evI, evJ, sx, sy, stageEventOf] at hpri
          exact hpri.symm
        -- (d) delay equality at r'+1 (conditional on strict stages)
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
          have hge_jk := stageRep_delay_ge_of_before_sep_ev T specs actOrd pos h_valid h_perm h_fit
            j k sy sx hj hk hsy_lt
            (by rw [← repLenAt_spec specs i k hspec]; exact hsx_lt)
            (by dsimp [sy]; exact hposy) (by dsimp [sx]; exact hposx)
            (by rw [stageTickOf_spec T specs k i sx hspec.symm]; exact htick_r.symm)
            (evJ T specs j (r' + 1)) (evK T specs k i (r' + 1)) (wi (r' + 1))
            (by dsimp [evJ, sy]) (by dsimp [evK, sx])
            (by dsimp [wi, wI, sx]; rw [htick_r])
            (by change stageEventOf T specs j sy ∈ popSeq (simWorld T specs actOrd pos (stageTickOf T specs i sx)); rw [htick_r]; exact hmem_stage j hj sy (Nat.le_of_lt hsy_lt))
            (by change stageEventOf T specs k sx ∈ popSeq (simWorld T specs actOrd pos (stageTickOf T specs i sx)); simpa [stageTickOf_spec T specs k i sx hspec.symm] using (hmem_stage k hk sx hsxk))
            (by rw [← hpri_r]; exact stagePriAt_spec specs i k sx hspec)
            hjk_r
          have hdelay_ki : stageDelayAt specs k sx = stageDelayAt specs i sx := by
            rw [stageDelayAt_spec specs k i sx hspec.symm]
          have hge_j_i : stageDelayAt specs j sy ≥ stageDelayAt specs i sx := by
            rw [hdelay_ki] at hge_jk
            exact hge_jk
          exact le_antisymm hge_j_i hge_ij
        exact ⟨htick_r, hpri_r, hij_r, hjk_r, hdel_r⟩
  exact hdesc
