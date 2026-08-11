import BasicProofs.GroupClustering.SurvivalFreeStageInduction
import BasicProofs.GroupClustering.SuccessorMembershipRange
import BasicProofs.GroupClustering.QSideOrderNoSurvival
import BasicProofs.GroupClustering.StageInductionSideFacts
import BasicProofs.GroupClustering.StageEventNodup

open BasicRedstoneSim List

/-- `zipIdx` followed by the first projection is the identity
    (reproven; private in NodupChain). -/
private theorem map_fst_zipIdx' {α : Type} (l : List α) :
    (l.zipIdx.map Prod.fst : List α) = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.zipIdx]

/-! # Group clustering — discharging the survival-free side hypotheses

For two same-spec chains activated at the same tick, every side
hypothesis of the survival-free stage step (`MBStepSideGeneral`,
SurvivalFreeStageInduction) follows from the simulation setup:

* bounds, targets: spec equality (`sameSpec_stageTarget`, SameSpecLockstep);
* memberships: completeness (`stageEvent_mem_gSimWorld`, StageEventCompleteness) and
  the successor range (`stageEvent_succ_mem_range_complete`, SuccessorMembershipRange);
* Nodup facts: `gSimWorld_events_Nodup` (NodupChain) and the
  `TickQueueOk` preservation of the burst (`gSimBurst_tickQueueOk`,
  NodupChain);
* reference order: the QSideOrderNoSurvival stage induction on the stage-0 base
  order supplied by the assembly (`h_base₀`);
* StageMemAt / NodeLayoutOk: StageInductionSideFacts and the foldl preservation;
* successor absence: StageEventNodup.

The reference order is oriented by the stage-0 base order `h_base₀`:
the assembly supplies the orientation that actually holds (the
Stage0BaseOrder cross-group base or the same-group withinOrd base).
-/

/-- `NodeLayoutOk` holds at every tick-start world. -/
private theorem NodeLayoutOk_gSimWorld (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (t : Nat) :
    NodeLayoutOk groups
      (gSimWorld groups actTick groupOrd withinOrd pos t) := by
  dsimp [gSimWorld]
  exact NodeLayoutOk_gSimFoldl groups actTick (buildGroups groups).2 groupOrd
    withinOrd pos (buildGroups groups).1 t (NodeLayoutOk_buildGroups groups)

/-- All side hypotheses of one survival-free stage step, discharged for
    same-spec chains with equal activation tick. The index `j` ranges
    over the middle stages below the last (`j < middleDelays.length`);
    `h_base₀` is the stage-0 order of the reference pair at the
    stage-0 pop queue and orients the pair. -/
theorem MBStepSideGeneral_discharge (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat)
    (h_valid : ∀ gi (c : ChainSpec), gi < groups.length →
        c ∈ groupAt groups gi →
        (∀ d ∈ c.middleDelays, ValidDelay d) ∧ ValidDelay c.lastDelay)
    (h_ord : List.Perm groupOrd (List.range groups.length))
    (h_within : ∀ gi, gi < groups.length →
        List.Perm (withinOrd gi) (List.range (groupAt groups gi).length))
    (g₁ c₁ g₂ c₂ : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_spec : chainAt groups g₁ c₁ = chainAt groups g₂ c₂)
    (h_act_eq : actTick g₁ = actTick g₂)
    (h_gord_nd : groupOrd.Nodup)
    (h_within_nd : ∀ gi, gi < groups.length → (withinOrd gi).Nodup)
    (h_base₀ : evBefore
        ((popQueueWorld groups actTick groupOrd withinOrd pos
          g₁ c₁ 0).events)
        (stageEvent actTick groups g₁ c₁ 0)
        (stageEvent actTick groups g₂ c₂ 0))
    (j : Nat) (h_j_ge : 1 ≤ j)
    (h_j_lt : j < (chainAt groups g₁ c₁).middleDelays.length) :
    MBStepSideGeneral groups actTick groupOrd withinOrd pos g₁ c₁ g₂ c₂ j := by
  have h_mlen₂ : j < (chainAt groups g₂ c₂).middleDelays.length := by
    rw [← h_spec]; exact h_j_lt
  exact {
    j_ge := h_j_ge
    j₁ := by omega
    j₂ := by omega
    tgt₂ := (sameSpec_stageTarget groups actTick g₁ c₁ g₂ c₂ j
      h_act_eq h_spec).symm
    tgt₂_next := (sameSpec_stageTarget groups actTick g₁ c₁ g₂ c₂ (j + 1)
      h_act_eq h_spec).symm
    A_mem_j :=
      stageEvent_mem_gSimWorld groups actTick groupOrd withinOrd pos
        h_valid h_ord h_within g₁ c₁ h_g₁ h_c₁ j (by omega)
    D_mem_j := by
      rw [sameSpec_stageTarget groups actTick g₁ c₁ g₂ c₂ j h_act_eq h_spec]
      exact stageEvent_mem_gSimWorld groups actTick groupOrd withinOrd pos
        h_valid h_ord h_within g₂ c₂ h_g₂ h_c₂ j (by omega)
    nodup_due := by
      exact List.Nodup.filter _
        (gSimWorld_events_Nodup groups actTick groupOrd withinOrd pos
          (stageTarget actTick groups g₁ c₁ j) h_gord_nd h_within_nd)
    AD := by
      have h_ind : evBefore
          ((popQueueWorld groups actTick groupOrd withinOrd pos g₁ c₁ j).events)
          (stageEvent actTick groups g₁ c₁ j)
          (stageEvent actTick groups g₂ c₂ j) :=
        sameSpec_stage_evBefore_ind_self groups actTick groupOrd withinOrd pos
          g₁ c₁ g₂ c₂ j h_g₁ h_c₁ h_g₂ h_c₂ h_spec h_act_eq (by omega)
          h_base₀
          (fun k _ => by
            dsimp [popQueueWorld]
            exact NodeLayoutOk_gSimWorld groups actTick groupOrd withinOrd pos
              (stageTarget actTick groups g₁ c₁ k))
          (fun k hk =>
            sameSpec_h_nodup_discharge groups actTick groupOrd withinOrd pos
              g₁ c₁ h_gord_nd h_within_nd k (by omega))
      dsimp [popQueueWorld] at h_ind
      apply evBefore.filter
        (fun e => e.targetTick == stageTarget actTick groups g₁ c₁ j)
      · show ((stageEvent actTick groups g₁ c₁ j).targetTick ==
          stageTarget actTick groups g₁ c₁ j) = true
        dsimp [stageEvent]
        simp
      · show ((stageEvent actTick groups g₂ c₂ j).targetTick ==
          stageTarget actTick groups g₁ c₁ j) = true
        dsimp [stageEvent]
        rw [← sameSpec_stageTarget groups actTick g₁ c₁ g₂ c₂ j h_act_eq
          h_spec]
        simp
      · exact h_ind
    stage_mem :=
      StageMemAt_gSimWorld groups actTick groupOrd withinOrd pos
        (stageTarget actTick groups g₁ c₁ j)
    layout :=
      NodeLayoutOk_gSimWorld groups actTick groupOrd withinOrd pos
        (stageTarget actTick groups g₁ c₁ j)
    sA_absent :=
      stageEvent_succ_not_mem_gSimWorld groups actTick groupOrd withinOrd pos
        g₁ c₁ j (stageTarget actTick groups g₁ c₁ j) h_g₁ h_c₁ (by omega) rfl
    sD_absent :=
      stageEvent_succ_not_mem_gSimWorld groups actTick groupOrd withinOrd pos
        g₂ c₂ j (stageTarget actTick groups g₁ c₁ j) h_g₂ h_c₂ (by omega)
        ((sameSpec_stageTarget groups actTick g₁ c₁ g₂ c₂ j h_act_eq
          h_spec).symm)
    nd_post_j :=
      gSimWorld_events_Nodup groups actTick groupOrd withinOrd pos
        (stageTarget actTick groups g₁ c₁ j + 1) h_gord_nd h_within_nd
    nd_burst := by
      set wQ := gSimWorld groups actTick groupOrd withinOrd pos
        (stageTarget actTick groups g₁ c₁ j)
      set wQ_log := wQ.logOutput s!"tick {wQ.tick}"
      set activeQ := groupOrd.filter (fun gi =>
        decide (gi < (buildGroups groups).2.length) &&
        (actTick gi == wQ.tick))
      have h_tick_w : wQ.tick = stageTarget actTick groups g₁ c₁ j :=
        gSimWorld_tick groups actTick groupOrd withinOrd pos
          (stageTarget actTick groups g₁ c₁ j)
      have h_ev_log : wQ_log.events = wQ.events := by dsimp [wQ_log]
      have h_tick_log : wQ_log.tick = wQ.tick := by dsimp [wQ_log]
      have h_ok_log : TickQueueOk groups actTick wQ_log [] := by
        dsimp [TickQueueOk, NoSpawnDue]
        rw [h_ev_log, h_tick_log]
        refine ⟨?_, ?_, ?_⟩
        · exact gSimWorld_events_Nodup groups actTick groupOrd withinOrd pos
            (stageTarget actTick groups g₁ c₁ j) h_gord_nd h_within_nd
        · intro ev h_ev
          obtain ⟨gi, ci, k, h_gi, h_ci, h_k, h_ev_eq, h_win⟩ :=
            gSimWorld_events_stageWindow groups actTick groupOrd withinOrd pos
              (stageTarget actTick groups g₁ c₁ j) ev h_ev
          refine ⟨gi, ci, k, h_gi, h_ci, h_k, h_ev_eq,
            Or.inl (by rw [h_tick_w]; exact h_win)⟩
        · intro gi ci k h_gi h_ci h_km h_tgt _
          exact stageEvent_succ_not_mem_gSimWorld groups actTick groupOrd
            withinOrd pos gi ci k (stageTarget actTick groups g₁ c₁ j)
            h_gi h_ci h_km (h_tgt.trans h_tick_w)
      have h_nd_gis : ([] ++ activeQ.zipIdx.map Prod.fst).Nodup := by
        rw [List.nil_append, map_fst_zipIdx']
        exact List.Nodup.filter (fun gi =>
          decide (gi < (buildGroups groups).2.length) &&
          (actTick gi == wQ.tick)) h_gord_nd
      have h_active_char : ∀ gi k, (gi, k) ∈ activeQ.zipIdx →
          gi < groups.length ∧ actTick gi = wQ.tick := by
        intro gi k h_mem
        have h_zip := List.mem_zipIdx h_mem
        obtain ⟨_, h_k_lt, h_gi_eq⟩ := h_zip
        have h_k_lt' : k < activeQ.length := by simpa using h_k_lt
        have h_gi_mem : gi ∈ activeQ := by
          have h_gi_eq' : gi = activeQ[k] := by simpa using h_gi_eq
          rw [h_gi_eq']
          exact List.getElem_mem h_k_lt'
        dsimp [activeQ] at h_gi_mem
        rw [List.mem_filter] at h_gi_mem
        obtain ⟨_, h_cond⟩ := h_gi_mem
        rw [Bool.and_eq_true] at h_cond
        obtain ⟨h_dec, h_beq⟩ := h_cond
        have h_gi_lt : gi < (buildGroups groups).2.length :=
          of_decide_eq_true h_dec
        have h_act_eq' : actTick gi = wQ.tick := by
          simpa [Nat.beq_eq] using h_beq
        exact ⟨by rwa [buildGroups_snd_length] at h_gi_lt, h_act_eq'⟩
      obtain ⟨h_ok_B, _⟩ := gSimBurst_tickQueueOk groups actTick wQ.tick
        withinOrd pos wQ_log activeQ.zipIdx [] h_tick_log
        (NodeLayoutOk_logOutput groups wQ _
          (NodeLayoutOk_gSimWorld groups actTick groupOrd withinOrd pos
            (stageTarget actTick groups g₁ c₁ j)))
        h_ok_log h_nd_gis h_active_char h_within_nd
      exact h_ok_B.1
    A_mem_carry := by
      intro k hk₁ hk₂
      exact stageEvent_succ_mem_range_complete groups actTick groupOrd
        withinOrd pos h_valid h_ord h_within g₁ c₁ j h_g₁ h_c₁ (by omega)
        k hk₁ (by omega)
    D_mem_carry := by
      intro k hk₁ hk₂
      have hk₁' : stageTarget actTick groups g₂ c₂ j + 1 ≤ k := by
        rw [← sameSpec_stageTarget groups actTick g₁ c₁ g₂ c₂ j h_act_eq
          h_spec]
        exact hk₁
      have hk₂' : k ≤ stageTarget actTick groups g₂ c₂ (j + 1) := by
        rw [← sameSpec_stageTarget groups actTick g₁ c₁ g₂ c₂ (j + 1)
          h_act_eq h_spec]
        omega
      exact stageEvent_succ_mem_range_complete groups actTick groupOrd
        withinOrd pos h_valid h_ord h_within g₂ c₂ j h_g₂ h_c₂ (by omega)
        k hk₁' hk₂'
    nd_post_carry := by
      intro k _ _
      exact gSimWorld_events_Nodup groups actTick groupOrd withinOrd pos
        (k + 1) h_gord_nd h_within_nd
  }
