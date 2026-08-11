import BasicProofs.GroupClustering.FinalStageAssemblySetup
import BasicProofs.GroupClustering.FinalsBackwardTransportIII
import BasicProofs.GroupClustering.ConverseFinalUnconditional
import BasicProofs.GroupClustering.StageEventCompleteness
import BasicProofs.GroupClustering.QSideOrderNoSurvival
import BasicProofs.GroupClustering.StageEventNodup
import BasicProofs.GroupClustering.StageInductionSideFacts
import BasicProofs.GroupClustering.SameSpecLockstep

open BasicRedstoneSim List

/-! # Group clustering — burst phase of the final converse

Both reference stage-`m` events pop during the burst: their
stage-`(m + 1)` finals are already present in the post-burst queue.
The burst consumer `ConverseSpawnFinal_converse` (ConverseFinalUnconditional) is
discharged here at the pre-burst logged tick-start queue:

* `hAD` comes from the QSideOrderNoSurvival same-spec order induction on the
  stage-0 base order `h_base₀`, supplied by the assembly;
* memberships/absences come from StageEventCompleteness/StageEventNodup;
* the `FinalBlockBetween` block premise comes from FinalsBackwardTransportIII, fed by the
  phase hypothesis that all three finals sit in the post-burst queue.
-/

/-- `NodeLayoutOk` holds at every tick-start queue (reproven; private
    in SideHypothesisDischarge/FinalStageAssemblySetup). -/
private theorem NodeLayoutOk_gSimWorld (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (t : Nat) :
    NodeLayoutOk groups
      (gSimWorld groups actTick groupOrd withinOrd pos t) := by
  dsimp [gSimWorld]
  exact NodeLayoutOk_gSimFoldl groups actTick (buildGroups groups).2 groupOrd
    withinOrd pos (buildGroups groups).1 t (NodeLayoutOk_buildGroups groups)

/-- The burst phase of the final converse. Both reference finals and
    the middle final sit in the post-burst queue. Concludes
    `ConverseSpawnFinal` at the pre-burst tick-start queue. The
    reference order is oriented by the stage-0 base order
    `h_base₀`. -/
theorem burstPhase_ConverseSpawnFinal (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat)
    (h_valid : ∀ gi (c : ChainSpec), gi < groups.length →
        c ∈ groupAt groups gi →
        (∀ d ∈ c.middleDelays, ValidDelay d) ∧ ValidDelay c.lastDelay)
    (h_uniform : ∀ gi (c₁ c₂ : ChainSpec), gi < groups.length →
        c₁ ∈ groupAt groups gi → c₂ ∈ groupAt groups gi →
        chainDelay c₁ = chainDelay c₂)
    (T : Nat)
    (h_act : ∀ gi, gi < groups.length → groupAt groups gi ≠ [] →
        actTick gi + groupDelay (groupAt groups gi) = T)
    (h_ord : List.Perm groupOrd (List.range groups.length))
    (h_within : ∀ gi, gi < groups.length →
        List.Perm (withinOrd gi) (List.range (groupAt groups gi).length))
    (g₁ c₁ gm cm g₂ c₂ m : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_gm : gm < groups.length) (h_cm : cm < (groupAt groups gm).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_spec : chainAt groups g₁ c₁ = chainAt groups g₂ c₂)
    (h_act_eq : actTick g₁ = actTick g₂)
    (h_base₀ : evBefore
        ((popQueueWorld groups actTick groupOrd withinOrd pos
          g₁ c₁ 0).events)
        (stageEvent actTick groups g₁ c₁ 0)
        (stageEvent actTick groups g₂ c₂ 0))
    (h_m₁ : (chainAt groups g₁ c₁).middleDelays.length = m)
    (h_m₂ : (chainAt groups g₂ c₂).middleDelays.length = m)
    (h_m_ge : 1 ≤ m)
    (h_mb_full : MiddleBlockOk groups actTick T
        ((gSimWorld groups actTick groupOrd withinOrd pos
          (stageTarget actTick groups g₁ c₁ m)).events) g₁ c₁ g₂ c₂ m)
    (h_mem₁ : stageEvent actTick groups g₁ c₁ (m + 1) ∈
        (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ m).events)
    (h_mem_e : stageEvent actTick groups gm cm
        ((chainAt groups gm cm).middleDelays.length + 1) ∈
        (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ m).events)
    (h_mem₂ : stageEvent actTick groups g₂ c₂ (m + 1) ∈
        (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ m).events)
    (h_spawn_e : stageTarget actTick groups gm cm
        ((chainAt groups gm cm).middleDelays.length) =
      stageTarget actTick groups g₁ c₁ m)
    (h_ne_left : stageEvent actTick groups g₁ c₁ (m + 1) ≠
      stageEvent actTick groups gm cm
        ((chainAt groups gm cm).middleDelays.length + 1))
    (h_ne_right : stageEvent actTick groups gm cm
        ((chainAt groups gm cm).middleDelays.length + 1) ≠
      stageEvent actTick groups g₂ c₂ (m + 1))
    (h_due_left : evBefore
        ((gSimWorld groups actTick groupOrd withinOrd pos T).events.filter
          (fun ev => ev.targetTick == T))
        (stageEvent actTick groups g₁ c₁ (m + 1))
        (stageEvent actTick groups gm cm
          ((chainAt groups gm cm).middleDelays.length + 1)))
    (h_due_right : evBefore
        ((gSimWorld groups actTick groupOrd withinOrd pos T).events.filter
          (fun ev => ev.targetTick == T))
        (stageEvent actTick groups gm cm
          ((chainAt groups gm cm).middleDelays.length + 1))
        (stageEvent actTick groups g₂ c₂ (m + 1))) :
    ConverseSpawnFinal groups actTick
      ((popQueueWorld groups actTick groupOrd withinOrd pos g₁ c₁ m).logOutput
        s!"tick {stageTarget actTick groups g₁ c₁ m}")
      g₁ c₁ g₂ c₂ m
      (stageEvent actTick groups gm cm
        ((chainAt groups gm cm).middleDelays.length + 1)) := by
  set τ := stageTarget actTick groups g₁ c₁ m
  set wQ := popQueueWorld groups actTick groupOrd withinOrd pos g₁ c₁ m
  set w_log := wQ.logOutput s!"tick {τ}"
  set W_B := preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ m
  set e := stageEvent actTick groups gm cm
    ((chainAt groups gm cm).middleDelays.length + 1)
  have h_tick_Q : wQ.tick = τ := by
    dsimp [wQ, popQueueWorld]
    rw [gSimWorld_tick]
  have h_tick_log : w_log.tick = τ := by
    dsimp [w_log]
    rw [h_tick_Q]
  have h_gord_nd : groupOrd.Nodup := Nodup.of_perm h_ord List.nodup_range
  have h_within_nd : ∀ gi, gi < groups.length → (withinOrd gi).Nodup :=
    fun gi h_gi => Nodup.of_perm (h_within gi h_gi) List.nodup_range
  -- layout, nodup, StageMemAt at the pre-burst queue
  have h_layout : NodeLayoutOk groups w_log := by
    dsimp [w_log, wQ, popQueueWorld]
    exact NodeLayoutOk_logOutput groups
      (gSimWorld groups actTick groupOrd withinOrd pos τ)
      s!"tick {τ}"
      (NodeLayoutOk_gSimWorld groups actTick groupOrd withinOrd pos τ)
  have h_nodup : (w_log.events.filter
      (fun ev => ev.targetTick == w_log.tick)).Nodup := by
    rw [World.logOutput_events, h_tick_log]
    exact List.Nodup.filter (fun ev => ev.targetTick == τ)
      (gSimWorld_events_Nodup groups actTick groupOrd withinOrd pos τ
        h_gord_nd h_within_nd)
  have h_stage : StageMemAt groups actTick w_log w_log.tick := by
    rw [h_tick_log]
    dsimp [w_log, wQ, popQueueWorld]
    exact StageMemAt_logOutput groups actTick
      (gSimWorld groups actTick groupOrd withinOrd pos τ)
      s!"tick {τ}" τ
      (StageMemAt_gSimWorld groups actTick groupOrd withinOrd pos τ)
  have h_tgt₂ : stageTarget actTick groups g₂ c₂ m =
      stageTarget actTick groups g₁ c₁ m :=
    (sameSpec_stageTarget groups actTick g₁ c₁ g₂ c₂ m h_act_eq h_spec).symm
  -- reference stage-m events in the pre-burst queue
  have hA_mem : stageEvent actTick groups g₁ c₁ m ∈ w_log.events := by
    rw [World.logOutput_events]
    dsimp [wQ, popQueueWorld]
    exact stageEvent_mem_gSimWorld groups actTick groupOrd withinOrd pos
      h_valid h_ord h_within g₁ c₁ h_g₁ h_c₁ m (by omega)
  have hD_mem : stageEvent actTick groups g₂ c₂ m ∈ w_log.events := by
    rw [World.logOutput_events]
    dsimp [wQ, popQueueWorld]
    have h_mem := stageEvent_mem_gSimWorld groups actTick groupOrd
      withinOrd pos h_valid h_ord h_within g₂ c₂ h_g₂ h_c₂ m (by omega)
    rwa [h_tgt₂] at h_mem
  -- Aₘ before Dₘ in the due filter (QSideOrderNoSurvival induction, SideHypothesisDischarge pattern)
  have hAD : evBefore (w_log.events.filter
      (fun ev => ev.targetTick == w_log.tick))
      (stageEvent actTick groups g₁ c₁ m)
      (stageEvent actTick groups g₂ c₂ m) := by
    have h_ind : evBefore
        ((popQueueWorld groups actTick groupOrd withinOrd pos g₁ c₁ m).events)
        (stageEvent actTick groups g₁ c₁ m)
        (stageEvent actTick groups g₂ c₂ m) :=
      sameSpec_stage_evBefore_ind_self groups actTick groupOrd withinOrd pos
        g₁ c₁ g₂ c₂ m h_g₁ h_c₁ h_g₂ h_c₂ h_spec h_act_eq (by omega)
        h_base₀
        (fun k _ => by
          dsimp [popQueueWorld]
          exact NodeLayoutOk_gSimWorld groups actTick groupOrd withinOrd pos
            (stageTarget actTick groups g₁ c₁ k))
        (fun k hk =>
          sameSpec_h_nodup_discharge groups actTick groupOrd withinOrd pos
            g₁ c₁ h_gord_nd h_within_nd k (by omega))
    dsimp [popQueueWorld] at h_ind
    rw [World.logOutput_events, h_tick_log]
    apply evBefore.filter (fun ev => ev.targetTick == τ)
    · show ((stageEvent actTick groups g₁ c₁ m).targetTick == τ) = true
      dsimp [stageEvent, τ]
      simp
    · show ((stageEvent actTick groups g₂ c₂ m).targetTick == τ) = true
      dsimp [stageEvent]
      rw [← sameSpec_stageTarget groups actTick g₁ c₁ g₂ c₂ m h_act_eq
        h_spec]
      dsimp [τ]
      simp
    · exact h_ind
  -- MiddleBlockOk on the due filter of the pre-burst queue
  have h_mb : MiddleBlockOk groups actTick T
      (w_log.events.filter (fun ev => ev.targetTick == w_log.tick))
      g₁ c₁ g₂ c₂ m := by
    rw [World.logOutput_events, h_tick_log]
    dsimp [wQ, popQueueWorld]
    exact MiddleBlockOk_filter groups actTick T
      ((gSimWorld groups actTick groupOrd withinOrd pos τ).events) τ
      g₁ c₁ g₂ c₂ m h_mb_full
  -- the stage-(m+1) events are not yet queued pre-burst
  have h_sA_absent : stageEvent actTick groups g₁ c₁ (m + 1) ∉
      w_log.events := by
    rw [World.logOutput_events]
    dsimp [wQ, popQueueWorld]
    exact stageEvent_succ_not_mem_gSimWorld groups actTick groupOrd
      withinOrd pos g₁ c₁ m τ h_g₁ h_c₁ (by omega) rfl
  have h_sD_absent : stageEvent actTick groups g₂ c₂ (m + 1) ∉
      w_log.events := by
    rw [World.logOutput_events]
    dsimp [wQ, popQueueWorld]
    exact stageEvent_succ_not_mem_gSimWorld groups actTick groupOrd
      withinOrd pos g₂ c₂ m τ h_g₂ h_c₂ (by omega) h_tgt₂
  have h_e_absent : e ∉ w_log.events := by
    dsimp [e]
    rw [World.logOutput_events]
    dsimp [wQ, popQueueWorld]
    exact stageEvent_succ_not_mem_gSimWorld groups actTick groupOrd
      withinOrd pos gm cm ((chainAt groups gm cm).middleDelays.length) τ
      h_gm h_cm (by omega) h_spawn_e
  have h_T : stageTarget actTick groups g₁ c₁ (m + 1) = T := by
    rw [← h_m₁]
    exact stageTarget_final_eq_T groups actTick T g₁ c₁ h_g₁ h_c₁
      h_uniform h_act
  -- the block premise at the post-burst queue (FinalsBackwardTransportIII)
  obtain ⟨h_ok_B, _⟩ := preStepWorld_tickQueueOk groups actTick groupOrd
    withinOrd pos h_gord_nd h_within_nd g₁ c₁ m
  have h_blk : FinalBlockBetween groups actTick T
      ((preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ m).events)
      g₁ c₁ g₂ c₂ m e := by
    dsimp [e]
    exact FinalBlockBetween_final_preStep_of_dueFilter groups actTick
      groupOrd withinOrd pos T h_valid h_uniform h_act h_ord h_within
      g₁ c₁ gm cm g₂ c₂ m h_g₁ h_c₁ h_gm h_cm h_g₂ h_c₂ h_m₁ h_m₂
      (le_of_eq h_spawn_e) (le_of_eq h_tgt₂) h_ne_left h_ne_right
      h_due_left
      h_due_right h_mem₁ h_mem_e h_mem₂ h_ok_B.1
  exact ConverseSpawnFinal_converse groups actTick T τ
    (buildGroups groups).2 withinOrd pos w_log
    ((popActive groups actTick groupOrd g₁ c₁ m).zipIdx)
    g₁ c₁ g₂ c₂ m h_g₁ h_c₁ h_g₂ h_c₂ h_layout h_m_ge h_m₁ h_m₂
    h_tick_log h_tgt₂ hA_mem hD_mem h_nodup hAD h_mb h_stage
    h_sA_absent h_sD_absent h_T e h_e_absent h_blk
