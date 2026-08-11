import BasicProofs.GroupClustering.SurvivalFreeStageInduction
import BasicProofs.GroupClustering.SideHypothesisDischarge
import BasicProofs.GroupClustering.Stage1BaseGeneral

open BasicRedstoneSim List

/-! # Group clustering — MiddleBlockOk at the last middle stage

Applying the survival-free stage induction (SurvivalFreeStageInduction) to two same-spec
chains: the base at stage 1 is Stage1BaseGeneral; every side hypothesis of every
middle stage is discharged by SideHypothesisDischarge. The result is the MiddleBlockOk
invariant at stage `m` (the last middle stage) on the tick-start queue
at the pop tick of stage `m` — the input of the final-converse
machinery (ConverseFinalUnconditional).
-/

/-- MiddleBlockOk at the last middle stage for two same-spec chains
    activated at the same tick, oriented by the stage-0 base order
    (`h_base₀`). -/
theorem MiddleBlockOk_sameSpec_stage_m (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat)
    (h_valid : ∀ gi (c : ChainSpec), gi < groups.length →
        c ∈ groupAt groups gi →
        (∀ d ∈ c.middleDelays, ValidDelay d) ∧ ValidDelay c.lastDelay)
    (h_ord : List.Perm groupOrd (List.range groups.length))
    (h_within : ∀ gi, gi < groups.length →
        List.Perm (withinOrd gi) (List.range (groupAt groups gi).length))
    (T : Nat) (g₁ c₁ g₂ c₂ : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_spec : chainAt groups g₁ c₁ = chainAt groups g₂ c₂)
    (h_act_eq : actTick g₁ = actTick g₂)
    (h_base₀ : evBefore
        ((popQueueWorld groups actTick groupOrd withinOrd pos
          g₁ c₁ 0).events)
        (stageEvent actTick groups g₁ c₁ 0)
        (stageEvent actTick groups g₂ c₂ 0))
    (m : Nat) (h_m : (chainAt groups g₁ c₁).middleDelays.length = m)
    (h_m_ge : 1 ≤ m) :
    MiddleBlockOk groups actTick T
      (gSimWorld groups actTick groupOrd withinOrd pos
        (stageTarget actTick groups g₁ c₁ m)).events g₁ c₁ g₂ c₂ m :=
  have h_gord_nd : groupOrd.Nodup := Nodup.of_perm h_ord List.nodup_range
  have h_within_nd : ∀ gi, gi < groups.length → (withinOrd gi).Nodup :=
    fun gi h_gi => Nodup.of_perm (h_within gi h_gi) List.nodup_range
  MiddleBlockOk_gSimFoldl_stage_general groups actTick groupOrd withinOrd pos
    g₁ c₁ g₂ c₂ m T h_g₁ h_c₁ h_g₂ h_c₂ h_m_ge
    (MiddleBlockOk_stage1_general groups actTick groupOrd withinOrd pos
      h_valid h_ord h_within T g₁ c₁ g₂ c₂ h_g₁ h_c₁ h_g₂ h_c₂
      (by rw [h_m]; exact h_m_ge)
      ((sameSpec_stageTarget groups actTick g₁ c₁ g₂ c₂ 0 h_act_eq
        h_spec).symm)
      ((sameSpec_stageTarget groups actTick g₁ c₁ g₂ c₂ 1 h_act_eq
        h_spec).symm))
    (fun j h_j_ge h_j_lt_m =>
      MBStepSideGeneral_discharge groups actTick groupOrd withinOrd pos
        h_valid h_ord h_within g₁ c₁ g₂ c₂ h_g₁ h_c₁ h_g₂ h_c₂ h_spec
        h_act_eq h_gord_nd h_within_nd h_base₀ j h_j_ge
        (by rw [h_m]; exact h_j_lt_m))
