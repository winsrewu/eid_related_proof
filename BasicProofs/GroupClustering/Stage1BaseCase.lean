import BasicProofs.GroupClustering.Stage1PostDrainBase
import BasicProofs.GroupClustering.MiddleBlockOkStageInduction

open BasicRedstoneSim List

/-! # Group clustering — the stage-1 base case of `MiddleBlockOk`

Assembles the base case `MiddleBlockOk` at stage 1 on the tick-start queue
at the stage-`1` pop tick `stageTarget g₁ c₁ 1`. It combines the post-drain
base case (Stage1PostDrainBase, on `gSimWorld (stageTarget g₁ c₁ 0 + 1)`) with the forward
multi-tick carry (MiddleBlockOkStageInduction `MiddleBlockOk_gSimWorld_carry_range`) across the
non-pop ticks up to the stage-`1` pop tick. This is the `h_base` consumed by
the stage induction `MiddleBlockOk_gSimFoldl_stage` (MiddleBlockOkStageInduction). -/

/-- The `MiddleBlockOk` base case at stage 1 on
    `gSimWorld (stageTarget g₁ c₁ 1)`. -/
theorem MiddleBlockOk_stage1_base (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat)
    (T : Nat) (g₁ c₁ g₂ c₂ : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_m₁ : 1 ≤ (chainAt groups g₁ c₁).middleDelays.length)
    (h_tgt0 : stageTarget actTick groups g₂ c₂ 0 =
        stageTarget actTick groups g₁ c₁ 0)
    (h_tgt1 : stageTarget actTick groups g₂ c₂ 1 =
        stageTarget actTick groups g₁ c₁ 1)
    -- post-drain base case (Stage1PostDrainBase) hypotheses
    (h_layout : NodeLayoutOk groups
        (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ 0))
    (h_nodup : ((preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ 0).events.filter
        (fun e => e.targetTick ==
          (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ 0).tick)).Nodup)
    (h_stage : StageMemAt groups actTick
        (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ 0)
        (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ 0).tick)
    (h_sA_absent : stageEvent actTick groups g₁ c₁ 1 ∉
        (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ 0).events)
    (h_sD_absent : stageEvent actTick groups g₂ c₂ 1 ∉
        (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ 0).events)
    (h_spawn_not_survivor : ∀ e, e.priority = (-3 : Int) →
        e.targetTick = stageTarget actTick groups g₁ c₁ 1 →
        evBefore (gSimWorld groups actTick groupOrd withinOrd pos
            (stageTarget actTick groups g₁ c₁ 0 + 1)).events
          (stageEvent actTick groups g₁ c₁ 1) e →
        evBefore (gSimWorld groups actTick groupOrd withinOrd pos
            (stageTarget actTick groups g₁ c₁ 0 + 1)).events
          e (stageEvent actTick groups g₂ c₂ 1) →
        e ∉ (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ 0).events)
    -- carry hypotheses: reference stage-1 events present and non-due on
    -- [stageTarget g₁ c₁ 0 + 1, stageTarget g₁ c₁ 1), with nodup queues
    (hA_mem : ∀ k, stageTarget actTick groups g₁ c₁ 0 + 1 ≤ k →
        k < stageTarget actTick groups g₁ c₁ 1 →
        stageEvent actTick groups g₁ c₁ 1 ∈
          (gSimWorld groups actTick groupOrd withinOrd pos k).events)
    (hD_mem : ∀ k, stageTarget actTick groups g₁ c₁ 0 + 1 ≤ k →
        k < stageTarget actTick groups g₁ c₁ 1 →
        stageEvent actTick groups g₂ c₂ 1 ∈
          (gSimWorld groups actTick groupOrd withinOrd pos k).events)
    (h_nd_post : ∀ k, stageTarget actTick groups g₁ c₁ 0 + 1 ≤ k →
        k < stageTarget actTick groups g₁ c₁ 1 →
        (gSimWorld groups actTick groupOrd withinOrd pos (k + 1)).events.Nodup) :
    MiddleBlockOk groups actTick T
      (gSimWorld groups actTick groupOrd withinOrd pos
        (stageTarget actTick groups g₁ c₁ 1)).events g₁ c₁ g₂ c₂ 1 := by
  -- base case on the post-drain queue right after the stage-0 pop tick
  have h_mb : MiddleBlockOk groups actTick T
      (gSimWorld groups actTick groupOrd withinOrd pos
        (stageTarget actTick groups g₁ c₁ 0 + 1)).events g₁ c₁ g₂ c₂ 1 :=
    MiddleBlockOk_stage1_postDrain groups actTick groupOrd withinOrd pos T
      g₁ c₁ g₂ c₂ h_g₁ h_c₁ h_g₂ h_c₂ h_m₁ h_tgt0
      h_layout h_nodup h_stage h_sA_absent h_sD_absent h_spawn_not_survivor
  -- the stage-1 pop tick is strictly after the stage-0 pop tick
  have h_le : stageTarget actTick groups g₁ c₁ 0 + 1 ≤
      stageTarget actTick groups g₁ c₁ 1 :=
    Nat.succ_le_of_lt (stageTarget_lt_succ actTick groups g₁ c₁ 0
      (Nat.zero_le ((chainAt groups g₁ c₁).middleDelays.length)))
  -- carry forward across the non-pop ticks to the stage-1 pop tick
  exact MiddleBlockOk_gSimWorld_carry_range groups actTick groupOrd withinOrd
    pos (stageTarget actTick groups g₁ c₁ 0 + 1)
    (stageTarget actTick groups g₁ c₁ 1) g₁ c₁ g₂ c₂ 1 T
    h_le h_mb hA_mem hD_mem
    (fun k _ h₂ => by
      dsimp [stageEvent]
      omega)
    (fun k _ h₂ => by
      dsimp [stageEvent]
      rw [h_tgt1]
      omega)
    h_nd_post
