import BasicProofs.GroupClustering.Stage1BaseClassification
import BasicProofs.GroupClustering.PreStepWorldFacts

open BasicRedstoneSim List

/-! # Group clustering — base case at stage 1 on the post-drain queue

The stage-`1` base case of `MiddleBlockOk`, stated on the tick-start queue
at `stageTarget g₁ c₁ 0 + 1` (the queue right after the stage-`0` pop tick
drains). By PreStepWorldFacts this queue is `(preStepWorld g₁ c₁ 0).stepUntilNextTick.events`,
so the classification core (Stage1BaseClassification) applies directly. The single remaining
per-event fact — that an interloper between the two reference stage-`1`
spawns is itself absent from the pre-drain world (i.e. it is a spawn, not a
survivor) — is taken as a hypothesis; it follows from the filter split of the
drain together with the betweenness. The forward carry to
`gSimWorld (stageTarget g₁ c₁ 1)` is handled separately by
`MiddleBlockOk_gSimWorld_carry_range` (MiddleBlockOkStageInduction). -/

/-- `MiddleBlockOk` at stage 1 on the post-drain queue
    `gSimWorld (stageTarget g₁ c₁ 0 + 1)`, from the Stage1BaseClassification core. -/
theorem MiddleBlockOk_stage1_postDrain (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat)
    (T : Nat) (g₁ c₁ g₂ c₂ : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_m₁ : 1 ≤ (chainAt groups g₁ c₁).middleDelays.length)
    (h_tgt0 : stageTarget actTick groups g₂ c₂ 0 =
        stageTarget actTick groups g₁ c₁ 0)
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
    -- an interloper between the reference stage-1 spawns in the post-drain
    -- queue is absent from the pre-drain world (it is a spawn, not a survivor)
    (h_spawn_not_survivor : ∀ e, e.priority = (-3 : Int) →
        e.targetTick = stageTarget actTick groups g₁ c₁ 1 →
        evBefore (gSimWorld groups actTick groupOrd withinOrd pos
            (stageTarget actTick groups g₁ c₁ 0 + 1)).events
          (stageEvent actTick groups g₁ c₁ 1) e →
        evBefore (gSimWorld groups actTick groupOrd withinOrd pos
            (stageTarget actTick groups g₁ c₁ 0 + 1)).events
          e (stageEvent actTick groups g₂ c₂ 1) →
        e ∉ (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ 0).events) :
    MiddleBlockOk groups actTick T
      (gSimWorld groups actTick groupOrd withinOrd pos
        (stageTarget actTick groups g₁ c₁ 0 + 1)).events g₁ c₁ g₂ c₂ 1 := by
  intro e h_b1 h_b2 h_pri h_tgt
  have h_e_absent : e ∉
      (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ 0).events :=
    h_spawn_not_survivor e h_pri h_tgt h_b1 h_b2
  have h_q : (gSimWorld groups actTick groupOrd withinOrd pos
      (stageTarget actTick groups g₁ c₁ 0 + 1)).events =
      (preStepWorld groups actTick groupOrd withinOrd pos
        g₁ c₁ 0).stepUntilNextTick.events :=
    gSimWorld_succ_events_eq_preStepWorld groups actTick groupOrd withinOrd
      pos g₁ c₁ 0
  rw [h_q] at h_b1 h_b2
  exact MiddleBlock_of_stage0_between groups actTick T
    (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ 0)
    g₁ c₁ g₂ c₂
    h_g₁ h_c₁ h_g₂ h_c₂ h_m₁ h_layout
    (preStepWorld_tick_eq groups actTick groupOrd withinOrd pos g₁ c₁ 0)
    h_tgt0 h_nodup h_stage h_sA_absent h_sD_absent
    e h_e_absent h_pri h_tgt h_b1 h_b2
