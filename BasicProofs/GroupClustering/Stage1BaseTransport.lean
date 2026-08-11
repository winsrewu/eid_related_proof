import BasicProofs.GroupClustering.Stage1BaseClassification
import BasicProofs.GroupClustering.PreStepWorldFacts

open BasicRedstoneSim List

/-! # Group clustering — base case at stage 1, modulo transport

The `MiddleBlockOk` base case at stage 1 asserts that an event between
the two reference stage-`1` events in the tick-start queue at
`stageTarget g₁ c₁ 1`, carrying priority `-3` and targeting that tick, is
a same-prefix stage-`1` event. The classification core
(`MiddleBlock_of_stage0_between`, Stage1BaseClassification) does this once the betweenness
is known in the drain queue `(preStepWorld g₁ c₁ 0).stepUntilNextTick.events`.
This file states the base case as following from a transport premise that
moves the tick-`stageTarget g₁ c₁ 1` betweenness back to that drain queue;
the transport itself (spawn-tick trichotomy + membership + backward
carry) is the remaining sub-goal. -/

/-- The `MiddleBlockOk` base case at stage 1, given the backward transport
    of the betweenness from the tick-start queue at the stage-`1` pop tick
    to the drain of the stage-`0` post-burst world. -/
theorem MiddleBlockOk_stage1_of_transport (groups : List GroupSpec)
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
    -- transport premise: betweenness at the stage-1 pop-tick queue moves
    -- back to the drain queue, and the interloper is absent pre-drain
    (h_transport : ∀ e, e.priority = (-3 : Int) →
        e.targetTick = stageTarget actTick groups g₁ c₁ 1 →
        evBefore (gSimWorld groups actTick groupOrd withinOrd pos
            (stageTarget actTick groups g₁ c₁ 1)).events
          (stageEvent actTick groups g₁ c₁ 1) e →
        evBefore (gSimWorld groups actTick groupOrd withinOrd pos
            (stageTarget actTick groups g₁ c₁ 1)).events
          e (stageEvent actTick groups g₂ c₂ 1) →
        e ∉ (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ 0).events ∧
        evBefore (preStepWorld groups actTick groupOrd withinOrd pos
            g₁ c₁ 0).stepUntilNextTick.events
          (stageEvent actTick groups g₁ c₁ 1) e ∧
        evBefore (preStepWorld groups actTick groupOrd withinOrd pos
            g₁ c₁ 0).stepUntilNextTick.events
          e (stageEvent actTick groups g₂ c₂ 1)) :
    MiddleBlockOk groups actTick T
      (gSimWorld groups actTick groupOrd withinOrd pos
        (stageTarget actTick groups g₁ c₁ 1)).events g₁ c₁ g₂ c₂ 1 := by
  intro e h_b1 h_b2 h_pri h_tgt
  obtain ⟨h_e_absent, h_b1', h_b2'⟩ := h_transport e h_pri h_tgt h_b1 h_b2
  exact MiddleBlock_of_stage0_between groups actTick T
    (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ 0)
    g₁ c₁ g₂ c₂
    h_g₁ h_c₁ h_g₂ h_c₂ h_m₁ h_layout
    (preStepWorld_tick_eq groups actTick groupOrd withinOrd pos g₁ c₁ 0)
    h_tgt0 h_nodup h_stage h_sA_absent h_sD_absent
    e h_e_absent h_pri h_tgt h_b1' h_b2'
