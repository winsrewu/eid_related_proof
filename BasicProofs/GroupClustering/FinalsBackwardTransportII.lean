import BasicProofs.GroupClustering.FinalTransition
import BasicProofs.GroupClustering.PreStepWorldFacts
import BasicProofs.GroupClustering.FinalsBackwardTransportI

set_option linter.unusedVariables false

open BasicRedstoneSim List

/-! # Group clustering — backward betweenness transport for finals, II

Transport of the tick-`T` due-filter betweenness of the final events
(OutputBetweennessBridge output) down to the DRAIN queue at the reference stage-`m` pop
tick, in the shape the drain-phase converse consumer needs.

## Consumer sub-goal decomposition

`ConverseSpawnFinal_stepUNT_converse` (ConverseFinalUnconditional) is applied with
`w := preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ m` (the
post-burst world at the stage-`m` pop tick `τ := stageTarget … g₁ c₁ m`;
its tick is `τ` by `preStepWorld_tick_eq`, PreStepWorldFacts). Its block premise
is

    FinalBlockBetween groups actTick T w.stepUntilNextTick.events
      g₁ c₁ g₂ c₂ m e

which unfolds to `e.priority = -1`, `e.targetTick = T`, and the two
betweenness facts in `w.stepUntilNextTick.events` with anchors
`stageEvent actTick groups g₁ c₁ (m + 1)` and
`stageEvent actTick groups g₂ c₂ (m + 1)`.

By `gSimWorld_succ_events_eq_preStepWorld` (PreStepWorldFacts),
`w.stepUntilNextTick.events` is the tick-start queue at `τ + 1`, so the
betweenness is obtained from FinalsBackwardTransportI with `a := τ + 1`, provided BOTH
spawn ticks are at most `τ`:

* the left anchor spawns at `τ` itself (its last middle stage is due at
  `τ`);
* the middle final `e = stageEvent actTick groups gm cm
  (middleDelays.length + 1)` spawns at
  `stageTarget actTick groups gm cm (middleDelays.length)`, bounded by
  `τ` via `h_spawn_e` (discharged at assembly by
  `final_spawnTick_eq_of_dueBetween` of MiddleFinalSpawnTick);
* the right anchor spawns at `stageTarget actTick groups g₂ c₂ m`,
  bounded by `τ` via `h_spawn₂` (discharged at assembly from the equal
  ChainSpec of chains 1 and 3).

The priority and target components of `FinalBlockBetween` are
unconditional: the last stage carries priority -1 (MiddleBlockInvariant) and targets
`T` (StageEventCompleteness). -/

/-- Betweenness of the three final events in the tick-`T` due filter,
    transported to the drain queue of the post-burst world at the
    reference stage-`m` pop tick. The middle final must have spawned no
    later than the reference pop tick, and so must the right reference
    final. -/
theorem evBefore_final_stepUNT_of_dueFilter (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (T : Nat)
    (h_valid : ∀ gi (c : ChainSpec), gi < groups.length →
        c ∈ groupAt groups gi →
        (∀ d ∈ c.middleDelays, ValidDelay d) ∧ ValidDelay c.lastDelay)
    (h_uniform : ∀ gi (c₁ c₂ : ChainSpec), gi < groups.length →
        c₁ ∈ groupAt groups gi → c₂ ∈ groupAt groups gi →
        chainDelay c₁ = chainDelay c₂)
    (h_act : ∀ gi, gi < groups.length → groupAt groups gi ≠ [] →
        actTick gi + groupDelay (groupAt groups gi) = T)
    (h_ord : List.Perm groupOrd (List.range groups.length))
    (h_within : ∀ gi, gi < groups.length →
        List.Perm (withinOrd gi) (List.range (groupAt groups gi).length))
    (g₁ c₁ gm cm g₂ c₂ m : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_gm : gm < groups.length) (h_cm : cm < (groupAt groups gm).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_m₁ : (chainAt groups g₁ c₁).middleDelays.length = m)
    (h_m₂ : (chainAt groups g₂ c₂).middleDelays.length = m)
    (h_spawn_e : stageTarget actTick groups gm cm
        ((chainAt groups gm cm).middleDelays.length) ≤
      stageTarget actTick groups g₁ c₁ m)
    (h_spawn₂ : stageTarget actTick groups g₂ c₂ m ≤
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
    evBefore
      ((preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ m).stepUntilNextTick.events)
      (stageEvent actTick groups g₁ c₁ (m + 1))
      (stageEvent actTick groups gm cm
        ((chainAt groups gm cm).middleDelays.length + 1)) ∧
    evBefore
      ((preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ m).stepUntilNextTick.events)
      (stageEvent actTick groups gm cm
        ((chainAt groups gm cm).middleDelays.length + 1))
      (stageEvent actTick groups g₂ c₂ (m + 1)) := by
  -- carry both pairs back to the tick-start queue at τ + 1
  have h_le : stageTarget actTick groups g₁ c₁ m + 1 ≤ T :=
    Nat.succ_le_of_lt (stageTarget_lt_T_of_middleLen groups actTick T
      g₁ c₁ m h_g₁ h_c₁ h_uniform h_act h_m₁)
  -- the left anchor in the final-stage index form FinalsBackwardTransportI consumes
  set e := stageEvent actTick groups gm cm
    ((chainAt groups gm cm).middleDelays.length + 1)
  have h_anchor₁ : stageEvent actTick groups g₁ c₁
      ((chainAt groups g₁ c₁).middleDelays.length + 1) =
      stageEvent actTick groups g₁ c₁ (m + 1) := by rw [h_m₁]
  have h_anchor₂ : stageEvent actTick groups g₂ c₂
      ((chainAt groups g₂ c₂).middleDelays.length + 1) =
      stageEvent actTick groups g₂ c₂ (m + 1) := by rw [h_m₂]
  have h_ne_left' : stageEvent actTick groups g₁ c₁
      ((chainAt groups g₁ c₁).middleDelays.length + 1) ≠ e := by
    rw [h_anchor₁]; exact h_ne_left
  have h_ne_right' : e ≠ stageEvent actTick groups g₂ c₂
      ((chainAt groups g₂ c₂).middleDelays.length + 1) := by
    rw [h_anchor₂]; exact h_ne_right
  have h_due_left' : evBefore
      ((gSimWorld groups actTick groupOrd withinOrd pos T).events.filter
        (fun ev => ev.targetTick == T))
      (stageEvent actTick groups g₁ c₁
        ((chainAt groups g₁ c₁).middleDelays.length + 1)) e := by
    rw [h_anchor₁]; exact h_due_left
  have h_due_right' : evBefore
      ((gSimWorld groups actTick groupOrd withinOrd pos T).events.filter
        (fun ev => ev.targetTick == T))
      e (stageEvent actTick groups g₂ c₂
        ((chainAt groups g₂ c₂).middleDelays.length + 1)) := by
    rw [h_anchor₂]; exact h_due_right
  have h_left : evBefore
      (gSimWorld groups actTick groupOrd withinOrd pos
        (stageTarget actTick groups g₁ c₁ m + 1)).events
      (stageEvent actTick groups g₁ c₁
        ((chainAt groups g₁ c₁).middleDelays.length + 1)) e :=
    evBefore_final_backward_to_tick groups actTick groupOrd withinOrd pos T
      h_valid h_uniform h_act h_ord h_within
      g₁ c₁ gm cm h_g₁ h_c₁ h_gm h_cm
      (stageTarget actTick groups g₁ c₁ m + 1) h_le
      (by rw [h_m₁]; omega) (by omega) h_ne_left' h_due_left'
  have h_right : evBefore
      (gSimWorld groups actTick groupOrd withinOrd pos
        (stageTarget actTick groups g₁ c₁ m + 1)).events
      e (stageEvent actTick groups g₂ c₂
        ((chainAt groups g₂ c₂).middleDelays.length + 1)) :=
    evBefore_final_backward_to_tick groups actTick groupOrd withinOrd pos T
      h_valid h_uniform h_act h_ord h_within
      gm cm g₂ c₂ h_gm h_cm h_g₂ h_c₂
      (stageTarget actTick groups g₁ c₁ m + 1) h_le
      (by omega) (by rw [h_m₂]; omega) h_ne_right' h_due_right'
  -- the drain queue at τ is the tick-start queue at τ + 1 (PreStepWorldFacts);
  -- rewrite the anchors back to the consumer's stage-(m + 1) form
  refine ⟨?_, ?_⟩
  · rw [← gSimWorld_succ_events_eq_preStepWorld groups actTick groupOrd
      withinOrd pos g₁ c₁ m, ← h_anchor₁]
    exact h_left
  · rw [← gSimWorld_succ_events_eq_preStepWorld groups actTick groupOrd
      withinOrd pos g₁ c₁ m, ← h_anchor₂]
    exact h_right

/-- The drain-path block premise of `ConverseSpawnFinal_stepUNT_converse`
    (ConverseFinalUnconditional), assembled from the transported betweenness. The middle
    final carries priority -1 and targets `T` unconditionally. -/
theorem FinalBlockBetween_final_stepUNT_of_dueFilter
    (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (T : Nat)
    (h_valid : ∀ gi (c : ChainSpec), gi < groups.length →
        c ∈ groupAt groups gi →
        (∀ d ∈ c.middleDelays, ValidDelay d) ∧ ValidDelay c.lastDelay)
    (h_uniform : ∀ gi (c₁ c₂ : ChainSpec), gi < groups.length →
        c₁ ∈ groupAt groups gi → c₂ ∈ groupAt groups gi →
        chainDelay c₁ = chainDelay c₂)
    (h_act : ∀ gi, gi < groups.length → groupAt groups gi ≠ [] →
        actTick gi + groupDelay (groupAt groups gi) = T)
    (h_ord : List.Perm groupOrd (List.range groups.length))
    (h_within : ∀ gi, gi < groups.length →
        List.Perm (withinOrd gi) (List.range (groupAt groups gi).length))
    (g₁ c₁ gm cm g₂ c₂ m : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_gm : gm < groups.length) (h_cm : cm < (groupAt groups gm).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_m₁ : (chainAt groups g₁ c₁).middleDelays.length = m)
    (h_m₂ : (chainAt groups g₂ c₂).middleDelays.length = m)
    (h_spawn_e : stageTarget actTick groups gm cm
        ((chainAt groups gm cm).middleDelays.length) ≤
      stageTarget actTick groups g₁ c₁ m)
    (h_spawn₂ : stageTarget actTick groups g₂ c₂ m ≤
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
    FinalBlockBetween groups actTick T
      ((preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ m).stepUntilNextTick.events)
      g₁ c₁ g₂ c₂ m
      (stageEvent actTick groups gm cm
        ((chainAt groups gm cm).middleDelays.length + 1)) := by
  obtain ⟨h_l, h_r⟩ := evBefore_final_stepUNT_of_dueFilter groups actTick
    groupOrd withinOrd pos T h_valid h_uniform h_act h_ord h_within
    g₁ c₁ gm cm g₂ c₂ m h_g₁ h_c₁ h_gm h_cm h_g₂ h_c₂ h_m₁ h_m₂
    h_spawn_e h_spawn₂ h_ne_left h_ne_right h_due_left h_due_right
  refine ⟨?_, ?_, h_l, h_r⟩
  · dsimp [stageEvent]
    exact stagePri_last groups gm cm
  · dsimp [stageEvent]
    exact stageTarget_final_eq_T groups actTick T gm cm h_gm h_cm
      h_uniform h_act
