import BasicProofs.GroupClustering.GSimBodyIteration
import BasicProofs.GroupClustering.MiddleBlockPopStep

set_option linter.unusedVariables false

open BasicRedstoneSim List

/-! # Group clustering — the final transition at stage `j = m`

This file handles the boundary case where the middle-block invariant
reaches the last middle stage of the reference chains. Stage `m` is
the last middle stage. Stage `m + 1` is the last-repeater stage. The
due events at stage `m + 1` carry priority -1, not -3. The
`MiddleBlockOk` invariant only constrains events of priority -3. It
becomes vacuous at stage `m + 1`. We instead characterize the
priority-(-1) events between the stage-`(m + 1)` anchors.

## Scope

* `Pri1FinalOf` — a predicate for a priority-(-1) event that matches
  the full spec of chain `(g₁, c₁)` at the last stage.
* `FinalBlockBetween` — the set of priority-(-1) events between two
  stage-`(m + 1)` anchors at the output tick.
* `finalStage_evBefore_of_middle` — order between stage-`m` parents
  propagates to order between their stage-`(m + 1)` children. This
  lemma is the order-preservation step at the boundary.
* `Pri1FinalOf_to_IsFinalEvent` — `Pri1FinalOf` implies
  `IsFinalEvent`. -/


/-! ## Final-event predicates -/

/-- A priority-(-1) event `e` matches the full spec of chain
    `(g₁, c₁)` at the last stage. The witness chain `(g, c)` has the
    same number of middle delays as `(g₁, c₁)`. The stage-`(m + 1)`
    event of `(g, c)` equals `e`. The prefix of length `m + 1` and
    the target at stage `m + 1` agree with those of `(g₁, c₁)`. -/
def Pri1FinalOf (groups : List GroupSpec) (actTick : Nat → Nat)
    (g₁ c₁ m : Nat) (e : ScheduledEvent) : Prop :=
  ∃ g c, g < groups.length ∧ c < (groupAt groups g).length ∧
    (chainAt groups g c).middleDelays.length =
      (chainAt groups g₁ c₁).middleDelays.length ∧
    e = stageEvent actTick groups g c (m + 1) ∧
    prefixDelays groups g c (m + 1) =
      prefixDelays groups g₁ c₁ (m + 1) ∧
    stageTarget actTick groups g c (m + 1) =
      stageTarget actTick groups g₁ c₁ (m + 1)

/-- The set of priority-(-1) events between two stage-`(m + 1)`
    anchors. These events target the output tick `T`. They sit in
    queue order between the two reference events. -/
def FinalBlockBetween (groups : List GroupSpec) (actTick : Nat → Nat)
    (T : Nat) (queue : List ScheduledEvent)
    (g₁ c₁ g₂ c₂ m : Nat) (e : ScheduledEvent) : Prop :=
  e.priority = (-1 : Int) ∧
  e.targetTick = T ∧
  evBefore queue (stageEvent actTick groups g₁ c₁ (m + 1)) e ∧
  evBefore queue e (stageEvent actTick groups g₂ c₂ (m + 1))


/-! ## Basic lemmas -/

/-- The priority of a stage-`(m + 1)` event is -1 when stage `m + 1`
    is the last stage of the chain. -/
theorem stagePri_last_of_m (groups : List GroupSpec) (gi ci m : Nat)
    (h_m : (chainAt groups gi ci).middleDelays.length = m) :
    stagePri groups gi ci (m + 1) = (-1 : Int) := by
  rw [← h_m]
  exact stagePri_last groups gi ci

/-- The priority of a stage-`m` event is -3 when `m` equals the
    number of middle delays and `m ≥ 1`. Stage `m` is the last
    middle stage. -/
theorem stagePri_lastMiddle (groups : List GroupSpec) (gi ci m : Nat)
    (h_m_ge : 1 ≤ m)
    (h_m : (chainAt groups gi ci).middleDelays.length = m) :
    stagePri groups gi ci m = (-3 : Int) := by
  rw [← h_m]
  have h_le :
      (chainAt groups gi ci).middleDelays.length ≤
        (chainAt groups gi ci).middleDelays.length := by omega
  exact stagePri_middle groups gi ci
    ((chainAt groups gi ci).middleDelays.length)
    (by omega) h_le

/-- `Pri1FinalOf` implies `IsFinalEvent`. The witness chain has `m`
    middle delays. Stage `m + 1` is its last stage. -/
theorem Pri1FinalOf_to_IsFinalEvent (groups : List GroupSpec)
    (actTick : Nat → Nat) (T : Nat) (g₁ c₁ m : Nat) (e : ScheduledEvent)
    (h_T : stageTarget actTick groups g₁ c₁ (m + 1) = T)
    (h_m : (chainAt groups g₁ c₁).middleDelays.length = m)
    (h_fin : Pri1FinalOf groups actTick g₁ c₁ m e) :
    IsFinalEvent groups actTick T e := by
  rcases h_fin with ⟨g, c, h_g, h_c, h_len, h_ev, _, h_tgt⟩
  refine ⟨g, c, h_g, h_c, ?_, ?_⟩
  · -- Goal: `e = stageEvent ... ((chainAt g c).middleDelays.length + 1)`.
    -- `h_len` equates the lengths. Substitute via `h_len` to turn the
    -- goal into `e = stageEvent ... (m + 1)`, then apply `h_ev`.
    have h_rw :
        (chainAt groups g c).middleDelays.length + 1 = m + 1 := by
      rw [h_len, h_m]
    rw [h_rw]
    exact h_ev
  · -- Goal: `stageTarget ... ((chainAt g c).middleDelays.length + 1) = T`.
    -- Convert the goal to use stage `m + 1`, then chain `h_tgt` and
    -- `h_T`.
    have h_rw :
        (chainAt groups g c).middleDelays.length + 1 = m + 1 := by
      rw [h_len, h_m]
    rw [h_rw]
    exact h_tgt.trans h_T

/-- A priority-(-1) event of `FinalBlockBetween` targets the common
    output tick `T`. -/
theorem FinalBlockBetween_target (groups : List GroupSpec)
    (actTick : Nat → Nat) (T : Nat) (queue : List ScheduledEvent)
    (g₁ c₁ g₂ c₂ m : Nat) (e : ScheduledEvent)
    (h_blk : FinalBlockBetween groups actTick T queue
        g₁ c₁ g₂ c₂ m e) :
    e.targetTick = T := h_blk.2.1

/-- A priority-(-1) event of `FinalBlockBetween` carries priority
    -1. -/
theorem FinalBlockBetween_priority (groups : List GroupSpec)
    (actTick : Nat → Nat) (T : Nat) (queue : List ScheduledEvent)
    (g₁ c₁ g₂ c₂ m : Nat) (e : ScheduledEvent)
    (h_blk : FinalBlockBetween groups actTick T queue
        g₁ c₁ g₂ c₂ m e) :
    e.priority = (-1 : Int) := h_blk.1


/-! ## Final-stage order preservation -/

/-- At the stage-`m` pop tick, the burst phase preserves the order
    of the stage-`(m + 1)` events. The middle-stage parent of `(g, c)`
    sits between the parents of the two reference chains. The order
    carries over to the stage-`(m + 1)` children. Stage `m` is the
    last middle stage for all three chains. Stage `m + 1` is the last
    stage. The stage-`m` events are due. The stage-`(m + 1)` events
    are absent from the pre-burst world. The stage-`m` events do not
    survive the burst. -/
theorem finalStage_evBefore_of_middle (groups : List GroupSpec)
    (actTick : Nat → Nat) (t : Nat)
    (obsAll : List (List Nat)) (withinOrd pos : Nat → List Nat)
    (w : World) (pairs : List (Nat × Nat))
    (g₁ c₁ g₂ c₂ g c m : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_g : g < groups.length) (h_c : c < (groupAt groups g).length)
    (h_layout : NodeLayoutOk groups w)
    (h_m_ge : 1 ≤ m)
    (h_m₁ : (chainAt groups g₁ c₁).middleDelays.length = m)
    (h_m₂ : (chainAt groups g₂ c₂).middleDelays.length = m)
    (h_m : (chainAt groups g c).middleDelays.length = m)
    (h_due : w.tick = stageTarget actTick groups g₁ c₁ m)
    (h_tgt₂ : stageTarget actTick groups g₂ c₂ m =
        stageTarget actTick groups g₁ c₁ m)
    (h_tgt : stageTarget actTick groups g c m =
        stageTarget actTick groups g₁ c₁ m)
    (hA_mem : stageEvent actTick groups g₁ c₁ m ∈ w.events)
    (hC_mem : stageEvent actTick groups g c m ∈ w.events)
    (hD_mem : stageEvent actTick groups g₂ c₂ m ∈ w.events)
    (h_nodup : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup)
    (hAC : evBefore (w.events.filter (fun e => e.targetTick == w.tick))
        (stageEvent actTick groups g₁ c₁ m)
        (stageEvent actTick groups g c m))
    (hCD : evBefore (w.events.filter (fun e => e.targetTick == w.tick))
        (stageEvent actTick groups g c m)
        (stageEvent actTick groups g₂ c₂ m))
    (hA_gone : stageEvent actTick groups g₁ c₁ m ∉
        (gSimBurst t obsAll withinOrd pos w pairs).events)
    (hC_gone : stageEvent actTick groups g c m ∉
        (gSimBurst t obsAll withinOrd pos w pairs).events)
    (hD_gone : stageEvent actTick groups g₂ c₂ m ∉
        (gSimBurst t obsAll withinOrd pos w pairs).events) :
    evBefore (gSimBurst t obsAll withinOrd pos w pairs).events
      (stageEvent actTick groups g₁ c₁ (m + 1))
      (stageEvent actTick groups g c (m + 1)) ∧
    evBefore (gSimBurst t obsAll withinOrd pos w pairs).events
      (stageEvent actTick groups g c (m + 1))
      (stageEvent actTick groups g₂ c₂ (m + 1)) := by
  have h_m_le₁ : m ≤ (chainAt groups g₁ c₁).middleDelays.length := by
    omega
  have h_m_le₂ : m ≤ (chainAt groups g₂ c₂).middleDelays.length := by
    omega
  have h_m_le : m ≤ (chainAt groups g c).middleDelays.length := by
    omega
  exact prefixClass_step_gSimBurst groups t obsAll withinOrd pos w pairs
    g₁ c₁ g₂ c₂ g c m
    h_g₁ h_c₁ h_g₂ h_c₂ h_g h_c h_layout
    h_m_le₁ h_m_le₂ h_m_le h_due h_tgt₂ h_tgt
    hA_mem hC_mem hD_mem h_nodup hAC hCD
    hA_gone hC_gone hD_gone


/-! ## Clustering at the output

The final events of chains with the same full spec as `(g₁, c₁)`
sit contiguously between the two stage-`(m + 1)` anchors. The
order follows from the order of the stage-`m` parents.

Status: a full proof requires a converse spawn lemma for
priority-(-1) events. That lemma mirrors
`converse_spawn_gSimBurst` of ConverseSpawn but accepts priority -1.
The `MiddleBlockOk` invariant at stage `m` then classifies the
parents. This part is left for future work. The present file
stays green. -/
