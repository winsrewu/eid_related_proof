import BasicProofs.GroupClustering.SameSpecBeforeness

open BasicRedstoneSim List

/-! # Group clustering — discharged premises and Q-side order preservation

SameSpecBeforeness proves that same-spec chains propagate their queue order through
the stages, assuming four premises: a base order at stage 0, layout
health, due-filter distinctness, and burst-phase survival. This file
discharges the layout premise from the simulation setup and assembles
the Q-side order-preservation lemma. The remaining premises (base
order, nodup, survival) stay as explicit hypotheses.
-/

/-! ## Re-definitions of SameSpecBeforeness private helpers

SameSpecBeforeness declares `popQueueWorld`, `popActive`, and `preStepWorld` as
private. We re-define them here with identical bodies so that the
public theorems of SameSpecBeforeness apply by definitional equality. -/

/-- The queue at the start of the pop tick of stage `j` of chain
    `(g₁, c₁)`. -/
def popQueueWorld (groups : List GroupSpec) (actTick : Nat → Nat)
    (groupOrd : List Nat) (withinOrd pos : Nat → List Nat)
    (g₁ c₁ j : Nat) : World :=
  gSimWorld groups actTick groupOrd withinOrd pos
    (stageTarget actTick groups g₁ c₁ j)

/-- The groups that activate at the pop tick of stage `j` of chain
    `(g₁, c₁)`. -/
def popActive (groups : List GroupSpec) (actTick : Nat → Nat)
    (groupOrd : List Nat) (g₁ c₁ j : Nat) : List Nat :=
  groupOrd.filter (fun gi =>
    decide (gi < (buildGroups groups).2.length) &&
    (actTick gi == stageTarget actTick groups g₁ c₁ j))

/-- The world just before the drain step of the pop tick of stage `j`
    of chain `(g₁, c₁)`: after the log entry and the burst phase. -/
def preStepWorld (groups : List GroupSpec) (actTick : Nat → Nat)
    (groupOrd : List Nat) (withinOrd pos : Nat → List Nat)
    (g₁ c₁ j : Nat) : World :=
  gSimBurst (stageTarget actTick groups g₁ c₁ j) (buildGroups groups).2
    withinOrd pos
    ((popQueueWorld groups actTick groupOrd withinOrd pos g₁ c₁ j).logOutput
      s!"tick {stageTarget actTick groups g₁ c₁ j}")
    ((popActive groups actTick groupOrd g₁ c₁ j).zipIdx)

/-! ## Layout health at every tick-start queue -/

/-- `NodeLayoutOk` holds at every tick-start world. The build phase
    establishes the layout and the simulation preserves it. -/
private theorem NodeLayoutOk_gSimWorld (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (t : Nat) :
    NodeLayoutOk groups
      (gSimWorld groups actTick groupOrd withinOrd pos t) := by
  dsimp [gSimWorld]
  exact NodeLayoutOk_gSimFoldl groups actTick (buildGroups groups).2 groupOrd
    withinOrd pos (buildGroups groups).1 t (NodeLayoutOk_buildGroups groups)

/-- The layout premise of `sameSpec_stage_evBefore_ind` holds at every
    stage below `j`. -/
private theorem popQueueWorld_layout (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat)
    (g₁ c₁ j : Nat) :
    ∀ k, k < j →
      NodeLayoutOk groups
        (popQueueWorld groups actTick groupOrd withinOrd pos g₁ c₁ k) := by
  intro k _
  dsimp [popQueueWorld]
  exact NodeLayoutOk_gSimWorld groups actTick groupOrd withinOrd pos
    (stageTarget actTick groups g₁ c₁ k)

/-! ## Assembled Q-side order-preservation lemma

We combine the induction of SameSpecBeforeness with the discharged layout premise.
The remaining premises (base order, due-filter nodup, burst survival)
are taken as explicit hypotheses. The lemma states that two same-spec
chains whose stage-0 events are ordered at the activation tick remain
ordered at every later stage up to the last repeater. -/

/-- Q-side order preservation for same-spec chains. Two same-spec
    chains whose stage-0 events are ordered in the pop-tick queue
    remain ordered at every stage up to the last repeater, provided
    the due-filter is Nodup and both events survive each burst phase.
    The layout premise is discharged by `popQueueWorld_layout`. -/
theorem sameSpec_orderPreservation (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (g₁ c₁ g₂ c₂ : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_spec : chainAt groups g₁ c₁ = chainAt groups g₂ c₂)
    (h_act_eq : actTick g₁ = actTick g₂)
    (h_base : evBefore
      ((popQueueWorld groups actTick groupOrd withinOrd pos g₁ c₁ 0).events)
      (stageEvent actTick groups g₁ c₁ 0)
      (stageEvent actTick groups g₂ c₂ 0))
    (h_nodup : ∀ k, k ≤ (chainAt groups g₁ c₁).middleDelays.length →
      ((popQueueWorld groups actTick groupOrd withinOrd pos g₁ c₁ k).events.filter
        (fun e => e.targetTick == stageTarget actTick groups g₁ c₁ k)).Nodup)
    (h_surv : ∀ k, k ≤ (chainAt groups g₁ c₁).middleDelays.length →
      stageEvent actTick groups g₁ c₁ k ∈
        (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ k).events ∧
      stageEvent actTick groups g₂ c₂ k ∈
        (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ k).events) :
    let m := (chainAt groups g₁ c₁).middleDelays.length
    evBefore
      ((popQueueWorld groups actTick groupOrd withinOrd pos g₁ c₁ (m + 1)).events)
      (stageEvent actTick groups g₁ c₁ (m + 1))
      (stageEvent actTick groups g₂ c₂ (m + 1)) := by
  intro m
  have h_j : m + 1 ≤ (chainAt groups g₁ c₁).middleDelays.length + 1 := by
    omega
  -- Apply the induction of SameSpecBeforeness with the layout premise discharged
  refine sameSpec_stage_evBefore_ind groups actTick groupOrd withinOrd pos
    g₁ c₁ g₂ c₂ (m + 1) h_g₁ h_c₁ h_g₂ h_c₂ h_spec h_act_eq h_j h_base ?_ ?_ ?_
  · -- h_layout: discharged
    exact popQueueWorld_layout groups actTick groupOrd withinOrd pos g₁ c₁
      (m + 1)
  · -- h_nodup: translate from ≤ to <
    intro k hk
    have h_k_le : k ≤ (chainAt groups g₁ c₁).middleDelays.length := by omega
    exact h_nodup k h_k_le
  · -- h_surv: translate from ≤ to <
    intro k hk
    have h_k_le : k ≤ (chainAt groups g₁ c₁).middleDelays.length := by omega
    exact h_surv k h_k_le

