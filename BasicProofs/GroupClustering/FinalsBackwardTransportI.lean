import BasicProofs.GroupClustering.ActivationListOrder
import BasicProofs.GroupClustering.BackwardTransport
import BasicProofs.GroupClustering.SuccessorMembershipRange

set_option linter.unusedVariables false

open BasicRedstoneSim List

/-! # Group clustering — backward betweenness transport for finals, I

The finals bundle (FinalsBundle) and the bridge (OutputBetweennessBridge) give betweenness of
the final events in the tick-`T` due filter. The converse machinery of
ConverseFinalUnconditional consumes betweenness at the stage-`m` POP tick of the reference
chains instead: `Pri1FinalOf_of_between` / `ConverseSpawnFinal_converse`
read the post-burst queue, and `ConverseSpawnFinal_stepUNT_converse`
reads the drain of the post-burst queue, all at tick
`stageTarget actTick groups g₁ c₁ m`.

A final event `stageEvent actTick groups g c (middleDelays.length + 1)`
SPAWNS at the pop tick of its last middle stage,
`stageTarget actTick groups g c (middleDelays.length)`, and the three
finals of the capstone may spawn at DIFFERENT ticks. A plain backward
carry of the tick-`T` betweenness to one fixed tick therefore does not
typecheck: each event is only present in the queues after its own spawn
tick. This file proves the per-pair transport parameterized by the two
spawn ticks: betweenness in the tick-`T` due filter holds in the
tick-start queue at any tick after BOTH spawn ticks and no later than
`T`. Membership at that tick is unconditional (SuccessorMembershipRange).

## Lemmas

* `stageTarget_lt_T_of_middleLen` — the stage-`m` pop tick of a chain
  with `m` middle delays is strictly before the common output tick.
* `evBefore_final_backward_to_tick` — the core pair transport from the
  tick-`T` due filter to the tick-start queue at tick `a`, discharging
  membership at `a` via SuccessorMembershipRange.

FinalsBackwardTransportII specializes `a` to the reference pop tick plus one (the drain
queue of `preStepWorld`), FinalsBackwardTransportIII steps further back into the post-burst
queue, and MiddleFinalSpawnTick proves that the middle final's spawn tick must in
fact equal the reference pop tick. -/

/-- The stage-`m` pop tick of a chain with exactly `m` middle delays is
    strictly before the common output tick `T`: the final stage still
    adds a positive delay on top. -/
theorem stageTarget_lt_T_of_middleLen (groups : List GroupSpec)
    (actTick : Nat → Nat) (T g c m : Nat)
    (h_g : g < groups.length) (h_c : c < (groupAt groups g).length)
    (h_uniform : ∀ gi (c₁ c₂ : ChainSpec), gi < groups.length →
        c₁ ∈ groupAt groups gi → c₂ ∈ groupAt groups gi →
        chainDelay c₁ = chainDelay c₂)
    (h_act : ∀ gi, gi < groups.length → groupAt groups gi ≠ [] →
        actTick gi + groupDelay (groupAt groups gi) = T)
    (h_m : (chainAt groups g c).middleDelays.length = m) :
    stageTarget actTick groups g c m < T := by
  rw [← stageTarget_final_eq_T groups actTick T g c h_g h_c
    h_uniform h_act]
  rw [show (chainAt groups g c).middleDelays.length + 1 = m + 1 by
    omega]
  exact stageTarget_lt_succ actTick groups g c m (by omega)

/-- Backward transport of betweenness for a pair of final-stage events.
    Betweenness in the tick-`T` due filter holds in the tick-start
    queue at any tick `a` after both spawn ticks (the stage targets of
    the last middle stages) and no later than `T`. Membership at `a`
    comes from SuccessorMembershipRange; both events target `T` (StageEventCompleteness), so BackwardTransport's
    backward transport applies. -/
theorem evBefore_final_backward_to_tick (groups : List GroupSpec)
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
    (ga ca gb cb : Nat)
    (h_ga : ga < groups.length) (h_ca : ca < (groupAt groups ga).length)
    (h_gb : gb < groups.length) (h_cb : cb < (groupAt groups gb).length)
    (a : Nat) (h_a_le : a ≤ T)
    (h_spawn_a : stageTarget actTick groups ga ca
        ((chainAt groups ga ca).middleDelays.length) < a)
    (h_spawn_b : stageTarget actTick groups gb cb
        ((chainAt groups gb cb).middleDelays.length) < a)
    (h_ne : stageEvent actTick groups ga ca
        ((chainAt groups ga ca).middleDelays.length + 1) ≠
      stageEvent actTick groups gb cb
        ((chainAt groups gb cb).middleDelays.length + 1))
    (h_due : evBefore
        ((gSimWorld groups actTick groupOrd withinOrd pos T).events.filter
          (fun ev => ev.targetTick == T))
        (stageEvent actTick groups ga ca
          ((chainAt groups ga ca).middleDelays.length + 1))
        (stageEvent actTick groups gb cb
          ((chainAt groups gb cb).middleDelays.length + 1))) :
    evBefore
      (gSimWorld groups actTick groupOrd withinOrd pos a).events
      (stageEvent actTick groups ga ca
        ((chainAt groups ga ca).middleDelays.length + 1))
      (stageEvent actTick groups gb cb
        ((chainAt groups gb cb).middleDelays.length + 1)) := by
  set fa := stageEvent actTick groups ga ca
    ((chainAt groups ga ca).middleDelays.length + 1)
  set fb := stageEvent actTick groups gb cb
    ((chainAt groups gb cb).middleDelays.length + 1)
  -- both final stages target the common output tick
  have h_Ta : stageTarget actTick groups ga ca
      ((chainAt groups ga ca).middleDelays.length + 1) = T :=
    stageTarget_final_eq_T groups actTick T ga ca h_ga h_ca
      h_uniform h_act
  have h_Tb : stageTarget actTick groups gb cb
      ((chainAt groups gb cb).middleDelays.length + 1) = T :=
    stageTarget_final_eq_T groups actTick T gb cb h_gb h_cb
      h_uniform h_act
  -- both events sit in the tick-a queue
  have h_mem_a : fa ∈
      (gSimWorld groups actTick groupOrd withinOrd pos a).events :=
    stageEvent_succ_mem_range_complete groups actTick groupOrd withinOrd
      pos h_valid h_ord h_within ga ca
      ((chainAt groups ga ca).middleDelays.length) h_ga h_ca (by omega) a
      (Nat.succ_le_of_lt h_spawn_a) (by rw [h_Ta]; exact h_a_le)
  have h_mem_b : fb ∈
      (gSimWorld groups actTick groupOrd withinOrd pos a).events :=
    stageEvent_succ_mem_range_complete groups actTick groupOrd withinOrd
      pos h_valid h_ord h_within gb cb
      ((chainAt groups gb cb).middleDelays.length) h_gb h_cb (by omega) a
      (Nat.succ_le_of_lt h_spawn_b) (by rw [h_Tb]; exact h_a_le)
  -- backward transport from the due filter at T
  exact evBefore_due_filter_backward groups actTick groupOrd withinOrd pos
    (Nodup.of_perm h_ord List.nodup_range)
    (fun gi h_gi => Nodup.of_perm (h_within gi h_gi) List.nodup_range)
    T a h_a_le fa fb h_due h_mem_a h_mem_b h_ne
    (by dsimp [fa, stageEvent]; rw [h_Ta])
    (by dsimp [fb, stageEvent]; rw [h_Tb])
