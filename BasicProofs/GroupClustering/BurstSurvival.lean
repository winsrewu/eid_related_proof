import BasicProofs.GroupClustering.QSideOrder
import BasicProofs.GroupClustering.LockstepComposition

open BasicRedstoneSim List

/-! # Group clustering — burst survival for Q-side order preservation

QSideOrder assembles the Q-side order-preservation lemma but keeps the
burst-survival premise `h_surv` as an explicit hypothesis. This file
investigates when stage events survive the burst phase.

## Key insight

At stage `k`, the reference event `stageEvent k` is DUE at the pop tick
`stageTarget k`. The burst phase processes due events via
`processNEvents`, which pops them. If the event is among the first
`(pos t)[k']` due events, it gets popped and does NOT survive in
`preStepWorld k`.

However, when a due event is popped, it fires and spawns its successor.
The successor `stageEvent (k+1)` has `targetTick = stageTarget (k+1)`
which is strictly greater than `stageTarget k`. So the successor is
non-due at the burst tick and survives via `mem_gSimBurst_of_notDue`.

## Approach

Instead of proving unconditional survival of `stageEvent k`, we prove:

1. **Successor membership**: when `stageEvent k` is popped by the burst,
   its successor `stageEvent (k+1)` appears in `preStepWorld k`.
2. **Reformulated survival**: a survival hypothesis that works with
   successors rather than the reference events themselves.

This allows the order-preservation argument to proceed by tracking
successors through the burst phase.
-/

/-! ## Successor events survive the burst -/

/-- A non-due event survives the burst phase. This is a direct
    application of `mem_gSimBurst_of_notDue` from LockstepComposition. -/
theorem mem_preStepWorld_of_notDue (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (g₁ c₁ j : Nat)
    (x : ScheduledEvent)
    (h_x : x ∈ (popQueueWorld groups actTick groupOrd withinOrd pos g₁ c₁ j).events)
    (h_nd : x.targetTick ≠ stageTarget actTick groups g₁ c₁ j) :
    x ∈ (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ j).events := by
  dsimp [preStepWorld, popQueueWorld, popActive]
  set t := stageTarget actTick groups g₁ c₁ j
  set W : World := gSimWorld groups actTick groupOrd withinOrd pos t
  set W₁ : World := W.logOutput s!"tick {t}"
  set active : List Nat := groupOrd.filter (fun gi =>
    decide (gi < (buildGroups groups).2.length) && (actTick gi == t))
  have h_tick_W : W.tick = t := by
    change (gSimFoldl actTick (buildGroups groups).2 groupOrd withinOrd pos
      (buildGroups groups).1 t).tick = t
    rw [gSimFoldl_tick, buildGroups_tick]
    omega
  have h_tick_W₁ : W₁.tick = t := by
    unfold W₁
    exact World.logOutput_tick W s!"tick {t}" ▸ h_tick_W
  have h_x_W₁ : x ∈ W₁.events := by
    unfold W₁
    exact World.logOutput_events W s!"tick {t}" ▸ h_x
  have h_nd_W₁ : x.targetTick ≠ W₁.tick := by
    rw [h_tick_W₁]
    exact h_nd
  change x ∈ (gSimBurst t (buildGroups groups).2 withinOrd pos W₁
    (active.zipIdx)).events
  exact mem_gSimBurst_of_notDue t (buildGroups groups).2 withinOrd pos W₁
    (active.zipIdx) x h_x_W₁ h_nd_W₁

/-! ## What remains for full h_surv discharge -/

/-
The full proof of `h_surv` requires showing that when `stageEvent k`
is popped by the burst, its successor `stageEvent (k+1)` appears in
`preStepWorld k`. The proof outline is:

1. **Spawning**: when `stageEvent k` fires via `onScheduledTick`, it
   spawns an event for the next node in the chain. This spawned event
   has the structure of `stageEvent (k+1)`.

2. **Membership after processNEvents**: the spawned event is appended
   to the events list during `processNEvents`. Since it is non-due
   (targetTick > current tick), it survives the remaining pops.

3. **Survival through activateGroup**: the spawned event survives
   `activateGroup` which only appends observer events.

4. **Survival through the rest of the burst**: the spawned event
   survives the remaining burst segments via `mem_gSimBurst_of_notDue`.

The key missing lemma is:

**stageEvent_succ_mem_after_pop**: if `stageEvent k` is popped by
`processNEvents w m` (i.e., it is among the first `m` due events),
then `stageEvent (k+1)` is in `(processNEvents w m).events`.

This requires:
- Expanding the definition of `stageEvent` to show it is a repeater
- Using `onScheduledTick_repeater_spawns` to show the spawn structure
- Proving the spawn equals `stageEvent (k+1)` by matching targetTick,
  priority, and nodeId

Once this lemma is proved, the full `stageEvent_succ_mem_preStepWorld`
follows by composing with `mem_gSimBurst_of_notDue`.

The reformulated survival hypothesis would then state:

**h_surv_reformulated**: for every stage `k`, either `stageEvent k`
survives the burst (not popped), or `stageEvent (k+1)` is in
`preStepWorld k` (spawned by the pop).

This allows the order-preservation induction to track successors
through the burst phase, applying the lockstep property at the
successor level rather than the reference level.
-/
