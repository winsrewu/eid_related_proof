import BasicProofs.GroupClustering.ForwardTransport

open BasicRedstoneSim List

/-! # Group clustering — public preStepWorld facts

Public versions of two facts about `preStepWorld` (the post-burst,
pre-drain world at a stage's pop tick) that ForwardTransport keeps private. The
base-case assembly needs them to relate the tick-start queue at
`stageTarget j + 1` to the drain of `preStepWorld j`, and to know the
tick of `preStepWorld j`. -/

/-- The tick-`(τ + 1)` queue is the drain of the post-burst world at the
    pop tick `τ = stageTarget j`. -/
theorem gSimWorld_succ_events_eq_preStepWorld (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (g₁ c₁ j : Nat) :
    (gSimWorld groups actTick groupOrd withinOrd pos
        (stageTarget actTick groups g₁ c₁ j + 1)).events =
    (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ j).stepUntilNextTick.events := by
  dsimp [gSimWorld, preStepWorld, popQueueWorld, popActive]
  set t := stageTarget actTick groups g₁ c₁ j
  simp only [gSimFoldl, List.range_succ, List.foldl_append, List.foldl_cons,
    List.foldl_nil]
  set W : World := List.foldl
    (gSimBody actTick (buildGroups groups).2 groupOrd withinOrd pos)
    (buildGroups groups).1 (List.range t)
  have h_tick_W : W.tick = t := by
    change (gSimFoldl actTick (buildGroups groups).2 groupOrd withinOrd pos
      (buildGroups groups).1 t).tick = t
    rw [gSimFoldl_tick, buildGroups_tick]
    omega
  dsimp [gSimBody]
  simp only [h_tick_W]
  split_ifs with h_active
  · have h_act_nil : groupOrd.filter (fun gi =>
        decide (gi < (buildGroups groups).2.length) && (actTick gi == t)) = [] := by
      simpa using h_active
    rw [h_act_nil]
    simp [gSimBurst]
  · rfl

/-- The post-burst world at the pop tick of stage `j` has tick
    `stageTarget j`. -/
theorem preStepWorld_tick_eq (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (g₁ c₁ j : Nat) :
    (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ j).tick =
      stageTarget actTick groups g₁ c₁ j := by
  dsimp [preStepWorld, popQueueWorld]
  rw [gSimBurst_tick, World.logOutput_tick, gSimWorld_tick]
