import BasicProofs.GroupClustering.BurstSurvival
import BasicProofs.GroupClustering.LockstepComposition

open BasicRedstoneSim List

/-! # Group clustering — spawned successors survive processNEvents and the
burst phase

When a due stage-j event fires during the tick, it spawns the stage-(j+1)
event. The successor has a strictly later target tick, so it is non-due at
the current tick. Non-due events survive both `processNEvents` and
`gSimBurst`.

This file composes the spawn characterization of SameSpecLockstep (`stage_spawn`)
with the survival lemmas of LockstepComposition (`processNEvents_spawn_mem`,
`gSimBurst_spawn_mem`) and the non-due growth of stage targets
(`stageTarget_lt_succ`).

Contents:

* `stageEvent_succ_mem_after_step` — a single step that pops stage-j
  appends stage-(j+1) to the events list;
* `stageEvent_succ_mem_processNEvents` — when `processNEvents` pops a
  stage-j event, stage-(j+1) is in the result;
* `stageEvent_succ_mem_preStepWorld` — when the burst phase pops a
  stage-j event, stage-(j+1) is in `preStepWorld`.
-/

/-! ## Helpers -/

/-- `NodeLayoutOk` holds at every tick-start world. Reproved here because
    the QSideOrder version is private. -/
private theorem NodeLayoutOk_gSimWorld (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (t : Nat) :
    NodeLayoutOk groups
      (gSimWorld groups actTick groupOrd withinOrd pos t) := by
  dsimp [gSimWorld]
  exact NodeLayoutOk_gSimFoldl groups actTick (buildGroups groups).2 groupOrd
    withinOrd pos (buildGroups groups).1 t (NodeLayoutOk_buildGroups groups)

/-- `NodeLayoutOk` holds at every pop-queue world. -/
private theorem NodeLayoutOk_popQueueWorld (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (g₁ c₁ j : Nat) :
    NodeLayoutOk groups
      (popQueueWorld groups actTick groupOrd withinOrd pos g₁ c₁ j) := by
  dsimp [popQueueWorld]
  exact NodeLayoutOk_gSimWorld groups actTick groupOrd withinOrd pos
    (stageTarget actTick groups g₁ c₁ j)

/-! ## Successor membership after a single step -/

/-- When `w.step` pops `stageEvent j`, the result contains
    `stageEvent (j + 1)`. The spawn equation comes from `stage_spawn`. -/
theorem stageEvent_succ_mem_after_step (groups : List GroupSpec)
    (actTick : Nat → Nat) (w : World) (gi ci j : Nat)
    (h_gi : gi < groups.length) (h_ci : ci < (groupAt groups gi).length)
    (h_j : j ≤ (chainAt groups gi ci).middleDelays.length)
    (h_tick : w.tick = stageTarget actTick groups gi ci j)
    (h_layout : NodeLayoutOk groups w)
    (w_pop : World) (ev : ScheduledEvent)
    (h_pop : w.popNextEvent = some (ev, w_pop))
    (h_ev : ev = stageEvent actTick groups gi ci j) :
    stageEvent actTick groups gi ci (j + 1) ∈
      (w_pop.onScheduledTick ev.nodeId).events := by
  have h_tick_pop : w_pop.tick = w.tick :=
    World.popNextEvent_tick w ev w_pop h_pop
  have h_layout_pop : NodeLayoutOk groups w_pop :=
    NodeLayoutOk_of_nodes_eq groups w w_pop
      (World.popNextEvent_nodes w ev w_pop h_pop) h_layout
  have h_tick_pop_full : w_pop.tick = stageTarget actTick groups gi ci j := by
    rw [h_tick_pop, h_tick]
  have h_nodeId : ev.nodeId = chainBaseId groups gi ci + 1 + j := by
    rw [h_ev]
    rfl
  have h_spawn := stage_spawn groups actTick w_pop gi ci j h_gi h_ci h_j
    h_tick_pop_full h_layout_pop
  -- h_spawn: (w_pop.onScheduledTick (chainBaseId + 1 + j)).events =
  --          w_pop.events ++ [stageEvent(j+1)]
  -- Replace ev.nodeId in the goal with chainBaseId + 1 + j
  rw [h_nodeId]
  rw [h_spawn]
  exact List.mem_append_right _ (by simp)

/-! ## Successor membership after processNEvents -/

/-- The successor stage-(j+1) is non-due at tick `stageTarget j`. -/
private theorem stageSucc_notDue (actTick : Nat → Nat) (groups : List GroupSpec)
    (gi ci j : Nat)
    (h_j : j ≤ (chainAt groups gi ci).middleDelays.length)
    (t : Nat) (h_t : t = stageTarget actTick groups gi ci j) :
    (stageEvent actTick groups gi ci (j + 1)).targetTick ≠ t := by
  dsimp [stageEvent]
  intro h_eq
  have h_lt := stageTarget_lt_succ actTick groups gi ci j h_j
  rw [← h_t] at h_lt
  omega

/-- When `processNEvents` pops a stage-j event, its successor
    stage-(j+1) is in the resulting queue. Direct application of
    `processNEvents_spawn_mem` with the spawn equation from
    `stage_spawn`. -/
theorem stageEvent_succ_mem_processNEvents (groups : List GroupSpec)
    (actTick : Nat → Nat) (w : World) (n gi ci j : Nat)
    (h_gi : gi < groups.length) (h_ci : ci < (groupAt groups gi).length)
    (h_j : j ≤ (chainAt groups gi ci).middleDelays.length)
    (h_layout : NodeLayoutOk groups w)
    (h_tick : w.tick = stageTarget actTick groups gi ci j)
    (h_mem : stageEvent actTick groups gi ci j ∈ w.events)
    (h_gone : stageEvent actTick groups gi ci j ∉
      (processNEvents w n).events) :
    stageEvent actTick groups gi ci (j + 1) ∈
      (processNEvents w n).events := by
  set e := stageEvent actTick groups gi ci j
  set s := stageEvent actTick groups gi ci (j + 1)
  have h_e_due : e.targetTick = w.tick := by
    dsimp [e, stageEvent]; rw [h_tick]
  have h_s_nd : s.targetTick ≠ w.tick :=
    stageSucc_notDue actTick groups gi ci j h_j w.tick h_tick
  have h_spawn : ∀ (v : World), v.tick = w.tick → NodeLayoutOk groups v →
      (v.onScheduledTick e.nodeId).events = v.events ++ [s] := by
    intro v h_v h_layout_v
    have h_v_tick : v.tick = stageTarget actTick groups gi ci j := by
      rw [h_v, h_tick]
    dsimp [e, stageEvent]
    exact stage_spawn groups actTick v gi ci j h_gi h_ci h_j h_v_tick
      h_layout_v
  exact processNEvents_spawn_mem groups w n e s h_layout
    (by dsimp [e]; exact h_mem) (by dsimp [e]; exact h_e_due)
    (by dsimp [e] at h_gone; exact h_gone) (by dsimp [s]; exact h_s_nd)
    h_spawn

/-! ## Successor membership in preStepWorld -/

/-- When the burst phase pops a stage-j event, its successor
    stage-(j+1) is in `preStepWorld`. Composes `gSimBurst_spawn_mem`
    with `stage_spawn` and `stageTarget_lt_succ`. -/
theorem stageEvent_succ_mem_preStepWorld (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (g₁ c₁ j : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_j : j ≤ (chainAt groups g₁ c₁).middleDelays.length)
    (h_mem : stageEvent actTick groups g₁ c₁ j ∈
      (popQueueWorld groups actTick groupOrd withinOrd pos g₁ c₁ j).events)
    (h_gone : stageEvent actTick groups g₁ c₁ j ∉
      (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ j).events) :
    stageEvent actTick groups g₁ c₁ (j + 1) ∈
      (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ j).events := by
  dsimp [preStepWorld, popQueueWorld, popActive] at *
  set t := stageTarget actTick groups g₁ c₁ j
  set W : World := gSimWorld groups actTick groupOrd withinOrd pos t
  set W₁ : World := W.logOutput s!"tick {t}"
  set active : List Nat := groupOrd.filter (fun gi =>
    decide (gi < (buildGroups groups).2.length) && (actTick gi == t))
  set e := stageEvent actTick groups g₁ c₁ j
  set s := stageEvent actTick groups g₁ c₁ (j + 1)
  -- tick and layout for W
  have h_tick_W : W.tick = t := by
    change (gSimFoldl actTick (buildGroups groups).2 groupOrd withinOrd pos
      (buildGroups groups).1 t).tick = t
    rw [gSimFoldl_tick, buildGroups_tick]
    omega
  have h_layout_W : NodeLayoutOk groups W :=
    NodeLayoutOk_gSimWorld groups actTick groupOrd withinOrd pos t
  -- tick and layout for W₁
  have h_tick_W₁ : W₁.tick = t := by
    unfold W₁
    exact World.logOutput_tick W s!"tick {t}" ▸ h_tick_W
  have h_layout_W₁ : NodeLayoutOk groups W₁ :=
    NodeLayoutOk_logOutput groups W s!"tick {t}" h_layout_W
  -- membership and due-ness of e in W₁
  have h_e_W₁ : e ∈ W₁.events := by
    unfold W₁
    dsimp [e, stageEvent]
    exact World.logOutput_events W s!"tick {t}" ▸ h_mem
  have h_e_due : e.targetTick = W₁.tick := by
    dsimp [e, stageEvent]; rw [h_tick_W₁]
  -- non-due of successor
  have h_s_nd : s.targetTick ≠ W₁.tick := by
    dsimp [s, stageEvent]
    rw [h_tick_W₁]
    exact stageSucc_notDue actTick groups g₁ c₁ j h_j t rfl
  -- spawn equation
  have h_spawn : ∀ (v : World), v.tick = W₁.tick → NodeLayoutOk groups v →
      (v.onScheduledTick e.nodeId).events = v.events ++ [s] := by
    intro v h_v h_layout_v
    have h_v_tick : v.tick = stageTarget actTick groups g₁ c₁ j := by
      rw [h_v, h_tick_W₁]
    dsimp [e, s, stageEvent]
    exact stage_spawn groups actTick v g₁ c₁ j h_g₁ h_c₁ h_j h_v_tick
      h_layout_v
  -- apply gSimBurst_spawn_mem
  change s ∈ (gSimBurst t (buildGroups groups).2 withinOrd pos W₁
    (active.zipIdx)).events
  change e ∉ (gSimBurst t (buildGroups groups).2 withinOrd pos W₁
    (active.zipIdx)).events at h_gone
  refine gSimBurst_spawn_mem groups t (buildGroups groups).2 withinOrd pos W₁
    (active.zipIdx) e s h_layout_W₁ h_e_W₁ h_e_due h_gone h_s_nd h_spawn
