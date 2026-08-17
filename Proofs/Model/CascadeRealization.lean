import Proofs.Model.Basic
import Proofs.Model.SimLemmas
import Proofs.Model.WorldInvariants
import Proofs.Model.Cascade
import Mathlib.Data.List.Defs
import Mathlib.Data.List.Basic
import Mathlib.Tactic


open BasicRedstoneSim
open World

/-! # Cascade realization

Connecting the simulation to `chainTickList`: activating a chain makes its
events fire in order and the output log at `activation tick + chainDelay`. -/

/-- `activateChain` appends exactly the observer's own-tick event. -/
theorem activateChain_events (w : World) (obs : Nat) :
    (activateChain w obs).events =
      w.events ++ [{ targetTick := w.tick + 2, priority := 0,
                     nodeId := obs }] := by
  dsimp [activateChain, scheduleEvent]

/-- A neighbor update of a repeater schedules exactly one delayed event. -/
theorem onNeighborUpdate_repeater_events (w : World) (id : Nat) (nd : NodeData)
    (d : PNat) (p : Int) (hget : w.getNode id = some nd)
    (hkind : nd.kind = NodeKind.repeater d p) :
    (w.onNeighborUpdate id).events =
      w.events ++ [{ targetTick := w.tick + (d : Nat), priority := p,
                     nodeId := id }] := by
  have hon : w.onNeighborUpdate id =
      w.scheduleEvent { targetTick := w.tick + (d : Nat), priority := p,
                        nodeId := id } := by
    dsimp [onNeighborUpdate]
    simp [hget, hkind]
  rw [hon]
  simp

/-- A neighbor update of an output node adds no events (it only logs). -/
theorem onNeighborUpdate_output_events (w : World) (id : Nat) (nd : NodeData)
    (name : String) (hget : w.getNode id = some nd)
    (hkind : nd.kind = .output name) :
    (w.onNeighborUpdate id).events = w.events := by
  have hon : w.onNeighborUpdate id =
      w.logOutput s!"{name}: {w.getInputSignal id}" := by
    dsimp [onNeighborUpdate]
    simp [hget, hkind]
  rw [hon]
  simp

/-- Firing an observer schedules its single output repeater. -/
theorem onScheduledTick_observer_schedules (w : World) (obs firstRep : Nat)
    (ndObs ndRep : NodeData) (d : PNat) (p : Int)
    (hne : firstRep ≠ obs)
    (hgetObs : w.getNode obs = some ndObs)
    (hkindObs : ndObs.kind = .observer)
    (houtsObs : ndObs.outputs = [firstRep])
    (hgetRep : w.getNode firstRep = some ndRep)
    (hkindRep : ndRep.kind = NodeKind.repeater d p) :
    (w.onScheduledTick obs).events =
      w.events ++ [{ targetTick := w.tick + (d : Nat), priority := p,
                     nodeId := firstRep }] := by
  set w1 := w.updateNode obs (fun nd => { nd with sigLevel := 15 }) with hw1
  have h1 : w.onScheduledTick obs = w1.notifyOutputs obs := by
    dsimp [onScheduledTick, w1]
    simp [hgetObs, hkindObs]
  rw [h1]
  have hgetObs1 : w1.getNode obs = some { ndObs with sigLevel := 15 } := by
    dsimp [w1]
    rw [getNode_updateNode_map, hgetObs]
    simp
  have hnotify : w1.notifyOutputs obs = w1.onNeighborUpdate firstRep := by
    dsimp [notifyOutputs]
    rw [hgetObs1]
    simp [houtsObs]
  rw [hnotify]
  have hgetRep1 : w1.getNode firstRep = some ndRep := by
    dsimp [w1]
    rw [getNode_updateNode_ne w obs firstRep
      (fun nd => { nd with sigLevel := 15 }) hne]
    exact hgetRep
  have hon : w1.onNeighborUpdate firstRep =
      w1.scheduleEvent { targetTick := w1.tick + (d : Nat), priority := p,
                         nodeId := firstRep } := by
    dsimp [onNeighborUpdate]
    simp [hgetRep1, hkindRep]
  rw [hon]
  simp [w1, scheduleEvent]

/-- Firing a repeater reduces to notifying its single output node. -/
theorem onScheduledTick_repeater_notify (w : World) (rep nextNode : Nat)
    (ndRep : NodeData) (delay : PNat) (pri : Int)
    (hgetRep : w.getNode rep = some ndRep)
    (hkindRep : ndRep.kind = NodeKind.repeater delay pri)
    (houtsRep : ndRep.outputs = [nextNode]) :
    w.onScheduledTick rep =
      ((w.updateNode rep (fun nd =>
          { nd with sigLevel := if w.getInputSignal rep > 0 then 15 else 0 }))
        ).onNeighborUpdate nextNode := by
  set w1 := w.updateNode rep (fun nd =>
    { nd with sigLevel := if w.getInputSignal rep > 0 then 15 else 0 }) with hw1
  have h1 : w.onScheduledTick rep = w1.notifyOutputs rep := by
    dsimp [onScheduledTick, w1]
    simp [hgetRep, hkindRep]
  have hgetRep1 : w1.getNode rep =
      some { ndRep with sigLevel := if w.getInputSignal rep > 0 then 15 else 0 } := by
    dsimp [w1]
    rw [getNode_updateNode_map, hgetRep]
    simp
  have hnotify : w1.notifyOutputs rep = w1.onNeighborUpdate nextNode := by
    dsimp [notifyOutputs]
    rw [hgetRep1]
    simp [houtsRep]
  rw [h1, hnotify]

/-- Firing a middle repeater schedules the next repeater's event. -/
theorem onScheduledTick_repeater_schedules_next (w : World) (rep nextRep : Nat)
    (ndRep ndNext : NodeData) (delay : PNat) (pri nextPri : Int)
    (nextDelay : PNat) (hne : nextRep ≠ rep)
    (hgetRep : w.getNode rep = some ndRep)
    (hkindRep : ndRep.kind = NodeKind.repeater delay pri)
    (houtsRep : ndRep.outputs = [nextRep])
    (hgetNext : w.getNode nextRep = some ndNext)
    (hkindNext : ndNext.kind = NodeKind.repeater nextDelay nextPri) :
    (w.onScheduledTick rep).events =
      w.events ++ [{ targetTick := w.tick + (nextDelay : Nat),
                     priority := nextPri, nodeId := nextRep }] := by
  set w1 := w.updateNode rep (fun nd =>
    { nd with sigLevel := if w.getInputSignal rep > 0 then 15 else 0 }) with hw1
  rw [onScheduledTick_repeater_notify w rep nextRep ndRep delay pri
    hgetRep hkindRep houtsRep]
  have hgetNext1 : w1.getNode nextRep = some ndNext := by
    dsimp [w1]
    rw [getNode_updateNode_ne w rep nextRep
      (fun nd => { nd with sigLevel := if w.getInputSignal rep > 0 then 15 else 0 })
      hne]
    exact hgetNext
  rw [onNeighborUpdate_repeater_events w1 nextRep ndNext nextDelay nextPri
    hgetNext1 hkindNext]
  simp [w1]

/-- Firing the last repeater appends the output's log entry and adds no
    events. -/
theorem onScheduledTick_lastRep_logs (w : World) (lastRep outputNode : Nat)
    (ndLast ndOut : NodeData) (lastDelay : PNat) (lastPri : Int) (name : String)
    (hne : outputNode ≠ lastRep)
    (hgetLast : w.getNode lastRep = some ndLast)
    (hkindLast : ndLast.kind = NodeKind.repeater lastDelay lastPri)
    (houtsLast : ndLast.outputs = [outputNode])
    (hgetOut : w.getNode outputNode = some ndOut)
    (hkindOut : ndOut.kind = .output name) :
    ∃ msg, (w.onScheduledTick lastRep).outputLog = w.outputLog ++ [msg] ∧
      (w.onScheduledTick lastRep).events = w.events := by
  set w1 := w.updateNode lastRep (fun nd =>
    { nd with sigLevel := if w.getInputSignal lastRep > 0 then 15 else 0 })
    with hw1
  rw [onScheduledTick_repeater_notify w lastRep outputNode ndLast lastDelay
    lastPri hgetLast hkindLast houtsLast]
  have hgetOut1 : w1.getNode outputNode = some ndOut := by
    dsimp [w1]
    rw [getNode_updateNode_ne w lastRep outputNode
      (fun nd => { nd with sigLevel := if w.getInputSignal lastRep > 0 then 15 else 0 })
      hne]
    exact hgetOut
  have hon : w1.onNeighborUpdate outputNode =
      w1.logOutput s!"{name}: {w1.getInputSignal outputNode}" := by
    dsimp [onNeighborUpdate]
    simp [hgetOut1, hkindOut]
  rw [hon]
  refine ⟨s!"{name}: {w1.getInputSignal outputNode}", ?_, ?_⟩
  · simp [w1, logOutput, World.updateNode]
  · simp [w1]

/-- Firing a middle repeater adds no log entries. -/
theorem onScheduledTick_repeater_outputLog (w : World) (rep nextNode : Nat)
    (ndRep ndNext : NodeData) (delay : PNat) (pri nextPri : Int)
    (nextDelay : PNat) (hne : nextNode ≠ rep)
    (hgetRep : w.getNode rep = some ndRep)
    (hkindRep : ndRep.kind = NodeKind.repeater delay pri)
    (houtsRep : ndRep.outputs = [nextNode])
    (hgetNext : w.getNode nextNode = some ndNext)
    (hkindNext : ndNext.kind = NodeKind.repeater nextDelay nextPri) :
    (w.onScheduledTick rep).outputLog = w.outputLog := by
  set w1 := w.updateNode rep (fun nd =>
    { nd with sigLevel := if w.getInputSignal rep > 0 then 15 else 0 })
    with hw1
  rw [onScheduledTick_repeater_notify w rep nextNode ndRep delay pri
    hgetRep hkindRep houtsRep]
  have hgetNext1 : w1.getNode nextNode = some ndNext := by
    dsimp [w1]
    rw [getNode_updateNode_ne w rep nextNode
      (fun nd => { nd with sigLevel := if w.getInputSignal rep > 0 then 15 else 0 })
      hne]
    exact hgetNext
  have hon : w1.onNeighborUpdate nextNode =
      w1.scheduleEvent
        { targetTick := w1.tick + (nextDelay : Nat), priority := nextPri,
          nodeId := nextNode } := by
    dsimp [onNeighborUpdate]
    simp [hgetNext1, hkindNext]
  rw [hon]
  simp [w1, World.updateNode]

/-! ## Node frame facts

Firing or notifying a node never disturbs the node list itself; only the
fired node's lookup changes. These feed the frame/locality obligations of
`stepUntilNextTick_uniform_drain`. -/

/-- `onNeighborUpdate` does not change the node list. -/
theorem onNeighborUpdate_nodes (w : World) (id : Nat) :
    (w.onNeighborUpdate id).nodes = w.nodes := by
  dsimp [onNeighborUpdate]
  split
  · rfl
  · split <;> rfl

/-- A foldl of `onNeighborUpdate` does not change the node list. -/
theorem foldl_onNeighborUpdate_nodes (l : List Nat) (w : World) :
    (l.foldl (fun w' outId => w'.onNeighborUpdate outId) w).nodes =
      w.nodes := by
  induction l generalizing w with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    rw [ih (w.onNeighborUpdate hd), onNeighborUpdate_nodes]

/-- `notifyOutputs` does not change the node list. -/
theorem notifyOutputs_nodes (w : World) (id : Nat) :
    (w.notifyOutputs id).nodes = w.nodes := by
  dsimp [notifyOutputs]
  split
  · rfl
  · exact foldl_onNeighborUpdate_nodes _ _

/-- `getNode` depends only on `nodes`. -/
theorem World.getNode_of_nodes_eq (w₁ w₂ : World)
    (h : w₁.nodes = w₂.nodes) (id : Nat) :
    w₁.getNode id = w₂.getNode id := by
  dsimp [World.getNode]
  rw [h]

/-- Firing a scheduled tick changes no other node's lookup. -/
theorem onScheduledTick_getNode_of_ne (w : World) (fired id : Nat)
    (hne : id ≠ fired) :
    (w.onScheduledTick fired).getNode id = w.getNode id := by
  dsimp [onScheduledTick]
  split
  · rfl
  · rename_i nd hget
    cases hkind : nd.kind
    · rfl
    · rfl
    · dsimp
      rw [World.getNode_of_nodes_eq _ _ (notifyOutputs_nodes _ _)]
      exact getNode_updateNode_ne w fired id _ hne
    · dsimp
      rw [World.getNode_of_nodes_eq _ _ (notifyOutputs_nodes _ _)]
      exact getNode_updateNode_ne w fired id _ hne
