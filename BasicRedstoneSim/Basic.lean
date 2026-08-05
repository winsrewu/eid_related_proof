import Mathlib.Data.PNat.Defs

namespace BasicRedstoneSim

/-! # Node Kinds

Models the different types of redstone components in the simulation. -/
inductive NodeKind
  | input
  | output (name : String)
  | repeater (delay : PNat) (priority : Int)
  | observer
  deriving Repr, Inhabited, BEq, DecidableEq

/-! # Node Data

Each node has a kind, signal level, and lists of input/output node IDs.
Instead of object references, we use `Nat` IDs to index into the world's node list. -/
structure NodeData where
  kind : NodeKind
  sigLevel : Nat
  inputs : List Nat
  outputs : List Nat
  deriving Repr, Inhabited, BEq, DecidableEq

/-! # Scheduled Events

An event targets a specific tick, has a priority (lower = processed first),
and references a node by ID. -/
structure ScheduledEvent where
  targetTick : Nat
  priority : Int
  nodeId : Nat
  deriving Repr, BEq, DecidableEq

/-! # World State

The entire simulation state is immutable. All operations return new world states. -/
@[ext]
structure World where
  nodes : List (Nat × NodeData)
  events : List ScheduledEvent
  tick : Nat
  nextId : Nat
  outputLog : List String
  deriving Repr, BEq, DecidableEq

namespace World

/-- An empty world with no nodes, events, or output. -/
def empty : World :=
  { nodes := [], events := [], tick := 0, nextId := 0, outputLog := [] }

/-- Look up a node by ID. -/
def getNode (w : World) (id : Nat) : Option NodeData :=
  match w.nodes.find? (fun (nid, _) => nid == id) with
  | some (_, nd) => some nd
  | none => none

/-- Apply a function to a specific node, returning a new world. -/
def updateNode (w : World) (id : Nat) (f : NodeData → NodeData) : World :=
  { w with
    nodes := w.nodes.map (fun (nid, nd) =>
      if nid == id then (nid, f nd) else (nid, nd)) }

@[simp] theorem updateNode_events (w : World) (id : Nat) (f : NodeData → NodeData) :
    (w.updateNode id f).events = w.events := rfl

@[simp] theorem updateNode_tick (w : World) (id : Nat) (f : NodeData → NodeData) :
    (w.updateNode id f).tick = w.tick := rfl

/-- Add a new node, returning its assigned ID and the updated world. -/
def addNode (w : World) (nd : NodeData) : Nat × World :=
  (w.nextId, { w with nodes := w.nodes ++ [(w.nextId, nd)], nextId := w.nextId + 1 })

/-- Append a scheduled event to the event queue. -/
def scheduleEvent (w : World) (ev : ScheduledEvent) : World :=
  { w with events := w.events ++ [ev] }

@[simp] theorem scheduleEvent_events (w : World) (ev : ScheduledEvent) :
    (w.scheduleEvent ev).events = w.events ++ [ev] := rfl

@[simp] theorem scheduleEvent_tick (w : World) (ev : ScheduledEvent) :
    (w.scheduleEvent ev).tick = w.tick := rfl

@[simp] theorem scheduleEvent_nodes (w : World) (ev : ScheduledEvent) :
    (w.scheduleEvent ev).nodes = w.nodes := rfl

@[simp] theorem scheduleEvent_outputLog (w : World) (ev : ScheduledEvent) :
    (w.scheduleEvent ev).outputLog = w.outputLog := rfl

@[simp] theorem scheduleEvent_nextId (w : World) (ev : ScheduledEvent) :
    (w.scheduleEvent ev).nextId = w.nextId := rfl

/-- Append a message to the output log. -/
def logOutput (w : World) (msg : String) : World :=
  { w with outputLog := w.outputLog ++ [msg] }

@[simp] theorem logOutput_events (w : World) (msg : String) :
    (w.logOutput msg).events = w.events := rfl

@[simp] theorem logOutput_tick (w : World) (msg : String) :
    (w.logOutput msg).tick = w.tick := rfl

@[simp] theorem logOutput_nodes (w : World) (msg : String) :
    (w.logOutput msg).nodes = w.nodes := rfl

@[simp] theorem logOutput_nextId (w : World) (msg : String) :
    (w.logOutput msg).nextId = w.nextId := rfl

/-- Compute the input signal for a node: the max output signal across all its inputs. -/
def getInputSignal (w : World) (id : Nat) : Nat :=
  match w.getNode id with
  | none => 0
  | some nd =>
    nd.inputs.foldl (fun maxSig inputId =>
      match w.getNode inputId with
      | none => maxSig
      | some inputNd => max maxSig inputNd.sigLevel
    ) 0

/-- Handle a neighbor update for a specific node.
- Repeaters schedule a delayed event.
- Observers schedule an event at tick+2.
- Output nodes log their current input signal.
- Input nodes do nothing. -/
def onNeighborUpdate (w : World) (id : Nat) : World :=
  match w.getNode id with
  | none => w
  | some nd =>
    match nd.kind with
    | .repeater delay priority =>
      w.scheduleEvent { targetTick := w.tick + delay, priority := priority, nodeId := id }
    | .observer =>
      w.scheduleEvent { targetTick := w.tick + 2, priority := 0, nodeId := id }
    | .output name =>
      w.logOutput s!"{name}: {w.getInputSignal id}"
    | .input => w

/-- Notify all output nodes of a given node by calling `onNeighborUpdate` on each. -/
def notifyOutputs (w : World) (id : Nat) : World :=
  match w.getNode id with
  | none => w
  | some nd =>
    nd.outputs.foldl (fun w' outId => w'.onNeighborUpdate outId) w

/-- Handle a scheduled tick event for a specific node.
- Repeaters read input signal, set output to 15 or 0, then notify outputs.
- Observers set signal to 15 and notify outputs.
- Other node kinds do nothing. -/
def onScheduledTick (w : World) (nid : Nat) : World :=
  match w.getNode nid with
  | none => w
  | some nd =>
    match nd.kind with
    | .repeater _ _ =>
      let inputSig := w.getInputSignal nid
      let newLevel := if inputSig > 0 then 15 else 0
      let w' := w.updateNode nid (fun nd' => { nd' with sigLevel := newLevel })
      w'.notifyOutputs nid
    | .observer =>
      let w' := w.updateNode nid (fun nd' => { nd' with sigLevel := 15 })
      w'.notifyOutputs nid
    | _ => w

/-- Set the signal level of an input node and notify its outputs. -/
def setInput (w : World) (id : Nat) (level : Nat) : World :=
  let w' := w.updateNode id (fun nd => { nd with sigLevel := level })
  w'.notifyOutputs id

def countEventAtThisTick (w : World) (t : Nat) : Nat :=
  (w.events.filter (fun ev => ScheduledEvent.targetTick ev == t)).length

/-- Pop the next event for the current tick (lowest priority, first in list).
Returns the event and the updated world, or `none` if no events remain. -/
def popNextEvent (w : World) : Option (ScheduledEvent × World) :=
  let indexed := List.zip (List.range w.events.length) w.events
  let candidates := indexed.filter (fun (_, e) => e.targetTick == w.tick)
  if candidates.isEmpty then none
  else
    let minPri := candidates.foldl (fun acc (_, e) => min acc e.priority) (candidates.head?.map (fun (_, e) => e.priority) |>.getD 0)
    match candidates.find? (fun (_, e) => e.priority == minPri) with
    | none => none
    | some (idx, ev) => some (ev, { w with events := w.events.eraseIdx idx })

/-! ### Termination proof helpers -/

/-- Erasing an element satisfying `p` decreases the filter count by exactly 1. -/
private theorem List.filter_eraseIdx_length {α : Type} (l : List α) (i : Nat) (p : α → Bool)
    (h_lt : i < l.length) (h_p : p l[i] = true) :
    ((l.eraseIdx i).filter p).length + 1 = (l.filter p).length := by
  revert i h_lt h_p
  induction l with
  | nil => intro i h_lt; simp [List.length] at h_lt
  | cons hd tl ih =>
    intro i h_lt h_p
    cases i with
    | zero =>
      have h_p' : p hd = true := by simpa using h_p
      have h_f : (hd :: tl).filter p = hd :: tl.filter p := by simp [List.filter, h_p']
      simp [List.eraseIdx, h_f]
    | succ i' =>
      have h_lt' : i' < tl.length := by simp [List.length] at h_lt; omega
      have h_p' : p tl[i'] = true := by simpa using h_p
      have h_ih := ih i' h_lt' h_p'
      by_cases h_hd : p hd = true
      · simp [List.eraseIdx]
        have h1 : (hd :: tl).filter p = hd :: tl.filter p := by simp [List.filter, h_hd]
        have h2 : (hd :: tl.eraseIdx i').filter p = hd :: (tl.eraseIdx i').filter p := by
          simp [List.filter, h_hd]
        rw [h2, h1]; simp [List.length]; omega
      · simp [List.eraseIdx]
        have h1 : (hd :: tl).filter p = tl.filter p := by simp [List.filter, h_hd]
        have h2 : (hd :: tl.eraseIdx i').filter p = (tl.eraseIdx i').filter p := by
          simp [List.filter, h_hd]
        rw [h2, h1]; exact h_ih

/-- `onNeighborUpdate` preserves the tick. -/
private theorem onNeighborUpdate_tick (w : World) (id : Nat) :
    (w.onNeighborUpdate id).tick = w.tick := by
  unfold onNeighborUpdate
  split
  · rfl
  · split <;> rfl

/-- A foldl of `onNeighborUpdate` preserves the tick. -/
private theorem foldl_onNeighborUpdate_tick (l : List Nat) (w : World) :
    (l.foldl (fun w' outId => w'.onNeighborUpdate outId) w).tick = w.tick := by
  induction l generalizing w with
  | nil => rfl
  | cons hd tl ih => simp [List.foldl_cons]; rw [ih, onNeighborUpdate_tick]

/-- `notifyOutputs` preserves the tick. -/
private theorem notifyOutputs_tick (w : World) (id : Nat) :
    (w.notifyOutputs id).tick = w.tick := by
  unfold notifyOutputs; split
  · rfl
  · exact foldl_onNeighborUpdate_tick _ _

/-- `onScheduledTick` preserves the tick. -/
private theorem onScheduledTick_tick (w : World) (id : Nat) :
    (w.onScheduledTick id).tick = w.tick := by
  unfold onScheduledTick; split
  · rfl
  · split
    · dsimp [updateNode]; exact notifyOutputs_tick _ _
    · dsimp [updateNode]; exact notifyOutputs_tick _ _
    · rfl

/-- `popNextEvent` preserves the tick in its returned world. -/
private theorem popNextEvent_tick (w : World) :
    ∀ ev w', popNextEvent w = some (ev, w') → w'.tick = w.tick := by
  intro ev w' h
  unfold popNextEvent at h
  dsimp (config := { zeta := true }) at h
  split at h <;> try contradiction
  · split at h <;> try contradiction
    · rw [Option.some_inj, Prod.mk.injEq] at h; rcases h with ⟨rfl, rfl⟩; rfl

/-- Process one event. Returns `none` if no event is available. -/
def step (w : World) : Option World :=
  match w.popNextEvent with
  | none => none
  | some (ev, w') => some (w'.onScheduledTick ev.nodeId)

/-- `step` preserves the tick. -/
private theorem step_tick (w : World) :
    ∀ w', w.step = some w' → w'.tick = w.tick := by
  intro w' h
  unfold step at h
  cases h_pop : w.popNextEvent with
  | none => simp [h_pop] at h
  | some p =>
    rcases p with ⟨ev, w''⟩
    simp [h_pop] at h
    rw [← h, onScheduledTick_tick, popNextEvent_tick w ev w'' h_pop]

/-- `onNeighborUpdate` appends at most one event, always at a future tick (PNat delay). -/
private theorem onNeighborUpdate_events_append (w : World) (id : Nat) :
    ∃ new_events, (w.onNeighborUpdate id).events = w.events ++ new_events ∧
    ∀ ev ∈ new_events, ev.targetTick > w.tick := by
  cases h_getNode : w.getNode id
  case none =>
    exact ⟨[], by simp [onNeighborUpdate, h_getNode], by simp⟩
  case some nd =>
    cases h_kind : nd.kind
    case repeater delay priority =>
      refine ⟨[{ targetTick := w.tick + (delay : Nat), priority := priority, nodeId := id }], ?_, ?_⟩
      · simp [onNeighborUpdate, h_getNode, h_kind, scheduleEvent_events]
      · intro ev h_ev; simp at h_ev; subst h_ev
        have := PNat.pos delay
        change w.tick + (delay : Nat) > w.tick; omega
    case observer =>
      refine ⟨[{ targetTick := w.tick + 2, priority := 0, nodeId := id }], ?_, ?_⟩
      · simp [onNeighborUpdate, h_getNode, h_kind, scheduleEvent_events]
      · intro ev h_ev; simp at h_ev; subst h_ev
        change w.tick + 2 > w.tick; omega
    case output name =>
      refine ⟨[], ?_, ?_⟩
      · simp [onNeighborUpdate, h_getNode, h_kind, logOutput_events]
      · simp
    case input =>
      refine ⟨[], ?_, ?_⟩
      · simp [onNeighborUpdate, h_getNode, h_kind]
      · simp

/-- foldl of `onNeighborUpdate` appends events at future ticks. -/
private theorem foldl_onNeighborUpdate_events_append (l : List Nat) (w : World) :
    ∃ new_events, (l.foldl (fun w' outId => w'.onNeighborUpdate outId) w).events = w.events ++ new_events ∧
    ∀ ev ∈ new_events, ev.targetTick > w.tick := by
  induction l generalizing w with
  | nil => exact ⟨[], by simp, by simp⟩
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    obtain ⟨new_hd, h_app_hd, h_fut_hd⟩ := onNeighborUpdate_events_append w hd
    have h_tick' : (w.onNeighborUpdate hd).tick = w.tick := onNeighborUpdate_tick w hd
    obtain ⟨new_tl, h_app_tl, h_fut_tl⟩ := ih (w.onNeighborUpdate hd)
    refine ⟨new_hd ++ new_tl, ?_, ?_⟩
    · rw [h_app_tl, h_app_hd, List.append_assoc]
    · intro ev h_ev
      simp [List.mem_append] at h_ev
      cases h_ev with
      | inl h => exact h_fut_hd ev h
      | inr h => rw [h_tick'] at h_fut_tl; exact h_fut_tl ev h

/-- `onScheduledTick` appends events at future ticks only. -/
private theorem onScheduledTick_events_append (w : World) (id : Nat) :
    ∃ new_events, (w.onScheduledTick id).events = w.events ++ new_events ∧
    ∀ ev ∈ new_events, ev.targetTick > w.tick := by
  unfold onScheduledTick
  split
  · exact ⟨[], by simp, by simp⟩
  · rename_i nd_input h_get
    cases h_kind : nd_input.kind with
    | repeater delay priority =>
      change ∃ new_events, ((w.updateNode id (fun nd' => { nd' with sigLevel := if w.getInputSignal id > 0 then 15 else 0 })).notifyOutputs id).events = w.events ++ new_events ∧ ∀ ev ∈ new_events, ev.targetTick > w.tick
      have h_ev' : (w.updateNode id (fun nd' => { nd' with sigLevel := if w.getInputSignal id > 0 then 15 else 0 })).events = w.events := by simp
      have h_tick' : (w.updateNode id (fun nd' => { nd' with sigLevel := if w.getInputSignal id > 0 then 15 else 0 })).tick = w.tick := by simp
      dsimp [notifyOutputs]
      cases h_go : (w.updateNode id (fun nd' => { nd' with sigLevel := if w.getInputSignal id > 0 then 15 else 0 })).getNode id with
      | none => exact ⟨[], by simp, by simp⟩
      | some nd' =>
        simp only
        obtain ⟨new_ev, h_app, h_fut⟩ := foldl_onNeighborUpdate_events_append nd'.outputs
          (w.updateNode id (fun nd' => { nd' with sigLevel := if w.getInputSignal id > 0 then 15 else 0 }))
        refine ⟨new_ev, ?_, ?_⟩
        · rw [h_app, h_ev']
        · intro ev h_ev; rw [h_tick'] at h_fut; exact h_fut ev h_ev
    | observer =>
      change ∃ new_events, ((w.updateNode id (fun nd' => { nd' with sigLevel := 15 })).notifyOutputs id).events = w.events ++ new_events ∧ ∀ ev ∈ new_events, ev.targetTick > w.tick
      have h_ev' : (w.updateNode id (fun nd' => { nd' with sigLevel := 15 })).events = w.events := by simp
      have h_tick' : (w.updateNode id (fun nd' => { nd' with sigLevel := 15 })).tick = w.tick := by simp
      dsimp [notifyOutputs]
      cases h_go : (w.updateNode id (fun nd' => { nd' with sigLevel := 15 })).getNode id with
      | none => exact ⟨[], by simp, by simp⟩
      | some nd' =>
        simp only
        obtain ⟨new_ev, h_app, h_fut⟩ := foldl_onNeighborUpdate_events_append nd'.outputs
          (w.updateNode id (fun nd' => { nd' with sigLevel := 15 }))
        refine ⟨new_ev, ?_, ?_⟩
        · rw [h_app, h_ev']
        · intro ev h_ev; rw [h_tick'] at h_fut; exact h_fut ev h_ev
    | output name => exact ⟨[], by simp, by simp⟩
    | input => exact ⟨[], by simp, by simp⟩

/-- `onScheduledTick` preserves `countEventAtThisTick` at the world's tick. -/
private theorem onScheduledTick_countEventAtThisTick (w : World) (id : Nat) :
    countEventAtThisTick (w.onScheduledTick id) w.tick = countEventAtThisTick w w.tick := by
  obtain ⟨new_events, h_app, h_fut⟩ := onScheduledTick_events_append w id
  dsimp [countEventAtThisTick]
  rw [h_app, List.filter_append]
  have h_empty : new_events.filter (fun ev => ev.targetTick == w.tick) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro ev h_ev
    have h_gt := h_fut ev h_ev
    simp; omega
  simp [h_empty]

/-- `popNextEvent` selects an event at the current tick and removes it via `eraseIdx`. -/
private theorem popNextEvent_eraseIdx (w : World) (ev : ScheduledEvent) (w' : World)
    (h : popNextEvent w = some (ev, w')) :
    ∃ (idx : Nat) (h_idx : idx < w.events.length),
    w'.events = w.events.eraseIdx idx ∧
    ev.targetTick = w.tick ∧ w.events[idx] = ev := by
  unfold popNextEvent at h
  dsimp (config := { zeta := true }) at h
  split at h <;> try contradiction
  · split at h <;> try contradiction
    · rename_i idx ev_found h_find
      rw [Option.some_inj, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      have h_mem := List.mem_of_find?_eq_some h_find
      rw [List.mem_filter] at h_mem
      have h_tick : ev_found.targetTick = w.tick :=
        Nat.eq_of_beq_eq_true (by simpa using h_mem.2)
      have h_idx_lt : idx < w.events.length := by
        obtain ⟨j, h_j_lt, h_j_eq⟩ := List.mem_iff_getElem.mp h_mem.1
        simp [List.zip, List.getElem_zipWith, List.getElem_range] at h_j_lt h_j_eq
        omega
      have h_getElem : w.events[idx] = ev_found := by
        obtain ⟨j, h_j_lt, h_j_eq⟩ := List.mem_iff_getElem.mp h_mem.1
        simp [List.zip, List.getElem_zipWith, List.getElem_range] at h_j_lt h_j_eq
        exact h_j_eq.1.symm ▸ h_j_eq.2
      exact ⟨idx, h_idx_lt, rfl, h_tick, h_getElem⟩

lemma popNextEvent_remove_one_current_tick_event_if_some (w : World) (ev : ScheduledEvent) (w' : World) :
  popNextEvent w = some (ev, w') →
  ev.targetTick = w.tick ∧
  countEventAtThisTick w' w.tick = countEventAtThisTick w w.tick - 1 := by
  intro h
  obtain ⟨idx, h_idx, h_erase, h_tick, h_getElem⟩ := popNextEvent_eraseIdx w ev w' h
  constructor
  · exact h_tick
  · dsimp [countEventAtThisTick]
    rw [h_erase]
    have h_p : (fun e => e.targetTick == w.tick) w.events[idx] = true := by
      simp [h_getElem, h_tick]
    have h_filter := List.filter_eraseIdx_length w.events idx
      (fun e => e.targetTick == w.tick) h_idx h_p
    omega

/-- One `step` decreases `countEventAtThisTick` at the current tick. -/
private theorem step_decreases_count (w w' : World) (h : w.step = some w') :
    countEventAtThisTick w' w'.tick < countEventAtThisTick w w.tick := by
  dsimp [step] at h
  cases h_pop : w.popNextEvent with
  | none => simp [h_pop] at h
  | some p =>
    rcases p with ⟨ev, w_pop⟩
    simp only [h_pop] at h
    injection h with h_w'
    have h_tick_pop : w_pop.tick = w.tick := popNextEvent_tick w ev w_pop h_pop
    have h_tick' : w'.tick = w.tick := by rw [← h_w', onScheduledTick_tick, h_tick_pop]
    have h_pop_dec := (popNextEvent_remove_one_current_tick_event_if_some w ev w_pop h_pop).2
    have h_st_pres : countEventAtThisTick (w_pop.onScheduledTick ev.nodeId) w.tick =
        countEventAtThisTick w_pop w.tick := by
      rw [← h_tick_pop]; exact onScheduledTick_countEventAtThisTick w_pop ev.nodeId
    have h_count_pos : countEventAtThisTick w w.tick > 0 := by
      obtain ⟨idx, h_idx, _, h_tick_ev, h_getElem⟩ := popNextEvent_eraseIdx w ev w_pop h_pop
      dsimp [countEventAtThisTick]
      have h_mem : ev ∈ w.events.filter (fun e => e.targetTick == w.tick) := by
        rw [List.mem_filter]
        exact ⟨by rw [← h_getElem]; exact List.getElem_mem h_idx, by simp [h_tick_ev]⟩
      exact Nat.succ_le_of_lt (List.length_pos_of_mem h_mem)
    rw [h_tick', ← h_w', h_st_pres]
    omega


set_option linter.unusedVariables false in
/-- Process all events for the current tick, then advance to the next tick.
`h` is used in `decreasing_by`; the unusedVariables linter does not see that scope. -/
def stepUntilNextTick (w : World) : World :=
  match h : w.step with
  | none => { w with tick := w.tick + 1 }
  | some w' => w'.stepUntilNextTick
  termination_by countEventAtThisTick w w.tick
  decreasing_by exact step_decreases_count w w' h

/-- Run the simulation for `n` ticks, logging the tick number at each step. -/
def runTicks (w : World) (n : Nat) : World :=
  match n with
  | 0 => w
  | n' + 1 =>
    let w' := (w.logOutput s!"tick {w.tick}").stepUntilNextTick
    w'.runTicks n'

end World

/-- Wire a chain of nodes so each consecutive pair is connected (prev → next). -/
def connectChain (w : World) (ids : List Nat) : World :=
  let pairs := ids.zip (ids.drop 1)
  pairs.foldl (fun w' (prev, curr) =>
    let w₁ := w'.updateNode curr (fun nd => { nd with inputs := nd.inputs ++ [prev] })
    w₁.updateNode prev (fun nd => { nd with outputs := nd.outputs ++ [curr] })
  ) w

end BasicRedstoneSim
