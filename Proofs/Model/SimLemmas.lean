import Proofs.Model.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Pairwise
import Mathlib.Data.List.Lemmas
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Convert
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push


open BasicRedstoneSim

/-! # Simulation lemmas for the no-group model

Tick preservation and tick-progression facts about the model primitives and
the driver. These are the foundation for reasoning about the tick at which a
chain's output is logged. -/

/-! ## Step / drain primitives -/

/-- `stepUntilNextTick` with no available events just advances the tick. -/
theorem stepUntilNextTick_of_step_none (w : World) (h : w.step = none) :
    w.stepUntilNextTick = { w with tick := w.tick + 1 } := by
  rw [World.stepUntilNextTick, h]

/-- `processNEvents w n` followed by `stepUntilNextTick` equals
    `stepUntilNextTick`: both drain all events at the current tick. -/
theorem processNEvents_stepUntilNextTick_eq (w : World) (n : Nat) :
    (processNEvents w n).stepUntilNextTick = w.stepUntilNextTick := by
  induction n generalizing w with
  | zero => simp [processNEvents]
  | succ n' ih =>
    simp only [processNEvents]
    cases h : w.step with
    | none => rw [stepUntilNextTick_of_step_none w h]
    | some w' =>
      have h_eq : w.stepUntilNextTick = w'.stepUntilNextTick := by
        rw [World.stepUntilNextTick, h]
      rw [ih w', h_eq]

/-! ## Tick preservation -/

/-- `onNeighborUpdate` preserves the tick. -/
theorem World.onNeighborUpdate_tick (w : World) (id : Nat) :
    (w.onNeighborUpdate id).tick = w.tick := by
  unfold World.onNeighborUpdate
  split <;> (first | rfl | (split <;> rfl))

/-- A foldl of `onNeighborUpdate` preserves the tick. -/
theorem foldl_onNeighborUpdate_tick (l : List Nat) (w : World) :
    (l.foldl (fun w' outId => w'.onNeighborUpdate outId) w).tick = w.tick := by
  induction l generalizing w with
  | nil => rfl
  | cons hd tl ih => simp [List.foldl_cons]; rw [ih, World.onNeighborUpdate_tick]

/-- `notifyOutputs` preserves the tick. -/
theorem World.notifyOutputs_tick (w : World) (id : Nat) :
    (w.notifyOutputs id).tick = w.tick := by
  unfold World.notifyOutputs; split
  · rfl
  · exact foldl_onNeighborUpdate_tick _ _

/-- `setInput` preserves the tick. -/
theorem World.setInput_tick (w : World) (id : Nat) (level : Nat) :
    (w.setInput id level).tick = w.tick := by
  dsimp [World.setInput]; rw [World.notifyOutputs_tick, World.updateNode_tick]

/-- `onScheduledTick` preserves the tick. -/
theorem World.onScheduledTick_tick (w : World) (id : Nat) :
    (w.onScheduledTick id).tick = w.tick := by
  unfold World.onScheduledTick
  split
  · rfl
  · split
    · dsimp [World.updateNode]; exact World.notifyOutputs_tick _ _
    · dsimp [World.updateNode]; exact World.notifyOutputs_tick _ _
    · rfl

/-- `popNextEvent` preserves the tick in its returned world. -/
theorem World.popNextEvent_tick (w : World) :
    ∀ ev w', w.popNextEvent = some (ev, w') → w'.tick = w.tick := by
  intro ev w' h
  unfold World.popNextEvent at h
  dsimp (config := { zeta := true }) at h
  split at h <;> try contradiction
  · split at h <;> try contradiction
    · rw [Option.some_inj, Prod.mk.injEq] at h; rcases h with ⟨rfl, rfl⟩; rfl

/-- `World.step` preserves the tick. -/
theorem World.step_tick (w : World) :
    ∀ w', w.step = some w' → w'.tick = w.tick := by
  intro w' h
  unfold World.step at h
  cases h_pop : w.popNextEvent with
  | none => simp [h_pop] at h
  | some p =>
    rcases p with ⟨ev, w''⟩
    simp [h_pop] at h
    rw [← h, World.onScheduledTick_tick, World.popNextEvent_tick w ev w'' h_pop]

/-- `stepUntilNextTick` always increments the tick by exactly 1. -/
theorem World.tick_stepUntilNextTick (w : World) :
    (w.stepUntilNextTick).tick = w.tick + 1 := by
  induction w using World.stepUntilNextTick.induct with
  | case1 x h => rw [World.stepUntilNextTick, h]
  | case2 x w' h ih =>
    rw [World.stepUntilNextTick, h, ih, World.step_tick x w' h]

/-- `processNEvents` preserves the tick. -/
theorem processNEvents_tick (w : World) (n : Nat) :
    (processNEvents w n).tick = w.tick := by
  induction n generalizing w with
  | zero => rfl
  | succ n' ih =>
    simp only [processNEvents]
    cases h : w.step with
    | none => rfl
    | some w' => rw [ih w', World.step_tick w w' h]

/-! ## Driver tick progression -/

/-- `activateChain` preserves the tick. -/
theorem activateChain_tick (w : World) (obs : Nat) :
    (activateChain w obs).tick = w.tick := by
  unfold activateChain; exact World.scheduleEvent_tick w _

/-- `simBurst` preserves the tick. -/
theorem simBurst_tick (t : Nat) (observers : List Nat) (pos : Nat → Nat → Nat)
    (w : World) (pairs : List (Nat × Nat)) :
    (simBurst t observers pos w pairs).tick = w.tick := by
  unfold simBurst
  induction pairs generalizing w with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.foldl_cons]
    cases p with
    | mk i k =>
      dsimp only
      split <;> rename_i h_obs
      · rw [ih, activateChain_tick, processNEvents_tick]
      · rw [ih, processNEvents_tick]

/-- `simBody` advances the tick by exactly 1. -/
theorem simBody_tick (actTick : Nat → Nat) (observers : List Nat)
    (actOrd : List Nat) (pos : Nat → Nat → Nat) (w : World) (n : Nat) :
    (simBody actTick observers actOrd pos w n).tick = w.tick + 1 := by
  unfold simBody
  dsimp only
  rw [World.tick_stepUntilNextTick, simBurst_tick, World.logOutput_tick]

/-- `simFoldl` advances the tick by `n`. -/
theorem simFoldl_tick (actTick : Nat → Nat) (observers : List Nat)
    (actOrd : List Nat) (pos : Nat → Nat → Nat) (w : World) (n : Nat) :
    (simFoldl actTick observers actOrd pos w n).tick = w.tick + n := by
  induction n generalizing w with
  | zero => simp [simFoldl]
  | succ n' ih =>
    have h_unfold : simFoldl actTick observers actOrd pos w (n' + 1) =
        simBody actTick observers actOrd pos
          (simFoldl actTick observers actOrd pos w n') n' := by
      simp [simFoldl, List.range_succ, List.foldl_append]
    rw [h_unfold, simBody_tick, ih]
    omega
