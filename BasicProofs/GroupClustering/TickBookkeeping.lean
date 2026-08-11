import BasicProofs.GroupClustering.Definitions


open BasicRedstoneSim

/-! # Group clustering — tick bookkeeping

Every `gSimBody` call advances the tick by exactly 1: the logOutput prelude
and the whole burst phase preserve the tick, and the trailing
`stepUntilNextTick` contributes the +1. Hence `gSimFoldl ... w n` afterwards
runs with tick `w.tick + n`.
-/

/-- `activateGroup` preserves the tick (enqueuing an event does). -/
theorem activateGroup_tick (w : World) (observers : List Nat) :
    (activateGroup w observers).tick = w.tick := by
  induction observers generalizing w with
  | nil => simp [activateGroup]
  | cons oid os ih =>
    simp only [activateGroup, List.foldl_cons]
    rw [← activateGroup, ih, World.scheduleEvent_tick]

/-- One burst step (pos-insertion then one atomic group firing) preserves
    the tick. -/
private theorem gSimBurstStep_tick (t : Nat) (obsAll : List (List Nat))
    (withinOrd : Nat → List Nat) (pos : Nat → List Nat) (w : World)
    (gi k : Nat) :
    (activateGroup
        (processNEvents w ((pos t)[k]?.getD 0))
        ((withinOrd gi).foldl (fun acc ci =>
          match (obsAll[gi]?.getD [])[ci]? with
          | some oid => acc ++ [oid]
          | none => acc) [])).tick = w.tick := by
  rw [activateGroup_tick, processNEvents_tick]

/-- `gSimBurst` preserves the tick. -/
theorem gSimBurst_tick (t : Nat) (obsAll : List (List Nat))
    (withinOrd : Nat → List Nat) (pos : Nat → List Nat) (w : World)
    (pairs : List (Nat × Nat)) :
    (gSimBurst t obsAll withinOrd pos w pairs).tick = w.tick := by
  induction pairs generalizing w with
  | nil => simp [gSimBurst]
  | cons p ps ih =>
    simp only [gSimBurst, List.foldl_cons]
    rw [← gSimBurst, ih]
    rcases p with ⟨gi, k⟩
    exact gSimBurstStep_tick t obsAll withinOrd pos w gi k

/-- One `gSimBody` call advances the tick by exactly 1. -/
theorem gSimBody_tick (actTick : Nat → Nat) (obsAll : List (List Nat))
    (groupOrd : List Nat) (withinOrd : Nat → List Nat) (pos : Nat → List Nat)
    (w : World) (i : Nat) :
    (gSimBody actTick obsAll groupOrd withinOrd pos w i).tick = w.tick + 1 := by
  dsimp only [gSimBody]
  split_ifs with h_active
  · rw [World.tick_stepUntilNextTick, World.logOutput_tick]
  · rw [World.tick_stepUntilNextTick, gSimBurst_tick, World.logOutput_tick]

/-- After `n` `gSimBody` calls, the tick has advanced by `n`. -/
theorem gSimFoldl_tick (actTick : Nat → Nat) (obsAll : List (List Nat))
    (groupOrd : List Nat) (withinOrd : Nat → List Nat) (pos : Nat → List Nat)
    (w : World) (n : Nat) :
    (gSimFoldl actTick obsAll groupOrd withinOrd pos w n).tick = w.tick + n := by
  induction n generalizing w with
  | zero => simp [gSimFoldl]
  | succ n' ih =>
    simp only [gSimFoldl, List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil]
    rw [gSimBody_tick, ← gSimFoldl, ih]
    omega
