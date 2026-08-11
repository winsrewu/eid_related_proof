import BasicProofs.GroupClustering.QueueMembership
import BasicProofs.GroupClustering.SameSpecLockstep

open BasicRedstoneSim List

/-! # Group clustering — side facts for the stage-induction step

Small discharges used by the general step assembly:

* `StageMemAt_gSimWorld` — the queue-membership invariant at every
  tick-start queue, from the stage-window characterization (QueueMembership);
* `StageMemAt_logOutput` — the invariant survives the log step;
* `evBefore.ne_of_nodup` — the endpoints of a betweenness in a
  duplicate-free list are distinct (the `h_ne` premise of
  `evBefore_stepUNT_backward`, BackwardTransport).
-/

/-- Every tick-start queue satisfies `StageMemAt` at its own tick. -/
theorem StageMemAt_gSimWorld (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (t : Nat) :
    StageMemAt groups actTick
      (gSimWorld groups actTick groupOrd withinOrd pos t) t := by
  intro ev h_ev
  obtain ⟨gi, ci, j, h_gi, h_ci, h_j_le, h_ev_eq, h_win⟩ :=
    gSimWorld_events_stageWindow groups actTick groupOrd withinOrd pos t ev
      h_ev
  refine ⟨gi, ci, j, h_gi, h_ci, h_j_le, h_ev_eq, ?_, ?_⟩
  · dsimp [stageWindow] at h_win
    omega
  · dsimp [stageWindow] at h_win
    exact h_win.2

/-- `StageMemAt` survives the log step (the events are unchanged). -/
theorem StageMemAt_logOutput (groups : List GroupSpec) (actTick : Nat → Nat)
    (w : World) (s : String) (t : Nat)
    (h_stage : StageMemAt groups actTick w t) :
    StageMemAt groups actTick (w.logOutput s) t := by
  intro ev h_ev
  exact h_stage ev (by rwa [World.logOutput_events] at h_ev)

/-- The endpoints of a betweenness in a duplicate-free list are
    distinct. -/
theorem evBefore.ne_of_nodup {l : List ScheduledEvent}
    (h_nd : l.Nodup) {x y : ScheduledEvent} (h : evBefore l x y) :
    x ≠ y := by
  obtain ⟨p, q, h_eq, h_y⟩ := h
  intro h_xy
  have h_x_q : x ∈ q := by rwa [h_xy]
  have h_nd' : (p ++ x :: q).Nodup := by rwa [← h_eq]
  exact nodup_cons_append_not_mem h_nd' h_x_q
