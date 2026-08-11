import BasicProofs.GroupClustering.NodupChain
import BasicProofs.GroupClustering.OrderPreservationPremises

set_option linter.unusedVariables false

open BasicRedstoneSim List

/-! # Group clustering — backward transport of betweenness

The finals bundle (FinalsBundle) gives betweenness of the final events in the
tick-`T` due filter. The converse machinery (ConverseFinalUnconditional) needs that
betweenness in the post-burst queue at the reference chains' stage-`m`
pop tick. This file builds the transport that moves betweenness
backwards across ticks.

The forward direction is `evBefore_gSimWorld_const` (OrderPreservationPremises): two
events that target no tick before `b` keep their order from tick-start
queue `a` to tick-start queue `b`. The backward direction follows by
totality + asymmetry: at the earlier tick two distinct present events
are comparable, and the wrong order would forward-preserve to contradict
the known order at the later tick. -/

/-- Backward betweenness across tick-start queues. If `x` precedes `y`
    in the tick-`b` queue, both target tick `≥ b`, and both are present
    and distinct in the tick-`a` queue (`a ≤ b`), then `x` precedes `y`
    in the tick-`a` queue. -/
theorem evBefore_gSimWorld_backward (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat)
    (h_gord_nd : groupOrd.Nodup)
    (h_within_nd : ∀ gi, gi < groups.length → (withinOrd gi).Nodup)
    (a b : Nat) (h_le : a ≤ b)
    (x y : ScheduledEvent)
    (h_x_a : x ∈ (gSimWorld groups actTick groupOrd withinOrd pos a).events)
    (h_y_a : y ∈ (gSimWorld groups actTick groupOrd withinOrd pos a).events)
    (h_ne : x ≠ y)
    (h_bx : b ≤ x.targetTick) (h_by : b ≤ y.targetTick)
    (h_after : evBefore
        (gSimWorld groups actTick groupOrd withinOrd pos b).events x y) :
    evBefore
      (gSimWorld groups actTick groupOrd withinOrd pos a).events x y := by
  have h_nd_a : (gSimWorld groups actTick groupOrd withinOrd pos a).events.Nodup :=
    gSimWorld_events_Nodup groups actTick groupOrd withinOrd pos a
      h_gord_nd h_within_nd
  have h_nd_b : (gSimWorld groups actTick groupOrd withinOrd pos b).events.Nodup :=
    gSimWorld_events_Nodup groups actTick groupOrd withinOrd pos b
      h_gord_nd h_within_nd
  obtain h_xy | h_yx := evBefore.total_of_nodup h_nd_a h_x_a h_y_a h_ne
  · exact h_xy
  · exfalso
    have h_yx_b : evBefore
        (gSimWorld groups actTick groupOrd withinOrd pos b).events y x :=
      evBefore_gSimWorld_const groups actTick groupOrd withinOrd pos a b y x
        h_le h_yx h_by h_bx
    exact evBefore.asymm h_nd_b h_after h_yx_b

/-- Backward transport from the tick-`T` due filter. Betweenness in the
    due filter at `T` lifts to the full tick-`T` queue, then transports
    back to any earlier tick-start queue where both events are present
    and target at least `T`. -/
theorem evBefore_due_filter_backward (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat)
    (h_gord_nd : groupOrd.Nodup)
    (h_within_nd : ∀ gi, gi < groups.length → (withinOrd gi).Nodup)
    (T a : Nat) (h_le : a ≤ T)
    (x y : ScheduledEvent)
    (h_due : evBefore
        ((gSimWorld groups actTick groupOrd withinOrd pos T).events.filter
          (fun e => e.targetTick == T)) x y)
    (h_x_a : x ∈ (gSimWorld groups actTick groupOrd withinOrd pos a).events)
    (h_y_a : y ∈ (gSimWorld groups actTick groupOrd withinOrd pos a).events)
    (h_ne : x ≠ y)
    (h_bx : T ≤ x.targetTick) (h_by : T ≤ y.targetTick) :
    evBefore
      (gSimWorld groups actTick groupOrd withinOrd pos a).events x y := by
  have h_T : evBefore
      (gSimWorld groups actTick groupOrd withinOrd pos T).events x y :=
    evBefore.of_filter (fun e => e.targetTick == T) h_due
  exact evBefore_gSimWorld_backward groups actTick groupOrd withinOrd pos
    h_gord_nd h_within_nd a T h_le x y h_x_a h_y_a h_ne h_bx h_by h_T

/-- Backward transport through a drain step. Two non-due events present
    in `w.events` whose order is known in the post-drain queue stood in
    that order already in `w.events`: the wrong order would
    forward-preserve (OrderPreservationPremises) and contradict asymmetry on the
    duplicate-free post-drain queue. -/
theorem evBefore_stepUNT_backward (w : World) (x y : ScheduledEvent)
    (h_nd_w : w.events.Nodup)
    (h_nd_post : w.stepUntilNextTick.events.Nodup)
    (h_x : x ∈ w.events) (h_y : y ∈ w.events)
    (h_nd_x : x.targetTick ≠ w.tick) (h_nd_y : y.targetTick ≠ w.tick)
    (h_ne : x ≠ y)
    (h_after : evBefore w.stepUntilNextTick.events x y) :
    evBefore w.events x y := by
  obtain h_xy | h_yx := evBefore.total_of_nodup h_nd_w h_x h_y h_ne
  · exact h_xy
  · exfalso
    have h_yx_post : evBefore w.stepUntilNextTick.events y x :=
      evBefore_stepUNT_of_notDue w y x h_y h_x h_nd_y h_nd_x h_yx
    exact evBefore.asymm h_nd_post h_after h_yx_post
