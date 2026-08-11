import BasicProofs.GroupClustering.ForwardTransport

open BasicRedstoneSim List

/-! # Group clustering — an interloper between two spawns is a spawn

The drain of a world `w` splits the resulting queue into survivors
(events of `w` not due at `w.tick`) followed by the spawn accumulator.
An event that lies strictly after one of the spawns, and is not due at
`w.tick`, cannot itself be a survivor of `w`: survivors sit in the first
part of the split and so precede every spawn. Hence the event is absent
from `w.events`. This supplies the `h_spawn_not_survivor` premise of the
stage-`1` base case (Stage1PostDrainBase). -/

/-- An event lying strictly after a spawn of the drain of `w`, and not due
    at `w.tick`, is not a survivor of `w` (hence not in `w.events`). -/
theorem spawn_not_survivor_of_between (w : World)
    (sA e : ScheduledEvent) (spawns : List ScheduledEvent)
    (h_split : w.stepUntilNextTick.events =
        w.events.filter (fun ev => ev.targetTick ≠ w.tick) ++ spawns)
    (h_sA_not_w : sA ∉ w.events)
    (h_e_tgt_ne : e.targetTick ≠ w.tick)
    (h_b1 : evBefore w.stepUntilNextTick.events sA e)
    (h_nd : (w.stepUntilNextTick.events).Nodup) :
    e ∉ w.events := by
  intro h_e_w
  -- e, not due at w.tick, would be a survivor
  have h_e_surv : e ∈ w.events.filter (fun ev => ev.targetTick ≠ w.tick) := by
    rw [List.mem_filter]
    exact ⟨h_e_w, decide_eq_true_eq.mpr h_e_tgt_ne⟩
  -- sA is in the drain queue but not in w.events, so it is a spawn
  have h_sA_mem : sA ∈ w.stepUntilNextTick.events := evBefore.mem_left h_b1
  have h_sA_spawn : sA ∈ spawns := by
    have h_sA_mem' : sA ∈
        w.events.filter (fun ev => ev.targetTick ≠ w.tick) ++ spawns := by
      rwa [← h_split]
    rw [List.mem_append] at h_sA_mem'
    rcases h_sA_mem' with h | h
    · exact absurd (List.mem_filter.mp h).1 h_sA_not_w
    · exact h
  -- a survivor precedes every spawn, contradicting sA before e
  have h_e_before_sA : evBefore w.stepUntilNextTick.events e sA := by
    rw [h_split]
    exact evBefore.of_mem_append h_e_surv h_sA_spawn
  exact (evBefore.asymm h_nd h_b1 h_e_before_sA).elim
