import BasicProofs.GroupClustering.LockstepComposition
import BasicProofs.GroupClustering.QueueMembership

open BasicRedstoneSim List

/-! # Group clustering — stageEvent disjointness and Nodup helpers

This file proves the key disjointness lemmas needed for the
stepUntilNextTick Nodup theorem and reports what remains for the
full h_nodup discharge.

Main results:

* `stageEvent_succ_not_mem_of_stageWindow`: stageEvent(j+1) does
  not appear in a list whose elements satisfy stageWindow at tick t
  when stageEvent(j) is due at tick t.
* `stageEvent_succ_not_mem_gSimWorld`: stageEvent(j+1) is not in
  the tick-start queue at tick t when stageEvent(j) is due.
* `stageEvent_succ_inj_of_distinct`: distinct due events produce
  distinct spawn events.
-/

/-! ## stageEvent disjointness from stageWindow -/

/-- stageEvent(j+1) does not appear in a list where every element
    satisfies stageWindow at tick t and stageEvent(j) is due at
    tick t. The stageWindow for j+1 requires stageTarget(j) < t
    but stageTarget(j) = t for a due event. -/
theorem stageEvent_succ_not_mem_of_stageWindow
    (actTick : Nat → Nat) (groups : List GroupSpec)
    (gi ci j t : Nat)
    (h_gi : gi < groups.length) (h_ci : ci < (groupAt groups gi).length)
    (h_j : j ≤ (chainAt groups gi ci).middleDelays.length)
    (h_due : stageTarget actTick groups gi ci j = t)
    (l : List ScheduledEvent)
    (h_win : ∀ ev ∈ l, ∃ gi' ci' j',
      gi' < groups.length ∧ ci' < (groupAt groups gi').length ∧
      j' ≤ (chainAt groups gi' ci').middleDelays.length + 1 ∧
      ev = stageEvent actTick groups gi' ci' j' ∧
      stageWindow actTick groups gi' ci' j' t) :
    stageEvent actTick groups gi ci (j + 1) ∉ l := by
  intro h_mem
  obtain ⟨gi', ci', j', h_gi', h_ci', h_j', h_ev, h_win'⟩ :=
    h_win _ h_mem
  dsimp [stageWindow] at h_win'
  have h_node : chainBaseId groups gi ci + 1 + (j + 1) =
      chainBaseId groups gi' ci' + 1 + j' := by
    have h := congr_arg ScheduledEvent.nodeId h_ev
    dsimp [stageEvent] at h
    exact h
  -- Use chainBaseId_interval_le for different chains
  by_cases h_lex₁₂ : gi < gi' ∨ gi = gi' ∧ ci < ci'
  · have h_le := chainBaseId_interval_le groups gi ci gi' ci'
      h_gi h_ci h_gi' h_ci' h_lex₁₂
    have h_cnt₁ : chainNodeCount (chainAt groups gi ci) =
        (chainAt groups gi ci).middleDelays.length + 4 := rfl
    omega
  · by_cases h_lex₂₁ : gi' < gi ∨ gi' = gi ∧ ci' < ci
    · have h_le := chainBaseId_interval_le groups gi' ci' gi ci
        h_gi' h_ci' h_gi h_ci h_lex₂₁
      have h_cnt₂ : chainNodeCount (chainAt groups gi' ci') =
          (chainAt groups gi' ci').middleDelays.length + 4 := rfl
      omega
    · -- Same chain: gi' = gi, ci' = ci
      have h_g : gi' = gi := by omega
      have h_c : ci' = ci := by omega
      rw [h_g, h_c] at h_node h_win'
      have h_j' : j' = j + 1 := by omega
      rw [h_j'] at h_win'
      -- stageWindow(j+1, t): predecessor condition
      have h_pred : stageTarget actTick groups gi ci j < t := by
        simpa [Nat.add_sub_cancel] using h_win'.1
      rw [h_due] at h_pred
      omega

/-- stageEvent(j+1) is not in the tick-start queue at tick t when
    stageEvent(j) is due at tick t. Uses the public
    gSimWorld_events_stageWindow to discharge the stageWindow
    hypothesis. -/
theorem stageEvent_succ_not_mem_gSimWorld
    (groups : List GroupSpec) (actTick : Nat → Nat)
    (groupOrd : List Nat) (withinOrd pos : Nat → List Nat)
    (gi ci j t : Nat)
    (h_gi : gi < groups.length) (h_ci : ci < (groupAt groups gi).length)
    (h_j : j ≤ (chainAt groups gi ci).middleDelays.length)
    (h_due : stageTarget actTick groups gi ci j = t) :
    stageEvent actTick groups gi ci (j + 1) ∉
      (gSimWorld groups actTick groupOrd withinOrd pos t).events := by
  apply stageEvent_succ_not_mem_of_stageWindow actTick groups gi ci j t
    h_gi h_ci h_j h_due
  intro ev h_ev
  exact gSimWorld_events_stageWindow groups actTick groupOrd withinOrd pos
    t ev h_ev

/-! ## Two distinct due events produce distinct spawns -/

/-- If two stageEvents from the same queue are distinct due events,
    their successor stage events are also distinct. -/
theorem stageEvent_succ_inj_of_distinct
    (actTick : Nat → Nat) (groups : List GroupSpec)
    (g₁ c₁ j₁ g₂ c₂ j₂ : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_j₁ : j₁ ≤ (chainAt groups g₁ c₁).middleDelays.length)
    (h_j₂ : j₂ ≤ (chainAt groups g₂ c₂).middleDelays.length)
    (h_ne : stageEvent actTick groups g₁ c₁ j₁ ≠
      stageEvent actTick groups g₂ c₂ j₂) :
    stageEvent actTick groups g₁ c₁ (j₁ + 1) ≠
      stageEvent actTick groups g₂ c₂ (j₂ + 1) := by
  intro h_eq
  have := stageEvent_injective actTick groups g₁ c₁ (j₁ + 1) g₂ c₂ (j₂ + 1)
    h_g₁ h_c₁ h_g₂ h_c₂ (by omega) (by omega) h_eq
  rcases this with ⟨rfl, rfl, h_j_eq⟩
  have : j₁ + 1 = j₂ + 1 := h_j_eq
  have : j₁ = j₂ := by omega
  subst this
  exact h_ne rfl

/-!
## What remains toward h_nodup and the order-preservation capstone

The full proof of h_nodup requires three additional lemmas:

1. **stepUntilNextTick_events_nodup**: One drain step preserves full
   events Nodup. The proof proceeds by induction on
   stepUntilNextTick with the invariant SInv: every event is either
   from the original queue (with stageWindow) or a spawn from a due
   event of the original queue. At each pop, the spawn is
   stageEvent(j+1) for the due stageEvent(j). This spawn is not in
   the intermediate queue because:
   (a) stageEvent_succ_not_mem_of_stageWindow prevents it from being
       among the original events.
   (b) stageEvent_succ_inj_of_distinct prevents it from colliding
       with a previous spawn (different due events give different
       spawns).
   (c) For the output stage (j = m + 1), onScheduledTick fires the
       last repeater whose only output is the output node. The
       output node logs but does not schedule events, so no spawn
       is appended. Proving this requires expanding onScheduledTick
       through updateNode, notifyOutputs, and onNeighborUpdate.
   The induction requires carrying the bundled invariant through
   World.step, which involves classifying the popped event and
   proving the spawn is fresh.

2. **gSimBurst_events_nodup**: The burst phase preserves full events
   Nodup. Each segment is processNEvents + activateGroup.
   processNEvents pops due events and appends spawns (same argument
   as stepUntilNextTick). activateGroup appends observer events that
   are stageEvent(0) events, which are not in the queue by
   stageWindow(0, t) requiring actTick(gi) < t.

3. **gSimWorld_events_nodup**: By induction on t. Base: buildGroups
   has empty events. Step: gSimBody preserves events Nodup, using
   stepUntilNextTick_events_nodup and gSimBurst_events_nodup.

Once gSimWorld_events_nodup is proved, gSimWorld_due_nodup and
popQueueWorld_due_nodup follow immediately (filter preserves Nodup).
The h_nodup premise of QSideOrder.sameSpec_orderPreservation is then
discharged.
-/
