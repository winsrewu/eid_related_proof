import BasicProofs.GroupClustering.QSideOrder
import BasicProofs.GroupClustering.LockstepComposition

open BasicRedstoneSim List

/-! # Group clustering — discharging order-preservation premises

QSideOrder states `sameSpec_orderPreservation` with three undischarged
premises: base order (h_base), due-filter Nodup (h_nodup), and
burst-phase survival (h_surv). This file proves helper lemmas that
characterize the stage-0 events and reports what remains for each
premise.
-/

/-! ## List split helper -/

/-- A list containing a member splits at that member. -/
private theorem split_at_mem {α : Type} (l : List α) (a : α)
    (h : a ∈ l) : ∃ pre post, l = pre ++ a :: post := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.mem_cons] at h
    cases h with
    | inl h_eq =>
      subst h_eq
      exact ⟨[], xs, rfl⟩
    | inr h_mem =>
      obtain ⟨pre, post, h_split⟩ := ih h_mem
      exact ⟨x :: pre, post, by rw [h_split]; rfl⟩

/-! ## Foldl append preserves membership -/

/-- A foldl that conditionally appends preserves membership. -/
private theorem foldl_obs_append_mem (obs : List Nat)
    (post : List Nat) (acc : List Nat) (x : Nat) (h : x ∈ acc) :
    x ∈ post.foldl (fun acc ci =>
        match obs[ci]? with
        | some oid => acc ++ [oid]
        | none => acc) acc := by
  induction post generalizing acc with
  | nil => exact h
  | cons ci cs ih =>
    simp only [foldl_cons]
    cases h_val : obs[ci]? with
    | none =>
      simp only
      exact ih acc h
    | some oid =>
      simp only
      exact ih (acc ++ [oid]) (List.mem_append_left _ h)

/-! ## Stage-0 event characterization -/

/-- The stage-0 target tick is the activation tick plus two. -/
theorem stageTarget_zero_eq (actTick : Nat → Nat)
    (groups : List GroupSpec) (gi ci : Nat) :
    stageTarget actTick groups gi ci 0 = actTick gi + 2 := by
  simp [stageTarget, stageCumDelay_zero]

/-- The stage-0 priority is zero. -/
theorem stagePri_zero_eq (groups : List GroupSpec)
    (gi ci : Nat) :
    stagePri groups gi ci 0 = (0 : Int) := by
  simp [stagePri]

/-- The stage-0 event has observer fields. -/
theorem stageEvent_zero_fields (actTick : Nat → Nat)
    (groups : List GroupSpec) (gi ci : Nat) :
    stageEvent actTick groups gi ci 0 =
      ({ targetTick := actTick gi + 2, priority := 0,
         nodeId := chainBaseId groups gi ci + 1 } : ScheduledEvent) := by
  simp [stageEvent, stageTarget_zero_eq, stagePri_zero_eq]

/-- The observer id for chain `(gi, ci)` in the built world. -/
theorem obsId_eq (groups : List GroupSpec)
    (gi ci : Nat) (h_gi : gi < groups.length)
    (h_ci : ci < (groupAt groups gi).length) :
    ((buildGroups groups).2[gi]?.getD [])[ci]? =
      some (chainBaseId groups gi ci + 1) :=
  buildGroups_snd_getElem_getElem? groups gi ci h_gi h_ci

/-! ## Observer id in ordered list -/

/-- If `ci` appears in `withinOrd gi` and is a valid chain index,
    then the observer id `chainBaseId groups gi ci + 1` is in the
    ordered observer list. -/
private theorem obsId_mem_ordered (withinOrd : Nat → List Nat)
    (groups : List GroupSpec) (gi ci : Nat)
    (h_gi : gi < groups.length)
    (h_ci : ci < (groupAt groups gi).length)
    (h_ci_in : ci ∈ withinOrd gi) :
    chainBaseId groups gi ci + 1 ∈
      (withinOrd gi).foldl (fun acc ci' =>
          match (((buildGroups groups).2)[gi]?.getD [])[ci']? with
          | some oid => acc ++ [oid]
          | none => acc) [] := by
  set obsAll := (buildGroups groups).2
  set obs := obsAll[gi]?.getD []
  -- Split withinOrd gi at ci
  obtain ⟨pre, post, h_split⟩ := split_at_mem (withinOrd gi) ci h_ci_in
  rw [h_split]
  -- foldl of (pre ++ ci :: post)
  simp only [foldl_append, foldl_cons]
  -- The lookup for ci succeeds
  have h_lookup : obs[ci]? = some (chainBaseId groups gi ci + 1) :=
    obsId_eq groups gi ci h_gi h_ci
  rw [h_lookup]
  -- After ci, the accumulator contains the observer id
  have h_base : chainBaseId groups gi ci + 1 ∈
      pre.foldl (fun acc ci' =>
          match obs[ci']? with
          | some oid => acc ++ [oid]
          | none => acc) [] ++
        [chainBaseId groups gi ci + 1] := by
    apply List.mem_append_right
    simp
  -- The post foldl preserves membership
  exact foldl_obs_append_mem obs post _ _ h_base

/-! ## Stage-0 event in activateGroup result -/

/-- An observer event is in the activateGroup result when the
    observer id is in the ordered list. -/
private theorem stageEvent0_mem_activateGroup
    (w : World) (ordered : List Nat) (actTick : Nat → Nat)
    (groups : List GroupSpec) (gi ci : Nat)
    (h_nid : chainBaseId groups gi ci + 1 ∈ ordered)
    (h_tick : w.tick = actTick gi) :
    stageEvent actTick groups gi ci 0 ∈
      (activateGroup w ordered).events := by
  rw [stageEvent_zero_fields, activateGroup_events_map]
  apply List.mem_append_right
  rw [List.mem_map]
  refine ⟨chainBaseId groups gi ci + 1, h_nid, ?_⟩
  simp [h_tick]

/-! ## Stage-0 event in burst result -/

/-- The stage-0 event for chain `(gi, ci)` is in the burst result
    when group `gi` is among the burst pairs and `ci` is in the
    withinOrd list. The event targets tick `actTick gi + 2`, which
    is strictly after the burst tick, so it survives all subsequent
    burst steps. -/
private theorem stageEvent0_mem_burst (t : Nat)
    (withinOrd pos : Nat → List Nat)
    (w : World) (pairs : List (Nat × Nat))
    (gi k : Nat)
    (actTick : Nat → Nat) (groups : List GroupSpec) (ci : Nat)
    (h_tick_w : w.tick = t) (h_tick_act : t = actTick gi)
    (h_gi : gi < groups.length) (h_ci : ci < (groupAt groups gi).length)
    (h_ci_in : ci ∈ withinOrd gi)
    (h_pair : (gi, k) ∈ pairs) :
    stageEvent actTick groups gi ci 0 ∈
      (gSimBurst t (buildGroups groups).2 withinOrd pos w pairs).events := by
  set obsAll := (buildGroups groups).2
  -- Split the burst at the (gi, k) step
  obtain ⟨pre, post, h_split⟩ := split_at_mem pairs (gi, k) h_pair
  -- Rewrite the burst using the split
  have h_burst_eq :
      gSimBurst t obsAll withinOrd pos w pairs =
        gSimBurst t obsAll withinOrd pos
          (gSimBurst t obsAll withinOrd pos w pre)
          ((gi, k) :: post) := by
    rw [h_split]
    simp [gSimBurst, List.foldl_append]
  rw [h_burst_eq]
  -- At the (gi, k) step
  simp only [gSimBurst, List.foldl_cons]
  set W_at := gSimBurst t obsAll withinOrd pos w pre
  set m := (pos t)[k]?.getD 0
  set Wproc := processNEvents W_at m
  -- Build the ordered list
  set ordered := (withinOrd gi).foldl (fun acc ci' =>
      match (obsAll[gi]?.getD [])[ci']? with
      | some oid => acc ++ [oid]
      | none => acc) []
  set Wact := activateGroup Wproc ordered
  set ev := stageEvent actTick groups gi ci 0
  -- tick of W_at is t
  have h_tick_Wat : W_at.tick = t := by
    dsimp [W_at]; rw [gSimBurst_tick, h_tick_w]
  -- tick of Wproc is t
  have h_tick_Wproc : Wproc.tick = t := by
    dsimp [Wproc]; rw [processNEvents_tick, h_tick_Wat]
  -- tick of Wact is t
  have h_tick_Wact : Wact.tick = t := by
    dsimp [Wact]; rw [activateGroup_tick, h_tick_Wproc]
  -- The observer id is in ordered
  have h_nid : chainBaseId groups gi ci + 1 ∈ ordered :=
    obsId_mem_ordered withinOrd groups gi ci h_gi h_ci h_ci_in
  -- ev is in Wact.events
  have h_ev_Wact : ev ∈ Wact.events :=
    stageEvent0_mem_activateGroup Wproc ordered actTick groups gi ci
      h_nid (by rw [h_tick_Wproc, h_tick_act])
  -- ev.targetTick ≠ Wact.tick
  have h_nd : ev.targetTick ≠ Wact.tick := by
    dsimp [ev, stageEvent]
    rw [stageTarget_zero_eq, h_tick_Wact, h_tick_act]
    omega
  -- ev survives the remaining burst
  exact mem_gSimBurst_of_notDue t obsAll withinOrd pos Wact post ev
    h_ev_Wact h_nd

/-! ## Order preservation restatements -/

/-- Two non-due events preserve their evBefore order through the
    burst. -/
theorem evBefore_burst_of_notDue (t : Nat)
    (obsAll : List (List Nat)) (withinOrd pos : Nat → List Nat)
    (w : World) (pairs : List (Nat × Nat))
    (x y : ScheduledEvent)
    (h_nd_x : x.targetTick ≠ w.tick) (h_nd_y : y.targetTick ≠ w.tick)
    (h_before : evBefore w.events x y) :
    evBefore (gSimBurst t obsAll withinOrd pos w pairs).events x y :=
  evBefore_gSimBurst_of_notDue t obsAll withinOrd pos w pairs x y
    h_nd_x h_nd_y h_before

/-- Two non-due events preserve their evBefore order through
    stepUntilNextTick. -/
theorem evBefore_stepUNT_of_notDue (w : World)
    (x y : ScheduledEvent)
    (h_x : x ∈ w.events) (h_y : y ∈ w.events)
    (h_nd_x : x.targetTick ≠ w.tick) (h_nd_y : y.targetTick ≠ w.tick)
    (h_before : evBefore w.events x y) :
    evBefore w.stepUntilNextTick.events x y :=
  World.stepUntilNextTick_notDue_order w x y h_x h_y h_nd_x h_nd_y
    h_before

/-- Two events that target no tick in a range preserve their order
    across the tick-start queues. -/
theorem evBefore_gSimWorld_const (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (a b : Nat)
    (x y : ScheduledEvent)
    (h_le : a ≤ b)
    (h_before : evBefore
      (gSimWorld groups actTick groupOrd withinOrd pos a).events x y)
    (h_bx : b ≤ x.targetTick) (h_by : b ≤ y.targetTick) :
    evBefore
      (gSimWorld groups actTick groupOrd withinOrd pos b).events x y :=
  gSimWorld_evBefore_const groups actTick groupOrd withinOrd pos a b
    x y h_le h_before h_bx h_by

/-! ## Delay condition for simulation worlds -/

/-- The delay condition holds at every tick-start world. -/
theorem gSimWorld_delay_ge2 (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (t : Nat)
    (h_valid : ∀ gi (c : ChainSpec), gi < groups.length →
        c ∈ groupAt groups gi →
        (∀ d ∈ c.middleDelays, ValidDelay d) ∧ ValidDelay c.lastDelay) :
    ∀ nid nd,
      (gSimWorld groups actTick groupOrd withinOrd pos t).getNode nid =
        some nd →
      ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
  dsimp [gSimWorld]
  exact gSimFoldl_delay_preserved actTick (buildGroups groups).2 groupOrd
    withinOrd pos (buildGroups groups).1 t
    (buildGroups_delay_ge2 groups h_valid)

/-! ## Non-due event survives stepUntilNextTick -/

/-- A non-due event survives stepUntilNextTick when the delay
    condition holds. -/
theorem mem_stepUNT_of_notDue (w : World)
    (x : ScheduledEvent) (h_x : x ∈ w.events)
    (h_nd : x.targetTick ≠ w.tick)
    (h_delay : ∀ nid nd, w.getNode nid = some nd → ∀ d p,
        nd.kind = .repeater d p → d ≥ 2) :
    x ∈ w.stepUntilNextTick.events := by
  obtain ⟨new, h_split, _⟩ :=
    World.stepUntilNextTick_events_filter_split w h_delay
  rw [h_split]
  apply List.mem_append_left
  rw [List.mem_filter]
  refine ⟨h_x, ?_⟩
  simp [h_nd]

/-!
## What remains toward the order-preservation capstone

The three premises of QSideOrder.sameSpec_orderPreservation:

1. **h_base** (stage-0 order): This file proves that stage-0 events
   are created by the burst (`stageEvent0_mem_burst`) and that
   non-due events preserve order through the burst, stepUntilNextTick,
   and intermediate ticks. What remains is proving the initial order
   in the burst result. This requires showing that `activateGroup`
   appends observer events in `withinOrd`/`groupOrd` order and that
   `processNEvents` calls between two groups' `activateGroup` steps
   do not disturb the order.

2. **h_nodup** (due-filter Nodup): No `stepUntilNextTick` Nodup lemma
   exists in the project. The MiddleBlockOkTicks and OutputPositionBridge files document this
   gap. The proof requires a structural Nodup invariant for
   `stepUntilNextTick`, showing that spawn events from different nodes
   never collide and never collide with surviving non-due events.

3. **h_surv** (burst survival): The stage events at each pop tick
   are due events. Whether they survive the burst's `processNEvents`
   depends on the `processNEvents` count and the priority ordering.
   This file proves `stageEvent0_mem_burst` for the initial creation
   at the activation tick. For stages k >= 1, the stage events have
   priority -3 or -1 and are spawned by the previous stage's drain
   step. Proving survival requires showing the `processNEvents` count
   does not reach the stage events, which depends on the `pos`
   function and the full due-filter composition.
-/
