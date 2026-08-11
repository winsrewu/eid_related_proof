import BasicProofs.GroupClustering.SameSpecLockstep


open BasicRedstoneSim List

/-! # Group clustering — lockstep composition across ticks

Same-spec chains move in lockstep. This file composes the within-tick
lockstep of PopSeqFuel with the spawn characterization of SameSpecLockstep and states the
facts over the tick-start queues `(gSimWorld ... t).events`.

Contents:

* order preservation for non-due events across one tick transition
  (`processNEvents`, `activateGroup`, burst phases, `stepUntilNextTick`,
  `gSimBody`) and across whole ranges of ticks;
* layout-threaded variants of the within-tick lockstep lemmas, whose spawn
  hypotheses hold for every reachable world of the current tick;
* queue-health facts: the due-sublist stays duplicate-free through pops and
  burst phases, and a popped due event is detected by its absence;
* the single-tick lockstep step for same-spec stage events through one full
  `gSimBody` tick, including the burst phase;
* the stage-advance step: the relative order of same-spec stage-`j` events
  at their pop tick carries over to the stage-`j + 1` events.
-/

/-! ## Order of non-due events across one tick -/

/-- `processNEvents` keeps the order of two events that do not target the
    current tick. -/
theorem evBefore_processNEvents_of_notDue (w : World) (n : Nat)
    (x y : ScheduledEvent)
    (h_nx : x.targetTick ≠ w.tick) (h_ny : y.targetTick ≠ w.tick)
    (h_before : evBefore w.events x y) :
    evBefore (processNEvents w n).events x y := by
  rw [processNEvents_eq_popSeqWorldFuel]
  obtain ⟨h_split, _⟩ := World.popSeqWorldFuel_filter_split w n
  have h_keep_x : decide (x.targetTick ≠ w.tick) = true := by simp [h_nx]
  have h_keep_y : decide (y.targetTick ≠ w.tick) = true := by simp [h_ny]
  have h_f : evBefore
      (w.events.filter (fun ev => ev.targetTick ≠ w.tick)) x y :=
    evBefore.filter (fun ev => ev.targetTick ≠ w.tick) h_keep_x h_keep_y
      h_before
  have h_app : evBefore
      (w.events.filter (fun ev => ev.targetTick ≠ w.tick) ++
        World.popSpawnAcc w n) x y := evBefore.append_right h_f
  rw [← h_split] at h_app
  exact evBefore.of_filter (fun ev => ev.targetTick ≠ w.tick) h_app

/-- `activateGroup` appends the observer events at the end. The old order
    stays. -/
theorem evBefore_activateGroup (w : World) (observers : List Nat)
    (x y : ScheduledEvent) (h_before : evBefore w.events x y) :
    evBefore (activateGroup w observers).events x y := by
  rw [activateGroup_events_map]
  exact evBefore.append_right h_before

/-- A burst phase keeps the order of two events that do not target the
    current tick. -/
theorem evBefore_gSimBurst_of_notDue (t : Nat) (obsAll : List (List Nat))
    (withinOrd pos : Nat → List Nat) (w : World) (pairs : List (Nat × Nat))
    (x y : ScheduledEvent)
    (h_nx : x.targetTick ≠ w.tick) (h_ny : y.targetTick ≠ w.tick)
    (h_before : evBefore w.events x y) :
    evBefore (gSimBurst t obsAll withinOrd pos w pairs).events x y := by
  induction pairs generalizing w with
  | nil =>
    simp [gSimBurst]
    exact h_before
  | cons p ps ih =>
    simp only [gSimBurst, List.foldl_cons]
    rcases p with ⟨gi, k⟩
    set m := (pos t)[k]?.getD 0
    set ordered : List Nat := (withinOrd gi).foldl (fun acc ci =>
      match (obsAll[gi]?.getD [])[ci]? with
      | some oid => acc ++ [oid]
      | none => acc) []
    set Wproc := processNEvents w m
    set W₁ := activateGroup Wproc ordered
    have h_tick_W₁ : W₁.tick = w.tick := by
      dsimp [W₁, Wproc]
      rw [activateGroup_tick, processNEvents_tick]
    have h_step₁ : evBefore Wproc.events x y :=
      evBefore_processNEvents_of_notDue w m x y h_nx h_ny h_before
    have h_step₂ : evBefore W₁.events x y :=
      evBefore_activateGroup Wproc ordered x y h_step₁
    have h_nx_W₁ : x.targetTick ≠ W₁.tick := by rw [h_tick_W₁]; exact h_nx
    have h_ny_W₁ : y.targetTick ≠ W₁.tick := by rw [h_tick_W₁]; exact h_ny
    change evBefore (gSimBurst t obsAll withinOrd pos W₁ ps).events x y
    exact ih W₁ h_nx_W₁ h_ny_W₁ h_step₂

/-- One `gSimBody` call keeps the order of two events that do not target the
    current tick. -/
theorem evBefore_gSimBody_of_notDue (actTick : Nat → Nat)
    (obsAll : List (List Nat)) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (w : World) (i : Nat)
    (x y : ScheduledEvent)
    (h_nx : x.targetTick ≠ w.tick) (h_ny : y.targetTick ≠ w.tick)
    (h_before : evBefore w.events x y) :
    evBefore (gSimBody actTick obsAll groupOrd withinOrd pos w i).events x y := by
  dsimp [gSimBody]
  split_ifs with h_active
  · -- no group activates: logOutput then stepUntilNextTick
    set W₁ := w.logOutput s!"tick {w.tick}"
    have h_x_W₁ : x ∈ W₁.events := by
      dsimp [W₁]
      exact evBefore.mem_left h_before
    have h_y_W₁ : y ∈ W₁.events := by
      dsimp [W₁]
      exact evBefore.mem_right h_before
    have h_nx_W₁ : x.targetTick ≠ W₁.tick := by dsimp [W₁]; exact h_nx
    have h_ny_W₁ : y.targetTick ≠ W₁.tick := by dsimp [W₁]; exact h_ny
    have h_before_W₁ : ∃ l₁ l₂, W₁.events = l₁ ++ x :: l₂ ∧ y ∈ l₂ := by
      dsimp [W₁]
      exact h_before
    exact World.stepUntilNextTick_notDue_order W₁ x y h_x_W₁ h_y_W₁ h_nx_W₁
      h_ny_W₁ h_before_W₁
  · -- some groups activate: burst phase then stepUntilNextTick
    set W₁ := w.logOutput s!"tick {w.tick}"
    set active := groupOrd.filter (fun gi =>
      decide (gi < obsAll.length) && (actTick gi == w.tick))
    set W_B := gSimBurst w.tick obsAll withinOrd pos W₁ (active.zipIdx)
    have h_nx_W₁ : x.targetTick ≠ W₁.tick := by dsimp [W₁]; exact h_nx
    have h_ny_W₁ : y.targetTick ≠ W₁.tick := by dsimp [W₁]; exact h_ny
    have h_before_W₁ : evBefore W₁.events x y := by dsimp [W₁]; exact h_before
    have h_B : evBefore W_B.events x y :=
      evBefore_gSimBurst_of_notDue w.tick obsAll withinOrd pos W₁
        (active.zipIdx) x y h_nx_W₁ h_ny_W₁ h_before_W₁
    have h_WB_tick : W_B.tick = w.tick := by
      dsimp [W_B, W₁]
      rw [gSimBurst_tick, World.logOutput_tick]
    have h_x_B : x ∈ W_B.events := evBefore.mem_left h_B
    have h_y_B : y ∈ W_B.events := evBefore.mem_right h_B
    have h_nx_B : x.targetTick ≠ W_B.tick := by rw [h_WB_tick]; exact h_nx
    have h_ny_B : y.targetTick ≠ W_B.tick := by rw [h_WB_tick]; exact h_ny
    exact World.stepUntilNextTick_notDue_order W_B x y h_x_B h_y_B h_nx_B
      h_ny_B h_B

/-- The queue at tick-start `t + 1` keeps the order of two events of the
    queue at tick-start `t` when neither event targets tick `t`. -/
theorem gSimWorld_evBefore_notDue (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (t : Nat)
    (x y : ScheduledEvent)
    (h_nx : x.targetTick ≠ t) (h_ny : y.targetTick ≠ t)
    (h_before : evBefore
      (gSimWorld groups actTick groupOrd withinOrd pos t).events x y) :
    evBefore
      (gSimWorld groups actTick groupOrd withinOrd pos (t + 1)).events x y := by
  dsimp [gSimWorld] at h_before ⊢
  simp only [gSimFoldl, List.range_succ, List.foldl_append, List.foldl_cons,
    List.foldl_nil]
  set W : World := List.foldl
    (gSimBody actTick (buildGroups groups).2 groupOrd withinOrd pos)
    (buildGroups groups).1 (List.range t)
  have h_tick_W : W.tick = t := by
    change (gSimFoldl actTick (buildGroups groups).2 groupOrd withinOrd pos
      (buildGroups groups).1 t).tick = t
    rw [gSimFoldl_tick, buildGroups_tick]
    omega
  change evBefore
    (gSimBody actTick (buildGroups groups).2 groupOrd withinOrd pos W t).events
    x y
  exact evBefore_gSimBody_of_notDue actTick (buildGroups groups).2 groupOrd
    withinOrd pos W t x y (by rw [h_tick_W]; exact h_nx)
    (by rw [h_tick_W]; exact h_ny) h_before

/-- Two events that target no tick of a range keep their order across the
    whole range of tick-start queues. -/
theorem gSimWorld_evBefore_const (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (a b : Nat)
    (x y : ScheduledEvent)
    (h_le : a ≤ b)
    (h_before : evBefore
      (gSimWorld groups actTick groupOrd withinOrd pos a).events x y)
    (h_bx : b ≤ x.targetTick) (h_by : b ≤ y.targetTick) :
    evBefore
      (gSimWorld groups actTick groupOrd withinOrd pos b).events x y := by
  revert a h_le h_before h_bx h_by
  induction b with
  | zero =>
    intro a h_le h_before h_bx h_by
    have h_a0 : a = 0 := by omega
    subst h_a0
    exact h_before
  | succ b ih =>
    intro a h_le h_before h_bx h_by
    by_cases h_eq : a = b + 1
    · subst h_eq
      exact h_before
    · have h_lt : a ≤ b := by omega
      have h_step : evBefore
          (gSimWorld groups actTick groupOrd withinOrd pos b).events x y :=
        ih a h_lt h_before (by omega) (by omega)
      have h_nx : x.targetTick ≠ b := by omega
      have h_ny : y.targetTick ≠ b := by omega
      exact gSimWorld_evBefore_notDue groups actTick groupOrd withinOrd pos b
        x y h_nx h_ny h_step

/-! ## Layout-threaded within-tick lockstep -/

/-- The node layout depends only on the node list. -/
theorem NodeLayoutOk_of_nodes_eq (groups : List GroupSpec) (w w' : World)
    (h_nodes : w'.nodes = w.nodes) :
    NodeLayoutOk groups w → NodeLayoutOk groups w' := by
  intro H
  rcases H with ⟨hO, hM, hL, hOut⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro gi ci h_gi h_ci
    obtain ⟨nd, h, hk, ho⟩ := hO gi ci h_gi h_ci
    exact ⟨nd, by dsimp [World.getNode]; rw [h_nodes]; exact h, hk, ho⟩
  · intro gi ci k h_gi h_ci h_k
    obtain ⟨nd, h, hk, ho⟩ := hM gi ci k h_gi h_ci h_k
    exact ⟨nd, by dsimp [World.getNode]; rw [h_nodes]; exact h, hk, ho⟩
  · intro gi ci h_gi h_ci
    obtain ⟨nd, h, hk, ho⟩ := hL gi ci h_gi h_ci
    exact ⟨nd, by dsimp [World.getNode]; rw [h_nodes]; exact h, hk, ho⟩
  · intro gi ci h_gi h_ci
    obtain ⟨nd, h, hk, ho⟩ := hOut gi ci h_gi h_ci
    exact ⟨nd, by dsimp [World.getNode]; rw [h_nodes]; exact h, hk, ho⟩

/-- A present non-due event stays before the spawn of a due event, when the
    spawn equation is known for every reachable world with a good node
    layout. The due event fires during the tick and appends its spawn after
    every surviving event. -/
theorem World.presentNotDue_before_dueSpawn_layout (groups : List GroupSpec)
    (w : World) (e D sD : ScheduledEvent)
    (h_layout : NodeLayoutOk groups w)
    (h_e : e ∈ w.events) (h_nd_e : e.targetTick ≠ w.tick)
    (h_D : D ∈ w.events) (h_due_D : D.targetTick = w.tick)
    (h_sD_nd : sD.targetTick ≠ w.tick)
    (h_spawnD : ∀ (v : World), v.tick = w.tick → NodeLayoutOk groups v →
        (v.onScheduledTick D.nodeId).events = v.events ++ [sD]) :
    ∃ p q, w.stepUntilNextTick.events = p ++ e :: q ∧ sD ∈ q := by
  induction w using World.stepUntilNextTick.induct with
  | case1 x h_step =>
    -- D is present and due, so x.step cannot be none
    dsimp [World.step] at h_step
    cases h_pop : x.popNextEvent with
    | none =>
      exact False.elim (popNextEvent_none_no_events x h_pop D h_D h_due_D)
    | some p =>
      simp only [h_pop] at h_step
      cases h_step
  | case2 x w' h_step ih =>
    have h_layout_w' : NodeLayoutOk groups w' :=
      NodeLayoutOk_step groups x w' h_step h_layout
    have h_sunt : x.stepUntilNextTick = w'.stepUntilNextTick := by
      rw [World.stepUntilNextTick, h_step]
    dsimp [World.step] at h_step
    cases h_pop : x.popNextEvent with
    | none =>
      simp only [h_pop] at h_step
      cases h_step
    | some p =>
      rcases p with ⟨ev₀, w_pop⟩
      simp only [h_pop] at h_step
      injection h_step with h_w'
      obtain ⟨idx, h_idx, h_erase, h_tick_ev, _, h_get_idx⟩ :=
        World.popNextEvent_eraseIdx x ev₀ w_pop h_pop
      have h_tick_pop : w_pop.tick = x.tick :=
        World.popNextEvent_tick x ev₀ w_pop h_pop
      have h_layout_pop : NodeLayoutOk groups w_pop :=
        NodeLayoutOk_of_nodes_eq groups x w_pop
          (World.popNextEvent_nodes x ev₀ w_pop h_pop) h_layout
      have h_ev_ne_e : ev₀ ≠ e := fun h ↦ h_nd_e (h ▸ h_tick_ev)
      by_cases h_ev_D : ev₀ = D
      · -- the popped event is D: sD is appended now, right after e
        have h_w'_events : w'.events = w_pop.events ++ [sD] := by
          rw [← h_w', h_ev_D]
          exact h_spawnD w_pop h_tick_pop h_layout_pop
        have h_e_pop : e ∈ w_pop.events := by
          rw [h_erase]
          exact mem_eraseIdx_of_ne x.events idx h_idx ev₀ e h_get_idx h_e
            (Ne.symm h_ev_ne_e)
        obtain ⟨p₀, q₀, h_peq⟩ : ∃ p q, w_pop.events = p ++ e :: q :=
          mem_split_append w_pop.events e h_e_pop
        have h_split_w' : w'.events = p₀ ++ e :: (q₀ ++ [sD]) := by
          rw [h_w'_events, h_peq, List.append_assoc, List.cons_append]
        have h_e_w' : e ∈ w'.events := by
          rw [h_w'_events]
          exact List.mem_append_left _ h_e_pop
        have h_sD_w' : sD ∈ w'.events := by
          rw [h_w'_events]
          exact List.mem_append_right _ (by simp)
        have h_tick_w' : w'.tick = x.tick := by
          rw [← h_w', World.onScheduledTick_tick, h_tick_pop]
        have h_nd_e_w' : e.targetTick ≠ w'.tick := by
          rw [h_tick_w']
          exact h_nd_e
        have h_sD_nd_w' : sD.targetTick ≠ w'.tick := by
          rw [h_tick_w']
          exact h_sD_nd
        have h_before_w' : ∃ l₁ l₂, w'.events = l₁ ++ e :: l₂ ∧ sD ∈ l₂ :=
          ⟨p₀, q₀ ++ [sD], h_split_w', List.mem_append_right _ (by simp)⟩
        obtain ⟨p, q, h_tail, h_sD_q⟩ :=
          World.stepUntilNextTick_notDue_order w' e sD h_e_w' h_sD_w'
            h_nd_e_w' h_sD_nd_w' h_before_w'
        rw [h_sunt]
        exact ⟨p, q, h_tail, h_sD_q⟩
      · -- some other event is popped: e and D both survive; apply the IH
        have h_ev_ne_D : ev₀ ≠ D := h_ev_D
        have h_e_pop : e ∈ w_pop.events := by
          rw [h_erase]
          exact mem_eraseIdx_of_ne x.events idx h_idx ev₀ e h_get_idx h_e
            (Ne.symm h_ev_ne_e)
        have h_D_pop : D ∈ w_pop.events := by
          rw [h_erase]
          exact mem_eraseIdx_of_ne x.events idx h_idx ev₀ D h_get_idx h_D
            (Ne.symm h_ev_ne_D)
        obtain ⟨new₀, h_app_new, _⟩ :=
          World.onScheduledTick_appends_future w_pop ev₀.nodeId
        have h_e_w' : e ∈ w'.events := by
          rw [← h_w', h_app_new]
          exact List.mem_append_left _ h_e_pop
        have h_D_w' : D ∈ w'.events := by
          rw [← h_w', h_app_new]
          exact List.mem_append_left _ h_D_pop
        have h_tick_w' : w'.tick = x.tick := by
          rw [← h_w', World.onScheduledTick_tick, h_tick_pop]
        have h_nd_e_w' : e.targetTick ≠ w'.tick := by
          rw [h_tick_w']
          exact h_nd_e
        have h_due_D_w' : D.targetTick = w'.tick := by
          rw [h_tick_w']
          exact h_due_D
        have h_sD_nd_w' : sD.targetTick ≠ w'.tick := by
          rw [h_tick_w']
          exact h_sD_nd
        have h_spawnD_w' : ∀ (v : World), v.tick = w'.tick →
            NodeLayoutOk groups v →
            (v.onScheduledTick D.nodeId).events = v.events ++ [sD] :=
          fun v h_v ↦ h_spawnD v (h_v.trans h_tick_w')
        obtain ⟨p, q, h_tail, h_sD_q⟩ :=
          ih h_layout_w' h_e_w' h_nd_e_w' h_D_w' h_due_D_w' h_sD_nd_w'
            h_spawnD_w'
        rw [h_sunt]
        exact ⟨p, q, h_tail, h_sD_q⟩

/-- Within one tick, two same-priority due events `A` (before) and `D`
    (after) spawn `sA` and `sD` with `sA` before `sD` in the resulting
    queue. The spawn equations only need to hold for reachable worlds with a
    good node layout. The layout persists through every pop of the tick. -/
theorem World.samePriLockstep_layout (groups : List GroupSpec) (w : World)
    (A D sA sD : ScheduledEvent)
    (h_layout : NodeLayoutOk groups w)
    (hA_mem : A ∈ w.events) (hD_mem : D ∈ w.events)
    (hA_due : A.targetTick = w.tick) (hD_due : D.targetTick = w.tick)
    (h_pri : A.priority = D.priority)
    (h_nodup : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup)
    (h_before : ∃ l₁ l₂, w.events.filter (fun e => e.targetTick == w.tick) =
      l₁ ++ A :: l₂ ∧ D ∈ l₂)
    (h_sA_nd : sA.targetTick ≠ w.tick) (h_sD_nd : sD.targetTick ≠ w.tick)
    (h_spawnA : ∀ (v : World), v.tick = w.tick → NodeLayoutOk groups v →
        (v.onScheduledTick A.nodeId).events = v.events ++ [sA])
    (h_spawnD : ∀ (v : World), v.tick = w.tick → NodeLayoutOk groups v →
        (v.onScheduledTick D.nodeId).events = v.events ++ [sD]) :
    ∃ p q, w.stepUntilNextTick.events = p ++ sA :: q ∧ sD ∈ q := by
  induction w using World.stepUntilNextTick.induct with
  | case1 x h_step =>
    dsimp [World.step] at h_step
    cases h_pop : x.popNextEvent with
    | none =>
      exact False.elim (popNextEvent_none_no_events x h_pop A hA_mem hA_due)
    | some p =>
      simp only [h_pop] at h_step
      cases h_step
  | case2 x w' h_step ih =>
    have h_layout_w' : NodeLayoutOk groups w' :=
      NodeLayoutOk_step groups x w' h_step h_layout
    have h_sunt : x.stepUntilNextTick = w'.stepUntilNextTick := by
      rw [World.stepUntilNextTick, h_step]
    dsimp [World.step] at h_step
    cases h_pop : x.popNextEvent with
    | none =>
      simp only [h_pop] at h_step
      cases h_step
    | some p =>
      rcases p with ⟨ev₀, w_pop⟩
      simp only [h_pop] at h_step
      injection h_step with h_w'
      obtain ⟨l₁, l₂, h_split, hD_l₂⟩ := h_before
      have h_ev_ne_D : ev₀ ≠ D :=
        popNextEvent_not_D_of_append_split x A D ev₀ w_pop h_pop h_nodup l₁ l₂
          h_split hD_l₂ (by omega)
      obtain ⟨idx, h_idx, h_erase, h_tick_ev, _, h_get_idx⟩ :=
        World.popNextEvent_eraseIdx x ev₀ w_pop h_pop
      have h_tick_pop : w_pop.tick = x.tick :=
        World.popNextEvent_tick x ev₀ w_pop h_pop
      have h_tick_w' : w'.tick = x.tick := by
        rw [← h_w', World.onScheduledTick_tick, h_tick_pop]
      have h_layout_pop : NodeLayoutOk groups w_pop :=
        NodeLayoutOk_of_nodes_eq groups x w_pop
          (World.popNextEvent_nodes x ev₀ w_pop h_pop) h_layout
      by_cases h_ev_A : ev₀ = A
      · -- the popped event is A itself: sA is appended now, D remains due
        have h_w'_events : w'.events = w_pop.events ++ [sA] := by
          rw [← h_w', h_ev_A]
          exact h_spawnA w_pop h_tick_pop h_layout_pop
        have h_sA_mem : sA ∈ w'.events := by
          rw [h_w'_events]
          exact List.mem_append_right _ (by simp)
        have h_sA_nd_w' : sA.targetTick ≠ w'.tick := by
          rw [h_tick_w']
          exact h_sA_nd
        have h_get_idx_A : x.events[idx]'h_idx = A := h_get_idx.trans h_ev_A
        have hD_ne_A : D ≠ A := fun h ↦ h_ev_ne_D (h_ev_A.trans h.symm)
        have hD_mem_pop : D ∈ w_pop.events := by
          rw [h_erase]
          exact mem_eraseIdx_of_ne x.events idx h_idx A D h_get_idx_A hD_mem
            hD_ne_A
        have hD_mem_w' : D ∈ w'.events := by
          rw [h_w'_events]
          exact List.mem_append_left _ hD_mem_pop
        have hD_due_w' : D.targetTick = w'.tick := by
          rw [h_tick_w']
          exact hD_due
        have h_sD_nd_w' : sD.targetTick ≠ w'.tick := by
          rw [h_tick_w']
          exact h_sD_nd
        have h_spawnD_w' : ∀ (v : World), v.tick = w'.tick →
            NodeLayoutOk groups v →
            (v.onScheduledTick D.nodeId).events = v.events ++ [sD] :=
          fun v h_v ↦ h_spawnD v (h_v.trans h_tick_w')
        obtain ⟨p, q, h_tail, h_sD_q⟩ :=
          World.presentNotDue_before_dueSpawn_layout groups w' sA D sD
            h_layout_w' h_sA_mem h_sA_nd_w' hD_mem_w' hD_due_w' h_sD_nd_w'
            h_spawnD_w'
        rw [h_sunt]
        exact ⟨p, q, h_tail, h_sD_q⟩
      · -- some other event is popped: A and D both survive; apply the IH
        set due := x.events.filter (fun e => e.targetTick == x.tick)
        have h_due_ev₀ : (fun e => e.targetTick == x.tick)
            (x.events[idx]'h_idx) = true := by
          simp [h_get_idx, h_tick_ev]
        obtain ⟨j, hj, h_filter_erase, h_get_due⟩ :=
          filter_eraseIdx_getElem (fun e => e.targetTick == x.tick) x.events
            idx h_idx h_due_ev₀
        have h_get_due_ev₀ : due[j]'hj = ev₀ := h_get_due.trans h_get_idx
        obtain ⟨new, h_app_new, h_fut_new⟩ :=
          World.onScheduledTick_appends_future w_pop ev₀.nodeId
        have h_due_tail : w'.events.filter (fun e => e.targetTick == w'.tick) =
            due.eraseIdx j := by
          rw [← h_w', World.onScheduledTick_tick, h_tick_pop, h_app_new,
            List.filter_append]
          have h_new_nil : new.filter (fun e => e.targetTick == x.tick) = [] :=
            by
            apply List.filter_eq_nil_iff.mpr
            intro e h_e
            have h_gt := h_fut_new e h_e
            rw [h_tick_pop] at h_gt
            simp
            omega
          rw [h_new_nil, List.append_nil, h_erase, h_filter_erase]
        have hA_mem_pop : A ∈ w_pop.events := by
          rw [h_erase]
          exact mem_eraseIdx_of_ne x.events idx h_idx ev₀ A h_get_idx hA_mem
            (Ne.symm h_ev_A)
        have hD_mem_pop : D ∈ w_pop.events := by
          rw [h_erase]
          exact mem_eraseIdx_of_ne x.events idx h_idx ev₀ D h_get_idx hD_mem
            (Ne.symm h_ev_ne_D)
        have hA_mem_w' : A ∈ w'.events := by
          rw [← h_w', h_app_new]
          exact List.mem_append_left _ hA_mem_pop
        have hD_mem_w' : D ∈ w'.events := by
          rw [← h_w', h_app_new]
          exact List.mem_append_left _ hD_mem_pop
        have hA_due_w' : A.targetTick = w'.tick := by
          rw [h_tick_w']
          exact hA_due
        have hD_due_w' : D.targetTick = w'.tick := by
          rw [h_tick_w']
          exact hD_due
        have h_sA_nd_w' : sA.targetTick ≠ w'.tick := by
          rw [h_tick_w']
          exact h_sA_nd
        have h_sD_nd_w' : sD.targetTick ≠ w'.tick := by
          rw [h_tick_w']
          exact h_sD_nd
        have h_nodup_w' :
            (w'.events.filter (fun e => e.targetTick == w'.tick)).Nodup := by
          rw [h_due_tail]
          exact nodup_eraseIdx due j h_nodup
        have h_before_w' : ∃ m₁ m₂,
            w'.events.filter (fun e => e.targetTick == w'.tick) =
              m₁ ++ A :: m₂ ∧ D ∈ m₂ := by
          rw [h_due_tail]
          obtain ⟨m₁, m₂, h_eq, hD_m₂⟩ :=
            eraseIdx_preserves_order due l₁ l₂ A D ev₀ h_split hD_l₂ h_ev_A
              h_ev_ne_D j hj h_get_due_ev₀
          exact ⟨m₁, m₂, h_eq, hD_m₂⟩
        have h_spawnA_w' : ∀ (v : World), v.tick = w'.tick →
            NodeLayoutOk groups v →
            (v.onScheduledTick A.nodeId).events = v.events ++ [sA] :=
          fun v h_v ↦ h_spawnA v (h_v.trans h_tick_w')
        have h_spawnD_w' : ∀ (v : World), v.tick = w'.tick →
            NodeLayoutOk groups v →
            (v.onScheduledTick D.nodeId).events = v.events ++ [sD] :=
          fun v h_v ↦ h_spawnD v (h_v.trans h_tick_w')
        obtain ⟨p, q, h_tail, h_sD_q⟩ :=
          ih h_layout_w' hA_mem_w' hD_mem_w' hA_due_w' hD_due_w' h_nodup_w'
            h_before_w' h_sA_nd_w' h_sD_nd_w' h_spawnA_w' h_spawnD_w'
        rw [h_sunt]
        exact ⟨p, q, h_tail, h_sD_q⟩

/-! ## The single-tick lockstep step for same-spec stage events -/

/-- Stage targets grow strictly with the stage while the stage index is in
    range. -/
theorem stageTarget_lt_succ (actTick : Nat → Nat) (groups : List GroupSpec)
    (gi ci j : Nat)
    (h_j : j ≤ (chainAt groups gi ci).middleDelays.length) :
    stageTarget actTick groups gi ci j <
    stageTarget actTick groups gi ci (j + 1) := by
  dsimp only [stageTarget]
  have h_lt := stageCumDelay_lt_succ (chainAt groups gi ci) j (by omega)
  omega

/-- At their common pop tick, two same-spec stage-`j` events pop in queue
    order and spawn their stage-`j + 1` events in the same order. This is
    the single-tick lockstep step: it joins `samePriLockstep_layout` with
    `stage_spawn`. -/
theorem sameSpec_stage_lockstep_step (groups : List GroupSpec)
    (actTick : Nat → Nat) (w : World) (g₁ c₁ g₂ c₂ j : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_spec : chainAt groups g₁ c₁ = chainAt groups g₂ c₂)
    (h_act_eq : actTick g₁ = actTick g₂)
    (h_layout : NodeLayoutOk groups w)
    (h_j : j ≤ (chainAt groups g₁ c₁).middleDelays.length)
    (h_due : w.tick = stageTarget actTick groups g₁ c₁ j)
    (hA_mem : stageEvent actTick groups g₁ c₁ j ∈ w.events)
    (hD_mem : stageEvent actTick groups g₂ c₂ j ∈ w.events)
    (h_nodup : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup)
    (h_before : evBefore
        (w.events.filter (fun e => e.targetTick == w.tick))
        (stageEvent actTick groups g₁ c₁ j)
        (stageEvent actTick groups g₂ c₂ j)) :
    evBefore w.stepUntilNextTick.events
      (stageEvent actTick groups g₁ c₁ (j + 1))
      (stageEvent actTick groups g₂ c₂ (j + 1)) := by
  set A := stageEvent actTick groups g₁ c₁ j
  set D := stageEvent actTick groups g₂ c₂ j
  set sA := stageEvent actTick groups g₁ c₁ (j + 1)
  set sD := stageEvent actTick groups g₂ c₂ (j + 1)
  have h_tgt_eq : stageTarget actTick groups g₂ c₂ j =
      stageTarget actTick groups g₁ c₁ j :=
    sameSpec_stageTarget groups actTick g₂ c₂ g₁ c₁ j h_act_eq.symm h_spec.symm
  have hA_due : A.targetTick = w.tick := by
    show stageTarget actTick groups g₁ c₁ j = w.tick
    exact h_due.symm
  have hD_due : D.targetTick = w.tick := by
    show stageTarget actTick groups g₂ c₂ j = w.tick
    rw [h_tgt_eq]
    exact h_due.symm
  have h_pri : A.priority = D.priority := by
    show stagePri groups g₁ c₁ j = stagePri groups g₂ c₂ j
    exact sameSpec_stagePri groups g₁ c₁ g₂ c₂ j h_spec
  have h_j₂ : j ≤ (chainAt groups g₂ c₂).middleDelays.length := by
    rw [← h_spec]
    exact h_j
  have h_sA_nd : sA.targetTick ≠ w.tick := by
    show stageTarget actTick groups g₁ c₁ (j + 1) ≠ w.tick
    rw [h_due]
    exact Ne.symm (Nat.ne_of_lt
      (stageTarget_lt_succ actTick groups g₁ c₁ j h_j))
  have h_sD_nd : sD.targetTick ≠ w.tick := by
    show stageTarget actTick groups g₂ c₂ (j + 1) ≠ w.tick
    rw [h_due]
    intro h_eq
    have h_lt_D := stageTarget_lt_succ actTick groups g₂ c₂ j h_j₂
    rw [h_tgt_eq] at h_lt_D
    rw [h_eq] at h_lt_D
    exact Nat.lt_irrefl _ h_lt_D
  have h_spawnA : ∀ (v : World), v.tick = w.tick → NodeLayoutOk groups v →
      (v.onScheduledTick A.nodeId).events = v.events ++ [sA] := by
    intro v h_v h_lay
    simpa [A, sA, stageEvent] using
      stage_spawn groups actTick v g₁ c₁ j h_g₁ h_c₁ h_j
        (h_v.trans h_due) h_lay
  have h_spawnD : ∀ (v : World), v.tick = w.tick → NodeLayoutOk groups v →
      (v.onScheduledTick D.nodeId).events = v.events ++ [sD] := by
    intro v h_v h_lay
    simpa [D, sD, stageEvent] using
      stage_spawn groups actTick v g₂ c₂ j h_g₂ h_c₂ h_j₂
        ((h_v.trans h_due).trans h_tgt_eq.symm) h_lay
  exact World.samePriLockstep_layout groups w A D sA sD h_layout hA_mem hD_mem
    hA_due hD_due h_pri h_nodup h_before h_sA_nd h_sD_nd h_spawnA h_spawnD

/-! ## Membership and due-filter facts for burst phases -/

/-- A Nat inequality decides the `==` comparison to false. -/
private theorem tick_beq_false_of_ne (a b : Nat) (h : a ≠ b) :
    (a == b) = false := by
  simp [h]

/-- A filter that rejects every element returns the empty list. -/
private theorem filter_nil_of_forall_false {α : Type} (p : α → Bool)
    (l : List α) (h : ∀ x ∈ l, p x = false) : l.filter p = [] := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have h_a := h a (List.mem_cons.mpr (Or.inl rfl))
    simp [List.filter, h_a,
      ih (fun x hx => h x (List.mem_cons.mpr (Or.inr hx)))]

/-- `activateGroup` appends events targeting tick `+ 2`. The due-filter of
    the queue does not change. -/
theorem activateGroup_due_filter (w : World) (observers : List Nat) :
    (activateGroup w observers).events.filter
        (fun e => e.targetTick == w.tick) =
    w.events.filter (fun e => e.targetTick == w.tick) := by
  rw [activateGroup_events_map, List.filter_append]
  have h_nil :
      (observers.map (fun nid =>
        ({ targetTick := w.tick + 2, priority := 0, nodeId := nid } :
          ScheduledEvent))).filter (fun e => e.targetTick == w.tick) = [] := by
    apply filter_nil_of_forall_false
    intro ev h_ev
    obtain ⟨nid, _, h_ev_eq⟩ := List.mem_map.mp h_ev
    rw [← h_ev_eq]
    exact tick_beq_false_of_ne (w.tick + 2) w.tick (by omega)
  rw [h_nil, List.append_nil]

/-- An event that does not target the current tick survives
    `processNEvents`. -/
theorem mem_processNEvents_of_notDue (w : World) (n : Nat)
    (x : ScheduledEvent)
    (h_x : x ∈ w.events) (h_nd : x.targetTick ≠ w.tick) :
    x ∈ (processNEvents w n).events := by
  induction n generalizing w with
  | zero =>
    simp [processNEvents]
    exact h_x
  | succ n ih =>
    dsimp only [processNEvents]
    cases h_step : w.step with
    | none => exact h_x
    | some w' =>
      dsimp [World.step] at h_step
      cases h_pop : w.popNextEvent with
      | none => simp [h_pop] at h_step
      | some p =>
        rcases p with ⟨ev₀, w_pop⟩
        simp only [h_pop] at h_step
        injection h_step with h_w'
        obtain ⟨idx, h_idx, h_erase, h_tick_ev, _, h_get_idx⟩ :=
          World.popNextEvent_eraseIdx w ev₀ w_pop h_pop
        have h_ev_ne_x : ev₀ ≠ x := fun h ↦ h_nd (h ▸ h_tick_ev)
        have h_x_pop : x ∈ w_pop.events := by
          rw [h_erase]
          exact mem_eraseIdx_of_ne w.events idx h_idx ev₀ x h_get_idx
            h_x (Ne.symm h_ev_ne_x)
        obtain ⟨new₀, h_app_new, _⟩ :=
          World.onScheduledTick_appends_future w_pop ev₀.nodeId
        have h_x_w' : x ∈ w'.events := by
          rw [← h_w', h_app_new]
          exact List.mem_append_left _ h_x_pop
        have h_nd_w' : x.targetTick ≠ w'.tick := by
          rw [← h_w', World.onScheduledTick_tick,
            World.popNextEvent_tick w ev₀ w_pop h_pop]
          exact h_nd
        exact ih w' h_x_w' h_nd_w'

/-- An event that targets the current tick and is still queued after
    `processNEvents` was already queued before it. -/
theorem mem_processNEvents_due_back (w : World) (n : Nat)
    (x : ScheduledEvent)
    (h_x : x ∈ (processNEvents w n).events)
    (h_due : x.targetTick = w.tick) : x ∈ w.events := by
  induction n generalizing w with
  | zero =>
    simp [processNEvents] at h_x
    exact h_x
  | succ n ih =>
    dsimp only [processNEvents] at h_x
    cases h_step : w.step with
    | none =>
      simp only [h_step] at h_x
      exact h_x
    | some w' =>
      simp only [h_step] at h_x
      dsimp [World.step] at h_step
      cases h_pop : w.popNextEvent with
      | none => simp [h_pop] at h_step
      | some p =>
        rcases p with ⟨ev₀, w_pop⟩
        simp only [h_pop] at h_step
        injection h_step with h_w'
        obtain ⟨idx, h_idx, h_erase, h_tick_ev, _, h_get_idx⟩ :=
          World.popNextEvent_eraseIdx w ev₀ w_pop h_pop
        have h_tick_pop : w_pop.tick = w.tick :=
          World.popNextEvent_tick w ev₀ w_pop h_pop
        have h_tick_w' : w'.tick = w.tick := by
          rw [← h_w', World.onScheduledTick_tick, h_tick_pop]
        have h_due_w' : x.targetTick = w'.tick := by
          rw [h_due, h_tick_w']
        have h_x_w' : x ∈ w'.events := ih w' h_x h_due_w'
        obtain ⟨new₀, h_app_new, h_fut_new⟩ :=
          World.onScheduledTick_appends_future w_pop ev₀.nodeId
        rw [← h_w', h_app_new, List.mem_append] at h_x_w'
        rcases h_x_w' with h_x_w' | h_x_new
        · rw [h_erase] at h_x_w'
          exact List.eraseIdx_subset' w.events idx h_x_w'
        · have h_gt := h_fut_new x h_x_new
          rw [h_tick_pop, h_due] at h_gt
          omega

/-- A due event queued after a burst phase was already queued before the
    burst phase: burst phases only append strictly future events. -/
theorem mem_gSimBurst_due_back (t : Nat) (obsAll : List (List Nat))
    (withinOrd pos : Nat → List Nat) (w : World)
    (pairs : List (Nat × Nat)) (x : ScheduledEvent)
    (h_x : x ∈ (gSimBurst t obsAll withinOrd pos w pairs).events)
    (h_due : x.targetTick = w.tick) : x ∈ w.events := by
  induction pairs generalizing w with
  | nil =>
    simp [gSimBurst] at h_x
    exact h_x
  | cons p ps ih =>
    simp only [gSimBurst, List.foldl_cons] at h_x
    rcases p with ⟨gi, k⟩
    set m := (pos t)[k]?.getD 0
    set ordered : List Nat := (withinOrd gi).foldl (fun acc ci =>
      match (obsAll[gi]?.getD [])[ci]? with
      | some oid => acc ++ [oid]
      | none => acc) []
    set Wproc := processNEvents w m
    set W₁ := activateGroup Wproc ordered
    change x ∈ (gSimBurst t obsAll withinOrd pos W₁ ps).events at h_x
    have h_tick_W₁ : W₁.tick = w.tick := by
      dsimp [W₁, Wproc]
      rw [activateGroup_tick, processNEvents_tick]
    have h_x_W₁ : x ∈ W₁.events :=
      ih W₁ h_x (by rw [h_due, h_tick_W₁])
    have h_x_proc : x ∈ Wproc.events := by
      dsimp [W₁] at h_x_W₁
      rw [activateGroup_events_map, List.mem_append] at h_x_W₁
      rcases h_x_W₁ with h_x_W₁ | h_obs
      · exact h_x_W₁
      · rcases List.mem_map.mp h_obs with ⟨nid, _, h_ev_eq⟩
        have h_tgt : x.targetTick = Wproc.tick + 2 := by
          rw [← h_ev_eq]
        have h_tick_proc : Wproc.tick = w.tick := by
          dsimp [Wproc]
          exact processNEvents_tick w m
        rw [h_tgt, h_tick_proc] at h_due
        omega
    exact mem_processNEvents_due_back w m x h_x_proc h_due

/-- An event that does not target the current tick survives a whole burst
    phase. -/
theorem mem_gSimBurst_of_notDue (t : Nat) (obsAll : List (List Nat))
    (withinOrd pos : Nat → List Nat) (w : World)
    (pairs : List (Nat × Nat)) (x : ScheduledEvent)
    (h_x : x ∈ w.events) (h_nd : x.targetTick ≠ w.tick) :
    x ∈ (gSimBurst t obsAll withinOrd pos w pairs).events := by
  induction pairs generalizing w with
  | nil =>
    simp [gSimBurst]
    exact h_x
  | cons p ps ih =>
    simp only [gSimBurst, List.foldl_cons]
    rcases p with ⟨gi, k⟩
    set m := (pos t)[k]?.getD 0
    set ordered : List Nat := (withinOrd gi).foldl (fun acc ci =>
      match (obsAll[gi]?.getD [])[ci]? with
      | some oid => acc ++ [oid]
      | none => acc) []
    set Wproc := processNEvents w m
    set W₁ := activateGroup Wproc ordered
    have h_tick_W₁ : W₁.tick = w.tick := by
      dsimp [W₁, Wproc]
      rw [activateGroup_tick, processNEvents_tick]
    have h_x_proc : x ∈ Wproc.events :=
      mem_processNEvents_of_notDue w m x h_x h_nd
    have h_x_W₁ : x ∈ W₁.events := by
      dsimp [W₁]
      rw [activateGroup_events_map]
      exact List.mem_append_left _ h_x_proc
    change x ∈ (gSimBurst t obsAll withinOrd pos W₁ ps).events
    exact ih W₁ h_x_W₁ (by rw [h_tick_W₁]; exact h_nd)

/-! ## Due-filter health through pops and bursts -/

/-- Erasing the element at index `j` of a duplicate-free list removes the
    only copy of that element. -/
private theorem nodup_eraseIdx_not_mem {α : Type} [DecidableEq α]
    (l : List α) (j : Nat) (hj : j < l.length) (h_nd : l.Nodup) (a : α)
    (h_get : l[j]'hj = a) : a ∉ l.eraseIdx j := by
  revert j hj h_nd h_get
  induction l with
  | nil => intro j hj; cases hj
  | cons x l ih =>
    intro j hj h_nd h_get
    rw [List.nodup_cons] at h_nd
    cases j with
    | zero =>
      dsimp at h_get
      dsimp [List.eraseIdx]
      rw [← h_get]
      exact h_nd.1
    | succ j' =>
      have hj' : j' < l.length := by simpa [List.length] using hj
      simp only [List.getElem_cons_succ] at h_get
      dsimp [List.eraseIdx]
      intro h_mem
      rw [List.mem_cons] at h_mem
      rcases h_mem with h_eq | h_mem
      · have h_x_l : x ∈ l := by
          rw [← h_eq, ← h_get]
          exact List.getElem_mem hj'
        exact h_nd.1 h_x_l
      · exact ih j' hj' h_nd.2 h_get h_mem

/-- Fuel-bounded pops keep the due-filter duplicate-free. -/
theorem World.popSeqWorldFuel_due_nodup (w : World) (fuel : Nat)
    (h_nd : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup) :
    ((World.popSeqWorldFuel w fuel).events.filter
        (fun e => e.targetTick == (World.popSeqWorldFuel w fuel).tick)).Nodup :=
  by
  induction fuel generalizing w with
  | zero =>
    dsimp only [World.popSeqWorldFuel]
    exact h_nd
  | succ fuel ih =>
    dsimp only [World.popSeqWorldFuel]
    cases h_pop : w.popNextEvent with
    | none => exact h_nd
    | some p =>
      rcases p with ⟨ev₀, w_pop⟩
      set due := w.events.filter (fun e => e.targetTick == w.tick)
      obtain ⟨idx, h_idx, h_erase, h_tick_ev, _, h_get_idx⟩ :=
        World.popNextEvent_eraseIdx w ev₀ w_pop h_pop
      have h_tick_pop : w_pop.tick = w.tick :=
        World.popNextEvent_tick w ev₀ w_pop h_pop
      have h_due_ev₀ : (fun e => e.targetTick == w.tick)
          (w.events[idx]'h_idx) = true := by
        rw [h_get_idx]
        simp [h_tick_ev]
      obtain ⟨j, hj, h_filter_erase, h_get_due⟩ :=
        filter_eraseIdx_getElem (fun e => e.targetTick == w.tick) w.events
          idx h_idx h_due_ev₀
      have h_get_due_ev₀ : due[j]'hj = ev₀ := h_get_due.trans h_get_idx
      obtain ⟨new, h_app_new, h_fut_new⟩ :=
        World.onScheduledTick_appends_future w_pop ev₀.nodeId
      have h_w'_tick : (w_pop.onScheduledTick ev₀.nodeId).tick = w.tick := by
        rw [World.onScheduledTick_tick, h_tick_pop]
      have h_due_tail :
          (w_pop.onScheduledTick ev₀.nodeId).events.filter
              (fun e => e.targetTick ==
                (w_pop.onScheduledTick ev₀.nodeId).tick) =
          due.eraseIdx j := by
        rw [h_w'_tick, h_app_new, List.filter_append]
        have h_new_nil : new.filter (fun e => e.targetTick == w.tick) = [] :=
          filter_nil_of_forall_false (fun e => e.targetTick == w.tick) new (by
            intro e h_e
            have h_gt := h_fut_new e h_e
            rw [h_tick_pop] at h_gt
            exact tick_beq_false_of_ne e.targetTick w.tick (by omega))
        rw [h_new_nil, List.append_nil, h_erase, h_filter_erase]
      exact ih (w_pop.onScheduledTick ev₀.nodeId) (by
        rw [h_due_tail]
        exact nodup_eraseIdx due j h_nd)

/-- `processNEvents` keeps the due-filter duplicate-free. -/
theorem processNEvents_due_nodup (w : World) (n : Nat)
    (h_nd : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup) :
    ((processNEvents w n).events.filter
        (fun e => e.targetTick == (processNEvents w n).tick)).Nodup := by
  have h := World.popSeqWorldFuel_due_nodup w n h_nd
  rw [World.popSeqWorldFuel_tick w n] at h
  rw [processNEvents_eq_popSeqWorldFuel]
  rw [show (World.popSeqWorldFuel w n).tick = w.tick from
    World.popSeqWorldFuel_tick w n]
  exact h

/-- A burst phase keeps the due-filter duplicate-free. -/
theorem gSimBurst_due_nodup (t : Nat) (obsAll : List (List Nat))
    (withinOrd pos : Nat → List Nat) (w : World)
    (pairs : List (Nat × Nat))
    (h_nd : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup) :
    ((gSimBurst t obsAll withinOrd pos w pairs).events.filter
        (fun e => e.targetTick ==
          (gSimBurst t obsAll withinOrd pos w pairs).tick)).Nodup := by
  induction pairs generalizing w with
  | nil =>
    simp [gSimBurst]
    exact h_nd
  | cons p ps ih =>
    simp only [gSimBurst, List.foldl_cons]
    rcases p with ⟨gi, k⟩
    set m := (pos t)[k]?.getD 0
    set ordered : List Nat := (withinOrd gi).foldl (fun acc ci =>
      match (obsAll[gi]?.getD [])[ci]? with
      | some oid => acc ++ [oid]
      | none => acc) []
    set Wproc := processNEvents w m
    set W₁ := activateGroup Wproc ordered
    have h_nd_proc : (Wproc.events.filter
        (fun e => e.targetTick == Wproc.tick)).Nodup := by
      dsimp [Wproc]
      exact processNEvents_due_nodup w m h_nd
    have h_nd_W₁ : (W₁.events.filter
        (fun e => e.targetTick == W₁.tick)).Nodup := by
      dsimp [W₁]
      rw [activateGroup_tick, activateGroup_due_filter]
      exact h_nd_proc
    change ((gSimBurst t obsAll withinOrd pos W₁ ps).events.filter
        (fun e => e.targetTick ==
          (gSimBurst t obsAll withinOrd pos W₁ ps).tick)).Nodup
    exact ih W₁ h_nd_W₁

/-- `processNEvents` keeps the due-filter order of two due events that
    survive it. -/
theorem evBefore_due_processNEvents_of_mem (w : World) (n : Nat)
    (A D : ScheduledEvent)
    (hA_due : A.targetTick = w.tick) (hD_due : D.targetTick = w.tick)
    (h_nodup : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup)
    (h_before : evBefore
      (w.events.filter (fun e => e.targetTick == w.tick)) A D)
    (hA_mem : A ∈ (processNEvents w n).events)
    (hD_mem : D ∈ (processNEvents w n).events) :
    evBefore ((processNEvents w n).events.filter
        (fun e => e.targetTick == (processNEvents w n).tick)) A D := by
  induction n generalizing w with
  | zero =>
    simp [processNEvents]
    exact h_before
  | succ n ih =>
    dsimp only [processNEvents] at hA_mem hD_mem ⊢
    cases h_step : w.step with
    | none =>
      simp only [h_step] at hA_mem hD_mem ⊢
      exact h_before
    | some w' =>
      simp only [h_step] at hA_mem hD_mem ⊢
      dsimp [World.step] at h_step
      cases h_pop : w.popNextEvent with
      | none => simp [h_pop] at h_step
      | some p =>
        rcases p with ⟨ev₀, w_pop⟩
        simp only [h_pop] at h_step
        injection h_step with h_w'
        obtain ⟨idx, h_idx, h_erase, h_tick_ev, _, h_get_idx⟩ :=
          World.popNextEvent_eraseIdx w ev₀ w_pop h_pop
        have h_tick_pop : w_pop.tick = w.tick :=
          World.popNextEvent_tick w ev₀ w_pop h_pop
        have h_tick_w' : w'.tick = w.tick := by
          rw [← h_w', World.onScheduledTick_tick, h_tick_pop]
        set due := w.events.filter (fun e => e.targetTick == w.tick)
        have h_due_ev₀ : (fun e => e.targetTick == w.tick)
            (w.events[idx]'h_idx) = true := by
          rw [h_get_idx]
          simp [h_tick_ev]
        obtain ⟨j, hj, h_filter_erase, h_get_due⟩ :=
          filter_eraseIdx_getElem (fun e => e.targetTick == w.tick) w.events
            idx h_idx h_due_ev₀
        have h_get_due_ev₀ : due[j]'hj = ev₀ := h_get_due.trans h_get_idx
        obtain ⟨new₀, h_app_new, h_fut_new⟩ :=
          World.onScheduledTick_appends_future w_pop ev₀.nodeId
        -- A and D survived this pop, so they differ from the popped event
        have hA_pop : A ∈ w_pop.events := by
          have hA_w' : A ∈ w'.events :=
            mem_processNEvents_due_back w' n A hA_mem (by
              rw [hA_due, h_tick_w'])
          rw [← h_w', h_app_new, List.mem_append] at hA_w'
          rcases hA_w' with hA_w' | hA_new
          · exact hA_w'
          · have h_gt := h_fut_new A hA_new
            rw [h_tick_pop, hA_due] at h_gt
            omega
        have hD_pop : D ∈ w_pop.events := by
          have hD_w' : D ∈ w'.events :=
            mem_processNEvents_due_back w' n D hD_mem (by
              rw [hD_due, h_tick_w'])
          rw [← h_w', h_app_new, List.mem_append] at hD_w'
          rcases hD_w' with hD_w' | hD_new
          · exact hD_w'
          · have h_gt := h_fut_new D hD_new
            rw [h_tick_pop, hD_due] at h_gt
            omega
        have h_ev_A : ev₀ ≠ A := by
          intro h_eq
          have h_A_mem : A ∈ due.eraseIdx j := by
            rw [← h_filter_erase, ← h_erase, List.mem_filter]
            exact ⟨hA_pop, by rw [hA_due]; simp⟩
          rw [h_eq] at h_get_due_ev₀
          exact nodup_eraseIdx_not_mem due j hj h_nodup A h_get_due_ev₀
            h_A_mem
        have h_ev_ne_D : ev₀ ≠ D := by
          intro h_eq
          have h_D_mem : D ∈ due.eraseIdx j := by
            rw [← h_filter_erase, ← h_erase, List.mem_filter]
            exact ⟨hD_pop, by rw [hD_due]; simp⟩
          rw [h_eq] at h_get_due_ev₀
          exact nodup_eraseIdx_not_mem due j hj h_nodup D h_get_due_ev₀
            h_D_mem
        -- the due-filter of w' is the due-filter of w minus the pop
        have h_due_tail : w'.events.filter
            (fun e => e.targetTick == w'.tick) = due.eraseIdx j := by
          rw [← h_w', World.onScheduledTick_tick, h_tick_pop, h_app_new,
            List.filter_append]
          have h_new_nil :
              new₀.filter (fun e => e.targetTick == w.tick) = [] :=
            filter_nil_of_forall_false (fun e => e.targetTick == w.tick)
              new₀ (by
              intro e h_e
              have h_gt := h_fut_new e h_e
              rw [h_tick_pop] at h_gt
              exact tick_beq_false_of_ne e.targetTick w.tick (by omega))
          rw [h_new_nil, List.append_nil, h_erase, h_filter_erase]
        -- order of the survivors in the due-filter
        have h_before_w' : evBefore
            (w'.events.filter (fun e => e.targetTick == w'.tick)) A D := by
          rw [h_due_tail]
          obtain ⟨l₁, l₂, h_split, hD_l₂⟩ := h_before
          obtain ⟨m₁, m₂, h_eq, hD_m₂⟩ :=
            eraseIdx_preserves_order due l₁ l₂ A D ev₀ h_split hD_l₂ h_ev_A
              h_ev_ne_D j hj h_get_due_ev₀
          exact ⟨m₁, m₂, h_eq, hD_m₂⟩
        have hA_due_w' : A.targetTick = w'.tick := by
          rw [h_tick_w']
          exact hA_due
        have hD_due_w' : D.targetTick = w'.tick := by
          rw [h_tick_w']
          exact hD_due
        have h_nodup_w' :
            (w'.events.filter (fun e => e.targetTick == w'.tick)).Nodup := by
          rw [h_due_tail]
          exact nodup_eraseIdx due j h_nodup
        exact ih w' hA_due_w' hD_due_w' h_nodup_w' h_before_w' hA_mem hD_mem

/-- A burst phase keeps the due-filter order of two due events that survive
    it. -/
theorem evBefore_due_gSimBurst_of_mem (t : Nat) (obsAll : List (List Nat))
    (withinOrd pos : Nat → List Nat) (w : World)
    (pairs : List (Nat × Nat)) (A D : ScheduledEvent)
    (hA_due : A.targetTick = w.tick) (hD_due : D.targetTick = w.tick)
    (h_nodup : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup)
    (h_before : evBefore
      (w.events.filter (fun e => e.targetTick == w.tick)) A D)
    (hA_mem : A ∈ (gSimBurst t obsAll withinOrd pos w pairs).events)
    (hD_mem : D ∈ (gSimBurst t obsAll withinOrd pos w pairs).events) :
    evBefore ((gSimBurst t obsAll withinOrd pos w pairs).events.filter
        (fun e => e.targetTick ==
          (gSimBurst t obsAll withinOrd pos w pairs).tick)) A D := by
  induction pairs generalizing w with
  | nil =>
    simp [gSimBurst]
    exact h_before
  | cons p ps ih =>
    simp only [gSimBurst, List.foldl_cons] at hA_mem hD_mem ⊢
    rcases p with ⟨gi, k⟩
    set m := (pos t)[k]?.getD 0
    set ordered : List Nat := (withinOrd gi).foldl (fun acc ci =>
      match (obsAll[gi]?.getD [])[ci]? with
      | some oid => acc ++ [oid]
      | none => acc) []
    set Wproc := processNEvents w m
    set W₁ := activateGroup Wproc ordered
    change A ∈ (gSimBurst t obsAll withinOrd pos W₁ ps).events at hA_mem
    change D ∈ (gSimBurst t obsAll withinOrd pos W₁ ps).events at hD_mem
    have h_tick_W₁ : W₁.tick = w.tick := by
      dsimp [W₁, Wproc]
      rw [activateGroup_tick, processNEvents_tick]
    -- both events were already queued at the start of this segment
    have hA_W₁ : A ∈ W₁.events :=
      mem_gSimBurst_due_back t obsAll withinOrd pos W₁ ps A hA_mem (by
        rw [hA_due, h_tick_W₁])
    have hD_W₁ : D ∈ W₁.events :=
      mem_gSimBurst_due_back t obsAll withinOrd pos W₁ ps D hD_mem (by
        rw [hD_due, h_tick_W₁])
    -- they survived the processNEvents part of the segment
    have hA_proc : A ∈ Wproc.events := by
      dsimp [W₁] at hA_W₁
      rw [activateGroup_events_map, List.mem_append] at hA_W₁
      rcases hA_W₁ with hA_W₁ | h_obs
      · exact hA_W₁
      · rcases List.mem_map.mp h_obs with ⟨nid, _, h_ev_eq⟩
        have h_tgt : A.targetTick = Wproc.tick + 2 := by
          rw [← h_ev_eq]
        have h_tick_proc : Wproc.tick = w.tick := by
          dsimp [Wproc]
          exact processNEvents_tick w m
        rw [h_tgt, h_tick_proc] at hA_due
        omega
    have hD_proc : D ∈ Wproc.events := by
      dsimp [W₁] at hD_W₁
      rw [activateGroup_events_map, List.mem_append] at hD_W₁
      rcases hD_W₁ with hD_W₁ | h_obs
      · exact hD_W₁
      · rcases List.mem_map.mp h_obs with ⟨nid, _, h_ev_eq⟩
        have h_tgt : D.targetTick = Wproc.tick + 2 := by
          rw [← h_ev_eq]
        have h_tick_proc : Wproc.tick = w.tick := by
          dsimp [Wproc]
          exact processNEvents_tick w m
        rw [h_tgt, h_tick_proc] at hD_due
        omega
    -- their order survives the segment
    have h_before_W₁ : evBefore
        (W₁.events.filter (fun e => e.targetTick == W₁.tick)) A D := by
      dsimp [W₁]
      rw [activateGroup_tick, activateGroup_due_filter]
      dsimp [Wproc]
      exact evBefore_due_processNEvents_of_mem w m A D hA_due hD_due h_nodup
        h_before hA_proc hD_proc
    have hA_due_W₁ : A.targetTick = W₁.tick := by rw [h_tick_W₁]; exact hA_due
    have hD_due_W₁ : D.targetTick = W₁.tick := by rw [h_tick_W₁]; exact hD_due
    have h_nodup_W₁ :
        (W₁.events.filter (fun e => e.targetTick == W₁.tick)).Nodup := by
      dsimp [W₁]
      rw [activateGroup_tick, activateGroup_due_filter]
      dsimp [Wproc]
      exact processNEvents_due_nodup w m h_nodup
    exact ih W₁ hA_due_W₁ hD_due_W₁ h_nodup_W₁ h_before_W₁ hA_mem hD_mem

/-! ## Spawn presence and spawn order through `processNEvents` -/

/-- A due event that `processNEvents` removes leaves its spawn in the
    queue. -/
theorem processNEvents_spawn_mem (groups : List GroupSpec) (w : World)
    (n : Nat) (e s : ScheduledEvent)
    (h_layout : NodeLayoutOk groups w)
    (h_e_mem : e ∈ w.events) (h_e_due : e.targetTick = w.tick)
    (h_e_gone : e ∉ (processNEvents w n).events)
    (h_s_nd : s.targetTick ≠ w.tick)
    (h_spawn : ∀ (v : World), v.tick = w.tick → NodeLayoutOk groups v →
        (v.onScheduledTick e.nodeId).events = v.events ++ [s]) :
    s ∈ (processNEvents w n).events := by
  induction n generalizing w h_layout with
  | zero =>
    simp [processNEvents] at h_e_gone
    exact (h_e_gone h_e_mem).elim
  | succ n ih =>
    dsimp only [processNEvents] at h_e_gone ⊢
    cases h_step : w.step with
    | none =>
      simp only [h_step] at h_e_gone
      exact (h_e_gone h_e_mem).elim
    | some w' =>
      have h_layout_w' : NodeLayoutOk groups w' :=
        NodeLayoutOk_step groups w w' h_step h_layout
      simp only [h_step] at h_e_gone ⊢
      dsimp [World.step] at h_step
      cases h_pop : w.popNextEvent with
      | none => simp [h_pop] at h_step
      | some p =>
        rcases p with ⟨ev₀, w_pop⟩
        simp only [h_pop] at h_step
        injection h_step with h_w'
        obtain ⟨idx, h_idx, h_erase, h_tick_ev, _, h_get_idx⟩ :=
          World.popNextEvent_eraseIdx w ev₀ w_pop h_pop
        have h_tick_pop : w_pop.tick = w.tick :=
          World.popNextEvent_tick w ev₀ w_pop h_pop
        have h_tick_w' : w'.tick = w.tick := by
          rw [← h_w', World.onScheduledTick_tick, h_tick_pop]
        have h_layout_pop : NodeLayoutOk groups w_pop :=
          NodeLayoutOk_of_nodes_eq groups w w_pop
            (World.popNextEvent_nodes w ev₀ w_pop h_pop) h_layout
        by_cases h_ev_e : ev₀ = e
        · -- e is popped now: its spawn is appended and then survives
          have h_s_w' : s ∈ w'.events := by
            rw [← h_w', h_ev_e]
            rw [h_spawn w_pop h_tick_pop h_layout_pop]
            exact List.mem_append_right _ (by simp)
          exact mem_processNEvents_of_notDue w' n s h_s_w' (by
            rw [h_tick_w']
            exact h_s_nd)
        · -- some other event is popped: e survives; apply the IH
          have h_e_pop : e ∈ w_pop.events := by
            rw [h_erase]
            exact mem_eraseIdx_of_ne w.events idx h_idx ev₀ e h_get_idx
              h_e_mem (Ne.symm h_ev_e)
          obtain ⟨new₀, h_app_new, _⟩ :=
            World.onScheduledTick_appends_future w_pop ev₀.nodeId
          have h_e_w' : e ∈ w'.events := by
            rw [← h_w', h_app_new]
            exact List.mem_append_left _ h_e_pop
          exact ih w' h_layout_w' h_e_w' (by rw [h_tick_w']; exact h_e_due)
            h_e_gone (by rw [h_tick_w']; exact h_s_nd)
            (fun v h_v ↦ h_spawn v (h_v.trans h_tick_w'))

/-- A present non-due event stays before the spawn of a due event that
    `processNEvents` removes. -/
theorem processNEvents_present_before_spawn (groups : List GroupSpec)
    (w : World) (n : Nat) (x e s : ScheduledEvent)
    (h_layout : NodeLayoutOk groups w)
    (h_x : x ∈ w.events) (h_x_nd : x.targetTick ≠ w.tick)
    (h_e : e ∈ w.events) (h_e_due : e.targetTick = w.tick)
    (h_e_gone : e ∉ (processNEvents w n).events)
    (h_s_nd : s.targetTick ≠ w.tick)
    (h_spawn : ∀ (v : World), v.tick = w.tick → NodeLayoutOk groups v →
        (v.onScheduledTick e.nodeId).events = v.events ++ [s]) :
    evBefore (processNEvents w n).events x s := by
  induction n generalizing w h_layout with
  | zero =>
    simp [processNEvents] at h_e_gone
    exact (h_e_gone h_e).elim
  | succ n ih =>
    dsimp only [processNEvents] at h_e_gone ⊢
    cases h_step : w.step with
    | none =>
      simp only [h_step] at h_e_gone
      exact (h_e_gone h_e).elim
    | some w' =>
      have h_layout_w' : NodeLayoutOk groups w' :=
        NodeLayoutOk_step groups w w' h_step h_layout
      simp only [h_step] at h_e_gone ⊢
      dsimp [World.step] at h_step
      cases h_pop : w.popNextEvent with
      | none => simp [h_pop] at h_step
      | some p =>
        rcases p with ⟨ev₀, w_pop⟩
        simp only [h_pop] at h_step
        injection h_step with h_w'
        obtain ⟨idx, h_idx, h_erase, h_tick_ev, _, h_get_idx⟩ :=
          World.popNextEvent_eraseIdx w ev₀ w_pop h_pop
        have h_tick_pop : w_pop.tick = w.tick :=
          World.popNextEvent_tick w ev₀ w_pop h_pop
        have h_tick_w' : w'.tick = w.tick := by
          rw [← h_w', World.onScheduledTick_tick, h_tick_pop]
        have h_layout_pop : NodeLayoutOk groups w_pop :=
          NodeLayoutOk_of_nodes_eq groups w w_pop
            (World.popNextEvent_nodes w ev₀ w_pop h_pop) h_layout
        have h_x_pop : x ∈ w_pop.events := by
          rw [h_erase]
          exact mem_eraseIdx_of_ne w.events idx h_idx ev₀ x h_get_idx h_x
            (fun h_eq ↦ h_x_nd (by rw [h_eq]; exact h_tick_ev))
        by_cases h_ev_e : ev₀ = e
        · -- e is popped now: s is appended at the end, after x
          have h_w'_events : w'.events = w_pop.events ++ [s] := by
            rw [← h_w', h_ev_e]
            exact h_spawn w_pop h_tick_pop h_layout_pop
          obtain ⟨p₀, q₀, h_peq⟩ : ∃ p q, w_pop.events = p ++ x :: q :=
            mem_split_append w_pop.events x h_x_pop
          have h_split_w' : w'.events = p₀ ++ x :: (q₀ ++ [s]) := by
            rw [h_w'_events, h_peq, List.append_assoc, List.cons_append]
          have h_before_w' : evBefore w'.events x s :=
            ⟨p₀, q₀ ++ [s], h_split_w', List.mem_append_right _ (by simp)⟩
          have h_x_nd_w' : x.targetTick ≠ w'.tick := by
            rw [h_tick_w']
            exact h_x_nd
          have h_s_nd_w' : s.targetTick ≠ w'.tick := by
            rw [h_tick_w']
            exact h_s_nd
          exact evBefore_processNEvents_of_notDue w' n x s h_x_nd_w'
            h_s_nd_w' h_before_w'
        · -- some other event is popped: x and e survive; apply the IH
          have h_e_pop : e ∈ w_pop.events := by
            rw [h_erase]
            exact mem_eraseIdx_of_ne w.events idx h_idx ev₀ e h_get_idx h_e
              (Ne.symm h_ev_e)
          obtain ⟨new₀, h_app_new, _⟩ :=
            World.onScheduledTick_appends_future w_pop ev₀.nodeId
          have h_x_w' : x ∈ w'.events := by
            rw [← h_w', h_app_new]
            exact List.mem_append_left _ h_x_pop
          have h_e_w' : e ∈ w'.events := by
            rw [← h_w', h_app_new]
            exact List.mem_append_left _ h_e_pop
          exact ih w' h_layout_w' h_x_w' (by rw [h_tick_w']; exact h_x_nd)
            h_e_w' (by rw [h_tick_w']; exact h_e_due) h_e_gone
            (by rw [h_tick_w']; exact h_s_nd)
            (fun v h_v ↦ h_spawn v (h_v.trans h_tick_w'))

/-- Two same-priority due events that `processNEvents` both removes spawn
    into the queue in their due-filter order. -/
theorem processNEvents_spawn_evBefore (groups : List GroupSpec) (w : World)
    (n : Nat) (A D sA sD : ScheduledEvent)
    (h_layout : NodeLayoutOk groups w)
    (hA_mem : A ∈ w.events) (hD_mem : D ∈ w.events)
    (hA_due : A.targetTick = w.tick) (hD_due : D.targetTick = w.tick)
    (h_pri : A.priority = D.priority)
    (h_nodup : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup)
    (h_before : evBefore
      (w.events.filter (fun e => e.targetTick == w.tick)) A D)
    (hA_gone : A ∉ (processNEvents w n).events)
    (hD_gone : D ∉ (processNEvents w n).events)
    (h_sA_nd : sA.targetTick ≠ w.tick) (h_sD_nd : sD.targetTick ≠ w.tick)
    (h_spawnA : ∀ (v : World), v.tick = w.tick → NodeLayoutOk groups v →
        (v.onScheduledTick A.nodeId).events = v.events ++ [sA])
    (h_spawnD : ∀ (v : World), v.tick = w.tick → NodeLayoutOk groups v →
        (v.onScheduledTick D.nodeId).events = v.events ++ [sD]) :
    evBefore (processNEvents w n).events sA sD := by
  induction n generalizing w h_layout with
  | zero =>
    simp [processNEvents] at hA_gone
    exact (hA_gone hA_mem).elim
  | succ n ih =>
    obtain ⟨l₁, l₂, h_split, hD_l₂⟩ := h_before
    have h_AD_ne : A ≠ D := fun h_eq =>
      nodup_cons_append_not_mem (h_split ▸ h_nodup) (by
        rw [h_eq]
        exact hD_l₂)
    dsimp only [processNEvents] at hA_gone hD_gone ⊢
    cases h_step : w.step with
    | none =>
      simp only [h_step] at hA_gone
      exact (hA_gone hA_mem).elim
    | some w' =>
      have h_layout_w' : NodeLayoutOk groups w' :=
        NodeLayoutOk_step groups w w' h_step h_layout
      simp only [h_step] at hA_gone hD_gone ⊢
      dsimp [World.step] at h_step
      cases h_pop : w.popNextEvent with
      | none => simp [h_pop] at h_step
      | some p =>
        rcases p with ⟨ev₀, w_pop⟩
        simp only [h_pop] at h_step
        injection h_step with h_w'
        obtain ⟨idx, h_idx, h_erase, h_tick_ev, _, h_get_idx⟩ :=
          World.popNextEvent_eraseIdx w ev₀ w_pop h_pop
        have h_tick_pop : w_pop.tick = w.tick :=
          World.popNextEvent_tick w ev₀ w_pop h_pop
        have h_tick_w' : w'.tick = w.tick := by
          rw [← h_w', World.onScheduledTick_tick, h_tick_pop]
        have h_layout_pop : NodeLayoutOk groups w_pop :=
          NodeLayoutOk_of_nodes_eq groups w w_pop
            (World.popNextEvent_nodes w ev₀ w_pop h_pop) h_layout
        by_cases h_ev_A : ev₀ = A
        · -- A is popped now; sA is appended now, sD is spawned later
          have h_sA_w' : sA ∈ w'.events := by
            rw [← h_w', h_ev_A]
            rw [h_spawnA w_pop h_tick_pop h_layout_pop]
            exact List.mem_append_right _ (by simp)
          have hD_pop : D ∈ w_pop.events := by
            rw [h_erase]
            exact mem_eraseIdx_of_ne w.events idx h_idx A D
              (h_get_idx.trans h_ev_A) hD_mem (fun h ↦ h_AD_ne h.symm)
          obtain ⟨new₀, h_app_new, _⟩ :=
            World.onScheduledTick_appends_future w_pop ev₀.nodeId
          have hD_w' : D ∈ w'.events := by
            rw [← h_w', h_app_new]
            exact List.mem_append_left _ hD_pop
          exact processNEvents_present_before_spawn groups w' n sA D sD
            h_layout_w' h_sA_w' (by rw [h_tick_w']; exact h_sA_nd) hD_w'
            (by rw [h_tick_w']; exact hD_due) hD_gone
            (by rw [h_tick_w']; exact h_sD_nd)
            (fun v h_v ↦ h_spawnD v (h_v.trans h_tick_w'))
        · -- D is never popped before A at equal priority
          have h_ev_D : ev₀ ≠ D :=
            popNextEvent_not_D_of_append_split w A D ev₀ w_pop h_pop h_nodup
              l₁ l₂ h_split hD_l₂ (by omega)
          · -- some other event is popped: A and D survive; apply the IH
            have hA_pop : A ∈ w_pop.events := by
              rw [h_erase]
              exact mem_eraseIdx_of_ne w.events idx h_idx ev₀ A h_get_idx
                hA_mem (Ne.symm h_ev_A)
            have hD_pop : D ∈ w_pop.events := by
              rw [h_erase]
              exact mem_eraseIdx_of_ne w.events idx h_idx ev₀ D h_get_idx
                hD_mem (Ne.symm h_ev_D)
            set due := w.events.filter (fun e => e.targetTick == w.tick)
            have h_due_ev₀ : (fun e => e.targetTick == w.tick)
                (w.events[idx]'h_idx) = true := by
              rw [h_get_idx]
              simp [h_tick_ev]
            obtain ⟨j, hj, h_filter_erase, h_get_due⟩ :=
              filter_eraseIdx_getElem (fun e => e.targetTick == w.tick)
                w.events idx h_idx h_due_ev₀
            have h_get_due_ev₀ : due[j]'hj = ev₀ :=
              h_get_due.trans h_get_idx
            obtain ⟨new₀, h_app_new, h_fut_new⟩ :=
              World.onScheduledTick_appends_future w_pop ev₀.nodeId
            have h_due_tail : w'.events.filter
                (fun e => e.targetTick == w'.tick) = due.eraseIdx j := by
              rw [← h_w', World.onScheduledTick_tick, h_tick_pop, h_app_new,
                List.filter_append]
              have h_new_nil :
                  new₀.filter (fun e => e.targetTick == w.tick) = [] :=
                filter_nil_of_forall_false
                  (fun e => e.targetTick == w.tick) new₀ (by
                  intro e h_e
                  have h_gt := h_fut_new e h_e
                  rw [h_tick_pop] at h_gt
                  exact tick_beq_false_of_ne e.targetTick w.tick (by omega))
              rw [h_new_nil, List.append_nil, h_erase, h_filter_erase]
            have hA_mem_w' : A ∈ w'.events := by
              rw [← h_w', h_app_new]
              exact List.mem_append_left _ hA_pop
            have hD_mem_w' : D ∈ w'.events := by
              rw [← h_w', h_app_new]
              exact List.mem_append_left _ hD_pop
            have hA_due_w' : A.targetTick = w'.tick := by
              rw [h_tick_w']
              exact hA_due
            have hD_due_w' : D.targetTick = w'.tick := by
              rw [h_tick_w']
              exact hD_due
            have h_nodup_w' : (w'.events.filter
                (fun e => e.targetTick == w'.tick)).Nodup := by
              rw [h_due_tail]
              exact nodup_eraseIdx due j h_nodup
            obtain ⟨m₁, m₂, h_split_w', hD_m₂⟩ :=
              eraseIdx_preserves_order due l₁ l₂ A D ev₀ h_split hD_l₂
                h_ev_A h_ev_D j hj h_get_due_ev₀
            have h_before_w' : evBefore
                (w'.events.filter (fun e => e.targetTick == w'.tick)) A D := by
              rw [h_due_tail]
              exact ⟨m₁, m₂, h_split_w', hD_m₂⟩
            exact ih w' h_layout_w' hA_mem_w' hD_mem_w' hA_due_w' hD_due_w'
              h_nodup_w' h_before_w' hA_gone hD_gone
              (by rw [h_tick_w']; exact h_sA_nd)
              (by rw [h_tick_w']; exact h_sD_nd)
              (fun (v : World) (h_v : v.tick = w'.tick) ↦
                h_spawnA v (h_v.trans h_tick_w'))
              (fun (v : World) (h_v : v.tick = w'.tick) ↦
                h_spawnD v (h_v.trans h_tick_w'))

/-! ## The same-priority prefix property and burst-level spawn facts -/

/-- `processNEvents` cannot pop `D` while an earlier same-priority (or
    higher-priority) due event `A` stays queued. -/
theorem processNEvents_not_pop_later_samePri (w : World) (n : Nat)
    (A D : ScheduledEvent)
    (hA_due : A.targetTick = w.tick) (hD_due : D.targetTick = w.tick)
    (h_pri : A.priority ≤ D.priority)
    (h_nodup : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup)
    (h_before : evBefore
      (w.events.filter (fun e => e.targetTick == w.tick)) A D)
    (hA_mem : A ∈ w.events)
    (hA_stays : A ∈ (processNEvents w n).events) :
    D ∈ (processNEvents w n).events := by
  obtain ⟨l₁, l₂, h_split, hD_l₂⟩ := h_before
  have h_D_mem : D ∈ w.events := by
    have h_filter : D ∈ w.events.filter (fun e => e.targetTick == w.tick) := by
      rw [h_split]
      exact List.mem_append_right _ (List.mem_cons.mpr (Or.inr hD_l₂))
    exact List.mem_filter.mp h_filter |>.1
  induction n generalizing w l₁ l₂ h_split hD_l₂ with
  | zero =>
    simp [processNEvents]
    exact h_D_mem
  | succ n ih =>
    dsimp only [processNEvents] at hA_stays ⊢
    cases h_step : w.step with
    | none =>
      simp only [h_step] at hA_stays ⊢
      exact h_D_mem
    | some w' =>
      simp only [h_step] at hA_stays ⊢
      dsimp [World.step] at h_step
      cases h_pop : w.popNextEvent with
      | none => simp [h_pop] at h_step
      | some p =>
        rcases p with ⟨ev₀, w_pop⟩
        simp only [h_pop] at h_step
        injection h_step with h_w'
        obtain ⟨idx, h_idx, h_erase, h_tick_ev, _, h_get_idx⟩ :=
          World.popNextEvent_eraseIdx w ev₀ w_pop h_pop
        have h_tick_pop : w_pop.tick = w.tick :=
          World.popNextEvent_tick w ev₀ w_pop h_pop
        have h_tick_w' : w'.tick = w.tick := by
          rw [← h_w', World.onScheduledTick_tick, h_tick_pop]
        -- the popped event is not D while A precedes it in the due-filter
        have h_ev_D : ev₀ ≠ D :=
          popNextEvent_not_D_of_append_split w A D ev₀ w_pop h_pop h_nodup
            l₁ l₂ h_split hD_l₂ h_pri
        -- if the popped event were A, then A could not stay queued
        have h_ev_A : ev₀ ≠ A := by
          intro h_ev_A
          have hA_w' : A ∈ w'.events :=
            mem_processNEvents_due_back w' n A hA_stays (by
              rw [hA_due, h_tick_w'])
          obtain ⟨new₀, h_app_new, h_fut_new⟩ :=
            World.onScheduledTick_appends_future w_pop ev₀.nodeId
          rw [← h_w', h_app_new, List.mem_append] at hA_w'
          rcases hA_w' with hA_pop | hA_new
          · set due := w.events.filter (fun e => e.targetTick == w.tick)
            have h_due_ev₀ : (fun e => e.targetTick == w.tick)
                (w.events[idx]'h_idx) = true := by
              rw [h_get_idx]
              simp [h_tick_ev]
            obtain ⟨j, hj, h_filter_erase, h_get_due⟩ :=
              filter_eraseIdx_getElem (fun e => e.targetTick == w.tick)
                w.events idx h_idx h_due_ev₀
            have h_A_erase : A ∈ due.eraseIdx j := by
              rw [← h_filter_erase, ← h_erase, List.mem_filter]
              exact ⟨hA_pop, by rw [hA_due]; simp⟩
            have h_get_due_ev₀ : due[j]'hj = A := by
              rw [h_get_due.trans h_get_idx, h_ev_A]
            exact nodup_eraseIdx_not_mem due j hj h_nodup A h_get_due_ev₀
              h_A_erase
          · have h_gt := h_fut_new A hA_new
            rw [h_tick_pop, hA_due] at h_gt
            omega
        -- A and D both survive this pop; apply the IH
        have hA_pop : A ∈ w_pop.events := by
          rw [h_erase]
          exact mem_eraseIdx_of_ne w.events idx h_idx ev₀ A h_get_idx
            hA_mem (Ne.symm h_ev_A)
        have hD_pop : D ∈ w_pop.events := by
          rw [h_erase]
          exact mem_eraseIdx_of_ne w.events idx h_idx ev₀ D h_get_idx
            h_D_mem (Ne.symm h_ev_D)
        obtain ⟨new₀, h_app_new, h_fut_new⟩ :=
          World.onScheduledTick_appends_future w_pop ev₀.nodeId
        have hA_w' : A ∈ w'.events := by
          rw [← h_w', h_app_new]
          exact List.mem_append_left _ hA_pop
        have hD_w' : D ∈ w'.events := by
          rw [← h_w', h_app_new]
          exact List.mem_append_left _ hD_pop
        set due := w.events.filter (fun e => e.targetTick == w.tick)
        have h_due_ev₀ : (fun e => e.targetTick == w.tick)
            (w.events[idx]'h_idx) = true := by
          rw [h_get_idx]
          simp [h_tick_ev]
        obtain ⟨j, hj, h_filter_erase, h_get_due⟩ :=
          filter_eraseIdx_getElem (fun e => e.targetTick == w.tick)
            w.events idx h_idx h_due_ev₀
        have h_get_due_ev₀ : due[j]'hj = ev₀ := h_get_due.trans h_get_idx
        have h_due_tail : w'.events.filter
            (fun e => e.targetTick == w'.tick) = due.eraseIdx j := by
          rw [← h_w', World.onScheduledTick_tick, h_tick_pop, h_app_new,
            List.filter_append]
          have h_new_nil :
              new₀.filter (fun e => e.targetTick == w.tick) = [] :=
            filter_nil_of_forall_false (fun e => e.targetTick == w.tick)
              new₀ (by
              intro e h_e
              have h_gt := h_fut_new e h_e
              rw [h_tick_pop] at h_gt
              exact tick_beq_false_of_ne e.targetTick w.tick (by omega))
          rw [h_new_nil, List.append_nil, h_erase, h_filter_erase]
        have h_nodup_w' : (w'.events.filter
            (fun e => e.targetTick == w'.tick)).Nodup := by
          rw [h_due_tail]
          exact nodup_eraseIdx due j h_nodup
        obtain ⟨m₁, m₂, h_split_w', hD_m₂⟩ :=
          eraseIdx_preserves_order due l₁ l₂ A D ev₀ h_split hD_l₂ h_ev_A
            h_ev_D j hj h_get_due_ev₀
        exact ih w' (by rw [hA_due, h_tick_w'])
          (by rw [hD_due, h_tick_w']) h_nodup_w' hA_w' hA_stays
          m₁ m₂ (h_due_tail.trans h_split_w') hD_m₂ hD_w'

/-- A burst phase cannot pop `D` while an earlier same-priority due event
    `A` stays queued. -/
theorem gSimBurst_not_pop_later_samePri (t : Nat) (obsAll : List (List Nat))
    (withinOrd pos : Nat → List Nat) (w : World)
    (pairs : List (Nat × Nat)) (A D : ScheduledEvent)
    (hA_due : A.targetTick = w.tick) (hD_due : D.targetTick = w.tick)
    (h_pri : A.priority ≤ D.priority)
    (h_nodup : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup)
    (h_before : evBefore
      (w.events.filter (fun e => e.targetTick == w.tick)) A D)
    (hA_mem : A ∈ w.events)
    (hA_stays : A ∈ (gSimBurst t obsAll withinOrd pos w pairs).events) :
    D ∈ (gSimBurst t obsAll withinOrd pos w pairs).events := by
  obtain ⟨l₁, l₂, h_split, hD_l₂⟩ := h_before
  have h_D_mem : D ∈ w.events := by
    have h_filter : D ∈ w.events.filter (fun e => e.targetTick == w.tick) := by
      rw [h_split]
      exact List.mem_append_right _ (List.mem_cons.mpr (Or.inr hD_l₂))
    exact List.mem_filter.mp h_filter |>.1
  induction pairs generalizing w l₁ l₂ h_split hD_l₂ with
  | nil =>
    simp [gSimBurst]
    exact h_D_mem
  | cons p ps ih =>
    simp only [gSimBurst, List.foldl_cons] at hA_stays ⊢
    rcases p with ⟨gi, k⟩
    set m := (pos t)[k]?.getD 0
    set ordered : List Nat := (withinOrd gi).foldl (fun acc ci =>
      match (obsAll[gi]?.getD [])[ci]? with
      | some oid => acc ++ [oid]
      | none => acc) []
    set Wproc := processNEvents w m
    set W₁ := activateGroup Wproc ordered
    change D ∈ (gSimBurst t obsAll withinOrd pos W₁ ps).events
    change A ∈ (gSimBurst t obsAll withinOrd pos W₁ ps).events at hA_stays
    have h_tick_W₁ : W₁.tick = w.tick := by
      dsimp [W₁, Wproc]
      rw [activateGroup_tick, processNEvents_tick]
    -- A stays queued through this segment too
    have hA_W₁ : A ∈ W₁.events :=
      mem_gSimBurst_due_back t obsAll withinOrd pos W₁ ps A hA_stays (by
        rw [hA_due, h_tick_W₁])
    have hA_proc : A ∈ Wproc.events := by
      dsimp [W₁] at hA_W₁
      rw [activateGroup_events_map, List.mem_append] at hA_W₁
      rcases hA_W₁ with hA_W₁ | h_obs
      · exact hA_W₁
      · rcases List.mem_map.mp h_obs with ⟨nid, _, h_ev_eq⟩
        have h_tgt : A.targetTick = Wproc.tick + 2 := by
          rw [← h_ev_eq]
        have h_tick_proc : Wproc.tick = w.tick := by
          dsimp [Wproc]
          exact processNEvents_tick w m
        rw [h_tgt, h_tick_proc] at hA_due
        omega
    -- D survives this segment by the processNEvents prefix property
    have hD_proc : D ∈ Wproc.events :=
      processNEvents_not_pop_later_samePri w m A D hA_due hD_due h_pri
        h_nodup ⟨l₁, l₂, h_split, hD_l₂⟩ hA_mem hA_proc
    have hD_W₁ : D ∈ W₁.events := by
      dsimp [W₁]
      rw [activateGroup_events_map]
      exact List.mem_append_left _ hD_proc
    -- order and health carry over to W₁
    have hA_due_W₁ : A.targetTick = W₁.tick := by
      rw [h_tick_W₁]
      exact hA_due
    have hD_due_W₁ : D.targetTick = W₁.tick := by
      rw [h_tick_W₁]
      exact hD_due
    have h_nodup_W₁ : (W₁.events.filter
        (fun e => e.targetTick == W₁.tick)).Nodup := by
      dsimp [W₁]
      rw [activateGroup_tick, activateGroup_due_filter]
      dsimp [Wproc]
      exact processNEvents_due_nodup w m h_nodup
    have h_before_W₁ : evBefore
        (W₁.events.filter (fun e => e.targetTick == W₁.tick)) A D := by
      dsimp [W₁]
      rw [activateGroup_tick, activateGroup_due_filter]
      dsimp [Wproc]
      exact evBefore_due_processNEvents_of_mem w m A D hA_due hD_due h_nodup
        ⟨l₁, l₂, h_split, hD_l₂⟩ hA_proc hD_proc
    obtain ⟨l₁', l₂', h_split_W₁, hD_l₂'⟩ := h_before_W₁
    exact ih W₁ hA_due_W₁ hD_due_W₁ h_nodup_W₁ hA_W₁ hA_stays
      l₁' l₂' h_split_W₁ hD_l₂' hD_W₁

/-- A due event removed by a burst phase leaves its spawn in the queue. -/
theorem gSimBurst_spawn_mem (groups : List GroupSpec) (t : Nat)
    (obsAll : List (List Nat)) (withinOrd pos : Nat → List Nat) (w : World)
    (pairs : List (Nat × Nat)) (e s : ScheduledEvent)
    (h_layout : NodeLayoutOk groups w)
    (h_e_mem : e ∈ w.events) (h_e_due : e.targetTick = w.tick)
    (h_e_gone : e ∉ (gSimBurst t obsAll withinOrd pos w pairs).events)
    (h_s_nd : s.targetTick ≠ w.tick)
    (h_spawn : ∀ (v : World), v.tick = w.tick → NodeLayoutOk groups v →
        (v.onScheduledTick e.nodeId).events = v.events ++ [s]) :
    s ∈ (gSimBurst t obsAll withinOrd pos w pairs).events := by
  induction pairs generalizing w h_layout with
  | nil =>
    simp [gSimBurst] at h_e_gone
    exact (h_e_gone h_e_mem).elim
  | cons p ps ih =>
    simp only [gSimBurst, List.foldl_cons] at h_e_gone ⊢
    rcases p with ⟨gi, k⟩
    set m := (pos t)[k]?.getD 0
    set ordered : List Nat := (withinOrd gi).foldl (fun acc ci =>
      match (obsAll[gi]?.getD [])[ci]? with
      | some oid => acc ++ [oid]
      | none => acc) []
    set Wproc := processNEvents w m
    set W₁ := activateGroup Wproc ordered
    change e ∉ (gSimBurst t obsAll withinOrd pos W₁ ps).events at h_e_gone
    change s ∈ (gSimBurst t obsAll withinOrd pos W₁ ps).events
    have h_tick_W₁ : W₁.tick = w.tick := by
      dsimp [W₁, Wproc]
      rw [activateGroup_tick, processNEvents_tick]
    have h_layout_W₁ : NodeLayoutOk groups W₁ := by
      dsimp [W₁, Wproc]
      exact NodeLayoutOk_activateGroup groups (processNEvents w m) ordered
        (NodeLayoutOk_processNEvents groups w m h_layout)
    by_cases h_e_W₁ : e ∈ W₁.events
    · -- e survives this segment: it pops in a later segment
      exact ih W₁ h_layout_W₁ h_e_W₁ (by rw [h_e_due, h_tick_W₁]) h_e_gone
        (by rw [h_tick_W₁]; exact h_s_nd)
        (fun (v : World) (h_v : v.tick = W₁.tick) ↦
          h_spawn v (h_v.trans h_tick_W₁))
    · -- e is popped in this segment
      have h_e_gone_proc : e ∉ Wproc.events := by
        dsimp [W₁] at h_e_W₁
        rw [activateGroup_events_map, List.mem_append] at h_e_W₁
        intro h_proc
        exact h_e_W₁ (Or.inl h_proc)
      have h_s_proc : s ∈ Wproc.events :=
        processNEvents_spawn_mem groups w m e s h_layout h_e_mem h_e_due
          h_e_gone_proc h_s_nd h_spawn
      have h_s_W₁ : s ∈ W₁.events := by
        dsimp [W₁]
        rw [activateGroup_events_map]
        exact List.mem_append_left _ h_s_proc
      exact mem_gSimBurst_of_notDue t obsAll withinOrd pos W₁ ps s h_s_W₁
        (by rw [h_tick_W₁]; exact h_s_nd)

/-- A present non-due event stays before the spawn of a due event removed
    by a burst phase. -/
theorem gSimBurst_present_before_spawn (groups : List GroupSpec) (t : Nat)
    (obsAll : List (List Nat)) (withinOrd pos : Nat → List Nat) (w : World)
    (pairs : List (Nat × Nat)) (x e s : ScheduledEvent)
    (h_layout : NodeLayoutOk groups w)
    (h_x : x ∈ w.events) (h_x_nd : x.targetTick ≠ w.tick)
    (h_e : e ∈ w.events) (h_e_due : e.targetTick = w.tick)
    (h_e_gone : e ∉ (gSimBurst t obsAll withinOrd pos w pairs).events)
    (h_s_nd : s.targetTick ≠ w.tick)
    (h_spawn : ∀ (v : World), v.tick = w.tick → NodeLayoutOk groups v →
        (v.onScheduledTick e.nodeId).events = v.events ++ [s]) :
    evBefore (gSimBurst t obsAll withinOrd pos w pairs).events x s := by
  induction pairs generalizing w h_layout with
  | nil =>
    simp [gSimBurst] at h_e_gone
    exact (h_e_gone h_e).elim
  | cons p ps ih =>
    simp only [gSimBurst, List.foldl_cons] at h_e_gone ⊢
    rcases p with ⟨gi, k⟩
    set m := (pos t)[k]?.getD 0
    set ordered : List Nat := (withinOrd gi).foldl (fun acc ci =>
      match (obsAll[gi]?.getD [])[ci]? with
      | some oid => acc ++ [oid]
      | none => acc) []
    set Wproc := processNEvents w m
    set W₁ := activateGroup Wproc ordered
    change e ∉ (gSimBurst t obsAll withinOrd pos W₁ ps).events at h_e_gone
    change evBefore (gSimBurst t obsAll withinOrd pos W₁ ps).events x s
    have h_tick_W₁ : W₁.tick = w.tick := by
      dsimp [W₁, Wproc]
      rw [activateGroup_tick, processNEvents_tick]
    have h_layout_W₁ : NodeLayoutOk groups W₁ := by
      dsimp [W₁, Wproc]
      exact NodeLayoutOk_activateGroup groups (processNEvents w m) ordered
        (NodeLayoutOk_processNEvents groups w m h_layout)
    by_cases h_e_W₁ : e ∈ W₁.events
    · -- e survives this segment: x survives too; apply the IH
      have h_x_proc : x ∈ Wproc.events :=
        mem_processNEvents_of_notDue w m x h_x h_x_nd
      have h_x_W₁ : x ∈ W₁.events := by
        dsimp [W₁]
        rw [activateGroup_events_map]
        exact List.mem_append_left _ h_x_proc
      exact ih W₁ h_layout_W₁ h_x_W₁ (by rw [h_tick_W₁]; exact h_x_nd)
        h_e_W₁ (by rw [h_e_due, h_tick_W₁]) h_e_gone
        (by rw [h_tick_W₁]; exact h_s_nd)
        (fun (v : World) (h_v : v.tick = W₁.tick) ↦
          h_spawn v (h_v.trans h_tick_W₁))
    · -- e is popped in this segment: s is appended after x there
      have h_e_gone_proc : e ∉ Wproc.events := by
        dsimp [W₁] at h_e_W₁
        rw [activateGroup_events_map, List.mem_append] at h_e_W₁
        intro h_proc
        exact h_e_W₁ (Or.inl h_proc)
      have h_bs : evBefore Wproc.events x s :=
        processNEvents_present_before_spawn groups w m x e s h_layout h_x
          h_x_nd h_e h_e_due h_e_gone_proc h_s_nd h_spawn
      have h_bs_W₁ : evBefore W₁.events x s := by
        dsimp [W₁]
        rw [activateGroup_events_map]
        exact evBefore.append_right h_bs
      exact evBefore_gSimBurst_of_notDue t obsAll withinOrd pos W₁ ps x s
        (by rw [h_tick_W₁]; exact h_x_nd)
        (by rw [h_tick_W₁]; exact h_s_nd) h_bs_W₁

/-- Two same-priority due events that a burst phase both removes spawn into
    the queue in their due-filter order. -/
theorem gSimBurst_spawn_evBefore (groups : List GroupSpec) (t : Nat)
    (obsAll : List (List Nat)) (withinOrd pos : Nat → List Nat) (w : World)
    (pairs : List (Nat × Nat)) (A D sA sD : ScheduledEvent)
    (h_layout : NodeLayoutOk groups w)
    (hA_mem : A ∈ w.events) (hD_mem : D ∈ w.events)
    (hA_due : A.targetTick = w.tick) (hD_due : D.targetTick = w.tick)
    (h_pri : A.priority = D.priority)
    (h_nodup : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup)
    (h_before : evBefore
      (w.events.filter (fun e => e.targetTick == w.tick)) A D)
    (hA_gone : A ∉ (gSimBurst t obsAll withinOrd pos w pairs).events)
    (hD_gone : D ∉ (gSimBurst t obsAll withinOrd pos w pairs).events)
    (h_sA_nd : sA.targetTick ≠ w.tick) (h_sD_nd : sD.targetTick ≠ w.tick)
    (h_spawnA : ∀ (v : World), v.tick = w.tick → NodeLayoutOk groups v →
        (v.onScheduledTick A.nodeId).events = v.events ++ [sA])
    (h_spawnD : ∀ (v : World), v.tick = w.tick → NodeLayoutOk groups v →
        (v.onScheduledTick D.nodeId).events = v.events ++ [sD]) :
    evBefore (gSimBurst t obsAll withinOrd pos w pairs).events sA sD := by
  induction pairs generalizing w h_layout with
  | nil =>
    simp [gSimBurst] at hA_gone
    exact (hA_gone hA_mem).elim
  | cons p ps ih =>
    obtain ⟨l₁, l₂, h_split, hD_l₂⟩ := h_before
    have h_AD_ne : A ≠ D := fun h_eq =>
      nodup_cons_append_not_mem (h_split ▸ h_nodup) (by
        rw [h_eq]
        exact hD_l₂)
    simp only [gSimBurst, List.foldl_cons] at hA_gone hD_gone ⊢
    rcases p with ⟨gi, k⟩
    set m := (pos t)[k]?.getD 0
    set ordered : List Nat := (withinOrd gi).foldl (fun acc ci =>
      match (obsAll[gi]?.getD [])[ci]? with
      | some oid => acc ++ [oid]
      | none => acc) []
    set Wproc := processNEvents w m
    set W₁ := activateGroup Wproc ordered
    change A ∉ (gSimBurst t obsAll withinOrd pos W₁ ps).events at hA_gone
    change D ∉ (gSimBurst t obsAll withinOrd pos W₁ ps).events at hD_gone
    change evBefore (gSimBurst t obsAll withinOrd pos W₁ ps).events sA sD
    have h_tick_W₁ : W₁.tick = w.tick := by
      dsimp [W₁, Wproc]
      rw [activateGroup_tick, processNEvents_tick]
    have h_layout_W₁ : NodeLayoutOk groups W₁ := by
      dsimp [W₁, Wproc]
      exact NodeLayoutOk_activateGroup groups (processNEvents w m) ordered
        (NodeLayoutOk_processNEvents groups w m h_layout)
    by_cases hA_W₁ : A ∈ W₁.events
    · -- A survives this segment; then so does D; apply the IH
      have hA_proc : A ∈ Wproc.events := by
        dsimp [W₁] at hA_W₁
        rw [activateGroup_events_map, List.mem_append] at hA_W₁
        rcases hA_W₁ with hA_W₁ | h_obs
        · exact hA_W₁
        · rcases List.mem_map.mp h_obs with ⟨nid, _, h_ev_eq⟩
          have h_tgt : A.targetTick = Wproc.tick + 2 := by
            rw [← h_ev_eq]
          have h_tick_proc : Wproc.tick = w.tick := by
            dsimp [Wproc]
            exact processNEvents_tick w m
          exfalso
          omega
      have hD_proc : D ∈ Wproc.events :=
        processNEvents_not_pop_later_samePri w m A D hA_due hD_due (by
          rw [h_pri]) h_nodup ⟨l₁, l₂, h_split, hD_l₂⟩ hA_mem hA_proc
      have hD_W₁ : D ∈ W₁.events := by
        dsimp [W₁]
        rw [activateGroup_events_map]
        exact List.mem_append_left _ hD_proc
      have hA_due_W₁ : A.targetTick = W₁.tick := by
        rw [h_tick_W₁]
        exact hA_due
      have hD_due_W₁ : D.targetTick = W₁.tick := by
        rw [h_tick_W₁]
        exact hD_due
      have h_nodup_W₁ : (W₁.events.filter
          (fun e => e.targetTick == W₁.tick)).Nodup := by
        dsimp [W₁]
        rw [activateGroup_tick, activateGroup_due_filter]
        dsimp [Wproc]
        exact processNEvents_due_nodup w m h_nodup
      have h_before_W₁ : evBefore
          (W₁.events.filter (fun e => e.targetTick == W₁.tick)) A D := by
        dsimp [W₁]
        rw [activateGroup_tick, activateGroup_due_filter]
        dsimp [Wproc]
        exact evBefore_due_processNEvents_of_mem w m A D hA_due hD_due
          h_nodup ⟨l₁, l₂, h_split, hD_l₂⟩ hA_proc hD_proc
      obtain ⟨l₁', l₂', h_split_W₁, hD_l₂'⟩ := h_before_W₁
      exact ih W₁ h_layout_W₁ hA_W₁ hD_W₁ hA_due_W₁ hD_due_W₁
        h_nodup_W₁ ⟨l₁', l₂', h_split_W₁, hD_l₂'⟩ hA_gone hD_gone
        (by rw [h_tick_W₁]; exact h_sA_nd)
        (by rw [h_tick_W₁]; exact h_sD_nd)
        (fun (v : World) (h_v : v.tick = W₁.tick) ↦
          h_spawnA v (h_v.trans h_tick_W₁))
        (fun (v : World) (h_v : v.tick = W₁.tick) ↦
          h_spawnD v (h_v.trans h_tick_W₁))
    · -- A is popped in this segment
      have hA_gone_proc : A ∉ Wproc.events := by
        dsimp [W₁] at hA_W₁
        rw [activateGroup_events_map, List.mem_append] at hA_W₁
        intro h_proc
        exact hA_W₁ (Or.inl h_proc)
      by_cases hD_W₁ : D ∈ W₁.events
      · -- D pops later: sA (already spawned) stays before sD
        have h_sA_proc : sA ∈ Wproc.events :=
          processNEvents_spawn_mem groups w m A sA h_layout hA_mem hA_due
            hA_gone_proc h_sA_nd h_spawnA
        have h_sA_W₁ : sA ∈ W₁.events := by
          dsimp [W₁]
          rw [activateGroup_events_map]
          exact List.mem_append_left _ h_sA_proc
        exact gSimBurst_present_before_spawn groups t obsAll withinOrd pos
          W₁ ps sA D sD h_layout_W₁ h_sA_W₁
          (by rw [h_tick_W₁]; exact h_sA_nd) hD_W₁
          (by rw [hD_due, h_tick_W₁]) hD_gone
          (by rw [h_tick_W₁]; exact h_sD_nd)
          (fun (v : World) (h_v : v.tick = W₁.tick) ↦
            h_spawnD v (h_v.trans h_tick_W₁))
      · -- both pop in this segment: spawn order from processNEvents
        have hD_gone_proc : D ∉ Wproc.events := by
          dsimp [W₁] at hD_W₁
          rw [activateGroup_events_map, List.mem_append] at hD_W₁
          intro h_proc
          exact hD_W₁ (Or.inl h_proc)
        have h_bs : evBefore Wproc.events sA sD :=
          processNEvents_spawn_evBefore groups w m A D sA sD h_layout hA_mem
            hD_mem hA_due hD_due h_pri h_nodup
            ⟨l₁, l₂, h_split, hD_l₂⟩ hA_gone_proc hD_gone_proc h_sA_nd
            h_sD_nd h_spawnA h_spawnD
        have h_bs_W₁ : evBefore W₁.events sA sD := by
          dsimp [W₁]
          rw [activateGroup_events_map]
          exact evBefore.append_right h_bs
        exact evBefore_gSimBurst_of_notDue t obsAll withinOrd pos W₁ ps sA
          sD (by rw [h_tick_W₁]; exact h_sA_nd)
          (by rw [h_tick_W₁]; exact h_sD_nd) h_bs_W₁
