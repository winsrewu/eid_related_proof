import BasicProofs.GroupClustering.CrossPriorityPopDiscipline
import BasicProofs.GroupClustering.PopSeqFuel

open BasicRedstoneSim List

/-! # Group clustering — same-priority pop-order correlation

Two due events of the same priority pop in queue order: the burst can
pop the later one only after popping the earlier one. Equivalently, if
the earlier event survives the burst, so does the later one. This
discharges the drain-phase side premise of the capstone assembly (the
stage-`m` final of the second reference chain is absent from the
post-burst queue whenever the first one is): at equal priority `A`
precedes `D` in the due filter, so `A` survives burst ⟹ `D` survives
burst.

The per-pop ingredients are PopSeqFuel's:
`popNextEvent_not_D_of_append_split` (the popped event is not `D`
while `A` is queued before it at priority `≤`), `filter_eraseIdx_getElem`,
`eraseIdx_preserves_order`, `nodup_eraseIdx`, and `mem_eraseIdx_of_ne`.
The inductions follow CrossPriorityPopDiscipline's `gSimBurst_not_pop_larger_pri` and
PopSeqFuel's `World.samePriLockstep` invariant maintenance.
-/

/-- A due event occupying the erased position cannot belong to the
    due-filter of the erased list: it would occur twice in the
    duplicate-free due-filter of the original list. -/
private theorem not_mem_eraseIdx_due (t : Nat) (l : List ScheduledEvent) :
    ∀ (i : Nat) (h_i : i < l.length) (A : ScheduledEvent),
      l[i]'h_i = A → A.targetTick = t →
      (l.filter (fun e => e.targetTick == t)).Nodup →
      A ∉ (l.eraseIdx i).filter (fun e => e.targetTick == t) := by
  induction l with
  | nil => intro i h_i; cases h_i
  | cons a l' ih =>
    intro i h_i A h_get hA_due h_nd
    cases i with
    | zero =>
      -- eraseIdx (a :: l') 0 = l'; A = a is due, so a heads the due
      -- filter of (a :: l') and cannot also sit in l''s due filter
      change a = A at h_get
      subst h_get
      simp only [List.eraseIdx]
      intro h_A
      have h_pa : (fun e => e.targetTick == t) a = true := by
        simpa using hA_due
      have h_filt : (a :: l').filter (fun e => e.targetTick == t) =
          a :: l'.filter (fun e => e.targetTick == t) := by
        simp only [List.filter, h_pa]
      rw [h_filt, List.nodup_cons] at h_nd
      exact h_nd.1 h_A
    | succ i' =>
      have h_i' : i' < l'.length := Nat.lt_of_succ_lt_succ h_i
      have h_get' : l'[i']'h_i' = A := by
        simpa using h_get
      -- case split on whether the head passes the due filter
      by_cases h_pa : (fun e => e.targetTick == t) a = true
      · have h_filt : (a :: l').filter (fun e => e.targetTick == t) =
            a :: l'.filter (fun e => e.targetTick == t) := by
          simp only [List.filter, h_pa]
        rw [h_filt, List.nodup_cons] at h_nd
        have h_nd' : (l'.filter (fun e => e.targetTick == t)).Nodup :=
          h_nd.2
        have h_a_not : a ∉ l'.filter (fun e => e.targetTick == t) :=
          h_nd.1
        simp only [List.eraseIdx]
        intro h_A
        have h_A' : A = a ∨ A ∈
            (l'.eraseIdx i').filter (fun e => e.targetTick == t) := by
          simpa only [List.filter, h_pa, List.mem_cons] using h_A
        rcases h_A' with h_Aa | h_A'
        · -- A = a would give a second due occurrence of a in l'
          have h_a_l' : a ∈ l' := by
            rw [← h_Aa, ← h_get']
            exact List.getElem_mem h_i'
          have h_a_filt : a ∈ l'.filter (fun e => e.targetTick == t) := by
            rw [List.mem_filter]
            exact ⟨h_a_l', by rw [← h_Aa]; simpa using hA_due⟩
          exact h_a_not h_a_filt
        · exact ih i' h_i' A h_get' hA_due h_nd' h_A'
      · have h_filt : (a :: l').filter (fun e => e.targetTick == t) =
            l'.filter (fun e => e.targetTick == t) := by
          simp only [List.filter, h_pa]
        rw [h_filt] at h_nd
        simp only [List.eraseIdx, List.filter, h_pa]
        exact ih i' h_i' A h_get' hA_due h_nd

/-- One `processNEvents` run cannot pop the later of two same-priority
    due events while the earlier one survives. Returns the survival of
    `D` together with the maintained due-filter invariant (Nodup and
    the `A`-before-`D` split) at the result world. -/
theorem processNEvents_samePri_later_survives (w : World) (n : Nat)
    (A D : ScheduledEvent)
    (hA_mem : A ∈ w.events) (hD_mem : D ∈ w.events)
    (hA_due : A.targetTick = w.tick) (hD_due : D.targetTick = w.tick)
    (h_pri : A.priority ≤ D.priority)
    (h_nodup : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup)
    (h_before : ∃ l₁ l₂,
        w.events.filter (fun e => e.targetTick == w.tick) =
        l₁ ++ A :: l₂ ∧ D ∈ l₂)
    (hA_stays : A ∈ (processNEvents w n).events) :
    D ∈ (processNEvents w n).events ∧
    ((processNEvents w n).events.filter
      (fun e => e.targetTick == (processNEvents w n).tick)).Nodup ∧
    ∃ m₁ m₂,
      (processNEvents w n).events.filter
        (fun e => e.targetTick == (processNEvents w n).tick) =
      m₁ ++ A :: m₂ ∧ D ∈ m₂ := by
  induction n generalizing w with
  | zero =>
    simp [processNEvents]
    exact ⟨hD_mem, h_nodup, h_before⟩
  | succ n ih =>
    dsimp only [processNEvents] at hA_stays ⊢
    cases h_step : w.step with
    | none =>
      exact ⟨hD_mem, h_nodup, h_before⟩
    | some w' =>
      simp only [h_step] at hA_stays ⊢
      dsimp [World.step] at h_step
      cases h_pop : w.popNextEvent with
      | none =>
        exact False.elim
          (popNextEvent_none_no_events w h_pop A hA_mem hA_due)
      | some p =>
        rcases p with ⟨ev₀, w_pop⟩
        simp only [h_pop] at h_step
        injection h_step with h_w'
        obtain ⟨l₁, l₂, h_split, hD_l₂⟩ := h_before
        have h_ev_ne_D : ev₀ ≠ D :=
          popNextEvent_not_D_of_append_split w A D ev₀ w_pop h_pop h_nodup
            l₁ l₂ h_split hD_l₂ h_pri
        obtain ⟨idx, h_idx, h_erase, h_tick_ev, _, h_get_idx⟩ :=
          World.popNextEvent_eraseIdx w ev₀ w_pop h_pop
        have h_tick_pop : w_pop.tick = w.tick :=
          World.popNextEvent_tick w ev₀ w_pop h_pop
        have h_tick_w' : w'.tick = w.tick := by
          rw [← h_w', World.onScheduledTick_tick, h_tick_pop]
        -- the popped event is not A either: A survives to the result
        have h_ev_ne_A : ev₀ ≠ A := by
          intro h_eq
          have hA_w' : A ∈ w'.events :=
            mem_processNEvents_due_back w' n A hA_stays (by
              rw [hA_due, h_tick_w'])
          obtain ⟨new₀, h_app_new, h_fut_new⟩ :=
            World.onScheduledTick_appends_future w_pop ev₀.nodeId
          have hA_pop : A ∈ w_pop.events := by
            rw [← h_w', h_app_new, List.mem_append] at hA_w'
            rcases hA_w' with h | h_new
            · exact h
            · have h_gt := h_fut_new A h_new
              rw [h_tick_pop, hA_due] at h_gt
              omega
          rw [h_erase] at hA_pop
          exact not_mem_eraseIdx_due w.tick w.events idx h_idx A
            (h_get_idx.trans h_eq) hA_due h_nodup (by
              rw [List.mem_filter]
              exact ⟨hA_pop, by simpa using hA_due⟩)
        -- A and D both survive this pop
        have hA_pop : A ∈ w_pop.events := by
          rw [h_erase]
          exact mem_eraseIdx_of_ne w.events idx h_idx ev₀ A h_get_idx hA_mem
            (Ne.symm h_ev_ne_A)
        have hD_pop : D ∈ w_pop.events := by
          rw [h_erase]
          exact mem_eraseIdx_of_ne w.events idx h_idx ev₀ D h_get_idx hD_mem
            (Ne.symm h_ev_ne_D)
        obtain ⟨new₀, h_app_new, h_fut_new⟩ :=
          World.onScheduledTick_appends_future w_pop ev₀.nodeId
        have hA_w' : A ∈ w'.events := by
          rw [← h_w', h_app_new]
          exact List.mem_append_left _ hA_pop
        have hD_w' : D ∈ w'.events := by
          rw [← h_w', h_app_new]
          exact List.mem_append_left _ hD_pop
        -- invariant maintenance: due filter after the pop
        set due := w.events.filter (fun e => e.targetTick == w.tick)
        have h_due_ev₀ : (fun e => e.targetTick == w.tick)
            (w.events[idx]'h_idx) = true := by
          simp [h_get_idx, h_tick_ev]
        obtain ⟨j, hj, h_filter_erase, h_get_due⟩ :=
          filter_eraseIdx_getElem (fun e => e.targetTick == w.tick) w.events
            idx h_idx h_due_ev₀
        have h_get_due_ev₀ : due[j]'hj = ev₀ := h_get_due.trans h_get_idx
        have h_due_tail : w'.events.filter
            (fun e => e.targetTick == w'.tick) = due.eraseIdx j := by
          rw [← h_w', World.onScheduledTick_tick, h_tick_pop, h_app_new,
            List.filter_append]
          have h_new_nil : new₀.filter
              (fun e => e.targetTick == w.tick) = [] := by
            apply List.filter_eq_nil_iff.mpr
            intro e h_e
            have h_gt := h_fut_new e h_e
            rw [h_tick_pop] at h_gt
            simp
            omega
          rw [h_new_nil, List.append_nil, h_erase, h_filter_erase]
        have h_nodup_w' : (w'.events.filter
            (fun e => e.targetTick == w'.tick)).Nodup := by
          rw [h_due_tail]
          exact nodup_eraseIdx due j h_nodup
        have h_before_w' : ∃ m₁ m₂, w'.events.filter
            (fun e => e.targetTick == w'.tick) = m₁ ++ A :: m₂ ∧ D ∈ m₂ := by
          rw [h_due_tail]
          obtain ⟨m₁, m₂, h_eq, hD_m₂⟩ :=
            eraseIdx_preserves_order due l₁ l₂ A D ev₀ h_split hD_l₂
              h_ev_ne_A h_ev_ne_D j hj h_get_due_ev₀
          exact ⟨m₁, m₂, h_eq, hD_m₂⟩
        exact ih (w := w') (hA_mem := hA_w') (hD_mem := hD_w')
          (hA_due := by rw [hA_due, h_tick_w'])
          (hD_due := by rw [hD_due, h_tick_w'])
          (h_nodup := h_nodup_w')
          (h_before := h_before_w') (hA_stays := hA_stays)

/-- The burst phase cannot pop the later of two same-priority due
    events while the earlier one survives. `activateGroup` steps only
    append strictly future events, so the due-filter invariant carries
    through them unchanged. -/
theorem gSimBurst_samePri_later_survives (t : Nat)
    (obsAll : List (List Nat)) (withinOrd pos : Nat → List Nat)
    (w : World) (pairs : List (Nat × Nat)) (A D : ScheduledEvent)
    (hA_mem : A ∈ w.events) (hD_mem : D ∈ w.events)
    (hA_due : A.targetTick = w.tick) (hD_due : D.targetTick = w.tick)
    (h_pri : A.priority ≤ D.priority)
    (h_nodup : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup)
    (h_before : ∃ l₁ l₂,
        w.events.filter (fun e => e.targetTick == w.tick) =
        l₁ ++ A :: l₂ ∧ D ∈ l₂)
    (hA_stays : A ∈ (gSimBurst t obsAll withinOrd pos w pairs).events) :
    D ∈ (gSimBurst t obsAll withinOrd pos w pairs).events := by
  induction pairs generalizing w with
  | nil =>
    simp [gSimBurst] at hA_stays
    exact hD_mem
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
    change A ∈ (gSimBurst t obsAll withinOrd pos W₁ ps).events at hA_stays
    change D ∈ (gSimBurst t obsAll withinOrd pos W₁ ps).events
    have h_tick_W₁ : W₁.tick = w.tick := by
      dsimp [W₁, Wproc]
      rw [activateGroup_tick, processNEvents_tick]
    -- A, due and present in the final result, is already present at W₁
    have hA_W₁ : A ∈ W₁.events :=
      mem_gSimBurst_due_back t obsAll withinOrd pos W₁ ps A hA_stays (by
        rw [hA_due, h_tick_W₁])
    have hA_proc : A ∈ Wproc.events := by
      dsimp [W₁] at hA_W₁
      rw [activateGroup_events_map, List.mem_append] at hA_W₁
      rcases hA_W₁ with h | h_obs
      · exact h
      · rcases List.mem_map.mp h_obs with ⟨nid, _, h_ev_eq⟩
        have h_tgt : A.targetTick = Wproc.tick + 2 := by
          rw [← h_ev_eq]
        have h_tick_proc : Wproc.tick = w.tick := by
          dsimp [Wproc]
          exact processNEvents_tick w m
        rw [h_tgt, h_tick_proc] at hA_due
        omega
    -- D and the due-filter invariant survive the processing segment
    obtain ⟨hD_proc, h_nd_proc, h_before_proc⟩ :=
      processNEvents_samePri_later_survives w m A D hA_mem hD_mem hA_due
        hD_due h_pri h_nodup h_before hA_proc
    -- the due filter is unchanged by activateGroup (strictly future
    -- appends)
    have h_due_W₁ : W₁.events.filter (fun e => e.targetTick == W₁.tick) =
        Wproc.events.filter (fun e => e.targetTick == Wproc.tick) := by
      dsimp only [W₁, Wproc]
      obtain ⟨new₁, h_app₁, h_fut₁⟩ := activateGroup_events_append
        (processNEvents w m) ordered
      rw [h_app₁, activateGroup_tick, List.filter_append]
      have h_nil : new₁.filter (fun e => e.targetTick ==
          (processNEvents w m).tick) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro e h_e
        have h_gt := h_fut₁ e h_e
        simp
        omega
      rw [h_nil, List.append_nil]
    have hD_W₁ : D ∈ W₁.events := by
      dsimp [W₁]
      rw [activateGroup_events_map]
      exact List.mem_append_left _ hD_proc
    have h_nd_W₁ : (W₁.events.filter
        (fun e => e.targetTick == W₁.tick)).Nodup := by
      rw [h_due_W₁]
      exact h_nd_proc
    have h_before_W₁ : ∃ m₁ m₂, W₁.events.filter
        (fun e => e.targetTick == W₁.tick) = m₁ ++ A :: m₂ ∧ D ∈ m₂ := by
      rw [h_due_W₁]
      exact h_before_proc
    exact ih (w := W₁) (hA_mem := hA_W₁) (hD_mem := hD_W₁)
      (hA_due := by rw [hA_due, h_tick_W₁])
      (hD_due := by rw [hD_due, h_tick_W₁])
      (h_nodup := h_nd_W₁)
      (h_before := h_before_W₁) (hA_stays := hA_stays)
