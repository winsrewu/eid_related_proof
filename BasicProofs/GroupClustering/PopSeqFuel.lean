import BasicProofs.GroupClustering.PopOrder


open BasicRedstoneSim List

/-! # Group clustering — fuel-bounded pop sequences

`World.popSeqFuel` records the events popped by successive `World.step`s
within one tick, bounded by a fuel parameter (structural recursion on the
fuel, no termination proof needed). Every popped event is due at the starting
tick, and same-priority due events are popped in list order: if `A` sits
before `D` in the due-sublist and both appear in the pop sequence, then `A`
appears before `D` in the pop sequence.

Note: `World.popSeqFuel` lives in the `World` namespace like the other
`World.*` declarations of this development, so it is applied explicitly
(`World.popSeqFuel w n`) rather than via dot notation.
-/

/-- The events popped during `stepUntilNextTick`, computed with a fuel bound. -/
def World.popSeqFuel (w : World) : Nat → List ScheduledEvent
  | 0 => []
  | fuel + 1 =>
    match w.popNextEvent with
    | none => []
    | some (ev, w_pop) => ev :: World.popSeqFuel (w_pop.onScheduledTick ev.nodeId) fuel

/-! ## Small list helpers -/

/-- Erasing an element does not remove other elements. -/
theorem mem_eraseIdx_of_ne {α : Type} (l : List α) :
    ∀ (i : Nat) (hi : i < l.length) (x y : α),
      l[i]'hi = x → y ∈ l → y ≠ x → y ∈ l.eraseIdx i := by
  induction l with
  | nil => intro i hi; cases hi
  | cons a l ih =>
    intro i hi x y hget hy hne
    cases i with
    | zero =>
      change a = x at hget
      rw [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact (hne hget).elim
      · exact hy
    | succ i' =>
      have hi' : i' < l.length := Nat.lt_of_succ_lt_succ hi
      change y ∈ a :: l.eraseIdx i'
      rw [List.mem_cons] at hy ⊢
      rcases hy with rfl | hy
      · left; rfl
      · right; exact ih i' hi' x y hget hy hne

/-- Indexing into the right part of an append `l₁ ++ a :: l₂`: the element at
    position `k + l₁.length + 1` is `l₂[k]`. -/
theorem getElem_append_cons_right {α : Type} (l₁ l₂ : List α) (a : α) :
    ∀ (k : Nat) (hk : k < l₂.length)
      (h : k + l₁.length + 1 < (l₁ ++ a :: l₂).length),
      (l₁ ++ a :: l₂)[k + l₁.length + 1]'h = l₂[k]'hk := by
  induction l₁ with
  | nil => intro k hk h; rfl
  | cons b l₁' ih =>
    intro k hk h
    have h' : k + l₁'.length + 1 < (l₁' ++ a :: l₂).length :=
      Nat.lt_of_succ_lt_succ h
    show (b :: (l₁' ++ a :: l₂))[k + l₁'.length + 1 + 1]'h = l₂[k]'hk
    exact (List.getElem_cons_succ b (l₁' ++ a :: l₂) (k + l₁'.length + 1) h).trans
      (ih k hk h')

/-- `filter` and `eraseIdx` commute when the erased element satisfies the
    predicate: the filtered list loses exactly that element. -/
theorem filter_eraseIdx_getElem {α : Type} (p : α → Bool) (l : List α) :
    ∀ (i : Nat) (hi : i < l.length),
      p (l[i]'hi) = true →
      ∃ (j : Nat) (hj : j < (l.filter p).length),
        (l.eraseIdx i).filter p = (l.filter p).eraseIdx j ∧ (l.filter p)[j]'hj = l[i]'hi := by
  induction l with
  | nil => intro i hi; cases hi
  | cons a l ih =>
    intro i hi h_p
    cases i with
    | zero =>
      change p a = true at h_p
      refine ⟨0, by simp [List.filter, h_p], ?_, ?_⟩
      · simp [List.eraseIdx, List.filter, h_p]
      · simp [List.filter, h_p]
    | succ i' =>
      have hi' : i' < l.length := Nat.lt_of_succ_lt_succ hi
      obtain ⟨j, hj, h_eq, h_get⟩ := ih i' hi' h_p
      cases h_pa : p a with
      | true =>
        refine ⟨j + 1, by simp [List.filter, h_pa]; omega, ?_, ?_⟩
        · simp only [List.eraseIdx, List.filter, h_pa, h_eq]
        · simp only [List.filter, h_pa, List.getElem_cons_succ]
          exact h_get
      | false =>
        refine ⟨j, by simpa [List.filter, h_pa] using hj, ?_, ?_⟩
        · simp only [List.eraseIdx, List.filter, h_pa, h_eq]
        · simp only [List.filter, h_pa]
          exact h_get

/-- Erasing an element `x` with `x ≠ A` and `x ≠ D` from a list decomposed as
    `l₁ ++ A :: l₂` (with `D ∈ l₂`) keeps `A` before `D`. -/
theorem eraseIdx_preserves_order {α : Type} (due l₁ l₂ : List α) (A D x : α)
    (h_split : due = l₁ ++ A :: l₂) (hD : D ∈ l₂) (hxA : x ≠ A) (hxD : x ≠ D) :
    ∀ (j : Nat) (hj : j < due.length),
      due[j]'hj = x → ∃ m₁ m₂, due.eraseIdx j = m₁ ++ A :: m₂ ∧ D ∈ m₂ := by
  subst h_split
  induction l₁ with
  | nil =>
    intro j hj hget
    cases j with
    | zero =>
      change A = x at hget
      exact (hxA hget.symm).elim
    | succ j' =>
      have hj' : j' < l₂.length := Nat.lt_of_succ_lt_succ hj
      refine ⟨[], l₂.eraseIdx j', ?_, ?_⟩
      · rfl
      · exact mem_eraseIdx_of_ne l₂ j' hj' x D hget hD hxD.symm
  | cons b l₁' ih =>
    intro j hj hget
    cases j with
    | zero =>
      refine ⟨l₁', l₂, ?_, hD⟩
      rfl
    | succ j' =>
      have hj' : j' < (l₁' ++ A :: l₂).length := Nat.lt_of_succ_lt_succ hj
      obtain ⟨m₁, m₂, h_eq, hD_m₂⟩ := ih j' hj' hget
      refine ⟨b :: m₁, m₂, ?_, hD_m₂⟩
      change (b :: (l₁' ++ A :: l₂)).eraseIdx j'.succ = b :: m₁ ++ A :: m₂
      simp only [List.eraseIdx, h_eq]
      rfl

/-- Erasing an element preserves `Nodup`. -/
theorem nodup_eraseIdx {α : Type} (l : List α) :
    ∀ i, l.Nodup → (l.eraseIdx i).Nodup := by
  induction l with
  | nil => intro i _; exact List.nodup_nil
  | cons a l ih =>
    intro i h_nd
    rw [List.nodup_cons] at h_nd
    cases i with
    | zero =>
      simp only [List.eraseIdx]
      exact h_nd.2
    | succ i' =>
      simp only [List.eraseIdx]
      rw [List.nodup_cons]
      refine ⟨?_, ih i' h_nd.2⟩
      intro h_a_mem
      exact h_nd.1 (List.eraseIdx_subset' l i' h_a_mem)

/-! ## Event-append facts without a delay hypothesis

The public `World.onScheduledTick_events_append` requires all repeater delays
to be at least 2; the weaker fact that appended events target strictly future
ticks holds unconditionally (delays are positive by `PNat`). -/

theorem onNeighborUpdate_appends_future (w : World) (id : Nat) :
    ∃ new_events, (w.onNeighborUpdate id).events = w.events ++ new_events ∧
    ∀ ev ∈ new_events, ev.targetTick > w.tick := by
  cases h_getNode : w.getNode id with
  | none => exact ⟨[], by simp [World.onNeighborUpdate, h_getNode], by simp⟩
  | some nd =>
    cases h_kind : nd.kind with
    | repeater delay priority =>
      refine ⟨[{ targetTick := w.tick + (delay : Nat), priority := priority, nodeId := id }], ?_, ?_⟩
      · simp [World.onNeighborUpdate, h_getNode, h_kind, World.scheduleEvent_events]
      · intro ev h_ev
        simp at h_ev
        subst h_ev
        change w.tick + (delay : Nat) > w.tick
        have := PNat.pos delay
        omega
    | observer =>
      refine ⟨[{ targetTick := w.tick + 2, priority := 0, nodeId := id }], ?_, ?_⟩
      · simp [World.onNeighborUpdate, h_getNode, h_kind, World.scheduleEvent_events]
      · intro ev h_ev
        simp at h_ev
        subst h_ev
        change w.tick + 2 > w.tick
        omega
    | output name =>
      refine ⟨[], ?_, ?_⟩ <;> simp [World.onNeighborUpdate, h_getNode, h_kind,
        World.logOutput_events]
    | input =>
      refine ⟨[], ?_, ?_⟩ <;> simp [World.onNeighborUpdate, h_getNode, h_kind]

theorem foldl_onNeighborUpdate_appends_future (l : List Nat) (w : World) :
    ∃ new_events, (l.foldl (fun w' outId => w'.onNeighborUpdate outId) w).events =
      w.events ++ new_events ∧
    ∀ ev ∈ new_events, ev.targetTick > w.tick := by
  induction l generalizing w with
  | nil => exact ⟨[], by simp, by simp⟩
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    obtain ⟨new_hd, h_app_hd, h_fut_hd⟩ := onNeighborUpdate_appends_future w hd
    obtain ⟨new_tl, h_app_tl, h_fut_tl⟩ := ih (w.onNeighborUpdate hd)
    refine ⟨new_hd ++ new_tl, ?_, ?_⟩
    · rw [h_app_tl, h_app_hd, List.append_assoc]
    · intro ev h_ev
      rw [List.mem_append] at h_ev
      rcases h_ev with h_ev | h_ev
      · exact h_fut_hd ev h_ev
      · rw [World.onNeighborUpdate_tick] at h_fut_tl
        exact h_fut_tl ev h_ev

theorem World.onScheduledTick_appends_future (w : World) (id : Nat) :
    ∃ new_events, (w.onScheduledTick id).events = w.events ++ new_events ∧
    ∀ ev ∈ new_events, ev.targetTick > w.tick := by
  dsimp [World.onScheduledTick]
  split
  · exact ⟨[], by simp, by simp⟩
  · rename_i nd
    split
    · set w' := w.updateNode id
        (fun nd' => { nd' with sigLevel := if w.getInputSignal id > 0 then 15 else 0 })
      have h_ev' : w'.events = w.events := World.updateNode_events w id _
      have h_tick' : w'.tick = w.tick := World.updateNode_tick w id _
      dsimp [World.notifyOutputs]
      cases h_go : w'.getNode id with
      | none => exact ⟨[], by simp [h_ev'], by simp⟩
      | some nd' =>
        obtain ⟨new_ev, h_app, h_fut⟩ := foldl_onNeighborUpdate_appends_future nd'.outputs w'
        refine ⟨new_ev, ?_, ?_⟩
        · rw [h_app, h_ev']
        · intro ev h_ev
          rw [h_tick'] at h_fut
          exact h_fut ev h_ev
    · set w' := w.updateNode id (fun nd' => { nd' with sigLevel := 15 })
      have h_ev' : w'.events = w.events := World.updateNode_events w id _
      have h_tick' : w'.tick = w.tick := World.updateNode_tick w id _
      dsimp [World.notifyOutputs]
      cases h_go : w'.getNode id with
      | none => exact ⟨[], by simp [h_ev'], by simp⟩
      | some nd' =>
        obtain ⟨new_ev, h_app, h_fut⟩ := foldl_onNeighborUpdate_appends_future nd'.outputs w'
        refine ⟨new_ev, ?_, ?_⟩
        · rw [h_app, h_ev']
        · intro ev h_ev
          rw [h_tick'] at h_fut
          exact h_fut ev h_ev
    · exact ⟨[], by simp, by simp⟩

/-! ## Popped event is not one that appears later at the same priority -/

/-- Instantiation of `popNextEvent_not_later_same_priority` for an
    append-decomposition `due = l₁ ++ A :: l₂` with `D ∈ l₂`. -/
theorem popNextEvent_not_D_of_append_split (w : World) (A D ev : ScheduledEvent)
    (w' : World) (h_pop : w.popNextEvent = some (ev, w'))
    (h_nodup : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup)
    (l₁ l₂ : List ScheduledEvent)
    (h_split : w.events.filter (fun e => e.targetTick == w.tick) = l₁ ++ A :: l₂)
    (hD : D ∈ l₂) (h_pri : A.priority ≤ D.priority) : ev ≠ D := by
  have hA_lt : l₁.length < (w.events.filter (fun e => e.targetTick == w.tick)).length := by
    rw [h_split]
    simp only [List.length_append, List.length_cons]
    omega
  have hA_get : (w.events.filter (fun e => e.targetTick == w.tick))[l₁.length]'hA_lt = A :=
    List.getElem_of_append h_split rfl
  obtain ⟨k, hk_lt, hk_get⟩ := List.getElem_of_mem hD
  have hD_lt : k + l₁.length + 1 < (w.events.filter (fun e => e.targetTick == w.tick)).length :=
    by
    rw [h_split]
    simp only [List.length_append, List.length_cons]
    omega
  have hD_get :
      (w.events.filter (fun e => e.targetTick == w.tick))[k + l₁.length + 1]'hD_lt = D := by
    have hlt : k + l₁.length + 1 < (l₁ ++ A :: l₂).length := by
      simpa [h_split] using hD_lt
    simpa [h_split] using (getElem_append_cons_right l₁ l₂ A k hk_lt hlt).trans hk_get
  exact popNextEvent_not_later_same_priority w A D ev w' h_pop h_nodup
    (l₁.length) (k + l₁.length + 1) hA_lt hD_lt (by omega) hA_get hD_get h_pri

/-! ## Every popped event is due -/

/-- Every event in `popSeqFuel` targets the tick of the world it was popped
    from (all worlds along the pop chain keep the same tick). -/
theorem World.mem_popSeqFuel_due (w : World) (fuel : Nat) (ev : ScheduledEvent)
    (h : ev ∈ World.popSeqFuel w fuel) : ev.targetTick = w.tick := by
  induction fuel generalizing w with
  | zero =>
    dsimp only [World.popSeqFuel] at h
    cases h
  | succ fuel ih =>
    cases h_pop : w.popNextEvent with
    | none =>
      simp only [World.popSeqFuel, h_pop] at h
      cases h
    | some p =>
      rcases p with ⟨ev₀, w_pop⟩
      simp only [World.popSeqFuel, h_pop] at h
      rw [List.mem_cons] at h
      rcases h with h | h
      · rw [h]
        exact (popNextEvent_first_min_priority w ev₀ w_pop h_pop).1
      · have h_tick_tail := ih (w_pop.onScheduledTick ev₀.nodeId) h
        rw [World.onScheduledTick_tick, World.popNextEvent_tick w ev₀ w_pop h_pop]
          at h_tick_tail
        exact h_tick_tail

/-! ## Same-priority due events pop in list order -/

/-- If `A` appears before `D` in the due-sublist, both have the same priority,
    the due-sublist is duplicate-free, and both are popped within `fuel` steps,
    then `A` appears before `D` in the pop sequence. -/
theorem World.popSeqFuel_same_priority_order (w : World) (fuel : Nat) (A D : ScheduledEvent)
    (hA_mem : A ∈ w.events) (hD_mem : D ∈ w.events)
    (hA_due : A.targetTick = w.tick) (hD_due : D.targetTick = w.tick)
    (h_pri : A.priority = D.priority)
    (h_nodup : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup)
    (h_before : ∃ l₁ l₂, w.events.filter (fun e => e.targetTick == w.tick) = l₁ ++ A :: l₂ ∧
      D ∈ l₂)
    (hA_pop : A ∈ World.popSeqFuel w fuel) (hD_pop : D ∈ World.popSeqFuel w fuel) :
    ∃ p q, World.popSeqFuel w fuel = p ++ A :: q ∧ D ∈ q := by
  induction fuel generalizing w with
  | zero =>
    dsimp only [World.popSeqFuel] at hA_pop
    cases hA_pop
  | succ fuel ih =>
    cases h_pop : w.popNextEvent with
    | none =>
      simp only [World.popSeqFuel, h_pop] at hA_pop
      cases hA_pop
    | some p =>
      rcases p with ⟨ev₀, w_pop⟩
      simp only [World.popSeqFuel, h_pop] at hA_pop hD_pop ⊢
      obtain ⟨l₁, l₂, h_split, hD_l₂⟩ := h_before
      have h_ev_ne_D : ev₀ ≠ D :=
        popNextEvent_not_D_of_append_split w A D ev₀ w_pop h_pop h_nodup l₁ l₂ h_split
          hD_l₂ (by omega)
      by_cases h_ev_A : ev₀ = A
      · -- the popped event is A itself
        subst ev₀
        have hD_tail : D ∈ World.popSeqFuel (w_pop.onScheduledTick A.nodeId) fuel := by
          rw [List.mem_cons] at hD_pop
          rcases hD_pop with h | h
          · exact (h_ev_ne_D h.symm).elim
          · exact h
        exact ⟨[], _, rfl, hD_tail⟩
      · -- A and D both survive this pop; apply the induction hypothesis
        have hA_tail : A ∈ World.popSeqFuel (w_pop.onScheduledTick ev₀.nodeId) fuel := by
          rw [List.mem_cons] at hA_pop
          rcases hA_pop with h | h
          · exact (h_ev_A h.symm).elim
          · exact h
        have hD_tail : D ∈ World.popSeqFuel (w_pop.onScheduledTick ev₀.nodeId) fuel := by
          rw [List.mem_cons] at hD_pop
          rcases hD_pop with h | h
          · exact (h_ev_ne_D h.symm).elim
          · exact h
        obtain ⟨idx, h_idx, h_erase, h_tick_ev, _, h_get_idx⟩ :=
          World.popNextEvent_eraseIdx w ev₀ w_pop h_pop
        set due := w.events.filter (fun e => e.targetTick == w.tick)
        have h_due_ev₀ : (fun e => e.targetTick == w.tick) (w.events[idx]'h_idx) = true := by
          simp [h_get_idx, h_tick_ev]
        obtain ⟨j, hj, h_filter_erase, h_get_due⟩ :=
          filter_eraseIdx_getElem (fun e => e.targetTick == w.tick) w.events idx h_idx h_due_ev₀
        have h_get_due_ev₀ : due[j]'hj = ev₀ := h_get_due.trans h_get_idx
        have h_tick_pop : w_pop.tick = w.tick := World.popNextEvent_tick w ev₀ w_pop h_pop
        obtain ⟨new, h_app_new, h_fut_new⟩ :=
          World.onScheduledTick_appends_future w_pop ev₀.nodeId
        have h_due_tail :
            (w_pop.onScheduledTick ev₀.nodeId).events.filter
                (fun e => e.targetTick == (w_pop.onScheduledTick ev₀.nodeId).tick) =
            due.eraseIdx j := by
          rw [World.onScheduledTick_tick, h_tick_pop, h_app_new, List.filter_append]
          have h_new_nil : new.filter (fun e => e.targetTick == w.tick) = [] := by
            apply List.filter_eq_nil_iff.mpr
            intro e h_e
            have h_gt := h_fut_new e h_e
            rw [h_tick_pop] at h_gt
            simp
            omega
          rw [h_new_nil, List.append_nil, h_erase, h_filter_erase]
        have hA_mem_pop : A ∈ w_pop.events := by
          rw [h_erase]
          exact mem_eraseIdx_of_ne w.events idx h_idx ev₀ A h_get_idx hA_mem (Ne.symm h_ev_A)
        have hD_mem_pop : D ∈ w_pop.events := by
          rw [h_erase]
          exact mem_eraseIdx_of_ne w.events idx h_idx ev₀ D h_get_idx hD_mem (Ne.symm h_ev_ne_D)
        have hA_mem_w1 : A ∈ (w_pop.onScheduledTick ev₀.nodeId).events := by
          rw [h_app_new]
          exact List.mem_append_left _ hA_mem_pop
        have hD_mem_w1 : D ∈ (w_pop.onScheduledTick ev₀.nodeId).events := by
          rw [h_app_new]
          exact List.mem_append_left _ hD_mem_pop
        have h_tick_w1 : (w_pop.onScheduledTick ev₀.nodeId).tick = w.tick := by
          rw [World.onScheduledTick_tick, h_tick_pop]
        have hA_due_w1 : A.targetTick = (w_pop.onScheduledTick ev₀.nodeId).tick := by
          rw [h_tick_w1]
          exact hA_due
        have hD_due_w1 : D.targetTick = (w_pop.onScheduledTick ev₀.nodeId).tick := by
          rw [h_tick_w1]
          exact hD_due
        have h_nodup_w1 :
            ((w_pop.onScheduledTick ev₀.nodeId).events.filter
                (fun e => e.targetTick == (w_pop.onScheduledTick ev₀.nodeId).tick)).Nodup := by
          rw [h_due_tail]
          exact nodup_eraseIdx due j h_nodup
        have h_before_w1 : ∃ m₁ m₂,
            (w_pop.onScheduledTick ev₀.nodeId).events.filter
                (fun e => e.targetTick == (w_pop.onScheduledTick ev₀.nodeId).tick) =
              m₁ ++ A :: m₂ ∧ D ∈ m₂ := by
          rw [h_due_tail]
          obtain ⟨m₁, m₂, h_eq, hD_m₂⟩ :=
            eraseIdx_preserves_order due l₁ l₂ A D ev₀ h_split hD_l₂ h_ev_A h_ev_ne_D j hj
              h_get_due_ev₀
          exact ⟨m₁, m₂, h_eq, hD_m₂⟩
        obtain ⟨p, q, h_tail, hD_q⟩ :=
          ih (w_pop.onScheduledTick ev₀.nodeId) hA_mem_w1 hD_mem_w1 hA_due_w1 hD_due_w1
            h_nodup_w1 h_before_w1 hA_tail hD_tail
        exact ⟨ev₀ :: p, q, by rw [h_tail]; rfl, hD_q⟩

/-! ## Non-due events keep their relative order through `stepUntilNextTick` -/

/-- If `e₁` sits before `e₂` in the event queue and neither event is due at
    the current tick, then `stepUntilNextTick` keeps `e₁` before `e₂`. -/
theorem World.stepUntilNextTick_notDue_order (w : World)
    (e₁ e₂ : ScheduledEvent)
    (h_e₁ : e₁ ∈ w.events) (h_e₂ : e₂ ∈ w.events)
    (h_nd₁ : e₁.targetTick ≠ w.tick) (h_nd₂ : e₂.targetTick ≠ w.tick)
    (h_before : ∃ l₁ l₂, w.events = l₁ ++ e₁ :: l₂ ∧ e₂ ∈ l₂) :
    ∃ p q, w.stepUntilNextTick.events = p ++ e₁ :: q ∧ e₂ ∈ q := by
  induction w using World.stepUntilNextTick.induct with
  | case1 x h_step =>
    obtain ⟨l₁, l₂, h_split, h_e₂_l₂⟩ := h_before
    rw [stepUntilNextTick_of_step_none x h_step]
    exact ⟨l₁, l₂, h_split, h_e₂_l₂⟩
  | case2 x w' h_step ih =>
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
      have h_ev_ne₁ : ev₀ ≠ e₁ := fun h ↦ h_nd₁ (h ▸ h_tick_ev)
      have h_ev_ne₂ : ev₀ ≠ e₂ := fun h ↦ h_nd₂ (h ▸ h_tick_ev)
      have h_e₁_pop : e₁ ∈ w_pop.events := by
        rw [h_erase]
        exact mem_eraseIdx_of_ne x.events idx h_idx ev₀ e₁ h_get_idx h_e₁ (Ne.symm h_ev_ne₁)
      have h_e₂_pop : e₂ ∈ w_pop.events := by
        rw [h_erase]
        exact mem_eraseIdx_of_ne x.events idx h_idx ev₀ e₂ h_get_idx h_e₂ (Ne.symm h_ev_ne₂)
      obtain ⟨l₁, l₂, h_split, h_e₂_l₂⟩ := h_before
      obtain ⟨m₁, m₂, h_m, h_e₂_m₂⟩ :=
        eraseIdx_preserves_order x.events l₁ l₂ e₁ e₂ ev₀ h_split h_e₂_l₂ h_ev_ne₁ h_ev_ne₂
          idx h_idx h_get_idx
      have h_pop_split : w_pop.events = m₁ ++ e₁ :: m₂ := by
        rw [h_erase, h_m]
      have h_tick_w' : w'.tick = x.tick := by
        rw [← h_w', World.onScheduledTick_tick, World.popNextEvent_tick x ev₀ w_pop h_pop]
      obtain ⟨new₀, h_app_new, _⟩ := World.onScheduledTick_appends_future w_pop ev₀.nodeId
      have h_split_w' : w'.events = m₁ ++ e₁ :: (m₂ ++ new₀) := by
        rw [← h_w', h_app_new, h_pop_split, List.append_assoc, List.cons_append]
      have h_e₁_w' : e₁ ∈ w'.events := by
        rw [← h_w', h_app_new]
        exact List.mem_append_left _ h_e₁_pop
      have h_e₂_w' : e₂ ∈ w'.events := by
        rw [← h_w', h_app_new]
        exact List.mem_append_left _ h_e₂_pop
      have h_nd₁_w' : e₁.targetTick ≠ w'.tick := by
        rw [h_tick_w']
        exact h_nd₁
      have h_nd₂_w' : e₂.targetTick ≠ w'.tick := by
        rw [h_tick_w']
        exact h_nd₂
      have h_before_w' : ∃ l₁' l₂', w'.events = l₁' ++ e₁ :: l₂' ∧ e₂ ∈ l₂' :=
        ⟨m₁, m₂ ++ new₀, h_split_w', List.mem_append_left _ h_e₂_m₂⟩
      obtain ⟨p, q, h_tail, h_e₂_q⟩ :=
        ih h_e₁_w' h_e₂_w' h_nd₁_w' h_nd₂_w' h_before_w'
      rw [h_sunt]
      exact ⟨p, q, h_tail, h_e₂_q⟩

/-! ## A present non-due event stays before an event spawned by a due event -/

/-- Membership gives an append decomposition `l = p ++ a :: q`. -/
theorem mem_split_append {α : Type} (l : List α) :
    ∀ (a : α), a ∈ l → ∃ p q, l = p ++ a :: q := by
  induction l with
  | nil => intro a h; cases h
  | cons b l ih =>
    intro a h
    rw [List.mem_cons] at h
    rcases h with h_eq | h
    · refine ⟨[], l, ?_⟩
      rw [← h_eq]
      rfl
    · obtain ⟨p, q, h_pq⟩ := ih a h
      refine ⟨b :: p, q, ?_⟩
      rw [h_pq, List.cons_append]

/-- If `e` is present but not due, `D` is present and due, and firing
    `D.nodeId` on any world at the current tick appends exactly `sD` (which is
    itself not due), then after `stepUntilNextTick` the event `e` appears
    before the spawned event `sD`: `e` survives every pop of this tick while
    `D` is eventually popped and `sD` is appended at the end, after `e`. -/
theorem World.presentNotDue_before_dueSpawn (w : World)
    (e D sD : ScheduledEvent)
    (h_e : e ∈ w.events) (h_nd_e : e.targetTick ≠ w.tick)
    (h_D : D ∈ w.events) (h_due_D : D.targetTick = w.tick)
    (h_sD_nd : sD.targetTick ≠ w.tick)
    (h_spawnD : ∀ (v : World), v.tick = w.tick →
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
      have h_tick_pop : w_pop.tick = x.tick := World.popNextEvent_tick x ev₀ w_pop h_pop
      have h_ev_ne_e : ev₀ ≠ e := fun h ↦ h_nd_e (h ▸ h_tick_ev)
      by_cases h_ev_D : ev₀ = D
      · -- the popped event is D: sD is appended now, right after e
        have h_w'_events : w'.events = w_pop.events ++ [sD] := by
          rw [← h_w', h_ev_D, h_spawnD w_pop h_tick_pop]
        have h_e_pop : e ∈ w_pop.events := by
          rw [h_erase]
          exact mem_eraseIdx_of_ne x.events idx h_idx ev₀ e h_get_idx h_e (Ne.symm h_ev_ne_e)
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
          rw [← h_w', World.onScheduledTick_tick, World.popNextEvent_tick x ev₀ w_pop h_pop]
        have h_nd_e_w' : e.targetTick ≠ w'.tick := by
          rw [h_tick_w']
          exact h_nd_e
        have h_sD_nd_w' : sD.targetTick ≠ w'.tick := by
          rw [h_tick_w']
          exact h_sD_nd
        have h_before_w' : ∃ l₁ l₂, w'.events = l₁ ++ e :: l₂ ∧ sD ∈ l₂ :=
          ⟨p₀, q₀ ++ [sD], h_split_w', List.mem_append_right _ (by simp)⟩
        obtain ⟨p, q, h_tail, h_sD_q⟩ :=
          World.stepUntilNextTick_notDue_order w' e sD h_e_w' h_sD_w' h_nd_e_w' h_sD_nd_w'
            h_before_w'
        rw [h_sunt]
        exact ⟨p, q, h_tail, h_sD_q⟩
      · -- some other event is popped: e and D both survive; apply the IH
        have h_ev_ne_D : ev₀ ≠ D := h_ev_D
        have h_e_pop : e ∈ w_pop.events := by
          rw [h_erase]
          exact mem_eraseIdx_of_ne x.events idx h_idx ev₀ e h_get_idx h_e (Ne.symm h_ev_ne_e)
        have h_D_pop : D ∈ w_pop.events := by
          rw [h_erase]
          exact mem_eraseIdx_of_ne x.events idx h_idx ev₀ D h_get_idx h_D (Ne.symm h_ev_ne_D)
        obtain ⟨new₀, h_app_new, _⟩ := World.onScheduledTick_appends_future w_pop ev₀.nodeId
        have h_e_w' : e ∈ w'.events := by
          rw [← h_w', h_app_new]
          exact List.mem_append_left _ h_e_pop
        have h_D_w' : D ∈ w'.events := by
          rw [← h_w', h_app_new]
          exact List.mem_append_left _ h_D_pop
        have h_tick_w' : w'.tick = x.tick := by
          rw [← h_w', World.onScheduledTick_tick, World.popNextEvent_tick x ev₀ w_pop h_pop]
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
            (v.onScheduledTick D.nodeId).events = v.events ++ [sD] :=
          fun v h_v ↦ h_spawnD v (h_v.trans h_tick_w')
        obtain ⟨p, q, h_tail, h_sD_q⟩ :=
          ih h_e_w' h_nd_e_w' h_D_w' h_due_D_w' h_sD_nd_w' h_spawnD_w'
        rw [h_sunt]
        exact ⟨p, q, h_tail, h_sD_q⟩

/-! ## Within-tick lockstep -/

/-- Within one tick, two same-priority due events `A` (before) and `D` (after)
    spawn `sA` and `sD` with `sA` before `sD` in the resulting queue: `A` pops
    first and appends `sA`; `D` is still due at that moment, so
    `presentNotDue_before_dueSpawn` places `sA` before `D`'s eventual spawn
    `sD`. If a different event pops, both `A` and `D` survive and the claim is
    inherited by the induction hypothesis. -/
theorem World.samePriLockstep (w : World) (A D sA sD : ScheduledEvent)
    (hA_mem : A ∈ w.events) (hD_mem : D ∈ w.events)
    (hA_due : A.targetTick = w.tick) (hD_due : D.targetTick = w.tick)
    (h_pri : A.priority = D.priority)
    (h_nodup : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup)
    (h_before : ∃ l₁ l₂, w.events.filter (fun e => e.targetTick == w.tick) = l₁ ++ A :: l₂ ∧
      D ∈ l₂)
    (h_sA_nd : sA.targetTick ≠ w.tick) (h_sD_nd : sD.targetTick ≠ w.tick)
    (h_spawnA : ∀ (v : World), v.tick = w.tick →
        (v.onScheduledTick A.nodeId).events = v.events ++ [sA])
    (h_spawnD : ∀ (v : World), v.tick = w.tick →
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
        popNextEvent_not_D_of_append_split x A D ev₀ w_pop h_pop h_nodup l₁ l₂ h_split
          hD_l₂ (by omega)
      obtain ⟨idx, h_idx, h_erase, h_tick_ev, _, h_get_idx⟩ :=
        World.popNextEvent_eraseIdx x ev₀ w_pop h_pop
      have h_tick_pop : w_pop.tick = x.tick := World.popNextEvent_tick x ev₀ w_pop h_pop
      have h_tick_w' : w'.tick = x.tick := by
        rw [← h_w', World.onScheduledTick_tick, h_tick_pop]
      by_cases h_ev_A : ev₀ = A
      · -- the popped event is A itself: sA is appended now, D remains due
        have h_w'_events : w'.events = w_pop.events ++ [sA] := by
          rw [← h_w', h_ev_A]
          exact h_spawnA w_pop h_tick_pop
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
          exact mem_eraseIdx_of_ne x.events idx h_idx A D h_get_idx_A hD_mem hD_ne_A
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
            (v.onScheduledTick D.nodeId).events = v.events ++ [sD] :=
          fun v h_v ↦ h_spawnD v (h_v.trans h_tick_w')
        obtain ⟨p, q, h_tail, h_sD_q⟩ :=
          World.presentNotDue_before_dueSpawn w' sA D sD h_sA_mem h_sA_nd_w' hD_mem_w'
            hD_due_w' h_sD_nd_w' h_spawnD_w'
        rw [h_sunt]
        exact ⟨p, q, h_tail, h_sD_q⟩
      · -- some other event is popped: A and D both survive; apply the IH
        set due := x.events.filter (fun e => e.targetTick == x.tick)
        have h_due_ev₀ : (fun e => e.targetTick == x.tick) (x.events[idx]'h_idx) = true := by
          simp [h_get_idx, h_tick_ev]
        obtain ⟨j, hj, h_filter_erase, h_get_due⟩ :=
          filter_eraseIdx_getElem (fun e => e.targetTick == x.tick) x.events idx h_idx h_due_ev₀
        have h_get_due_ev₀ : due[j]'hj = ev₀ := h_get_due.trans h_get_idx
        obtain ⟨new, h_app_new, h_fut_new⟩ :=
          World.onScheduledTick_appends_future w_pop ev₀.nodeId
        have h_due_tail : w'.events.filter (fun e => e.targetTick == w'.tick) = due.eraseIdx j :=
          by
          rw [← h_w', World.onScheduledTick_tick, h_tick_pop, h_app_new, List.filter_append]
          have h_new_nil : new.filter (fun e => e.targetTick == x.tick) = [] := by
            apply List.filter_eq_nil_iff.mpr
            intro e h_e
            have h_gt := h_fut_new e h_e
            rw [h_tick_pop] at h_gt
            simp
            omega
          rw [h_new_nil, List.append_nil, h_erase, h_filter_erase]
        have hA_mem_pop : A ∈ w_pop.events := by
          rw [h_erase]
          exact mem_eraseIdx_of_ne x.events idx h_idx ev₀ A h_get_idx hA_mem (Ne.symm h_ev_A)
        have hD_mem_pop : D ∈ w_pop.events := by
          rw [h_erase]
          exact mem_eraseIdx_of_ne x.events idx h_idx ev₀ D h_get_idx hD_mem (Ne.symm h_ev_ne_D)
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
        have h_nodup_w' : (w'.events.filter (fun e => e.targetTick == w'.tick)).Nodup := by
          rw [h_due_tail]
          exact nodup_eraseIdx due j h_nodup
        have h_before_w' : ∃ m₁ m₂,
            w'.events.filter (fun e => e.targetTick == w'.tick) = m₁ ++ A :: m₂ ∧ D ∈ m₂ := by
          rw [h_due_tail]
          obtain ⟨m₁, m₂, h_eq, hD_m₂⟩ :=
            eraseIdx_preserves_order due l₁ l₂ A D ev₀ h_split hD_l₂ h_ev_A h_ev_ne_D j hj
              h_get_due_ev₀
          exact ⟨m₁, m₂, h_eq, hD_m₂⟩
        have h_spawnA_w' : ∀ (v : World), v.tick = w'.tick →
            (v.onScheduledTick A.nodeId).events = v.events ++ [sA] :=
          fun v h_v ↦ h_spawnA v (h_v.trans h_tick_w')
        have h_spawnD_w' : ∀ (v : World), v.tick = w'.tick →
            (v.onScheduledTick D.nodeId).events = v.events ++ [sD] :=
          fun v h_v ↦ h_spawnD v (h_v.trans h_tick_w')
        obtain ⟨p, q, h_tail, h_sD_q⟩ :=
          ih hA_mem_w' hD_mem_w' hA_due_w' hD_due_w' h_nodup_w' h_before_w'
            h_sA_nd_w' h_sD_nd_w' h_spawnA_w' h_spawnD_w'
        rw [h_sunt]
        exact ⟨p, q, h_tail, h_sD_q⟩
