import BasicProofs.GroupClustering.PopSeqFuel


open BasicRedstoneSim List

/-! # Group clustering — full-tick structure, lockstep, and assembly

This file builds the capstone machinery:

* `evBefore` — the strict "before" relation on event lists;
* fuel-bounded pop worlds (`World.popSeqWorldFuel`) and their relation to
  `processNEvents`;
* the tick-level structural theorem: `W(t+1).events = W(t).events.filter(≠t)
  ++ new` with `new` the chronological list of spawned events and observer
  batches (`newAt`), proven together with `Nodup` of every tick-start queue;
* spawn presence/order: a due event's spawn lands in `new` when the event
  pops, and spawn order in `new` = pop order;
* backward membership (windowed stage events are queued) and survival;
* the full lockstep corollaries (same-priority and cross-priority);
* the before-ness induction `Q(j)` and the between-ness induction `P(j)`;
* the log bridge (outputs = final pops in pop order) and the assembly of
  the two capstone theorems.
-/

/-! ## The `evBefore` relation -/

/-- `x` occurs strictly before `y` in the list. -/
def evBefore (l : List ScheduledEvent) (x y : ScheduledEvent) : Prop :=
  ∃ p q, l = p ++ x :: q ∧ y ∈ q

theorem evBefore.mem_left {l : List ScheduledEvent} {x y : ScheduledEvent}
    (h : evBefore l x y) : x ∈ l := by
  obtain ⟨p, q, h_eq, _⟩ := h
  rw [h_eq]
  exact List.mem_append_right _ (List.mem_cons.mpr (Or.inl rfl))

theorem evBefore.mem_right {l : List ScheduledEvent} {x y : ScheduledEvent}
    (h : evBefore l x y) : y ∈ l := by
  obtain ⟨p, q, h_eq, h_y⟩ := h
  rw [h_eq]
  exact List.mem_append_right _ (List.mem_cons.mpr (Or.inr h_y))

/-- Cons decomposition of `evBefore`. -/
theorem evBefore.cons_iff {l : List ScheduledEvent} {a x y : ScheduledEvent} :
    evBefore (a :: l) x y ↔ a = x ∧ y ∈ l ∨ evBefore l x y := by
  constructor
  · intro h
    obtain ⟨p, q, h_eq, h_y⟩ := h
    cases p with
    | nil =>
      dsimp at h_eq
      injection h_eq with h_ax h_lq
      exact Or.inl ⟨h_ax, by rwa [h_lq]⟩
    | cons b p' =>
      change a :: l = (b :: p') ++ (x :: q) at h_eq
      rw [List.cons_append] at h_eq
      injection h_eq with _ h_rest
      exact Or.inr ⟨p', q, h_rest, h_y⟩
  · intro h
    rcases h with ⟨rfl, h_y⟩ | h
    · exact ⟨[], l, rfl, h_y⟩
    · obtain ⟨p, q, h_eq, h_y⟩ := h
      refine ⟨a :: p, q, ?_, h_y⟩
      rw [h_eq, ← List.cons_append]

/-- `evBefore` is irreflexive-ish: nothing is before anything in `[]`. -/
theorem evBefore.not_nil {x y : ScheduledEvent} (h : evBefore [] x y) : False := by
  obtain ⟨p, q, h_eq, _⟩ := h
  cases p with
  | nil => cases h_eq
  | cons b p' => cases h_eq

/-- `evBefore` is asymmetric on duplicate-free lists. -/
theorem evBefore.asymm {l : List ScheduledEvent} (h_nd : l.Nodup) {x y : ScheduledEvent}
    (h : evBefore l x y) : ¬ evBefore l y x := by
  induction l generalizing x y with
  | nil => exact fun _ => evBefore.not_nil h
  | cons a l ih =>
    rw [List.nodup_cons] at h_nd
    rw [evBefore.cons_iff] at h
    intro h_rev
    rw [evBefore.cons_iff] at h_rev
    rcases h with ⟨h_ax, h_y⟩ | h
    · rcases h_rev with ⟨h_ay, h_x⟩ | h_rev
      · exact h_nd.1 (by rwa [← h_ax] at h_x)
      · have h_x_l : x ∈ l := evBefore.mem_right h_rev
        exact h_nd.1 (by rwa [← h_ax] at h_x_l)
    · rcases h_rev with ⟨h_ay, h_x⟩ | h_rev
      · have h_y_l : y ∈ l := evBefore.mem_right h
        exact h_nd.1 (by rwa [← h_ay] at h_y_l)
      · exact ih h_nd.2 h h_rev

/-- Appending on the right preserves `evBefore`. -/
theorem evBefore.append_right {l r : List ScheduledEvent} {x y : ScheduledEvent}
    (h : evBefore l x y) : evBefore (l ++ r) x y := by
  obtain ⟨p, q, h_eq, h_y⟩ := h
  refine ⟨p, q ++ r, ?_, ?_⟩
  · rw [h_eq, List.append_assoc, List.cons_append]
  · exact List.mem_append.mpr (Or.inl h_y)

/-- Prepending a whole list on the left preserves `evBefore`. -/
theorem evBefore.append_left {l r : List ScheduledEvent} {x y : ScheduledEvent}
    (h : evBefore r x y) : evBefore (l ++ r) x y := by
  obtain ⟨p, q, h_eq, h_y⟩ := h
  refine ⟨l ++ p, q, ?_, h_y⟩
  rw [h_eq, ← List.append_assoc]

/-- Prepending an element preserves `evBefore`. -/
theorem evBefore.cons_extend {l : List ScheduledEvent} {a x y : ScheduledEvent}
    (h : evBefore l x y) : evBefore (a :: l) x y := by
  obtain ⟨p, q, h_eq, h_y⟩ := h
  refine ⟨a :: p, q, ?_, h_y⟩
  rw [h_eq, ← List.cons_append]

/-- A head different from `x` can be dropped. -/
theorem evBefore.of_cons_ne {l : List ScheduledEvent} {a x y : ScheduledEvent}
    (h : evBefore (a :: l) x y) (h_ne : a ≠ x) : evBefore l x y := by
  rw [evBefore.cons_iff] at h
  rcases h with ⟨h_ax, _⟩ | h
  · exact absurd h_ax h_ne
  · exact h

/-- `evBefore` from membership in the two parts of an append. -/
theorem evBefore.of_mem_append {l₁ l₂ : List ScheduledEvent} {x y : ScheduledEvent}
    (h_x : x ∈ l₁) (h_y : y ∈ l₂) : evBefore (l₁ ++ l₂) x y := by
  obtain ⟨p, q, h_eq⟩ : ∃ p q, l₁ = p ++ x :: q := by
    induction l₁ generalizing x with
    | nil => cases h_x
    | cons b l ih =>
      rw [List.mem_cons] at h_x
      rcases h_x with rfl | h_x
      · exact ⟨[], l, rfl⟩
      · obtain ⟨p, q, h_eq⟩ := ih h_x
        refine ⟨b :: p, q, ?_⟩
        rw [h_eq, ← List.cons_append]
  refine ⟨p, q ++ l₂, ?_, List.mem_append_right _ h_y⟩
  rw [h_eq, List.append_assoc, List.cons_append]

/-- Filter reduction for a kept head. -/
private theorem filter_cons_true (p : ScheduledEvent → Bool) (a : ScheduledEvent)
    (l : List ScheduledEvent) (h_pa : p a = true) :
    (a :: l).filter p = a :: l.filter p := by
  simp [List.filter, h_pa]

/-- Filter reduction for a dropped head. -/
private theorem filter_cons_false (p : ScheduledEvent → Bool) (a : ScheduledEvent)
    (l : List ScheduledEvent) (h_pa : p a = false) :
    (a :: l).filter p = l.filter p := by
  simp [List.filter, h_pa]

/-- A filter that keeps `x` and `y` preserves `evBefore`. -/
theorem evBefore.filter {l : List ScheduledEvent} {x y : ScheduledEvent}
    (p : ScheduledEvent → Bool) (h_px : p x = true) (h_py : p y = true)
    (h : evBefore l x y) : evBefore (l.filter p) x y := by
  obtain ⟨p₀, q₀, h_eq, h_y⟩ := h
  subst h_eq
  induction p₀ generalizing q₀ with
  | nil =>
    have h_red : ([] ++ x :: q₀).filter p = x :: q₀.filter p := by
      rw [List.nil_append]
      exact filter_cons_true p x q₀ h_px
    rw [h_red]
    refine ⟨[], q₀.filter p, by rfl, ?_⟩
    rw [List.mem_filter]
    exact ⟨h_y, h_py⟩
  | cons b p₀' ih =>
    rw [List.cons_append]
    cases h_pb : p b with
    | true =>
      rw [filter_cons_true p b (p₀' ++ x :: q₀) h_pb]
      exact evBefore.cons_extend (ih q₀ h_y)
    | false =>
      rw [filter_cons_false p b (p₀' ++ x :: q₀) h_pb]
      exact ih q₀ h_y

/-- `evBefore` in a filter sublist lifts to the whole list. -/
theorem evBefore.of_filter {l : List ScheduledEvent} {x y : ScheduledEvent}
    (p : ScheduledEvent → Bool) (h : evBefore (l.filter p) x y) : evBefore l x y := by
  induction l generalizing x y with
  | nil => exact h
  | cons a l ih =>
    cases h_pa : p a with
    | true =>
      rw [filter_cons_true p a l h_pa] at h
      rw [evBefore.cons_iff] at h
      rcases h with ⟨h_ax, h_y⟩ | h
      · refine ⟨[], l, ?_, (List.mem_filter.mp h_y).1⟩
        subst h_ax
        rfl
      · exact evBefore.cons_extend (ih h)
    | false =>
      rw [filter_cons_false p a l h_pa] at h
      exact evBefore.cons_extend (ih h)

/-- Transferring `evBefore` out of a drop. -/
theorem evBefore.of_drop {l : List ScheduledEvent} {x y : ScheduledEvent} (n : Nat)
    (h : evBefore (l.drop n) x y) : evBefore l x y := by
  induction n generalizing l with
  | zero => exact h
  | succ n ih =>
    cases l with
    | nil => exact h
    | cons a l' =>
      have h' : evBefore (l'.drop n) x y := h
      exact evBefore.cons_extend (ih h')

/-- Distinct members of a duplicate-free list are comparable by `evBefore`. -/
theorem evBefore.total_of_nodup {l : List ScheduledEvent} (h_nd : l.Nodup)
    {x y : ScheduledEvent} (h_x : x ∈ l) (h_y : y ∈ l) (h_ne : x ≠ y) :
    evBefore l x y ∨ evBefore l y x := by
  induction l generalizing y with
  | nil => cases h_x
  | cons a l ih =>
    rw [List.nodup_cons] at h_nd
    rw [List.mem_cons] at h_x
    rcases h_x with rfl | h_x
    · rw [List.mem_cons] at h_y
      rcases h_y with h_eq | h_y
      · exact absurd h_eq.symm h_ne
      · exact Or.inl ⟨[], l, rfl, h_y⟩
    · rw [List.mem_cons] at h_y
      rcases h_y with rfl | h_y
      · exact Or.inr ⟨[], l, rfl, h_x⟩
      · obtain h | h := ih h_nd.2 h_x h_y h_ne
        · exact Or.inl (evBefore.cons_extend h)
        · exact Or.inr (evBefore.cons_extend h)

/-- Appending a single fresh element keeps a duplicate-free list
    duplicate-free. -/
private theorem nodup_append_singleton {α : Type} {l : List α} {a : α}
    (h : l.Nodup) (h_na : a ∉ l) : (l ++ [a]).Nodup := by
  induction l with
  | nil => simp
  | cons b l ih =>
    simp only [List.cons_append, List.nodup_cons]
    rw [List.nodup_cons] at h
    refine ⟨?_, ih h.2 (fun h_mem => h_na (List.mem_cons.mpr (Or.inr h_mem)))⟩
    intro h_mem
    rw [List.mem_append, List.mem_singleton] at h_mem
    rcases h_mem with h_mem | rfl
    · exact h.1 h_mem
    · exact h_na (List.mem_cons.mpr (Or.inl rfl))

/-- Appending a fresh duplicate-free tail keeps the append duplicate-free. -/
theorem nodup_append_of_disjoint {α : Type} {l₁ l₂ : List α}
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) (h_dis : ∀ x ∈ l₂, x ∉ l₁) :
    (l₁ ++ l₂).Nodup := by
  induction l₂ generalizing l₁ with
  | nil =>
    rw [List.append_nil]
    exact h₁
  | cons a l ih =>
    rw [List.nodup_cons] at h₂
    have h_l₁a : (l₁ ++ [a]).Nodup :=
      nodup_append_singleton h₁ (h_dis a (List.mem_cons.mpr (Or.inl rfl)))
    have h_dis' : ∀ x ∈ l, x ∉ l₁ ++ [a] := by
      intro x hx h_mem
      rw [List.mem_append, List.mem_singleton] at h_mem
      rcases h_mem with h_mem | rfl
      · exact h_dis x (List.mem_cons.mpr (Or.inr hx)) h_mem
      · exact h₂.1 hx
    have h_assoc : l₁ ++ (a :: l) = (l₁ ++ [a]) ++ l := by
      calc l₁ ++ (a :: l)
          = l₁ ++ ([a] ++ l) := by rfl
        _ = (l₁ ++ [a]) ++ l := (List.append_assoc l₁ [a] l).symm
    rw [h_assoc]
    exact ih (l₁ := l₁ ++ [a]) h_l₁a h₂.2 h_dis'

/-! ## Fuel-bounded pop worlds -/

/-- The world after `fuel` pops (no tick advance; stops when nothing is
    due). Mirrors `processNEvents`. -/
def World.popSeqWorldFuel (w : World) : Nat → World
  | 0 => w
  | fuel + 1 =>
    match w.popNextEvent with
    | none => w
    | some (ev, w_pop) => World.popSeqWorldFuel (w_pop.onScheduledTick ev.nodeId) fuel

theorem World.popSeqWorldFuel_tick (w : World) (fuel : Nat) :
    (World.popSeqWorldFuel w fuel).tick = w.tick := by
  induction fuel generalizing w with
  | zero => rfl
  | succ fuel ih =>
    dsimp only [World.popSeqWorldFuel]
    cases h_pop : w.popNextEvent with
    | none => rfl
    | some p =>
      rcases p with ⟨ev, w_pop⟩
      rw [ih, World.onScheduledTick_tick, World.popNextEvent_tick w ev w_pop h_pop]

/-- `processNEvents` is exactly the fuel-bounded pop world. -/
theorem processNEvents_eq_popSeqWorldFuel (w : World) (n : Nat) :
    processNEvents w n = World.popSeqWorldFuel w n := by
  induction n generalizing w with
  | zero =>
    simp [processNEvents, World.popSeqWorldFuel]
  | succ n ih =>
    dsimp only [processNEvents, World.popSeqWorldFuel]
    cases h_pop : w.popNextEvent with
    | none =>
      have h_step : w.step = none := by
        dsimp [World.step]; rw [h_pop]
      rw [h_step]
    | some p =>
      rcases p with ⟨ev, w_pop⟩
      have h_step : w.step = some (w_pop.onScheduledTick ev.nodeId) := by
        dsimp [World.step]; rw [h_pop]
      rw [h_step]
      exact ih (w_pop.onScheduledTick ev.nodeId)

/-- `popNextEvent = none` exactly when no event is due. -/
theorem World.popNextEvent_none_of_no_due (w : World)
    (h_no : ∀ ev ∈ w.events, ev.targetTick ≠ w.tick) :
    w.popNextEvent = none := by
  cases h_pop : w.popNextEvent with
  | none => rfl
  | some p =>
    rcases p with ⟨ev', w_pop⟩
    obtain ⟨idx, h_idx, _, h_due, _, h_get⟩ :=
      World.popNextEvent_eraseIdx w ev' w_pop h_pop
    exact False.elim
      (h_no ev' (by rw [← h_get]; exact List.getElem_mem h_idx) h_due)

/-- When nothing is due, the pop sequence is empty. -/
theorem World.popSeqFuel_of_no_due (w : World) (fuel : Nat)
    (h_no : ∀ ev ∈ w.events, ev.targetTick ≠ w.tick) :
    World.popSeqFuel w fuel = [] := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    dsimp only [World.popSeqFuel]
    rw [World.popNextEvent_none_of_no_due w h_no]

/-- A world with no due events is unchanged by further fuel. -/
theorem World.popSeqWorldFuel_of_no_due (w : World)
    (h_no : ∀ ev ∈ w.events, ev.targetTick ≠ w.tick) (fuel : Nat) :
    World.popSeqWorldFuel w fuel = w := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    dsimp only [World.popSeqWorldFuel]
    rw [World.popNextEvent_none_of_no_due w h_no]

/-- Fuel concatenation for the pop sequence. -/
theorem World.popSeqFuel_concat (w : World) (a b : Nat) :
    World.popSeqFuel w (a + b) =
    World.popSeqFuel w a ++ World.popSeqFuel (World.popSeqWorldFuel w a) b := by
  induction a generalizing w b with
  | zero =>
    rw [Nat.zero_add]
    dsimp only [World.popSeqFuel, World.popSeqWorldFuel]
    simp
  | succ a ih =>
    rw [Nat.succ_add]
    dsimp only [World.popSeqFuel, World.popSeqWorldFuel]
    cases h_pop : w.popNextEvent with
    | none =>
      change [] = [] ++ World.popSeqFuel w b
      have h_no := popNextEvent_none_no_events w h_pop
      rw [World.popSeqFuel_of_no_due w b h_no]
      simp
    | some p =>
      rcases p with ⟨ev, w_pop⟩
      change ev :: World.popSeqFuel (w_pop.onScheduledTick ev.nodeId) (a + b) =
        (ev :: World.popSeqFuel (w_pop.onScheduledTick ev.nodeId) a) ++
          World.popSeqFuel (World.popSeqWorldFuel (w_pop.onScheduledTick ev.nodeId) a) b
      rw [List.cons_append, ih (w_pop.onScheduledTick ev.nodeId) b]

/-- Fuel concatenation for the pop worlds. -/
theorem World.popSeqWorldFuel_concat (w : World) (a b : Nat) :
    World.popSeqWorldFuel w (a + b) =
    World.popSeqWorldFuel (World.popSeqWorldFuel w a) b := by
  induction a generalizing w b with
  | zero =>
    rw [Nat.zero_add]
    rfl
  | succ a ih =>
    rw [Nat.succ_add]
    dsimp only [World.popSeqWorldFuel]
    cases h_pop : w.popNextEvent with
    | none =>
      change w = World.popSeqWorldFuel w b
      exact (World.popSeqWorldFuel_of_no_due w
        (popNextEvent_none_no_events w h_pop) b).symm
    | some p =>
      rcases p with ⟨ev, w_pop⟩
      change World.popSeqWorldFuel (w_pop.onScheduledTick ev.nodeId) (a + b) =
        World.popSeqWorldFuel (World.popSeqWorldFuel (w_pop.onScheduledTick ev.nodeId) a) b
      exact ih (w_pop.onScheduledTick ev.nodeId) b

/-- Every popped event was already present in the starting world: appended
    events target strictly later ticks, so they are never popped within the
    same tick. -/
theorem World.mem_popSeqFuel_mem_events (w : World) (fuel : Nat)
    (ev : ScheduledEvent) (h : ev ∈ World.popSeqFuel w fuel) : ev ∈ w.events := by
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
      obtain ⟨idx, h_idx, h_erase, _, _, h_get⟩ :=
        World.popNextEvent_eraseIdx w ev₀ w_pop h_pop
      rcases h with rfl | h
      · rw [← h_get]
        exact List.getElem_mem h_idx
      · have h_mem_w' : ev ∈ (w_pop.onScheduledTick ev₀.nodeId).events :=
          ih (w_pop.onScheduledTick ev₀.nodeId) h
        obtain ⟨new, h_app_new, h_fut_new⟩ :=
          World.onScheduledTick_appends_future w_pop ev₀.nodeId
        have h_tick_pop : w_pop.tick = w.tick :=
          World.popNextEvent_tick w ev₀ w_pop h_pop
        rw [h_app_new, List.mem_append] at h_mem_w'
        rcases h_mem_w' with h_mem | h_new
        · rw [h_erase] at h_mem
          exact List.eraseIdx_subset' w.events idx h_mem
        · have h_due :=
            World.mem_popSeqFuel_due (w_pop.onScheduledTick ev₀.nodeId) fuel ev h
          rw [World.onScheduledTick_tick, h_tick_pop] at h_due
          have h_gt := h_fut_new ev h_new
          rw [h_tick_pop] at h_gt
          omega

/-- Unpopped events survive the fuel-bounded pops. -/
theorem World.mem_popSeqWorldFuel_of_not_popped (w : World) (fuel : Nat)
    (ev : ScheduledEvent) (h_ev : ev ∈ w.events)
    (h_np : ev ∉ World.popSeqFuel w fuel) :
    ev ∈ (World.popSeqWorldFuel w fuel).events := by
  induction fuel generalizing w with
  | zero =>
    dsimp only [World.popSeqWorldFuel]
    exact h_ev
  | succ fuel ih =>
    dsimp only [World.popSeqWorldFuel, World.popSeqFuel] at h_np ⊢
    cases h_pop : w.popNextEvent with
    | none =>
      change ev ∈ w.events
      exact h_ev
    | some p =>
      rcases p with ⟨ev₀, w_pop⟩
      simp only [h_pop] at h_np
      rw [List.mem_cons] at h_np
      change ev ∈ (World.popSeqWorldFuel (w_pop.onScheduledTick ev₀.nodeId) fuel).events
      obtain ⟨idx, h_idx, h_erase, _, _, h_get⟩ :=
        World.popNextEvent_eraseIdx w ev₀ w_pop h_pop
      have h_ne : ev ≠ ev₀ := fun h_eq =>
        h_np (Or.inl h_eq)
      have h_ev_pop : ev ∈ w_pop.events := by
        rw [h_erase]
        exact mem_eraseIdx_of_ne w.events idx h_idx ev₀ ev h_get h_ev h_ne
      have h_ev_w' : ev ∈ (w_pop.onScheduledTick ev₀.nodeId).events :=
        World.onScheduledTick_events_subset w_pop ev₀.nodeId h_ev_pop
      apply ih (w_pop.onScheduledTick ev₀.nodeId) h_ev_w'
      intro h_contra
      exact h_np (Or.inr h_contra)

/-! ## Chronological spawn accumulators -/

/-- `(l₁ ++ l₂).drop l₁.length = l₂`. -/
private theorem drop_append_self {α : Type} (l₁ l₂ : List α) :
    (l₁ ++ l₂).drop l₁.length = l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a l ih => simp [ih]

/-- `filter` keeps a list unchanged when the predicate holds everywhere. -/
private theorem filter_eq_self_of_forall' {α : Type} (p : α → Bool) (l : List α)
    (h : ∀ x ∈ l, p x = true) : l.filter p = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have h_x := h x (List.mem_cons.mpr (Or.inl rfl))
    simp [List.filter, h_x, ih (fun y hy => h y (List.mem_cons.mpr (Or.inr hy)))]

/-- Append cancellation on the left. -/
private theorem append_left_cancel' {α : Type} (l l₁ l₂ : List α)
    (h : l ++ l₁ = l ++ l₂) : l₁ = l₂ := by
  induction l generalizing l₁ l₂ with
  | nil => simpa using h
  | cons a l ih =>
    simp only [List.cons_append] at h
    have h_tail : l ++ l₁ = l ++ l₂ := by
      simpa using congrArg List.tail h
    exact ih l₁ l₂ h_tail

/-- Erasing an element that fails `p` does not change the `p`-filter. -/
private theorem filter_eraseIdx_of_neg' {α : Type} (p : α → Bool) (l : List α)
    (i : Nat) (hi : i < l.length) (h_neg : p (l[i]'hi) = false) :
    (l.eraseIdx i).filter p = l.filter p := by
  revert i hi h_neg
  induction l with
  | nil => intro i hi; cases hi
  | cons x xs ih =>
    intro i hi h_neg
    cases i with
    | zero =>
      have h_px : p x = false := by simpa using h_neg
      simp [List.eraseIdx, List.filter, h_px]
    | succ i' =>
      have hi' : i' < xs.length := Nat.lt_of_succ_lt_succ hi
      simp only [List.getElem_cons_succ] at h_neg
      simp only [List.eraseIdx, List.filter]
      rw [ih i' hi' h_neg]

/-- The events appended by `fuel` pops, in chronological pop order. -/
def World.popSpawnAcc (w : World) : Nat → List ScheduledEvent
  | 0 => []
  | fuel + 1 =>
    match w.popNextEvent with
    | none => []
    | some (ev, w_pop) =>
      (w_pop.onScheduledTick ev.nodeId).events.drop w_pop.events.length ++
        World.popSpawnAcc (w_pop.onScheduledTick ev.nodeId) fuel

/-- Every event in `World.popSpawnAcc` targets a strictly later tick. -/
theorem World.popSpawnAcc_future (w : World) (fuel : Nat) :
    ∀ ev ∈ World.popSpawnAcc w fuel, ev.targetTick > w.tick := by
  induction fuel generalizing w with
  | zero => intro ev h; cases h
  | succ fuel ih =>
    dsimp only [World.popSpawnAcc]
    cases h_pop : w.popNextEvent with
    | none =>
      change ∀ (ev : ScheduledEvent), ev ∈ [] → ev.targetTick > w.tick
      intro ev h
      cases h
    | some p =>
      rcases p with ⟨ev₀, w_pop⟩
      dsimp
      intro ev h_ev
      rw [List.mem_append] at h_ev
      obtain ⟨new₀, h_app₀, h_fut₀⟩ := World.onScheduledTick_appends_future w_pop ev₀.nodeId
      have h_drop : (w_pop.onScheduledTick ev₀.nodeId).events.drop w_pop.events.length =
          new₀ := by
        rw [h_app₀, drop_append_self]
      rcases h_ev with h_ev | h_ev
      · rw [h_drop] at h_ev
        have := h_fut₀ ev h_ev
        rw [World.popNextEvent_tick w ev₀ w_pop h_pop] at this
        exact this
      · have := ih (w_pop.onScheduledTick ev₀.nodeId) ev h_ev
        rw [World.onScheduledTick_tick, World.popNextEvent_tick w ev₀ w_pop h_pop] at this
        exact this

/-- The fuel-bounded pop world, seen through the target-≠-tick filter: the
    old future events stay, and the chronological spawn accumulator is
    appended. -/
theorem World.popSeqWorldFuel_filter_split (w : World) (fuel : Nat) :
    (World.popSeqWorldFuel w fuel).events.filter
        (fun ev => ev.targetTick ≠ w.tick) =
      w.events.filter (fun ev => ev.targetTick ≠ w.tick) ++ World.popSpawnAcc w fuel ∧
    ∀ ev ∈ World.popSpawnAcc w fuel, ev.targetTick > w.tick := by
  induction fuel generalizing w with
  | zero =>
    dsimp only [World.popSeqWorldFuel, World.popSpawnAcc]
    exact ⟨by simp, by simp⟩
  | succ fuel ih =>
    dsimp only [World.popSeqWorldFuel, World.popSpawnAcc]
    cases h_pop : w.popNextEvent with
    | none =>
      exact ⟨by simp, by simp⟩
    | some p =>
      rcases p with ⟨ev₀, w_pop⟩
      dsimp
      obtain ⟨idx, h_idx, h_erase, h_tick_ev, _, h_idx_eq⟩ :=
        World.popNextEvent_eraseIdx w ev₀ w_pop h_pop
      obtain ⟨new₀, h_app₀, h_fut₀⟩ := World.onScheduledTick_appends_future w_pop ev₀.nodeId
      have h_tick_pop : w_pop.tick = w.tick := World.popNextEvent_tick w ev₀ w_pop h_pop
      have h_drop : (w_pop.onScheduledTick ev₀.nodeId).events.drop w_pop.events.length =
          new₀ := by
        rw [h_app₀, drop_append_self]
      obtain ⟨h_ih, h_fut_ih⟩ := ih (w_pop.onScheduledTick ev₀.nodeId)
      have h_filter_pop : w_pop.events.filter (fun ev => ev.targetTick ≠ w.tick) =
          w.events.filter (fun ev => ev.targetTick ≠ w.tick) := by
        rw [h_erase]
        exact filter_eraseIdx_of_neg' (fun ev => ev.targetTick ≠ w.tick) w.events idx
          h_idx (by rw [h_idx_eq, h_tick_ev]; simp)
      have h_keep_new₀ : new₀.filter (fun ev => ev.targetTick ≠ w.tick) = new₀ :=
        filter_eq_self_of_forall' (fun ev => ev.targetTick ≠ w.tick) new₀ (by
          intro ev h_ev
          have := h_fut₀ ev h_ev
          rw [h_tick_pop] at this
          simp [Nat.ne_of_gt this])
      constructor
      · have h_w'_filter : (w_pop.onScheduledTick ev₀.nodeId).events.filter
            (fun ev => ev.targetTick ≠ w.tick) =
          w.events.filter (fun ev => ev.targetTick ≠ w.tick) ++ new₀ := by
          rw [h_app₀, List.filter_append, h_filter_pop, h_keep_new₀]
        have h_tick_w' : (w_pop.onScheduledTick ev₀.nodeId).tick = w.tick := by
          rw [World.onScheduledTick_tick, h_tick_pop]
        rw [h_tick_w'] at h_ih
        rw [h_ih, h_w'_filter, h_drop]
        simp only [List.append_assoc]
      · intro ev h_ev
        rw [h_drop, List.mem_append] at h_ev
        rcases h_ev with h_ev | h_ev
        · have := h_fut₀ ev h_ev
          rw [h_tick_pop] at this
          exact this
        · have := h_fut_ih ev h_ev
          rw [World.onScheduledTick_tick, h_tick_pop] at this
          exact this

/-- A spawn of a popped event is present in the spawn accumulator. -/
theorem World.spawn_mem_of_pop_mem (w : World) (fuel : Nat)
    (X sX : ScheduledEvent)
    (h_X : X ∈ World.popSeqFuel w fuel)
    (h_spawn : ∀ (v : World), v.tick = w.tick →
        (v.onScheduledTick X.nodeId).events = v.events ++ [sX]) :
    sX ∈ World.popSpawnAcc w fuel := by
  induction fuel generalizing w with
  | zero =>
    dsimp only [World.popSeqFuel] at h_X
    cases h_X
  | succ fuel ih =>
    dsimp only [World.popSeqFuel, World.popSpawnAcc] at h_X
    dsimp only [World.popSpawnAcc]
    cases h_pop : w.popNextEvent with
    | none =>
      simp only [h_pop] at h_X
      cases h_X
    | some p =>
      rcases p with ⟨ev₀, w_pop⟩
      change sX ∈
        (w_pop.onScheduledTick ev₀.nodeId).events.drop w_pop.events.length ++
          World.popSpawnAcc (w_pop.onScheduledTick ev₀.nodeId) fuel
      simp only [h_pop, List.mem_cons] at h_X
      rcases h_X with h_X | h_X
      · -- X is the event popped now: sX is in this step's spawn part
        have h_tick_pop : w_pop.tick = w.tick :=
          World.popNextEvent_tick w ev₀ w_pop h_pop
        obtain ⟨new₀, h_app₀, _⟩ := World.onScheduledTick_appends_future w_pop ev₀.nodeId
        have h_drop : (w_pop.onScheduledTick ev₀.nodeId).events.drop w_pop.events.length =
            new₀ := by
          rw [h_app₀, drop_append_self]
        rw [h_drop]
        have h_sp : sX ∈ new₀ := by
          have h_appX := h_spawn w_pop h_tick_pop
          rw [h_X] at h_appX
          have h_eq : w_pop.events ++ [sX] = w_pop.events ++ new₀ := by
            rw [← h_appX, h_app₀]
          have h_new₀ : new₀ = [sX] := (append_left_cancel' w_pop.events [sX] new₀ h_eq).symm
          rw [h_new₀]
          simp
        exact List.mem_append.mpr (Or.inl h_sp)
      · exact List.mem_append.mpr (Or.inr
          (ih (w := w_pop.onScheduledTick ev₀.nodeId) h_X (fun v h_v =>
            h_spawn v (by
              rw [h_v, World.onScheduledTick_tick,
                World.popNextEvent_tick w ev₀ w_pop h_pop]))))

/-- Spawn order in the accumulator follows pop order in the pop sequence. -/
theorem World.spawn_evBefore_of_pop_evBefore (w : World) (fuel : Nat)
    (X Y sX sY : ScheduledEvent)
    (h_before : evBefore (World.popSeqFuel w fuel) X Y)
    (h_spawnX : ∀ (v : World), v.tick = w.tick →
        (v.onScheduledTick X.nodeId).events = v.events ++ [sX])
    (h_spawnY : ∀ (v : World), v.tick = w.tick →
        (v.onScheduledTick Y.nodeId).events = v.events ++ [sY]) :
    evBefore (World.popSpawnAcc w fuel) sX sY := by
  induction fuel generalizing w with
  | zero =>
    dsimp only [World.popSeqFuel] at h_before
    exact (evBefore.not_nil h_before).elim
  | succ fuel ih =>
    dsimp only [World.popSeqFuel] at h_before
    dsimp only [World.popSpawnAcc]
    cases h_pop : w.popNextEvent with
    | none =>
      simp only [h_pop] at h_before
      exact (evBefore.not_nil h_before).elim
    | some p =>
      rcases p with ⟨ev₀, w_pop⟩
      change evBefore
        ((w_pop.onScheduledTick ev₀.nodeId).events.drop w_pop.events.length ++
          World.popSpawnAcc (w_pop.onScheduledTick ev₀.nodeId) fuel) sX sY
      simp only [h_pop] at h_before
      rw [evBefore.cons_iff] at h_before
      rcases h_before with ⟨h_ev₀_X, h_Y_tail⟩ | h_before_tail
      · -- X is popped now; sX is appended in this step's spawn part
        have h_tick_pop : w_pop.tick = w.tick :=
          World.popNextEvent_tick w ev₀ w_pop h_pop
        have h_sX_mem : sX ∈
            (w_pop.onScheduledTick ev₀.nodeId).events.drop w_pop.events.length := by
          obtain ⟨new₀, h_app₀, _⟩ := World.onScheduledTick_appends_future w_pop ev₀.nodeId
          have h_drop : (w_pop.onScheduledTick ev₀.nodeId).events.drop w_pop.events.length =
              new₀ := by
            rw [h_app₀, drop_append_self]
          rw [h_drop]
          have h_appX := h_spawnX w_pop h_tick_pop
          rw [← h_ev₀_X] at h_appX
          have h_eq : w_pop.events ++ [sX] = w_pop.events ++ new₀ := by
            rw [← h_appX, h_app₀]
          have h_new₀ : new₀ = [sX] :=
            (append_left_cancel' w_pop.events [sX] new₀ h_eq).symm
          rw [h_new₀]
          simp
        have h_sY_mem : sY ∈
            World.popSpawnAcc (w_pop.onScheduledTick ev₀.nodeId) fuel :=
          World.spawn_mem_of_pop_mem (w_pop.onScheduledTick ev₀.nodeId) fuel Y sY
            h_Y_tail (fun v h_v =>
              h_spawnY v (by
                rw [h_v, World.onScheduledTick_tick, h_tick_pop]))
        exact evBefore.of_mem_append h_sX_mem h_sY_mem
      · -- some other (or Y's) case: both spawn later
        exact evBefore.append_left
          (ih (w := w_pop.onScheduledTick ev₀.nodeId) h_before_tail
            (fun v h_v => h_spawnX v (by
              rw [h_v, World.onScheduledTick_tick,
                World.popNextEvent_tick w ev₀ w_pop h_pop]))
            (fun v h_v => h_spawnY v (by
              rw [h_v, World.onScheduledTick_tick,
                World.popNextEvent_tick w ev₀ w_pop h_pop])))
