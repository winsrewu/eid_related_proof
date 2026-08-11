import BasicProofs.GroupClustering.MiddleBlockInvariant


open BasicRedstoneSim List

/-! # Group clustering — the converse spawn-origin fact

At the pop tick of stage `j`, the two reference events `A` and `D` spawn
`sA` and `sD`. This file proves the converse of the spawn-order step. Take
any event that sits between `sA` and `sD` in the next queue, carries
priority -3, and targets the stage-`j + 1` tick of the first reference
chain. That event is the stage-`j + 1` event of some chain, and the
stage-`j` event of that chain sits between `A` and `D` in the due filter.

The proof drains the tick with `processNEvents`, splits the next queue
into survivors and spawns, and traces the event back to its unique parent
pop.
-/

/-! ## List and `evBefore` helpers -/

/-- In a split `l ++ r = p ++ s` with `p` at least as long as `l`, the
    prefix `p` starts with `l`. -/
private theorem append_prefix_of_length_le {α : Type} (l r p s : List α)
    (h_eq : l ++ r = p ++ s) (h_len : l.length ≤ p.length) :
    ∃ p₁, p = l ++ p₁ ∧ r = p₁ ++ s := by
  revert h_eq h_len
  induction l generalizing p with
  | nil =>
    intro h_eq _
    simp only [List.nil_append] at h_eq
    exact ⟨p, by simp, h_eq⟩
  | cons a l ih =>
    intro h_eq h_len
    cases p with
    | nil => simp at h_len
    | cons b p' =>
      simp only [List.cons_append, List.length_cons] at h_eq h_len
      injection h_eq with h_ab h_rest
      obtain ⟨p₁, h_p', h_r⟩ := ih p' h_rest (by omega)
      refine ⟨p₁, ?_, h_r⟩
      rw [h_p', ← h_ab]
      rfl

/-- In `l ++ r = p ++ x :: q` with a short `p`, `x` lies in `l`. -/
private theorem mem_left_of_short_prefix_split {α : Type} (l r p q : List α)
    (x : α) (h_eq : l ++ r = p ++ x :: q) (h_lt : p.length < l.length) :
    x ∈ l := by
  induction p generalizing l with
  | nil =>
    simp only [List.nil_append] at h_eq
    cases l with
    | nil => exfalso; omega
    | cons a l' =>
      simp only [List.cons_append] at h_eq
      injection h_eq with h_ax _
      rw [← h_ax]
      exact List.mem_cons.mpr (Or.inl rfl)
  | cons b p' ih =>
    cases l with
    | nil => simp at h_lt
    | cons a l' =>
      simp only [List.cons_append, List.length_cons] at h_eq h_lt
      injection h_eq with _ h_rest
      have h_mem := ih l' h_rest (by omega)
      exact List.mem_cons.mpr (Or.inr h_mem)

/-- An event that comes after an anchor absent from the left part lies in
    the appended part. -/
private theorem evBefore_append_right_mem {l r : List ScheduledEvent}
    {x z : ScheduledEvent} (h_x : x ∉ l) (h : evBefore (l ++ r) x z) :
    z ∈ r := by
  obtain ⟨p, q, h_eq, h_z⟩ := h
  have h_len : l.length ≤ p.length := by
    by_contra h_lt
    exact h_x (mem_left_of_short_prefix_split l r p q x h_eq (by omega))
  obtain ⟨p₁, _, h_r⟩ := append_prefix_of_length_le l r p (x :: q) h_eq h_len
  rw [h_r]
  exact List.mem_append_right p₁ (List.mem_cons.mpr (Or.inr h_z))

/-- If the left anchor is absent from `l`, then `evBefore (l ++ r) x y`
    already holds in `r`. -/
private theorem evBefore_append_left_absent {l r : List ScheduledEvent}
    {x y : ScheduledEvent} (h_x : x ∉ l) (h : evBefore (l ++ r) x y) :
    evBefore r x y := by
  obtain ⟨p, q, h_eq, h_y⟩ := h
  have h_len : l.length ≤ p.length := by
    by_contra h_lt
    exact h_x (mem_left_of_short_prefix_split l r p q x h_eq (by omega))
  obtain ⟨p₁, _, h_r⟩ := append_prefix_of_length_le l r p (x :: q) h_eq h_len
  exact ⟨p₁, q, h_r, h_y⟩

/-- With `y` absent from `l`, the split of `evBefore (l ++ r) x y` starts
    in `l` or lies in `r`. -/
private theorem evBefore_append_split_right {l r : List ScheduledEvent}
    {x y : ScheduledEvent} (h : evBefore (l ++ r) x y) :
    x ∈ l ∨ evBefore r x y := by
  obtain ⟨p, q, h_eq, h_yq⟩ := h
  by_cases h_lt : p.length < l.length
  · exact Or.inl (mem_left_of_short_prefix_split l r p q x h_eq h_lt)
  · obtain ⟨p₁, _, h_r⟩ :=
      append_prefix_of_length_le l r p (x :: q) h_eq (by omega)
    exact Or.inr ⟨p₁, q, h_r, h_yq⟩

/-- An `evBefore` witness against itself places two copies of the
    event. -/
private theorem evBefore_self_two_split {l : List ScheduledEvent}
    {x : ScheduledEvent} (h : evBefore l x x) :
    ∃ l₁ l₂ l₃, l = l₁ ++ x :: (l₂ ++ x :: l₃) := by
  obtain ⟨p, q, h_eq, h_x⟩ := h
  obtain ⟨p₂, q₂, h_q⟩ := mem_split_append q x h_x
  refine ⟨p, p₂, q₂, ?_⟩
  rw [h_eq, h_q]

/-- `(l₁ ++ l₂).drop l₁.length = l₂`. -/
private theorem drop_append_self {α : Type} (l₁ l₂ : List α) :
    (l₁ ++ l₂).drop l₁.length = l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a l ih => simp [ih]

/-- Append cancellation on the left. -/
private theorem append_left_cancel' {α : Type} (l l₁ l₂ : List α)
    (h : l ++ l₁ = l ++ l₂) : l₁ = l₂ := by
  induction l generalizing l₁ l₂ with
  | nil => simpa using h
  | cons a l ih =>
    simp only [List.cons_append] at h
    exact ih l₁ l₂ (by simpa using congrArg List.tail h)

/-- Filter reduction for a kept head. -/
private theorem filter_cons_true (p : ScheduledEvent → Bool)
    (a : ScheduledEvent) (l : List ScheduledEvent) (h_pa : p a = true) :
    (a :: l).filter p = a :: l.filter p := by
  simp [List.filter, h_pa]

/-- `filter` keeps a list unchanged when the predicate holds
    everywhere. -/
private theorem filter_eq_self_of_forall' {α : Type} (p : α → Bool)
    (l : List α) (h : ∀ x ∈ l, p x = true) : l.filter p = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have h_x := h x (List.mem_cons.mpr (Or.inl rfl))
    simp [List.filter, h_x, ih (fun y hy => h y (List.mem_cons.mpr (Or.inr hy)))]

/-- A filter is empty when no member satisfies the predicate. -/
private theorem filter_empty_of_none {α : Type} (p : α → Bool) (l : List α)
    (h : ∀ x ∈ l, p x = false) : l.filter p = [] := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp [List.filter, h x (List.mem_cons.mpr (Or.inl rfl)),
      ih (fun y hy => h y (List.mem_cons.mpr (Or.inr hy)))]

/-- A Nat inequality decides the `==` comparison to false. -/
private theorem nat_beq_false_of_ne (a b : Nat) (h : a ≠ b) :
    (a == b) = false := by
  simp [h]

/-- A list of length zero is empty. -/
private theorem list_nil_of_length_zero {α : Type} (l : List α)
    (h : l.length = 0) : l = [] := by
  cases l with
  | nil => rfl
  | cons _ _ => simp at h

/-- Erasing an in-range element removes exactly one position. -/
private theorem length_eraseIdx_of_lt {α : Type} (l : List α) (i : Nat)
    (h : i < l.length) : (l.eraseIdx i).length = l.length - 1 := by
  revert i h
  induction l with
  | nil => intro i h; cases h
  | cons x xs ih =>
    intro i h
    cases i with
    | zero => simp [List.eraseIdx]
    | succ i' =>
      have h_i' : i' < xs.length := Nat.lt_of_succ_lt_succ (by simpa using h)
      simp only [List.eraseIdx, List.length_cons]
      rw [ih i' h_i']
      have h_ge : xs.length ≥ 1 := by omega
      omega

/-- If `l[idx] = a` and `a` survives `eraseIdx idx`, then `l` carries `a`
    at two positions. -/
private theorem two_split_of_mem_eraseIdx {α : Type} (l : List α)
    (idx : Nat) (h_idx : idx < l.length) (a : α)
    (h_get : l[idx]'h_idx = a) (h_mem : a ∈ l.eraseIdx idx) :
    ∃ l₁ l₂ l₃, l = l₁ ++ a :: l₂ ++ a :: l₃ := by
  revert idx h_idx h_get h_mem
  induction l with
  | nil => intro idx h_idx; cases h_idx
  | cons x xs ih =>
    intro idx h_idx h_get h_mem
    cases idx with
    | zero =>
      dsimp at h_get
      dsimp only [List.eraseIdx] at h_mem
      obtain ⟨t₁, t₂, h_t⟩ := mem_split_append xs a h_mem
      subst h_get
      refine ⟨[], t₁, t₂, ?_⟩
      rw [h_t]
      rfl
    | succ idx' =>
      have h_idx' : idx' < xs.length := by simpa using h_idx
      dsimp only [List.eraseIdx] at h_mem
      rw [List.mem_cons] at h_mem
      rcases h_mem with rfl | h_mem
      · have h_xs_mem : a ∈ xs := by
          rw [← h_get]
          exact List.getElem_mem h_idx'
        obtain ⟨xs₁, xs₂, h_xs⟩ := mem_split_append xs a h_xs_mem
        refine ⟨[], xs₁, xs₂, ?_⟩
        rw [h_xs]
        rfl
      · obtain ⟨xs₁, xs₂, xs₃, h_xs⟩ :=
          ih idx' h_idx' (by simpa [List.getElem_cons_succ] using h_get) h_mem
        refine ⟨x :: xs₁, xs₂, xs₃, ?_⟩
        simpa using congrArg (cons x) h_xs

/-! ## Pop-world helpers -/

/-- A popped due event leaves the queue of the popped world. The due
    filter is duplicate-free, so the pop removed its only copy. -/
private theorem not_mem_popWorld_of_due_nodup (w : World)
    (ev₀ : ScheduledEvent) (w_pop : World)
    (h_pop : w.popNextEvent = some (ev₀, w_pop))
    (h_nodup : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup) :
    ev₀ ∉ w_pop.events := by
  obtain ⟨idx, h_idx, h_erase, h_tick_ev, _, h_get⟩ :=
    World.popNextEvent_eraseIdx w ev₀ w_pop h_pop
  rw [h_erase]
  intro h_mem
  obtain ⟨l₁, l₂, l₃, h_split⟩ :=
    two_split_of_mem_eraseIdx w.events idx h_idx ev₀ h_get h_mem
  set p := (fun e : ScheduledEvent => e.targetTick == w.tick)
  have h_p : p ev₀ = true := by dsimp [p]; rw [h_tick_ev]; simp
  have h_filter : w.events.filter p =
      l₁.filter p ++ ev₀ :: (l₂.filter p ++ ev₀ :: l₃.filter p) := by
    rw [h_split, List.filter_append, List.filter_append,
      filter_cons_true p ev₀ l₂ h_p, filter_cons_true p ev₀ l₃ h_p,
      ← List.cons_append, List.append_assoc]
  exact nodup_cons_append_not_mem (h_filter ▸ h_nodup)
    (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))

/-- One pop removes the popped event from the due filter. -/
private theorem due_tail_eq_eraseIdx (w : World) (ev₀ : ScheduledEvent)
    (w_pop : World) (h_pop : w.popNextEvent = some (ev₀, w_pop)) :
    ∃ j, j < (w.events.filter (fun e => e.targetTick == w.tick)).length ∧
      (w_pop.onScheduledTick ev₀.nodeId).events.filter
          (fun e => e.targetTick == w.tick) =
        (w.events.filter (fun e => e.targetTick == w.tick)).eraseIdx j := by
  obtain ⟨idx, h_idx, h_erase, h_tick_ev, _, h_get⟩ :=
    World.popNextEvent_eraseIdx w ev₀ w_pop h_pop
  set due := w.events.filter (fun e => e.targetTick == w.tick)
  have h_due_ev₀ : (fun e => e.targetTick == w.tick)
      (w.events[idx]'h_idx) = true := by
    simp [h_get, h_tick_ev]
  obtain ⟨j, hj, h_filter_erase, _⟩ :=
    filter_eraseIdx_getElem (fun e => e.targetTick == w.tick) w.events idx
      h_idx h_due_ev₀
  refine ⟨j, hj, ?_⟩
  obtain ⟨new, h_app_new, h_fut_new⟩ :=
    World.onScheduledTick_appends_future w_pop ev₀.nodeId
  have h_tick_pop : w_pop.tick = w.tick :=
    World.popNextEvent_tick w ev₀ w_pop h_pop
  rw [h_app_new, List.filter_append]
  have h_new_nil : new.filter (fun e => e.targetTick == w.tick) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro e h_e
    have h_gt := h_fut_new e h_e
    rw [h_tick_pop] at h_gt
    simp
    omega
  rw [h_new_nil, List.append_nil, h_erase, h_filter_erase]

/-- The node layout survives one `onScheduledTick`. Only signal levels
    change. -/
private theorem NodeLayoutOk_onScheduledTick (groups : List GroupSpec)
    (w : World) (id : Nat) (h_layout : NodeLayoutOk groups w) :
    NodeLayoutOk groups (w.onScheduledTick id) := by
  suffices h_keep : ∀ nid nd₀, w.getNode nid = some nd₀ →
      ∃ nd, (w.onScheduledTick id).getNode nid = some nd ∧
        nd.kind = nd₀.kind ∧ nd.outputs = nd₀.outputs by
    rcases h_layout with ⟨hO, hM, hL, hOut⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro gi ci h_gi h_ci
      obtain ⟨nd₀, h₀, hk, ho⟩ := hO gi ci h_gi h_ci
      obtain ⟨nd, h₁, hk₁, ho₁⟩ :=
        h_keep (chainBaseId groups gi ci + 1) nd₀ h₀
      exact ⟨nd, h₁, by rw [hk₁, hk], by rw [ho₁, ho]⟩
    · intro gi ci k h_gi h_ci h_k
      obtain ⟨nd₀, h₀, hk, ho⟩ := hM gi ci k h_gi h_ci h_k
      obtain ⟨nd, h₁, hk₁, ho₁⟩ :=
        h_keep (chainBaseId groups gi ci + 2 + k) nd₀ h₀
      exact ⟨nd, h₁, by rw [hk₁, hk], by rw [ho₁, ho]⟩
    · intro gi ci h_gi h_ci
      obtain ⟨nd₀, h₀, hk, ho⟩ := hL gi ci h_gi h_ci
      obtain ⟨nd, h₁, hk₁, ho₁⟩ :=
        h_keep (chainBaseId groups gi ci +
          (chainAt groups gi ci).middleDelays.length + 2) nd₀ h₀
      exact ⟨nd, h₁, by rw [hk₁, hk], by rw [ho₁, ho]⟩
    · intro gi ci h_gi h_ci
      obtain ⟨nd₀, h₀, hk, ho⟩ := hOut gi ci h_gi h_ci
      obtain ⟨nd, h₁, hk₁, ho₁⟩ :=
        h_keep (chainBaseId groups gi ci +
          (chainAt groups gi ci).middleDelays.length + 3) nd₀ h₀
      exact ⟨nd, h₁, by rw [hk₁, hk], by rw [ho₁, ho]⟩
  intro nid nd₀ h₀
  by_cases h_none : w.getNode id = none
  · have h_eq : w.onScheduledTick id = w := by
      dsimp [World.onScheduledTick]
      rw [h_none]
    exact ⟨nd₀, by rwa [h_eq], rfl, rfl⟩
  · obtain ⟨nd_id, h_gid⟩ : ∃ nd, w.getNode id = some nd := by
      match h_gid' : w.getNode id with
      | none => exact absurd h_gid' h_none
      | some nd => exact ⟨nd, rfl⟩
    dsimp [World.onScheduledTick]
    rw [h_gid]
    dsimp
    split
    · -- repeater node
      rw [World.notifyOutputs_getNode]
      by_cases h_eq : nid = id
      · have h_gid₀ : w.getNode id = some nd₀ := by rwa [← h_eq]
        refine ⟨{ nd₀ with
            sigLevel := if w.getInputSignal id > 0 then 15 else 0 },
            ?_, rfl, rfl⟩
        rw [h_eq]
        exact World.updateNode_getNode_eq w id
          (fun nd' => { nd' with
            sigLevel := if w.getInputSignal id > 0 then 15 else 0 })
          nd₀ h_gid₀
      · refine ⟨nd₀, ?_, rfl, rfl⟩
        rw [World.updateNode_getNode_ne w id nid
          (fun nd' => { nd' with
            sigLevel := if w.getInputSignal id > 0 then 15 else 0 })
          (Ne.symm h_eq), h₀]
    · -- observer node
      rw [World.notifyOutputs_getNode]
      by_cases h_eq : nid = id
      · have h_gid₀ : w.getNode id = some nd₀ := by rwa [← h_eq]
        refine ⟨{ nd₀ with sigLevel := 15 }, ?_, rfl, rfl⟩
        rw [h_eq]
        exact World.updateNode_getNode_eq w id
          (fun nd' => { nd' with sigLevel := 15 }) nd₀ h_gid₀
      · refine ⟨nd₀, ?_, rfl, rfl⟩
        rw [World.updateNode_getNode_ne w id nid
          (fun nd' => { nd' with sigLevel := 15 }) (Ne.symm h_eq), h₀]
    · -- other node kinds: the world stays unchanged
      exact ⟨nd₀, h₀, rfl, rfl⟩

/-- The pop sequence is duplicate-free when the due filter is. -/
theorem popSeqFuel_nodup (w : World) (fuel : Nat)
    (h_nodup : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup) :
    (World.popSeqFuel w fuel).Nodup := by
  induction fuel generalizing w h_nodup with
  | zero => dsimp [World.popSeqFuel]; exact List.nodup_nil
  | succ fuel ih =>
    dsimp only [World.popSeqFuel]
    cases h_pop : w.popNextEvent with
    | none => simp
    | some p =>
      rcases p with ⟨ev₀, w_pop⟩
      obtain ⟨_, _, _, h_tick_ev, _, _⟩ :=
        World.popNextEvent_eraseIdx w ev₀ w_pop h_pop
      set w' := w_pop.onScheduledTick ev₀.nodeId
      rw [List.nodup_cons]
      refine ⟨?_, ih w' ?_⟩
      · intro h_mem
        have h_w' : ev₀ ∈ w'.events :=
          World.mem_popSeqFuel_mem_events w' fuel ev₀ h_mem
        obtain ⟨new₀, h_app₀, h_fut₀⟩ :=
          World.onScheduledTick_appends_future w_pop ev₀.nodeId
        rw [h_app₀, List.mem_append] at h_w'
        rcases h_w' with h_w' | h_new
        · exact not_mem_popWorld_of_due_nodup w ev₀ w_pop h_pop h_nodup h_w'
        · have h_gt := h_fut₀ ev₀ h_new
          rw [World.popNextEvent_tick w ev₀ w_pop h_pop, h_tick_ev] at h_gt
          exact Nat.lt_irrefl _ h_gt
      · have h_tick_w' : w'.tick = w.tick := by
          change (w_pop.onScheduledTick ev₀.nodeId).tick = w.tick
          rw [World.onScheduledTick_tick,
            World.popNextEvent_tick w ev₀ w_pop h_pop]
        obtain ⟨j, hj, h_eq⟩ := due_tail_eq_eraseIdx w ev₀ w_pop h_pop
        rw [h_tick_w', h_eq]
        exact nodup_eraseIdx _ j h_nodup

/-- Processing one full due-filter's worth of events empties the due
    filter. -/
theorem drain_due_filter (w : World) :
    (processNEvents w
        ((w.events.filter (fun e => e.targetTick == w.tick)).length)).events.filter
      (fun e => e.targetTick == w.tick) = [] := by
  have h_gen : ∀ (w : World) (n : Nat),
      (w.events.filter (fun e => e.targetTick == w.tick)).length ≤ n →
      (processNEvents w n).events.filter
        (fun e => e.targetTick == w.tick) = [] := by
    intro w n
    induction n generalizing w with
    | zero =>
      intro h_len
      dsimp only [processNEvents]
      apply list_nil_of_length_zero
      omega
    | succ n ih =>
      intro h_len
      dsimp only [processNEvents]
      cases h_step : w.step with
      | none =>
        dsimp
        dsimp [World.step] at h_step
        cases h_pop : w.popNextEvent with
        | none =>
          apply filter_empty_of_none
          intro e h_e
          by_cases h_be : e.targetTick = w.tick
          · exact (popNextEvent_none_no_events w h_pop e h_e h_be).elim
          · exact nat_beq_false_of_ne e.targetTick w.tick h_be
        | some p => simp [h_pop] at h_step
      | some w' =>
        dsimp [World.step] at h_step
        cases h_pop : w.popNextEvent with
        | none => simp [h_pop] at h_step
        | some p =>
          rcases p with ⟨ev₀, w_pop⟩
          simp only [h_pop] at h_step
          injection h_step with h_w'
          have h_len' :
              (w'.events.filter
                (fun e => e.targetTick == w'.tick)).length ≤ n := by
            rw [← h_w']
            have h_tick :
                (w_pop.onScheduledTick ev₀.nodeId).tick = w.tick := by
              rw [World.onScheduledTick_tick,
                World.popNextEvent_tick w ev₀ w_pop h_pop]
            obtain ⟨j, hj, h_eq⟩ := due_tail_eq_eraseIdx w ev₀ w_pop h_pop
            rw [h_tick, h_eq, length_eraseIdx_of_lt _ _ hj]
            omega
          have h_tick_w' : w'.tick = w.tick := by
            rw [← h_w', World.onScheduledTick_tick,
              World.popNextEvent_tick w ev₀ w_pop h_pop]
          rw [← h_tick_w']
          exact ih w' h_len'
  exact h_gen w _ (by omega)

/-- Every due event pops within one full drain. -/
private theorem mem_popSeqFuel_of_due (w : World) (ev : ScheduledEvent)
    (h_ev : ev ∈ w.events) (h_due : ev.targetTick = w.tick) :
    ev ∈ World.popSeqFuel w
      ((w.events.filter (fun e => e.targetTick == w.tick)).length) := by
  have h_gen : ∀ (m : Nat) (w : World) (ev : ScheduledEvent),
      (w.events.filter (fun e => e.targetTick == w.tick)).length = m →
      ev ∈ w.events → ev.targetTick = w.tick →
      ev ∈ World.popSeqFuel w m := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro w ev h_len h_ev h_due
      cases m with
      | zero =>
        exfalso
        have h_mem :
            ev ∈ w.events.filter (fun e => e.targetTick == w.tick) := by
          rw [List.mem_filter]
          exact ⟨h_ev, by rw [h_due]; simp⟩
        have h_nil := list_nil_of_length_zero _ h_len
        rw [h_nil] at h_mem
        cases h_mem
      | succ m =>
        cases h_pop : w.popNextEvent with
        | none =>
          exact False.elim (popNextEvent_none_no_events w h_pop ev h_ev h_due)
        | some p =>
          rcases p with ⟨ev₀, w_pop⟩
          simp only [World.popSeqFuel, h_pop]
          rw [List.mem_cons]
          by_cases h_eq : ev = ev₀
          · exact Or.inl h_eq
          · obtain ⟨idx, h_idx, h_erase, _, _, h_get⟩ :=
              World.popNextEvent_eraseIdx w ev₀ w_pop h_pop
            have h_ev_pop : ev ∈ w_pop.events := by
              rw [h_erase]
              exact mem_eraseIdx_of_ne w.events idx h_idx ev₀ ev h_get h_ev
                h_eq
            set w' := w_pop.onScheduledTick ev₀.nodeId
            obtain ⟨new₀, h_app₀, _⟩ :=
              World.onScheduledTick_appends_future w_pop ev₀.nodeId
            have h_ev_w' : ev ∈ w'.events := by
              rw [h_app₀]
              exact List.mem_append_left _ h_ev_pop
            have h_tick_w' : w'.tick = w.tick := by
              change (w_pop.onScheduledTick ev₀.nodeId).tick = w.tick
              rw [World.onScheduledTick_tick,
                World.popNextEvent_tick w ev₀ w_pop h_pop]
            have h_len' : (w'.events.filter
                (fun e => e.targetTick == w'.tick)).length = m := by
              obtain ⟨j, hj, h_eq_tail⟩ := due_tail_eq_eraseIdx w ev₀ w_pop h_pop
              rw [h_tick_w', h_eq_tail, length_eraseIdx_of_lt _ _ hj]
              omega
            exact Or.inr
              (ih m (by omega) w' ev h_len' h_ev_w' (by
                rwa [h_tick_w']))
  exact h_gen _ w ev rfl h_ev h_due

/-- Firing the last-stage event of a chain appends no event. The output
    node only logs. -/
theorem lastStage_spawn_nil (groups : List GroupSpec)
    (actTick : Nat → Nat) (v : World) (gi ci : Nat)
    (h_gi : gi < groups.length) (h_ci : ci < (groupAt groups gi).length)
    (h_layout : NodeLayoutOk groups v) :
    (v.onScheduledTick
        (stageEvent actTick groups gi ci
          ((chainAt groups gi ci).middleDelays.length + 1)).nodeId).events =
      v.events := by
  dsimp [stageEvent]
  set base := chainBaseId groups gi ci
  set m := (chainAt groups gi ci).middleDelays.length
  obtain ⟨ndL, h_gnL, h_kindL, h_outsL⟩ := h_layout.2.2.1 gi ci h_gi h_ci
  obtain ⟨ndO, h_gnO, h_kindO, _⟩ := h_layout.2.2.2 gi ci h_gi h_ci
  have h_nid : base + 1 + (m + 1) = base + m + 2 := by omega
  rw [h_nid]
  dsimp only [World.onScheduledTick]
  rw [h_gnL]
  dsimp
  rw [h_kindL]
  dsimp
  dsimp only [World.notifyOutputs]
  rw [World.updateNode_getNode_eq v (base + m + 2)
    (fun nd' => { nd' with
      sigLevel := if v.getInputSignal (base + m + 2) > 0 then 15 else 0 })
    ndL h_gnL]
  dsimp
  rw [h_outsL]
  dsimp only [List.foldl]
  rw [World.onNeighborUpdate]
  rw [World.updateNode_getNode_ne v (base + m + 2)
    (chainBaseId groups gi ci + (chainAt groups gi ci).middleDelays.length +
      3)
    (fun nd' => { nd' with
      sigLevel := if v.getInputSignal (base + m + 2) > 0 then 15 else 0 })
    (by dsimp [base, m]; omega), h_gnO]
  dsimp
  rw [h_kindO]
  dsimp

/-! ## Spawn-accumulator membership and order -/

/-- Membership in the spawn accumulator gives a pop that appended the
    event as its single spawn. -/
theorem mem_popSpawnAcc_singleton_spawn (groups : List GroupSpec)
    (w : World) (fuel : Nat) (e : ScheduledEvent)
    (h_layout : NodeLayoutOk groups w)
    (h_single : ∀ ev ∈ World.popSeqFuel w fuel, ∀ (v : World),
        v.tick = w.tick → NodeLayoutOk groups v →
        ∃ s, (v.onScheduledTick ev.nodeId).events = v.events ++ [s] ∨
          (v.onScheduledTick ev.nodeId).events = v.events)
    (h_mem : e ∈ World.popSpawnAcc w fuel) :
    ∃ ev ∈ World.popSeqFuel w fuel, ∃ (v : World) (s : ScheduledEvent),
      v.tick = w.tick ∧ NodeLayoutOk groups v ∧
      (v.onScheduledTick ev.nodeId).events = v.events ++ [s] ∧ e = s := by
  induction fuel generalizing w h_layout with
  | zero =>
    dsimp [World.popSpawnAcc] at h_mem
    cases h_mem
  | succ fuel ih =>
    dsimp only [World.popSpawnAcc] at h_mem
    cases h_pop : w.popNextEvent with
    | none =>
      simp only [h_pop] at h_mem
      cases h_mem
    | some p =>
      rcases p with ⟨ev₀, w_pop⟩
      simp only [h_pop] at h_mem
      set w' := w_pop.onScheduledTick ev₀.nodeId
      have h_seq_cons : World.popSeqFuel w (fuel + 1) =
          ev₀ :: World.popSeqFuel w' fuel := by
        dsimp only [World.popSeqFuel]
        rw [h_pop]
      obtain ⟨new₀, h_app₀, _⟩ :=
        World.onScheduledTick_appends_future w_pop ev₀.nodeId
      have h_drop : w'.events.drop w_pop.events.length = new₀ := by
        rw [h_app₀, drop_append_self]
      rw [h_drop, List.mem_append] at h_mem
      have h_tick_pop : w_pop.tick = w.tick :=
        World.popNextEvent_tick w ev₀ w_pop h_pop
      have h_layout_pop : NodeLayoutOk groups w_pop :=
        NodeLayoutOk_of_nodes_eq groups w w_pop
          (World.popNextEvent_nodes w ev₀ w_pop h_pop) h_layout
      have h_ev₀_seq : ev₀ ∈ World.popSeqFuel w (fuel + 1) := by
        rw [h_seq_cons]
        exact List.mem_cons.mpr (Or.inl rfl)
      rcases h_mem with h_new | h_acc
      · obtain ⟨s₀, h_sp | h_nil⟩ :=
          h_single ev₀ h_ev₀_seq w_pop h_tick_pop h_layout_pop
        · refine ⟨ev₀, h_ev₀_seq, w_pop, s₀, h_tick_pop, h_layout_pop, h_sp,
            ?_⟩
          have h_new₀ : new₀ = [s₀] := by
            exact append_left_cancel' w_pop.events new₀ [s₀] (h_app₀.symm.trans h_sp)
          rw [h_new₀] at h_new
          simpa using h_new
        · have h_new₀ : new₀ = [] := by
            exact append_left_cancel' w_pop.events new₀ []
              ((h_app₀.symm.trans h_nil).trans
                (List.append_nil _).symm)
          rw [h_new₀] at h_new
          cases h_new
      · by_cases h_new_mem : e ∈ new₀
        · obtain ⟨s₀, h_sp | h_nil⟩ :=
            h_single ev₀ h_ev₀_seq w_pop h_tick_pop h_layout_pop
          · refine ⟨ev₀, h_ev₀_seq, w_pop, s₀, h_tick_pop, h_layout_pop,
              h_sp, ?_⟩
            have h_new₀ : new₀ = [s₀] := by
              exact append_left_cancel' w_pop.events new₀ [s₀] (h_app₀.symm.trans h_sp)
            rw [h_new₀] at h_new_mem
            simpa using h_new_mem
          · have h_new₀ : new₀ = [] := by
              exact append_left_cancel' w_pop.events new₀ []
                ((h_app₀.symm.trans h_nil).trans
                  (List.append_nil _).symm)
            rw [h_new₀] at h_new_mem
            cases h_new_mem
        · have h_layout_w' : NodeLayoutOk groups w' :=
            NodeLayoutOk_onScheduledTick groups w_pop ev₀.nodeId h_layout_pop
          obtain ⟨ev, h_ev, v, s, h_v, h_lay, h_sp, h_s⟩ :=
            ih w' h_layout_w'
              (fun ev₁ h_ev₁ v₁ h_v₁ h_lay₁ =>
                h_single ev₁ (by rw [h_seq_cons]; exact
                  List.mem_cons.mpr (Or.inr h_ev₁)) v₁
                  (by rw [h_v₁, World.onScheduledTick_tick, h_tick_pop])
                  h_lay₁)
              h_acc
          refine ⟨ev, by rw [h_seq_cons]; exact
            List.mem_cons.mpr (Or.inr h_ev), v, s, ?_, h_lay, h_sp, h_s⟩
          rw [h_v, World.onScheduledTick_tick, h_tick_pop]

/-- A fresh event in the spawn accumulator is the single spawn of one pop,
    and it is absent from that pop's world. Distinct pops spawn distinct
    events. -/
theorem mem_popSpawnAcc_singleton_spawn_fresh
    (groups : List GroupSpec) (w : World) (fuel : Nat) (e : ScheduledEvent)
    (h_layout : NodeLayoutOk groups w)
    (h_e_absent : e ∉ w.events)
    (h_single : ∀ ev ∈ World.popSeqFuel w fuel, ∀ (v : World),
        v.tick = w.tick → NodeLayoutOk groups v →
        ∃ s, (v.onScheduledTick ev.nodeId).events = v.events ++ [s] ∨
          (v.onScheduledTick ev.nodeId).events = v.events)
    (h_distinct : ∀ ev₁ ∈ World.popSeqFuel w fuel,
        ∀ ev₂ ∈ World.popSeqFuel w fuel, ev₁ ≠ ev₂ →
        ∀ (v₁ v₂ : World), v₁.tick = w.tick → v₂.tick = w.tick →
        NodeLayoutOk groups v₁ → NodeLayoutOk groups v₂ →
        ∀ s₁ s₂, (v₁.onScheduledTick ev₁.nodeId).events = v₁.events ++ [s₁] →
        (v₂.onScheduledTick ev₂.nodeId).events = v₂.events ++ [s₂] →
        s₁ ≠ s₂)
    (h_mem : e ∈ World.popSpawnAcc w fuel) :
    ∃ ev ∈ World.popSeqFuel w fuel, ∃ (v : World) (s : ScheduledEvent),
      v.tick = w.tick ∧ NodeLayoutOk groups v ∧
      (v.onScheduledTick ev.nodeId).events = v.events ++ [s] ∧ e = s ∧
      e ∉ v.events := by
  induction fuel generalizing w h_layout h_e_absent with
  | zero =>
    dsimp [World.popSpawnAcc] at h_mem
    cases h_mem
  | succ fuel ih =>
    dsimp only [World.popSpawnAcc] at h_mem
    cases h_pop : w.popNextEvent with
    | none =>
      simp only [h_pop] at h_mem
      cases h_mem
    | some p =>
      rcases p with ⟨ev₀, w_pop⟩
      simp only [h_pop] at h_mem
      set w' := w_pop.onScheduledTick ev₀.nodeId
      have h_seq_cons : World.popSeqFuel w (fuel + 1) =
          ev₀ :: World.popSeqFuel w' fuel := by
        dsimp only [World.popSeqFuel]
        rw [h_pop]
      obtain ⟨idx, h_idx, h_erase, _, _, _⟩ :=
        World.popNextEvent_eraseIdx w ev₀ w_pop h_pop
      obtain ⟨new₀, h_app₀, _⟩ :=
        World.onScheduledTick_appends_future w_pop ev₀.nodeId
      have h_drop : w'.events.drop w_pop.events.length = new₀ := by
        rw [h_app₀, drop_append_self]
      rw [h_drop, List.mem_append] at h_mem
      have h_tick_pop : w_pop.tick = w.tick :=
        World.popNextEvent_tick w ev₀ w_pop h_pop
      have h_layout_pop : NodeLayoutOk groups w_pop :=
        NodeLayoutOk_of_nodes_eq groups w w_pop
          (World.popNextEvent_nodes w ev₀ w_pop h_pop) h_layout
      have h_ev₀_seq : ev₀ ∈ World.popSeqFuel w (fuel + 1) := by
        rw [h_seq_cons]
        exact List.mem_cons.mpr (Or.inl rfl)
      rcases h_mem with h_new | h_acc
      · obtain ⟨s₀, h_sp | h_nil⟩ :=
          h_single ev₀ h_ev₀_seq w_pop h_tick_pop h_layout_pop
        · refine ⟨ev₀, h_ev₀_seq, w_pop, s₀, h_tick_pop, h_layout_pop, h_sp,
            ?_, ?_⟩
          · have h_new₀ : new₀ = [s₀] := by
              exact append_left_cancel' w_pop.events new₀ [s₀] (h_app₀.symm.trans h_sp)
            rw [h_new₀] at h_new
            simpa using h_new
          · intro h_contra
            rw [h_erase] at h_contra
            exact h_e_absent (List.eraseIdx_subset' w.events idx h_contra)
        · have h_new₀ : new₀ = [] := by
            exact append_left_cancel' w_pop.events new₀ []
              ((h_app₀.symm.trans h_nil).trans
                (List.append_nil _).symm)
          rw [h_new₀] at h_new
          cases h_new
      · by_cases h_new_mem : e ∈ new₀
        · obtain ⟨s₀, h_sp | h_nil⟩ :=
            h_single ev₀ h_ev₀_seq w_pop h_tick_pop h_layout_pop
          · refine ⟨ev₀, h_ev₀_seq, w_pop, s₀, h_tick_pop, h_layout_pop,
              h_sp, ?_, ?_⟩
            · have h_new₀ : new₀ = [s₀] := by
                exact append_left_cancel' w_pop.events new₀ [s₀] (h_app₀.symm.trans h_sp)
              rw [h_new₀] at h_new_mem
              simpa using h_new_mem
            · intro h_contra
              rw [h_erase] at h_contra
              exact h_e_absent (List.eraseIdx_subset' w.events idx h_contra)
          · have h_new₀ : new₀ = [] := by
              exact append_left_cancel' w_pop.events new₀ []
                ((h_app₀.symm.trans h_nil).trans
                  (List.append_nil _).symm)
            rw [h_new₀] at h_new_mem
            cases h_new_mem
        · have h_layout_w' : NodeLayoutOk groups w' :=
            NodeLayoutOk_onScheduledTick groups w_pop ev₀.nodeId h_layout_pop
          have h_e_absent_w' : e ∉ w'.events := by
            rw [h_app₀, List.mem_append]
            intro h_mem'
            rcases h_mem' with h_mem' | h_mem'
            · rw [h_erase] at h_mem'
              exact h_e_absent (List.eraseIdx_subset' w.events idx h_mem')
            · exact h_new_mem h_mem'
          obtain ⟨ev, h_ev, v, s, h_v, h_lay, h_sp, h_s, h_fresh⟩ :=
            ih w' h_layout_w' h_e_absent_w'
              (fun ev₁ h_ev₁ v₁ h_v₁ h_lay₁ =>
                h_single ev₁ (by rw [h_seq_cons]; exact
                  List.mem_cons.mpr (Or.inr h_ev₁)) v₁
                  (by rw [h_v₁, World.onScheduledTick_tick, h_tick_pop])
                  h_lay₁)
              (fun ev₁ h₁ ev₂ h₂ h_ne v₁ v₂ h_v₁ h_v₂ h_l₁ h_l₂ s₁ s₂
                  h_sp₁ h_sp₂ =>
                h_distinct ev₁ (by rw [h_seq_cons]; exact
                    List.mem_cons.mpr (Or.inr h₁)) ev₂
                  (by rw [h_seq_cons]; exact
                    List.mem_cons.mpr (Or.inr h₂)) h_ne v₁ v₂
                  (by rw [h_v₁, World.onScheduledTick_tick, h_tick_pop])
                  (by rw [h_v₂, World.onScheduledTick_tick, h_tick_pop])
                  h_l₁ h_l₂ s₁ s₂ h_sp₁ h_sp₂)
              h_acc
          refine ⟨ev, by rw [h_seq_cons]; exact
            List.mem_cons.mpr (Or.inr h_ev), v, s, ?_, h_lay, h_sp, h_s,
            h_fresh⟩
          rw [h_v, World.onScheduledTick_tick, h_tick_pop]

/-- The spawn accumulator is duplicate-free when distinct pops spawn
    distinct events. -/
theorem popSpawnAcc_nodup (groups : List GroupSpec) (w : World)
    (fuel : Nat)
    (h_layout : NodeLayoutOk groups w)
    (h_nodup : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup)
    (h_single : ∀ ev ∈ World.popSeqFuel w fuel, ∀ (v : World),
        v.tick = w.tick → NodeLayoutOk groups v →
        ∃ s, (v.onScheduledTick ev.nodeId).events = v.events ++ [s] ∨
          (v.onScheduledTick ev.nodeId).events = v.events)
    (h_distinct : ∀ ev₁ ∈ World.popSeqFuel w fuel,
        ∀ ev₂ ∈ World.popSeqFuel w fuel, ev₁ ≠ ev₂ →
        ∀ (v₁ v₂ : World), v₁.tick = w.tick → v₂.tick = w.tick →
        NodeLayoutOk groups v₁ → NodeLayoutOk groups v₂ →
        ∀ s₁ s₂, (v₁.onScheduledTick ev₁.nodeId).events = v₁.events ++ [s₁] →
        (v₂.onScheduledTick ev₂.nodeId).events = v₂.events ++ [s₂] →
        s₁ ≠ s₂) :
    (World.popSpawnAcc w fuel).Nodup := by
  induction fuel generalizing w h_layout h_nodup with
  | zero => dsimp [World.popSpawnAcc]; exact List.nodup_nil
  | succ fuel ih =>
    dsimp only [World.popSpawnAcc]
    cases h_pop : w.popNextEvent with
    | none => exact List.nodup_nil
    | some p =>
      rcases p with ⟨ev₀, w_pop⟩
      dsimp
      set w' := w_pop.onScheduledTick ev₀.nodeId
      have h_seq_cons : World.popSeqFuel w (fuel + 1) =
          ev₀ :: World.popSeqFuel w' fuel := by
        dsimp only [World.popSeqFuel]
        rw [h_pop]
      obtain ⟨new₀, h_app₀, _⟩ :=
        World.onScheduledTick_appends_future w_pop ev₀.nodeId
      have h_drop : w'.events.drop w_pop.events.length = new₀ := by
        rw [h_app₀, drop_append_self]
      rw [h_drop]
      have h_tick_pop : w_pop.tick = w.tick :=
        World.popNextEvent_tick w ev₀ w_pop h_pop
      have h_tick_w' : w'.tick = w.tick := by
        change (w_pop.onScheduledTick ev₀.nodeId).tick = w.tick
        rw [World.onScheduledTick_tick, h_tick_pop]
      have h_layout_pop : NodeLayoutOk groups w_pop :=
        NodeLayoutOk_of_nodes_eq groups w w_pop
          (World.popNextEvent_nodes w ev₀ w_pop h_pop) h_layout
      have h_layout_w' : NodeLayoutOk groups w' :=
        NodeLayoutOk_onScheduledTick groups w_pop ev₀.nodeId h_layout_pop
      have h_single_w' : ∀ ev ∈ World.popSeqFuel w' fuel,
          ∀ (v : World), v.tick = w'.tick → NodeLayoutOk groups v →
          ∃ s, (v.onScheduledTick ev.nodeId).events = v.events ++ [s] ∨
            (v.onScheduledTick ev.nodeId).events = v.events :=
        fun ev h_ev v h_v h_lay =>
          h_single ev (by rw [h_seq_cons]; exact
            List.mem_cons.mpr (Or.inr h_ev)) v
            (by rw [h_v, h_tick_w']) h_lay
      have h_distinct_w' : ∀ ev₁ ∈ World.popSeqFuel w' fuel,
          ∀ ev₂ ∈ World.popSeqFuel w' fuel, ev₁ ≠ ev₂ →
          ∀ (v₁ v₂ : World), v₁.tick = w'.tick → v₂.tick = w'.tick →
          NodeLayoutOk groups v₁ → NodeLayoutOk groups v₂ →
          ∀ s₁ s₂,
          (v₁.onScheduledTick ev₁.nodeId).events = v₁.events ++ [s₁] →
          (v₂.onScheduledTick ev₂.nodeId).events = v₂.events ++ [s₂] →
          s₁ ≠ s₂ :=
        fun ev₁ h₁ ev₂ h₂ h_ne v₁ v₂ h_v₁ h_v₂ h_l₁ h_l₂ s₁ s₂ h_sp₁ h_sp₂ =>
          h_distinct ev₁ (by rw [h_seq_cons]; exact
              List.mem_cons.mpr (Or.inr h₁)) ev₂
            (by rw [h_seq_cons]; exact List.mem_cons.mpr (Or.inr h₂)) h_ne
            v₁ v₂ (by rw [h_v₁, h_tick_w']) (by rw [h_v₂, h_tick_w'])
            h_l₁ h_l₂ s₁ s₂ h_sp₁ h_sp₂
      have h_nodup_w' :
          (w'.events.filter (fun e => e.targetTick == w'.tick)).Nodup := by
        obtain ⟨j, hj, h_eq⟩ := due_tail_eq_eraseIdx w ev₀ w_pop h_pop
        rw [h_tick_w', h_eq]
        exact nodup_eraseIdx _ j h_nodup
      obtain ⟨s₀, h_sp₀ | h_nil₀⟩ :=
        h_single ev₀ (by rw [h_seq_cons]; exact
          List.mem_cons.mpr (Or.inl rfl)) w_pop h_tick_pop h_layout_pop
      · have h_new₀ : new₀ = [s₀] := by
          exact append_left_cancel' w_pop.events new₀ [s₀] (h_app₀.symm.trans h_sp₀)
        rw [h_new₀]
        dsimp
        rw [List.nodup_cons]
        refine ⟨?_, ih w' h_layout_w' h_nodup_w' h_single_w' h_distinct_w'⟩
        · intro h_mem
          obtain ⟨ev₁, h_ev₁, v₁, s₁, h_v₁, h_l₁, h_sp₁, h_s₁⟩ :=
            mem_popSpawnAcc_singleton_spawn groups w' fuel s₀ h_layout_w'
              h_single_w' h_mem
          have h_ne : ev₀ ≠ ev₁ := by
            intro h_eq
            have h_nd_seq : (World.popSeqFuel w (fuel + 1)).Nodup :=
              popSeqFuel_nodup w (fuel + 1) h_nodup
            rw [h_seq_cons, h_eq] at h_nd_seq
            exact nodup_cons_append_not_mem (l₁ := []) h_nd_seq h_ev₁
          have h_contra := h_distinct ev₀
            (by rw [h_seq_cons]; exact List.mem_cons.mpr (Or.inl rfl))
            ev₁
            (by rw [h_seq_cons]; exact List.mem_cons.mpr (Or.inr h_ev₁))
            h_ne w_pop v₁ h_tick_pop
            (by rw [h_v₁, h_tick_w']) h_layout_pop h_l₁ s₀ s₁ h_sp₀
            h_sp₁
          exact h_contra (by rw [h_s₁])
      · have h_new₀ : new₀ = [] := by
          exact append_left_cancel' w_pop.events new₀ []
            ((h_app₀.symm.trans h_nil₀).trans
              (List.append_nil _).symm)
        rw [h_new₀]
        simp only [List.nil_append]
        exact ih w' h_layout_w' h_nodup_w' h_single_w' h_distinct_w'

/-- Popped events appear in nondecreasing priority order. -/
theorem popSeqFuel_priority_mono (w : World) (fuel : Nat)
    (X Y : ScheduledEvent)
    (h_b : evBefore (World.popSeqFuel w fuel) X Y) :
    X.priority ≤ Y.priority := by
  induction fuel generalizing w with
  | zero =>
    dsimp [World.popSeqFuel] at h_b
    exact (evBefore.not_nil h_b).elim
  | succ fuel ih =>
    dsimp only [World.popSeqFuel] at h_b
    cases h_pop : w.popNextEvent with
    | none =>
      simp only [h_pop] at h_b
      exact (evBefore.not_nil h_b).elim
    | some p =>
      rcases p with ⟨ev₀, w_pop⟩
      simp only [h_pop] at h_b
      rw [evBefore.cons_iff] at h_b
      rcases h_b with ⟨h_X₀, h_Y_tail⟩ | h_tail
      · subst h_X₀
        obtain ⟨_, h_min, _⟩ :=
          popNextEvent_first_min_priority w ev₀ w_pop h_pop
        have h_Y_due : Y.targetTick = w.tick := by
          have h_tick := World.mem_popSeqFuel_due
            (w_pop.onScheduledTick ev₀.nodeId) fuel Y h_Y_tail
          rw [World.onScheduledTick_tick,
            World.popNextEvent_tick w ev₀ w_pop h_pop] at h_tick
          exact h_tick
        obtain ⟨new₀, h_app₀, h_fut₀⟩ :=
          World.onScheduledTick_appends_future w_pop ev₀.nodeId
        have h_Y_w : Y ∈ (w_pop.onScheduledTick ev₀.nodeId).events :=
          World.mem_popSeqFuel_mem_events (w_pop.onScheduledTick ev₀.nodeId)
            fuel Y h_Y_tail
        have h_Y_pop : Y ∈ w_pop.events := by
          rw [h_app₀, List.mem_append] at h_Y_w
          rcases h_Y_w with h | h
          · exact h
          · have h_gt := h_fut₀ Y h
            rw [World.popNextEvent_tick w ev₀ w_pop h_pop, h_Y_due] at h_gt
            exact (Nat.lt_irrefl _ h_gt).elim
        obtain ⟨idx, h_idx, h_erase, _, _, _⟩ :=
          World.popNextEvent_eraseIdx w ev₀ w_pop h_pop
        have h_Y_wev : Y ∈ w.events :=
          List.eraseIdx_subset' w.events idx (by rwa [← h_erase])
        exact h_min Y (by
          rw [List.mem_filter]
          exact ⟨h_Y_wev, by rw [h_Y_due]; simp⟩)
      · exact ih (w_pop.onScheduledTick ev₀.nodeId) h_tail

/-- Same-priority pop order comes from the due-filter order. -/
theorem due_evBefore_of_popSeq_evBefore (w : World) (fuel : Nat)
    (X Y : ScheduledEvent)
    (hX_pop : X ∈ World.popSeqFuel w fuel)
    (hY_pop : Y ∈ World.popSeqFuel w fuel)
    (hX_due : X.targetTick = w.tick) (hY_due : Y.targetTick = w.tick)
    (h_pri : X.priority = Y.priority)
    (h_nodup : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup)
    (h_b : evBefore (World.popSeqFuel w fuel) X Y) :
    evBefore (w.events.filter (fun e => e.targetTick == w.tick)) X Y := by
  by_cases h_fwd :
      evBefore (w.events.filter (fun e => e.targetTick == w.tick)) X Y
  · exact h_fwd
  · have h_XY_ne : X ≠ Y := by
      intro h_eq
      rw [h_eq] at h_b
      obtain ⟨l₁, l₂, l₃, h_split⟩ := evBefore_self_two_split h_b
      exact nodup_cons_append_not_mem
        (h_split ▸ popSeqFuel_nodup w fuel h_nodup)
        (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
    have h_total := evBefore.total_of_nodup h_nodup
      (by
        rw [List.mem_filter]
        exact ⟨World.mem_popSeqFuel_mem_events w fuel X hX_pop,
          by rw [hX_due]; simp⟩)
      (by
        rw [List.mem_filter]
        exact ⟨World.mem_popSeqFuel_mem_events w fuel Y hY_pop,
          by rw [hY_due]; simp⟩)
      h_XY_ne
    rcases h_total with h_same | h_rev
    · exact absurd h_same h_fwd
    · have h_rev_seq : evBefore (World.popSeqFuel w fuel) Y X :=
        World.popSeqFuel_same_priority_order w fuel Y X
          (World.mem_popSeqFuel_mem_events w fuel Y hY_pop)
          (World.mem_popSeqFuel_mem_events w fuel X hX_pop)
          hY_due hX_due h_pri.symm h_nodup h_rev hY_pop hX_pop
      exact (evBefore.asymm (popSeqFuel_nodup w fuel h_nodup) h_b
        h_rev_seq).elim

/-- An event that sits before the spawn of `D` in the accumulator is the
    spawn of a pop that happens before `D`. -/
theorem popSpawnAcc_right_converse (groups : List GroupSpec)
    (w : World) (fuel : Nat) (D sD e : ScheduledEvent)
    (h_layout : NodeLayoutOk groups w)
    (h_nodup : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup)
    (hD_pop : D ∈ World.popSeqFuel w fuel)
    (hD_due : D.targetTick = w.tick)
    (h_sD_absent : sD ∉ w.events)
    (h_sD_gt : sD.targetTick > w.tick)
    (h_spawnD : ∀ (v : World), v.tick = w.tick → NodeLayoutOk groups v →
        (v.onScheduledTick D.nodeId).events = v.events ++ [sD])
    (h_single : ∀ ev ∈ World.popSeqFuel w fuel, ∀ (v : World),
        v.tick = w.tick → NodeLayoutOk groups v →
        ∃ s, (v.onScheduledTick ev.nodeId).events = v.events ++ [s] ∨
          (v.onScheduledTick ev.nodeId).events = v.events)
    (h_uniqueD : ∀ ev ∈ World.popSeqFuel w fuel, ∀ (v : World),
        v.tick = w.tick → NodeLayoutOk groups v → ∀ s,
        (v.onScheduledTick ev.nodeId).events = v.events ++ [s] →
        s = sD → ev = D)
    (h_e_absent : e ∉ w.events) (h_e_ne : e ≠ sD)
    (h_b : evBefore (World.popSpawnAcc w fuel) e sD) :
    ∃ e' ∈ World.popSeqFuel w fuel,
      evBefore (World.popSeqFuel w fuel) e' D ∧
      ∃ (v : World), v.tick = w.tick ∧ NodeLayoutOk groups v ∧
        e ∈ (v.onScheduledTick e'.nodeId).events ∧ e ∉ v.events := by
  induction fuel generalizing w h_layout h_nodup with
  | zero =>
    dsimp [World.popSpawnAcc] at h_b
    exact (evBefore.not_nil h_b).elim
  | succ fuel ih =>
    dsimp only [World.popSpawnAcc] at h_b
    cases h_pop : w.popNextEvent with
    | none =>
      simp only [h_pop] at h_b
      exact (evBefore.not_nil h_b).elim
    | some p =>
      rcases p with ⟨ev₀, w_pop⟩
      simp only [h_pop] at h_b
      set w' := w_pop.onScheduledTick ev₀.nodeId
      have h_seq_cons : World.popSeqFuel w (fuel + 1) =
          ev₀ :: World.popSeqFuel w' fuel := by
        dsimp only [World.popSeqFuel]
        rw [h_pop]
      obtain ⟨idx, h_idx, h_erase, _, _, _⟩ :=
        World.popNextEvent_eraseIdx w ev₀ w_pop h_pop
      obtain ⟨new₀, h_app₀, h_fut₀⟩ :=
        World.onScheduledTick_appends_future w_pop ev₀.nodeId
      have h_drop : w'.events.drop w_pop.events.length = new₀ := by
        rw [h_app₀, drop_append_self]
      have h_tick_pop : w_pop.tick = w.tick :=
        World.popNextEvent_tick w ev₀ w_pop h_pop
      have h_tick_w' : w'.tick = w.tick := by
        change (w_pop.onScheduledTick ev₀.nodeId).tick = w.tick
        rw [World.onScheduledTick_tick, h_tick_pop]
      have h_layout_pop : NodeLayoutOk groups w_pop :=
        NodeLayoutOk_of_nodes_eq groups w w_pop
          (World.popNextEvent_nodes w ev₀ w_pop h_pop) h_layout
      have h_layout_w' : NodeLayoutOk groups w' :=
        NodeLayoutOk_onScheduledTick groups w_pop ev₀.nodeId h_layout_pop
      have h_nodup_w' :
          (w'.events.filter (fun e => e.targetTick == w'.tick)).Nodup := by
        obtain ⟨j, hj, h_eq⟩ := due_tail_eq_eraseIdx w ev₀ w_pop h_pop
        rw [h_tick_w', h_eq]
        exact nodup_eraseIdx _ j h_nodup
      have h_single_w' : ∀ ev ∈ World.popSeqFuel w' fuel,
          ∀ (v : World), v.tick = w'.tick → NodeLayoutOk groups v →
          ∃ s, (v.onScheduledTick ev.nodeId).events = v.events ++ [s] ∨
            (v.onScheduledTick ev.nodeId).events = v.events :=
        fun ev h_ev v h_v h_lay =>
          h_single ev (by rw [h_seq_cons]; exact
            List.mem_cons.mpr (Or.inr h_ev)) v
            (by rw [h_v, h_tick_w']) h_lay
      rw [h_drop] at h_b
      obtain ⟨s₀, h_sp₀ | h_nil₀⟩ :=
        h_single ev₀ (by rw [h_seq_cons]; exact
          List.mem_cons.mpr (Or.inl rfl)) w_pop h_tick_pop h_layout_pop
      · -- the current pop appends exactly s₀
        have h_new₀ : new₀ = [s₀] := by
          exact append_left_cancel' w_pop.events new₀ [s₀] (h_app₀.symm.trans h_sp₀)
        by_cases h_evD : ev₀ = D
        · -- D pops now: nothing sits before its spawn
          have h_new₀_sD : new₀ = [sD] := by
            have h_app₀' := h_app₀
            rw [h_evD] at h_app₀'
            exact append_left_cancel' w_pop.events new₀ [sD]
              (h_app₀'.symm.trans (h_spawnD w_pop h_tick_pop h_layout_pop))
          rw [h_new₀_sD] at h_b
          obtain ⟨pp, qq, h_pq, h_sD_qq⟩ := h_b
          cases pp with
          | nil =>
            dsimp at h_pq
            injection h_pq with h_e_sD _
            exact (h_e_ne h_e_sD.symm).elim
          | cons b pp' =>
            injection h_pq with _ h_rest
            have h_sD_acc' : sD ∈ World.popSpawnAcc w' fuel := by
              dsimp at h_rest
              rw [h_rest]
              exact List.mem_append_right _
                (List.mem_cons.mpr (Or.inr h_sD_qq))
            obtain ⟨ev₁, h_ev₁, v₁, s₁, h_v₁, h_l₁, h_sp₁, h_s₁⟩ :=
              mem_popSpawnAcc_singleton_spawn groups w' fuel sD h_layout_w'
                h_single_w' h_sD_acc'
            have h_ev₁_D : ev₁ = D :=
              h_uniqueD ev₁ (by rw [h_seq_cons]; exact
                  List.mem_cons.mpr (Or.inr h_ev₁)) v₁
                (by rw [h_v₁, h_tick_w']) h_l₁ s₁ h_sp₁ h_s₁.symm
            have h_D_w' : D ∈ w'.events := by
              rw [h_ev₁_D] at h_ev₁
              exact World.mem_popSeqFuel_mem_events w' fuel D h_ev₁
            rw [h_app₀, List.mem_append] at h_D_w'
            rcases h_D_w' with h_D_pop' | h_D_new
            · exact (not_mem_popWorld_of_due_nodup w D w_pop
                (by rw [← h_evD]; exact h_pop) h_nodup h_D_pop').elim
            · have h_gt := h_fut₀ D h_D_new
              rw [h_tick_pop, hD_due] at h_gt
              exact (Nat.lt_irrefl _ h_gt).elim
        · -- some other event pops now
          have h_sD_new₀ : sD ∉ new₀ := by
            rw [h_new₀]
            intro h_mem
            have h_s₀ : s₀ = sD := (List.mem_singleton.mp h_mem).symm
            apply h_evD
            exact h_uniqueD ev₀
              (by rw [h_seq_cons]; exact List.mem_cons.mpr (Or.inl rfl))
              w_pop h_tick_pop h_layout_pop s₀ h_sp₀ h_s₀
          by_cases h_e_new₀ : e ∈ new₀
          · -- e is the spawn of the current pop
            refine ⟨ev₀, by rw [h_seq_cons]; exact
                List.mem_cons.mpr (Or.inl rfl), ?_, w_pop, h_tick_pop,
              h_layout_pop, ?_, ?_⟩
            · rw [h_seq_cons, evBefore.cons_iff]
              exact Or.inl ⟨rfl, by
                rw [h_seq_cons, List.mem_cons] at hD_pop
                rcases hD_pop with h_D₀ | h_D_tail
                · exact absurd h_D₀ (Ne.symm h_evD)
                · exact h_D_tail⟩
            · rw [h_app₀]
              exact List.mem_append.mpr (Or.inr h_e_new₀)
            · intro h_contra
              rw [h_erase] at h_contra
              exact h_e_absent (List.eraseIdx_subset' w.events idx h_contra)
          · -- recurse into the tail accumulator
            have h_b_tail : evBefore (World.popSpawnAcc w' fuel) e sD := by
              rcases evBefore_append_split_right h_b with
                  h_e_new | h_tail
              · exact absurd h_e_new h_e_new₀
              · exact h_tail
            have h_e_absent_w' : e ∉ w'.events := by
              rw [h_app₀, List.mem_append]
              intro h_mem
              rcases h_mem with h_mem | h_mem
              · rw [h_erase] at h_mem
                exact h_e_absent (List.eraseIdx_subset' w.events idx h_mem)
              · exact h_e_new₀ h_mem
            have hD_pop_tail : D ∈ World.popSeqFuel w' fuel := by
              rw [h_seq_cons, List.mem_cons] at hD_pop
              rcases hD_pop with h | h
              · exact absurd h (Ne.symm h_evD)
              · exact h
            have h_sD_absent_w' : sD ∉ w'.events := by
              rw [h_app₀, List.mem_append]
              intro h_mem
              rcases h_mem with h_mem | h_mem
              · rw [h_erase] at h_mem
                exact h_sD_absent (List.eraseIdx_subset' w.events idx h_mem)
              · exact h_sD_new₀ h_mem
            obtain ⟨e', h_e'_tail, h_b_tail', v, h_v, h_lay, h_fire,
                h_fresh⟩ :=
              ih w' h_layout_w' h_nodup_w' hD_pop_tail
                (by rw [h_tick_w']; exact hD_due) h_sD_absent_w'
                (by rw [h_tick_w']; exact h_sD_gt)
                (fun v h_v h_lay => h_spawnD v (by rw [h_v, h_tick_w']) h_lay)
                h_single_w'
                (fun ev h_ev v h_v h_lay s h_sp h_s =>
                  h_uniqueD ev (by rw [h_seq_cons]; exact
                      List.mem_cons.mpr (Or.inr h_ev)) v
                    (by rw [h_v, h_tick_w']) h_lay s h_sp h_s)
                h_e_absent_w' h_b_tail
            refine ⟨e', by rw [h_seq_cons]; exact
                List.mem_cons.mpr (Or.inr h_e'_tail),
              by rw [h_seq_cons]; exact evBefore.cons_extend h_b_tail',
              v, ?_, h_lay, h_fire, h_fresh⟩
            rw [h_v, h_tick_w']
      · -- the current pop appends nothing
        have h_new₀ : new₀ = [] := by
          exact append_left_cancel' w_pop.events new₀ []
            ((h_app₀.symm.trans h_nil₀).trans
              (List.append_nil _).symm)
        have h_evD : ev₀ ≠ D := by
          intro h_eq
          have h_sp := h_spawnD w_pop h_tick_pop h_layout_pop
          rw [← h_eq, h_nil₀] at h_sp
          have h_len := congrArg List.length h_sp
          simp at h_len
        have h_e_absent_w' : e ∉ w'.events := by
          rw [h_app₀, h_new₀, List.append_nil]
          intro h_mem
          rw [h_erase] at h_mem
          exact h_e_absent (List.eraseIdx_subset' w.events idx h_mem)
        have h_sD_absent_w' : sD ∉ w'.events := by
          rw [h_app₀, h_new₀, List.append_nil]
          intro h_mem
          rw [h_erase] at h_mem
          exact h_sD_absent (List.eraseIdx_subset' w.events idx h_mem)
        rw [h_new₀, List.nil_append] at h_b
        have hD_pop_tail : D ∈ World.popSeqFuel w' fuel := by
          rw [h_seq_cons, List.mem_cons] at hD_pop
          rcases hD_pop with h | h
          · exact absurd h (Ne.symm h_evD)
          · exact h
        obtain ⟨e', h_e'_tail, h_b_tail', v, h_v, h_lay, h_fire, h_fresh⟩ :=
          ih w' h_layout_w' h_nodup_w' hD_pop_tail
            (by rw [h_tick_w']; exact hD_due) h_sD_absent_w'
            (by rw [h_tick_w']; exact h_sD_gt)
            (fun v h_v h_lay => h_spawnD v (by rw [h_v, h_tick_w']) h_lay)
            h_single_w'
            (fun ev h_ev v h_v h_lay s h_sp h_s =>
              h_uniqueD ev (by rw [h_seq_cons]; exact
                  List.mem_cons.mpr (Or.inr h_ev)) v
                (by rw [h_v, h_tick_w']) h_lay s h_sp h_s)
            h_e_absent_w' h_b
        refine ⟨e', by rw [h_seq_cons]; exact
            List.mem_cons.mpr (Or.inr h_e'_tail),
          by rw [h_seq_cons]; exact evBefore.cons_extend h_b_tail',
          v, ?_, h_lay, h_fire, h_fresh⟩
        rw [h_v, h_tick_w']

/-- An event that sits after the spawn of `A` in the accumulator is the
    spawn of a pop that happens after `A`. -/
theorem popSpawnAcc_left_converse (groups : List GroupSpec)
    (w : World) (fuel : Nat) (A sA e : ScheduledEvent)
    (h_layout : NodeLayoutOk groups w)
    (h_nodup : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup)
    (hA_pop : A ∈ World.popSeqFuel w fuel)
    (hA_due : A.targetTick = w.tick)
    (h_sA_absent : sA ∉ w.events)
    (h_sA_gt : sA.targetTick > w.tick)
    (h_spawnA : ∀ (v : World), v.tick = w.tick → NodeLayoutOk groups v →
        (v.onScheduledTick A.nodeId).events = v.events ++ [sA])
    (h_single : ∀ ev ∈ World.popSeqFuel w fuel, ∀ (v : World),
        v.tick = w.tick → NodeLayoutOk groups v →
        ∃ s, (v.onScheduledTick ev.nodeId).events = v.events ++ [s] ∨
          (v.onScheduledTick ev.nodeId).events = v.events)
    (h_uniqueA : ∀ ev ∈ World.popSeqFuel w fuel, ∀ (v : World),
        v.tick = w.tick → NodeLayoutOk groups v → ∀ s,
        (v.onScheduledTick ev.nodeId).events = v.events ++ [s] →
        s = sA → ev = A)
    (h_distinct : ∀ ev₁ ∈ World.popSeqFuel w fuel,
        ∀ ev₂ ∈ World.popSeqFuel w fuel, ev₁ ≠ ev₂ →
        ∀ (v₁ v₂ : World), v₁.tick = w.tick → v₂.tick = w.tick →
        NodeLayoutOk groups v₁ → NodeLayoutOk groups v₂ →
        ∀ s₁ s₂, (v₁.onScheduledTick ev₁.nodeId).events = v₁.events ++ [s₁] →
        (v₂.onScheduledTick ev₂.nodeId).events = v₂.events ++ [s₂] →
        s₁ ≠ s₂)
    (h_e_absent : e ∉ w.events) (h_e_ne : e ≠ sA)
    (h_b : evBefore (World.popSpawnAcc w fuel) sA e) :
    ∃ e' ∈ World.popSeqFuel w fuel,
      evBefore (World.popSeqFuel w fuel) A e' ∧
      ∃ (v : World), v.tick = w.tick ∧ NodeLayoutOk groups v ∧
        e ∈ (v.onScheduledTick e'.nodeId).events ∧ e ∉ v.events := by
  induction fuel generalizing w h_layout h_nodup with
  | zero =>
    dsimp [World.popSpawnAcc] at h_b
    exact (evBefore.not_nil h_b).elim
  | succ fuel ih =>
    dsimp only [World.popSpawnAcc] at h_b
    cases h_pop : w.popNextEvent with
    | none =>
      simp only [h_pop] at h_b
      exact (evBefore.not_nil h_b).elim
    | some p =>
      rcases p with ⟨ev₀, w_pop⟩
      simp only [h_pop] at h_b
      set w' := w_pop.onScheduledTick ev₀.nodeId
      have h_seq_cons : World.popSeqFuel w (fuel + 1) =
          ev₀ :: World.popSeqFuel w' fuel := by
        dsimp only [World.popSeqFuel]
        rw [h_pop]
      obtain ⟨idx, h_idx, h_erase, _, _, _⟩ :=
        World.popNextEvent_eraseIdx w ev₀ w_pop h_pop
      obtain ⟨new₀, h_app₀, h_fut₀⟩ :=
        World.onScheduledTick_appends_future w_pop ev₀.nodeId
      have h_drop : w'.events.drop w_pop.events.length = new₀ := by
        rw [h_app₀, drop_append_self]
      have h_tick_pop : w_pop.tick = w.tick :=
        World.popNextEvent_tick w ev₀ w_pop h_pop
      have h_tick_w' : w'.tick = w.tick := by
        change (w_pop.onScheduledTick ev₀.nodeId).tick = w.tick
        rw [World.onScheduledTick_tick, h_tick_pop]
      have h_layout_pop : NodeLayoutOk groups w_pop :=
        NodeLayoutOk_of_nodes_eq groups w w_pop
          (World.popNextEvent_nodes w ev₀ w_pop h_pop) h_layout
      have h_layout_w' : NodeLayoutOk groups w' :=
        NodeLayoutOk_onScheduledTick groups w_pop ev₀.nodeId h_layout_pop
      have h_nodup_w' :
          (w'.events.filter (fun e => e.targetTick == w'.tick)).Nodup := by
        obtain ⟨j, hj, h_eq⟩ := due_tail_eq_eraseIdx w ev₀ w_pop h_pop
        rw [h_tick_w', h_eq]
        exact nodup_eraseIdx _ j h_nodup
      have h_single_w' : ∀ ev ∈ World.popSeqFuel w' fuel,
          ∀ (v : World), v.tick = w'.tick → NodeLayoutOk groups v →
          ∃ s, (v.onScheduledTick ev.nodeId).events = v.events ++ [s] ∨
            (v.onScheduledTick ev.nodeId).events = v.events :=
        fun ev h_ev v h_v h_lay =>
          h_single ev (by rw [h_seq_cons]; exact
            List.mem_cons.mpr (Or.inr h_ev)) v
            (by rw [h_v, h_tick_w']) h_lay
      rw [h_drop] at h_b
      obtain ⟨s₀, h_sp₀ | h_nil₀⟩ :=
        h_single ev₀ (by rw [h_seq_cons]; exact
          List.mem_cons.mpr (Or.inl rfl)) w_pop h_tick_pop h_layout_pop
      · -- the current pop appends exactly s₀
        have h_new₀ : new₀ = [s₀] := by
          exact append_left_cancel' w_pop.events new₀ [s₀] (h_app₀.symm.trans h_sp₀)
        by_cases h_evA : ev₀ = A
        · -- A pops now: every later pop happens after A
          have h_new₀_sA : new₀ = [sA] := by
            have h_app₀' := h_app₀
            rw [h_evA] at h_app₀'
            exact append_left_cancel' w_pop.events new₀ [sA]
              (h_app₀'.symm.trans (h_spawnA w_pop h_tick_pop h_layout_pop))
          have h_e_acc' : e ∈ World.popSpawnAcc w' fuel := by
            rw [h_new₀_sA] at h_b
            dsimp at h_b
            rw [evBefore.cons_iff] at h_b
            rcases h_b with ⟨_, h_e⟩ | h_b_tail
            · exact h_e
            · -- sA appears again in the tail: contradiction
              have h_sA_acc' : sA ∈ World.popSpawnAcc w' fuel :=
                evBefore.mem_left h_b_tail
              obtain ⟨ev₁, h_ev₁, v₁, s₁, h_v₁, h_l₁, h_sp₁, h_s₁⟩ :=
                mem_popSpawnAcc_singleton_spawn groups w' fuel sA
                  h_layout_w' h_single_w' h_sA_acc'
              have h_ev₁_A : ev₁ = A :=
                h_uniqueA ev₁ (by rw [h_seq_cons]; exact
                    List.mem_cons.mpr (Or.inr h_ev₁)) v₁
                  (by rw [h_v₁, h_tick_w']) h_l₁ s₁ h_sp₁ h_s₁.symm
              have h_A_w' : A ∈ w'.events := by
                rw [h_ev₁_A] at h_ev₁
                exact World.mem_popSeqFuel_mem_events w' fuel A h_ev₁
              rw [h_app₀, List.mem_append] at h_A_w'
              rcases h_A_w' with h_A_pop' | h_A_new
              · exact absurd h_A_pop'
                  (not_mem_popWorld_of_due_nodup w A w_pop
                    (by rw [← h_evA]; exact h_pop) h_nodup)
              · have h_gt := h_fut₀ A h_A_new
                rw [h_tick_pop, hA_due] at h_gt
                exact absurd h_gt (by omega)
          have h_e_absent_w' : e ∉ w'.events := by
            rw [h_app₀, List.mem_append]
            intro h_mem
            rcases h_mem with h_mem | h_mem
            · rw [h_erase] at h_mem
              exact h_e_absent (List.eraseIdx_subset' w.events idx h_mem)
            · rw [h_new₀_sA] at h_mem
              exact h_e_ne (List.mem_singleton.mp h_mem)
          obtain ⟨ev₁, h_ev₁, v₁, s₁, h_v₁, h_l₁, h_sp₁, h_s₁, h_fresh₁⟩ :=
            mem_popSpawnAcc_singleton_spawn_fresh groups w' fuel e
              h_layout_w' h_e_absent_w' h_single_w'
              (fun ev₁ h₁ ev₂ h₂ h_ne v₁ v₂ h_v₁ h_v₂ h_l₁ h_l₂ s₁ s₂
                  h_sp₁ h_sp₂ =>
                h_distinct ev₁ (by rw [h_seq_cons]; exact
                    List.mem_cons.mpr (Or.inr h₁)) ev₂
                  (by rw [h_seq_cons]; exact
                    List.mem_cons.mpr (Or.inr h₂)) h_ne v₁ v₂
                  (by rw [h_v₁, h_tick_w']) (by rw [h_v₂, h_tick_w'])
                  h_l₁ h_l₂ s₁ s₂ h_sp₁ h_sp₂)
              h_e_acc'
          refine ⟨ev₁, by rw [h_seq_cons]; exact
              List.mem_cons.mpr (Or.inr h_ev₁), ?_, v₁, ?_, h_l₁, ?_,
            h_fresh₁⟩
          · rw [h_seq_cons, evBefore.cons_iff]
            exact Or.inl ⟨h_evA, h_ev₁⟩
          · rw [h_v₁, h_tick_w']
          · rw [h_sp₁]
            exact List.mem_append_right _ (by simp [h_s₁])
        · -- some other event pops now
          have h_sA_new₀ : sA ∉ new₀ := by
            rw [h_new₀]
            intro h_mem
            have h_s₀ : s₀ = sA := (List.mem_singleton.mp h_mem).symm
            apply h_evA
            exact h_uniqueA ev₀
              (by rw [h_seq_cons]; exact List.mem_cons.mpr (Or.inl rfl))
              w_pop h_tick_pop h_layout_pop s₀ h_sp₀ h_s₀
          have h_b_tail : evBefore (World.popSpawnAcc w' fuel) sA e :=
            evBefore_append_left_absent h_sA_new₀ h_b
          by_cases h_e_new₀ : e ∈ new₀
          · -- e spawns now but sA spawns later: impossible
            exfalso
            have h_e_acc' : e ∈ World.popSpawnAcc w' fuel :=
              evBefore.mem_right h_b_tail
            obtain ⟨ev₁, h_ev₁, v₁, s₁, h_v₁, h_l₁, h_sp₁, h_s₁⟩ :=
              mem_popSpawnAcc_singleton_spawn groups w' fuel e h_layout_w'
                h_single_w' h_e_acc'
            have h_ne : ev₀ ≠ ev₁ := by
              intro h_eq
              have h_nd_seq : (World.popSeqFuel w (fuel + 1)).Nodup :=
                popSeqFuel_nodup w (fuel + 1) h_nodup
              rw [h_seq_cons, h_eq] at h_nd_seq
              exact nodup_cons_append_not_mem (l₁ := []) h_nd_seq h_ev₁
            have h_s₀_eq : e = s₀ := by
              rw [h_new₀] at h_e_new₀
              simpa using h_e_new₀
            exact h_distinct ev₀
              (by rw [h_seq_cons]; exact List.mem_cons.mpr (Or.inl rfl))
              ev₁
              (by rw [h_seq_cons]; exact List.mem_cons.mpr (Or.inr h_ev₁))
              h_ne w_pop v₁ h_tick_pop
              (by rw [h_v₁, h_tick_w']) h_layout_pop h_l₁ s₀ s₁ h_sp₀
              h_sp₁ (by rw [← h_s₀_eq, h_s₁])
          · -- recurse into the tail accumulator
            have h_e_absent_w' : e ∉ w'.events := by
              rw [h_app₀, List.mem_append]
              intro h_mem
              rcases h_mem with h_mem | h_mem
              · rw [h_erase] at h_mem
                exact h_e_absent (List.eraseIdx_subset' w.events idx h_mem)
              · exact h_e_new₀ h_mem
            have hA_pop_tail : A ∈ World.popSeqFuel w' fuel := by
              rw [h_seq_cons, List.mem_cons] at hA_pop
              rcases hA_pop with h | h
              · exact absurd h (Ne.symm h_evA)
              · exact h
            have h_sA_absent_w' : sA ∉ w'.events := by
              rw [h_app₀, List.mem_append]
              intro h_mem
              rcases h_mem with h_mem | h_mem
              · rw [h_erase] at h_mem
                exact h_sA_absent (List.eraseIdx_subset' w.events idx h_mem)
              · rw [h_new₀] at h_mem
                apply h_evA
                exact h_uniqueA ev₀
                  (by rw [h_seq_cons]; exact List.mem_cons.mpr (Or.inl rfl))
                  w_pop h_tick_pop h_layout_pop s₀ h_sp₀
                  (List.mem_singleton.mp h_mem).symm
            obtain ⟨e', h_e'_tail, h_b_tail', v, h_v, h_lay, h_fire,
                h_fresh⟩ :=
              ih w' h_layout_w' h_nodup_w' hA_pop_tail
                (by rw [h_tick_w']; exact hA_due) h_sA_absent_w'
                (by rw [h_tick_w']; exact h_sA_gt)
                (fun v h_v h_lay => h_spawnA v (by rw [h_v, h_tick_w']) h_lay)
                h_single_w'
                (fun ev h_ev v h_v h_lay s h_sp h_s =>
                  h_uniqueA ev (by rw [h_seq_cons]; exact
                      List.mem_cons.mpr (Or.inr h_ev)) v
                    (by rw [h_v, h_tick_w']) h_lay s h_sp h_s)
                (fun ev₁ h₁ ev₂ h₂ h_ne v₁ v₂ h_v₁ h_v₂ h_l₁ h_l₂ s₁ s₂
                    h_sp₁ h_sp₂ =>
                  h_distinct ev₁ (by rw [h_seq_cons]; exact
                      List.mem_cons.mpr (Or.inr h₁)) ev₂
                    (by rw [h_seq_cons]; exact
                      List.mem_cons.mpr (Or.inr h₂)) h_ne v₁ v₂
                    (by rw [h_v₁, h_tick_w']) (by rw [h_v₂, h_tick_w'])
                    h_l₁ h_l₂ s₁ s₂ h_sp₁ h_sp₂)
                h_e_absent_w' h_b_tail
            refine ⟨e', by rw [h_seq_cons]; exact
                List.mem_cons.mpr (Or.inr h_e'_tail),
              by rw [h_seq_cons]; exact evBefore.cons_extend h_b_tail',
              v, ?_, h_lay, h_fire, h_fresh⟩
            rw [h_v, h_tick_w']
      · -- the current pop appends nothing
        have h_new₀ : new₀ = [] := by
          exact append_left_cancel' w_pop.events new₀ []
            ((h_app₀.symm.trans h_nil₀).trans
              (List.append_nil _).symm)
        have h_evA : ev₀ ≠ A := by
          intro h_eq
          have h_sp := h_spawnA w_pop h_tick_pop h_layout_pop
          rw [← h_eq, h_nil₀] at h_sp
          have h_len := congrArg List.length h_sp
          simp at h_len
        have h_e_absent_w' : e ∉ w'.events := by
          rw [h_app₀, h_new₀, List.append_nil]
          intro h_mem
          rw [h_erase] at h_mem
          exact h_e_absent (List.eraseIdx_subset' w.events idx h_mem)
        have h_sA_absent_w' : sA ∉ w'.events := by
          rw [h_app₀, h_new₀, List.append_nil]
          intro h_mem
          rw [h_erase] at h_mem
          exact h_sA_absent (List.eraseIdx_subset' w.events idx h_mem)
        rw [h_new₀, List.nil_append] at h_b
        have hA_pop_tail : A ∈ World.popSeqFuel w' fuel := by
          rw [h_seq_cons, List.mem_cons] at hA_pop
          rcases hA_pop with h | h
          · exact absurd h (Ne.symm h_evA)
          · exact h
        obtain ⟨e', h_e'_tail, h_b_tail', v, h_v, h_lay, h_fire, h_fresh⟩ :=
          ih w' h_layout_w' h_nodup_w' hA_pop_tail
            (by rw [h_tick_w']; exact hA_due) h_sA_absent_w'
            (by rw [h_tick_w']; exact h_sA_gt)
            (fun v h_v h_lay => h_spawnA v (by rw [h_v, h_tick_w']) h_lay)
            h_single_w'
            (fun ev h_ev v h_v h_lay s h_sp h_s =>
              h_uniqueA ev (by rw [h_seq_cons]; exact
                  List.mem_cons.mpr (Or.inr h_ev)) v
                (by rw [h_v, h_tick_w']) h_lay s h_sp h_s)
            (fun ev₁ h₁ ev₂ h₂ h_ne v₁ v₂ h_v₁ h_v₂ h_l₁ h_l₂ s₁ s₂
                h_sp₁ h_sp₂ =>
              h_distinct ev₁ (by rw [h_seq_cons]; exact
                  List.mem_cons.mpr (Or.inr h₁)) ev₂
                (by rw [h_seq_cons]; exact List.mem_cons.mpr (Or.inr h₂))
                h_ne v₁ v₂
                (by rw [h_v₁, h_tick_w']) (by rw [h_v₂, h_tick_w'])
                h_l₁ h_l₂ s₁ s₂ h_sp₁ h_sp₂)
            h_e_absent_w' h_b
        refine ⟨e', by rw [h_seq_cons]; exact
            List.mem_cons.mpr (Or.inr h_e'_tail),
          by rw [h_seq_cons]; exact evBefore.cons_extend h_b_tail',
          v, ?_, h_lay, h_fire, h_fresh⟩
        rw [h_v, h_tick_w']

/-! ## The converse spawn-origin theorem -/

set_option linter.unusedVariables false in
/-- At the pop tick of stage `j`, two reference events spawn `sA` and
    `sD`. Take an event between `sA` and `sD` in the next queue. It
    carries priority -3. It targets the stage-`j + 1` tick of the first
    chain. That event is the stage-`j + 1` event of some chain. The
    stage-`j` event of that chain sits between the two reference events
    in the due filter. The priority and target hypotheses classify the
    event. The betweenness hypotheses already determine it. So the proof
    does not reference those two facts. -/
theorem converse_spawn_stepUntilNextTick (groups : List GroupSpec)
    (actTick : Nat → Nat) (T : Nat) (w : World) (g₁ c₁ g₂ c₂ j : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_layout : NodeLayoutOk groups w)
    (h_j₁ : j ≤ (chainAt groups g₁ c₁).middleDelays.length)
    (h_j₂ : j ≤ (chainAt groups g₂ c₂).middleDelays.length)
    (h_j_ge : 1 ≤ j)
    (h_due : w.tick = stageTarget actTick groups g₁ c₁ j)
    (h_tgt₂ : stageTarget actTick groups g₂ c₂ j =
        stageTarget actTick groups g₁ c₁ j)
    (hA_mem : stageEvent actTick groups g₁ c₁ j ∈ w.events)
    (hD_mem : stageEvent actTick groups g₂ c₂ j ∈ w.events)
    (h_nodup : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup)
    (hAD : evBefore (w.events.filter (fun e => e.targetTick == w.tick))
        (stageEvent actTick groups g₁ c₁ j)
        (stageEvent actTick groups g₂ c₂ j))
    (h_mb : MiddleBlockOk groups actTick T
        (w.events.filter (fun e => e.targetTick == w.tick)) g₁ c₁ g₂ c₂ j)
    (h_stage : StageMemAt groups actTick w w.tick)
    (h_sA_absent : stageEvent actTick groups g₁ c₁ (j + 1) ∉ w.events)
    (h_sD_absent : stageEvent actTick groups g₂ c₂ (j + 1) ∉ w.events)
    (e : ScheduledEvent)
    (h_e_absent : e ∉ w.events)
    (h_b1 : evBefore w.stepUntilNextTick.events
        (stageEvent actTick groups g₁ c₁ (j + 1)) e)
    (h_b2 : evBefore w.stepUntilNextTick.events e
        (stageEvent actTick groups g₂ c₂ (j + 1)))
    (h_tgt : e.targetTick = stageTarget actTick groups g₁ c₁ (j + 1)) :
    ∃ g c, g < groups.length ∧ c < (groupAt groups g).length ∧
      e = stageEvent actTick groups g c (j + 1) ∧
      evBefore (w.events.filter (fun ev => ev.targetTick == w.tick))
        (stageEvent actTick groups g₁ c₁ j)
        (stageEvent actTick groups g c j) ∧
      evBefore (w.events.filter (fun ev => ev.targetTick == w.tick))
        (stageEvent actTick groups g c j)
        (stageEvent actTick groups g₂ c₂ j) := by
  set A := stageEvent actTick groups g₁ c₁ j
  set D := stageEvent actTick groups g₂ c₂ j
  set sA := stageEvent actTick groups g₁ c₁ (j + 1)
  set sD := stageEvent actTick groups g₂ c₂ (j + 1)
  set due := w.events.filter (fun ev => ev.targetTick == w.tick)
  -- basic facts about the two reference events
  have hA_due : A.targetTick = w.tick := by
    dsimp [A, stageEvent]
    exact h_due.symm
  have hD_due : D.targetTick = w.tick := by
    dsimp [D, stageEvent]
    rw [h_tgt₂, h_due]
  have hA_pri : A.priority = (-3 : Int) := by
    dsimp [A, stageEvent]
    exact stagePri_middle groups g₁ c₁ j h_j_ge h_j₁
  have hD_pri : D.priority = (-3 : Int) := by
    dsimp [D, stageEvent]
    exact stagePri_middle groups g₂ c₂ j h_j_ge h_j₂
  have h_sA_gt : sA.targetTick > w.tick := by
    dsimp [sA, stageEvent]
    rw [h_due]
    exact stageTarget_lt_succ actTick groups g₁ c₁ j h_j₁
  have h_sD_gt : sD.targetTick > w.tick := by
    dsimp [sD, stageEvent]
    rw [h_due, ← h_tgt₂]
    exact stageTarget_lt_succ actTick groups g₂ c₂ j h_j₂
  have h_spawnA : ∀ (v : World), v.tick = w.tick → NodeLayoutOk groups v →
      (v.onScheduledTick A.nodeId).events = v.events ++ [sA] := by
    intro v h_v h_lay
    simpa [A, sA, stageEvent] using
      stage_spawn groups actTick v g₁ c₁ j h_g₁ h_c₁ h_j₁
        (h_v.trans h_due) h_lay
  have h_spawnD : ∀ (v : World), v.tick = w.tick → NodeLayoutOk groups v →
      (v.onScheduledTick D.nodeId).events = v.events ++ [sD] := by
    intro v h_v h_lay
    simpa [D, sD, stageEvent] using
      stage_spawn groups actTick v g₂ c₂ j h_g₂ h_c₂ h_j₂
        ((h_v.trans h_due).trans h_tgt₂.symm) h_lay
  -- drain the tick and split the next queue into survivors and spawns
  set n := due.length
  set W := processNEvents w n
  have h_drain : W.events.filter (fun ev => ev.targetTick == w.tick) = [] :=
    drain_due_filter w
  have h_no : ∀ ev ∈ W.events, ev.targetTick ≠ W.tick := by
    intro ev h_ev h_eq
    have h_mem : ev ∈ W.events.filter (fun e => e.targetTick == w.tick) := by
      rw [List.mem_filter]
      exact ⟨h_ev, by
        rw [processNEvents_tick] at h_eq
        rw [h_eq]
        simp⟩
    rw [h_drain] at h_mem
    cases h_mem
  have h_post_events : w.stepUntilNextTick.events = W.events := by
    have h_pop_none : W.popNextEvent = none :=
      World.popNextEvent_none_of_no_due W h_no
    have h_step_none : W.step = none := by
      simp only [World.step, h_pop_none]
    rw [← processNEvents_stepUntilNextTick_eq w n,
      stepUntilNextTick_of_step_none W h_step_none]
  have h_split : W.events =
      w.events.filter (fun ev => ev.targetTick ≠ w.tick) ++
        World.popSpawnAcc w n := by
    have h_f := (World.popSeqWorldFuel_filter_split w n).1
    rw [← processNEvents_eq_popSeqWorldFuel] at h_f
    have h_keep : W.events.filter (fun ev => ev.targetTick ≠ w.tick) =
        W.events := by
      apply filter_eq_self_of_forall'
      intro ev h_ev
      have h_ne : ev.targetTick ≠ w.tick := by
        have h := h_no ev h_ev
        rwa [processNEvents_tick] at h
      rw [decide_eq_true_eq]
      exact h_ne
    rw [← h_keep]
    exact h_f
  have h_surv_sA : sA ∉ w.events.filter (fun ev => ev.targetTick ≠ w.tick) :=
    fun h_mem => h_sA_absent (List.mem_filter.mp h_mem).1
  have h_b1' : evBefore
      (w.events.filter (fun ev => ev.targetTick ≠ w.tick) ++
        World.popSpawnAcc w n) sA e := by
    rwa [← h_split, ← h_post_events]
  have h_b_left : evBefore (World.popSpawnAcc w n) sA e :=
    evBefore_append_left_absent h_surv_sA h_b1'
  have h_surv_sD : sD ∉ w.events.filter (fun ev => ev.targetTick ≠ w.tick) :=
    fun h_mem => h_sD_absent (List.mem_filter.mp h_mem).1
  have h_b2' : evBefore
      (w.events.filter (fun ev => ev.targetTick ≠ w.tick) ++
        World.popSpawnAcc w n) e sD := by
    rwa [← h_split, ← h_post_events]
  have h_b_right : evBefore (World.popSpawnAcc w n) e sD := by
    rcases evBefore_append_split_right h_b2' with h_e_surv | h_b
    · exact absurd h_e_surv (fun h_mem =>
        h_e_absent (List.mem_filter.mp h_mem).1)
    · exact h_b
  have hA_pop : A ∈ World.popSeqFuel w n :=
    mem_popSeqFuel_of_due w A hA_mem hA_due
  have hD_pop : D ∈ World.popSeqFuel w n :=
    mem_popSeqFuel_of_due w D hD_mem hD_due
  -- every pop spawns at most one event
  have h_single : ∀ ev ∈ World.popSeqFuel w n, ∀ (v : World),
      v.tick = w.tick → NodeLayoutOk groups v →
      ∃ s, (v.onScheduledTick ev.nodeId).events = v.events ++ [s] ∨
        (v.onScheduledTick ev.nodeId).events = v.events := by
    intro ev h_ev v h_v h_lay
    have h_ev_w : ev ∈ w.events :=
      World.mem_popSeqFuel_mem_events w n ev h_ev
    obtain ⟨gi₀, ci₀, k₀, h_gi₀, h_ci₀, h_k₀, h_ev_eq₀, _, _⟩ :=
      h_stage ev h_ev_w
    by_cases h_last :
        k₀ = (chainAt groups gi₀ ci₀).middleDelays.length + 1
    · refine ⟨ev, Or.inr ?_⟩
      rw [h_ev_eq₀, h_last]
      exact lastStage_spawn_nil groups actTick v gi₀ ci₀ h_gi₀ h_ci₀ h_lay
    · refine ⟨stageEvent actTick groups gi₀ ci₀ (k₀ + 1), Or.inl ?_⟩
      have h_mid : k₀ ≤ (chainAt groups gi₀ ci₀).middleDelays.length := by
        omega
      have h_ev_due : ev.targetTick = w.tick :=
        World.mem_popSeqFuel_due w n ev h_ev
      have h_tick : v.tick = stageTarget actTick groups gi₀ ci₀ k₀ := by
        rw [h_v, ← h_ev_due]
        have := congr_arg ScheduledEvent.targetTick h_ev_eq₀
        dsimp [stageEvent] at this
        exact this
      rw [h_ev_eq₀]
      exact stage_spawn groups actTick v gi₀ ci₀ k₀ h_gi₀ h_ci₀ h_mid
        h_tick h_lay
  -- only A spawns sA
  have h_uniqueA : ∀ ev ∈ World.popSeqFuel w n, ∀ (v : World),
      v.tick = w.tick → NodeLayoutOk groups v → ∀ s,
      (v.onScheduledTick ev.nodeId).events = v.events ++ [s] →
      s = sA → ev = A := by
    intro ev h_ev v h_v h_lay s h_sp h_s
    have h_ev_w : ev ∈ w.events :=
      World.mem_popSeqFuel_mem_events w n ev h_ev
    obtain ⟨gi₀, ci₀, k₀, h_gi₀, h_ci₀, h_k₀, h_ev_eq₀, _, _⟩ :=
      h_stage ev h_ev_w
    by_cases h_last :
        k₀ = (chainAt groups gi₀ ci₀).middleDelays.length + 1
    · have h_nil : (v.onScheduledTick ev.nodeId).events = v.events := by
        rw [h_ev_eq₀, h_last]
        exact lastStage_spawn_nil groups actTick v gi₀ ci₀ h_gi₀ h_ci₀
          h_lay
      rw [h_nil] at h_sp
      have h_len := congrArg List.length h_sp
      simp at h_len
    · have h_mid : k₀ ≤ (chainAt groups gi₀ ci₀).middleDelays.length := by
        omega
      have h_ev_due : ev.targetTick = w.tick :=
        World.mem_popSeqFuel_due w n ev h_ev
      have h_tick : v.tick = stageTarget actTick groups gi₀ ci₀ k₀ := by
        rw [h_v, ← h_ev_due]
        have := congr_arg ScheduledEvent.targetTick h_ev_eq₀
        dsimp [stageEvent] at this
        exact this
      have h_sp' : (v.onScheduledTick ev.nodeId).events =
          v.events ++ [stageEvent actTick groups gi₀ ci₀ (k₀ + 1)] := by
        rw [h_ev_eq₀]
        exact stage_spawn groups actTick v gi₀ ci₀ k₀ h_gi₀ h_ci₀ h_mid
          h_tick h_lay
      rw [h_sp'] at h_sp
      have h_inj := append_left_cancel' v.events
        [stageEvent actTick groups gi₀ ci₀ (k₀ + 1)] [s] h_sp
      injection h_inj with h_one
      rw [h_s] at h_one
      obtain ⟨h_g_eq, h_c_eq, _⟩ :=
        stageEvent_injective actTick groups gi₀ ci₀ (k₀ + 1) g₁ c₁ (j + 1)
          h_gi₀ h_ci₀ h_g₁ h_c₁ (by omega) (by omega) h_one
      rw [h_ev_eq₀, h_g_eq, h_c_eq]
      dsimp [A]
      congr 1
      omega
  -- only D spawns sD
  have h_uniqueD : ∀ ev ∈ World.popSeqFuel w n, ∀ (v : World),
      v.tick = w.tick → NodeLayoutOk groups v → ∀ s,
      (v.onScheduledTick ev.nodeId).events = v.events ++ [s] →
      s = sD → ev = D := by
    intro ev h_ev v h_v h_lay s h_sp h_s
    have h_ev_w : ev ∈ w.events :=
      World.mem_popSeqFuel_mem_events w n ev h_ev
    obtain ⟨gi₀, ci₀, k₀, h_gi₀, h_ci₀, h_k₀, h_ev_eq₀, _, _⟩ :=
      h_stage ev h_ev_w
    by_cases h_last :
        k₀ = (chainAt groups gi₀ ci₀).middleDelays.length + 1
    · have h_nil : (v.onScheduledTick ev.nodeId).events = v.events := by
        rw [h_ev_eq₀, h_last]
        exact lastStage_spawn_nil groups actTick v gi₀ ci₀ h_gi₀ h_ci₀
          h_lay
      rw [h_nil] at h_sp
      have h_len := congrArg List.length h_sp
      simp at h_len
    · have h_mid : k₀ ≤ (chainAt groups gi₀ ci₀).middleDelays.length := by
        omega
      have h_ev_due : ev.targetTick = w.tick :=
        World.mem_popSeqFuel_due w n ev h_ev
      have h_tick : v.tick = stageTarget actTick groups gi₀ ci₀ k₀ := by
        rw [h_v, ← h_ev_due]
        have := congr_arg ScheduledEvent.targetTick h_ev_eq₀
        dsimp [stageEvent] at this
        exact this
      have h_sp' : (v.onScheduledTick ev.nodeId).events =
          v.events ++ [stageEvent actTick groups gi₀ ci₀ (k₀ + 1)] := by
        rw [h_ev_eq₀]
        exact stage_spawn groups actTick v gi₀ ci₀ k₀ h_gi₀ h_ci₀ h_mid
          h_tick h_lay
      rw [h_sp'] at h_sp
      have h_inj := append_left_cancel' v.events
        [stageEvent actTick groups gi₀ ci₀ (k₀ + 1)] [s] h_sp
      injection h_inj with h_one
      rw [h_s] at h_one
      obtain ⟨h_g_eq, h_c_eq, _⟩ :=
        stageEvent_injective actTick groups gi₀ ci₀ (k₀ + 1) g₂ c₂ (j + 1)
          h_gi₀ h_ci₀ h_g₂ h_c₂ (by omega) (by omega) h_one
      rw [h_ev_eq₀, h_g_eq, h_c_eq]
      dsimp [D]
      congr 1
      omega
  -- distinct pops spawn distinct events
  have h_distinct : ∀ ev₁ ∈ World.popSeqFuel w n,
      ∀ ev₂ ∈ World.popSeqFuel w n, ev₁ ≠ ev₂ →
      ∀ (v₁ v₂ : World), v₁.tick = w.tick → v₂.tick = w.tick →
      NodeLayoutOk groups v₁ → NodeLayoutOk groups v₂ →
      ∀ s₁ s₂, (v₁.onScheduledTick ev₁.nodeId).events = v₁.events ++ [s₁] →
      (v₂.onScheduledTick ev₂.nodeId).events = v₂.events ++ [s₂] →
      s₁ ≠ s₂ := by
    intro ev₁ h₁ ev₂ h₂ h_ne v₁ v₂ h_v₁ h_v₂ h_l₁ h_l₂ s₁ s₂ h_sp₁ h_sp₂
        h_s_eq
    obtain ⟨gi₁, ci₁, k₁, h_gi₁, h_ci₁, h_k₁, h_ev₁, _, _⟩ :=
      h_stage ev₁ (World.mem_popSeqFuel_mem_events w n ev₁ h₁)
    obtain ⟨gi₂, ci₂, k₂, h_gi₂, h_ci₂, h_k₂, h_ev₂, _, _⟩ :=
      h_stage ev₂ (World.mem_popSeqFuel_mem_events w n ev₂ h₂)
    have h_k₁_mid : k₁ ≤ (chainAt groups gi₁ ci₁).middleDelays.length := by
      by_contra h_last
      have h_last' :
          k₁ = (chainAt groups gi₁ ci₁).middleDelays.length + 1 := by omega
      have h_nil : (v₁.onScheduledTick ev₁.nodeId).events = v₁.events := by
        rw [h_ev₁, h_last']
        exact lastStage_spawn_nil groups actTick v₁ gi₁ ci₁ h_gi₁ h_ci₁
          h_l₁
      rw [h_nil] at h_sp₁
      have h_len := congrArg List.length h_sp₁
      simp at h_len
    have h_k₂_mid : k₂ ≤ (chainAt groups gi₂ ci₂).middleDelays.length := by
      by_contra h_last
      have h_last' :
          k₂ = (chainAt groups gi₂ ci₂).middleDelays.length + 1 := by omega
      have h_nil : (v₂.onScheduledTick ev₂.nodeId).events = v₂.events := by
        rw [h_ev₂, h_last']
        exact lastStage_spawn_nil groups actTick v₂ gi₂ ci₂ h_gi₂ h_ci₂
          h_l₂
      rw [h_nil] at h_sp₂
      have h_len := congrArg List.length h_sp₂
      simp at h_len
    have h_due₁ : ev₁.targetTick = w.tick :=
      World.mem_popSeqFuel_due w n ev₁ h₁
    have h_due₂ : ev₂.targetTick = w.tick :=
      World.mem_popSeqFuel_due w n ev₂ h₂
    have h_tick₁ : v₁.tick = stageTarget actTick groups gi₁ ci₁ k₁ := by
      rw [h_v₁, ← h_due₁]
      have := congr_arg ScheduledEvent.targetTick h_ev₁
      dsimp [stageEvent] at this
      exact this
    have h_tick₂ : v₂.tick = stageTarget actTick groups gi₂ ci₂ k₂ := by
      rw [h_v₂, ← h_due₂]
      have := congr_arg ScheduledEvent.targetTick h_ev₂
      dsimp [stageEvent] at this
      exact this
    have h_sp₁' : (v₁.onScheduledTick ev₁.nodeId).events =
        v₁.events ++ [stageEvent actTick groups gi₁ ci₁ (k₁ + 1)] := by
      rw [h_ev₁]
      exact stage_spawn groups actTick v₁ gi₁ ci₁ k₁ h_gi₁ h_ci₁ h_k₁_mid
        h_tick₁ h_l₁
    have h_sp₂' : (v₂.onScheduledTick ev₂.nodeId).events =
        v₂.events ++ [stageEvent actTick groups gi₂ ci₂ (k₂ + 1)] := by
      rw [h_ev₂]
      exact stage_spawn groups actTick v₂ gi₂ ci₂ k₂ h_gi₂ h_ci₂ h_k₂_mid
        h_tick₂ h_l₂
    rw [h_sp₁'] at h_sp₁
    rw [h_sp₂'] at h_sp₂
    have h_inj₁ := append_left_cancel' v₁.events
      [stageEvent actTick groups gi₁ ci₁ (k₁ + 1)] [s₁] h_sp₁
    have h_inj₂ := append_left_cancel' v₂.events
      [stageEvent actTick groups gi₂ ci₂ (k₂ + 1)] [s₂] h_sp₂
    injection h_inj₁ with h_s₁
    injection h_inj₂ with h_s₂
    rw [← h_s₁, ← h_s₂] at h_s_eq
    obtain ⟨h_g, h_c, h_k⟩ := stageEvent_injective actTick groups gi₁ ci₁
      (k₁ + 1) gi₂ ci₂ (k₂ + 1) h_gi₁ h_ci₁ h_gi₂ h_ci₂ (by omega)
      (by omega) h_s_eq
    rw [h_ev₁, h_ev₂, h_g, h_c] at h_ne
    exact h_ne (by congr 1; omega)
  -- the accumulator is duplicate-free; e differs from sA and sD
  have h_acc_nd : (World.popSpawnAcc w n).Nodup :=
    popSpawnAcc_nodup groups w n h_layout h_nodup h_single h_distinct
  have h_e_ne_sA : e ≠ sA := by
    intro h_eq
    rw [h_eq] at h_b_left
    obtain ⟨l₁, l₂, l₃, h_two⟩ := evBefore_self_two_split h_b_left
    exact nodup_cons_append_not_mem (h_two ▸ h_acc_nd)
      (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
  have h_e_ne_sD : e ≠ sD := by
    intro h_eq
    rw [h_eq] at h_b_right
    obtain ⟨l₁, l₂, l₃, h_two⟩ := evBefore_self_two_split h_b_right
    exact nodup_cons_append_not_mem (h_two ▸ h_acc_nd)
      (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
  -- trace e back to its parent pops on both sides
  obtain ⟨eL, h_eL_pop, h_AeL, vL, h_vL_tick, h_vL_lay, h_eL_fire,
      h_eL_fresh⟩ :=
    popSpawnAcc_left_converse groups w n A sA e h_layout h_nodup hA_pop
      hA_due h_sA_absent h_sA_gt h_spawnA h_single h_uniqueA h_distinct
      h_e_absent h_e_ne_sA h_b_left
  obtain ⟨eR, h_eR_pop, h_eRD, vR, h_vR_tick, h_vR_lay, h_eR_fire,
      h_eR_fresh⟩ :=
    popSpawnAcc_right_converse groups w n D sD e h_layout h_nodup hD_pop
      hD_due h_sD_absent h_sD_gt h_spawnD h_single h_uniqueD h_e_absent
      h_e_ne_sD h_b_right
  -- decode the right parent: it is a middle-stage event
  have h_eR_w : eR ∈ w.events :=
    World.mem_popSeqFuel_mem_events w n eR h_eR_pop
  obtain ⟨gi, ci, k, h_gi, h_ci, h_k_le, h_eR_eq, _, _⟩ :=
    h_stage eR h_eR_w
  have h_eR_due : eR.targetTick = w.tick :=
    World.mem_popSeqFuel_due w n eR h_eR_pop
  have h_k_mid : k ≤ (chainAt groups gi ci).middleDelays.length := by
    by_contra h_last
    have h_last' :
        k = (chainAt groups gi ci).middleDelays.length + 1 := by omega
    have h_nil : (vR.onScheduledTick eR.nodeId).events = vR.events := by
      rw [h_eR_eq, h_last']
      exact lastStage_spawn_nil groups actTick vR gi ci h_gi h_ci h_vR_lay
    rw [h_nil] at h_eR_fire
    exact h_eR_fresh h_eR_fire
  have h_tick_R : vR.tick = stageTarget actTick groups gi ci k := by
    rw [h_vR_tick, ← h_eR_due]
    have := congr_arg ScheduledEvent.targetTick h_eR_eq
    dsimp [stageEvent] at this
    exact this
  have h_fire_R : (vR.onScheduledTick eR.nodeId).events =
      vR.events ++ [stageEvent actTick groups gi ci (k + 1)] := by
    rw [h_eR_eq]
    exact stage_spawn groups actTick vR gi ci k h_gi h_ci h_k_mid h_tick_R
      h_vR_lay
  have h_e_eq : e = stageEvent actTick groups gi ci (k + 1) := by
    rw [h_fire_R] at h_eR_fire
    rcases List.mem_append.mp h_eR_fire with h_mem | h_mem
    · exact absurd h_mem h_eR_fresh
    · simpa using h_mem
  -- decode the left parent and identify it with the right parent
  have h_eL_w : eL ∈ w.events :=
    World.mem_popSeqFuel_mem_events w n eL h_eL_pop
  obtain ⟨gi', ci', k', h_gi', h_ci', h_k_le', h_eL_eq, _, _⟩ :=
    h_stage eL h_eL_w
  have h_parent_eq : eL = eR := by
    by_cases h_k'_last :
        k' = (chainAt groups gi' ci').middleDelays.length + 1
    · have h_nil : (vL.onScheduledTick eL.nodeId).events = vL.events := by
        rw [h_eL_eq, h_k'_last]
        exact lastStage_spawn_nil groups actTick vL gi' ci' h_gi' h_ci'
          h_vL_lay
      rw [h_nil] at h_eL_fire
      exact absurd h_eL_fire h_eL_fresh
    · have h_k'_mid : k' ≤ (chainAt groups gi' ci').middleDelays.length := by
        omega
      have h_eL_due : eL.targetTick = w.tick :=
        World.mem_popSeqFuel_due w n eL h_eL_pop
      have h_tick_L : vL.tick = stageTarget actTick groups gi' ci' k' := by
        rw [h_vL_tick, ← h_eL_due]
        have := congr_arg ScheduledEvent.targetTick h_eL_eq
        dsimp [stageEvent] at this
        exact this
      have h_fire_L : (vL.onScheduledTick eL.nodeId).events =
          vL.events ++ [stageEvent actTick groups gi' ci' (k' + 1)] := by
        rw [h_eL_eq]
        exact stage_spawn groups actTick vL gi' ci' k' h_gi' h_ci' h_k'_mid
          h_tick_L h_vL_lay
      have h_e_eq_L : e = stageEvent actTick groups gi' ci' (k' + 1) := by
        rw [h_fire_L] at h_eL_fire
        rcases List.mem_append.mp h_eL_fire with h_mem | h_mem
        · exact absurd h_mem h_eL_fresh
        · simpa using h_mem
      obtain ⟨h_g_eq, h_c_eq, _⟩ :=
        stageEvent_injective actTick groups gi' ci' (k' + 1) gi ci (k + 1)
          h_gi' h_ci' h_gi h_ci (by omega) (by omega)
          (h_e_eq_L.symm.trans h_e_eq)
      rw [h_eL_eq, h_eR_eq, h_g_eq, h_c_eq]
      congr 1
      omega
  have h_AeR : evBefore (World.popSeqFuel w n) A eR := by
    rwa [← h_parent_eq]
  -- the parent carries the middle priority
  have h_pri_eR : eR.priority = (-3 : Int) := by
    have h_le₁ : A.priority ≤ eR.priority :=
      popSeqFuel_priority_mono w n A eR h_AeR
    have h_le₂ : eR.priority ≤ D.priority :=
      popSeqFuel_priority_mono w n eR D h_eRD
    rw [hA_pri] at h_le₁
    rw [hD_pri] at h_le₂
    omega
  -- transfer the pop order to the due-filter order
  have h_due_AeR : evBefore due A eR :=
    due_evBefore_of_popSeq_evBefore w n A eR hA_pop h_eR_pop hA_due
      h_eR_due (by rw [hA_pri, h_pri_eR]) h_nodup h_AeR
  have h_due_eRD : evBefore due eR D :=
    due_evBefore_of_popSeq_evBefore w n eR D h_eR_pop hD_pop h_eR_due
      hD_due (by rw [h_pri_eR, hD_pri]) h_nodup h_eRD
  -- the middle-block invariant classifies the parent
  have h_mb_eR : MiddleBlock groups actTick T g₁ c₁ j eR :=
    h_mb eR h_due_AeR h_due_eRD h_pri_eR (by
      rw [show eR.targetTick = w.tick from h_eR_due, h_due])
  rcases h_mb_eR with h_fin | h_mid
  · exfalso
    exact IsFinalEvent_priority_ne_middle groups actTick T eR h_fin h_pri_eR
  · obtain ⟨g, c, h_g, h_c, h_ev_eq, h_mb_pri, _, _⟩ := h_mid
    have h_mb_pri' : stagePri groups g c j = (-3 : Int) := by
      have h := congr_arg ScheduledEvent.priority h_ev_eq
      dsimp [stageEvent] at h
      rw [h_mb_pri] at h
      exact h.symm
    have h_j_bound : j ≤ (chainAt groups g c).middleDelays.length + 1 := by
      dsimp only [stagePri] at h_mb_pri'
      split_ifs at h_mb_pri' <;> omega
    obtain ⟨h_g_eq, h_c_eq, h_j_eq⟩ :=
      stageEvent_injective actTick groups g c j gi ci k h_g h_c h_gi h_ci
        h_j_bound (by omega) (h_ev_eq.symm.trans h_eR_eq)
    refine ⟨g, c, h_g, h_c, ?_, ?_, ?_⟩
    · rw [h_e_eq, h_g_eq, h_c_eq]
      congr 1
      omega
    · rw [← h_ev_eq]
      exact h_due_AeR
    · rw [← h_ev_eq]
      exact h_due_eRD

/-! ## Converse spawn origin for pop phases and burst phases

`converse_spawn_stepUntilNextTick` covers a full tick. Two more worlds
need the same fact. `processNEvents w n` stops after `n` pops.
`gSimBurst` runs several pop phases and appends observer events.
Both cases reduce to the spawn accumulator. A private core theorem
carries the shared argument.
-/

/-- Equal node lists give equal node lists after one
    `onScheduledTick`. Only signal levels change. -/
private theorem onScheduledTick_nodes_of_nodes_eq (w₁ w₂ : World)
    (id : Nat) (h_nodes : w₁.nodes = w₂.nodes) :
    (w₁.onScheduledTick id).nodes = (w₂.onScheduledTick id).nodes := by
  have h_get : w₁.getNode id = w₂.getNode id := by
    dsimp [World.getNode]
    rw [h_nodes]
  cases h₁ : w₁.getNode id with
  | none =>
    have h₂ : w₂.getNode id = none := by rwa [← h_get]
    have h_e₁ : w₁.onScheduledTick id = w₁ := by
      simp only [World.onScheduledTick, h₁]
    have h_e₂ : w₂.onScheduledTick id = w₂ := by
      simp only [World.onScheduledTick, h₂]
    rw [h_e₁, h_e₂]
    exact h_nodes
  | some nd =>
    have h₂ : w₂.getNode id = some nd := by rwa [← h_get]
    cases h_kind : nd.kind with
    | input =>
      have h_e₁ : w₁.onScheduledTick id = w₁ := by
        simp only [World.onScheduledTick, h₁, h_kind]
      have h_e₂ : w₂.onScheduledTick id = w₂ := by
        simp only [World.onScheduledTick, h₂, h_kind]
      rw [h_e₁, h_e₂]
      exact h_nodes
    | output name =>
      have h_e₁ : w₁.onScheduledTick id = w₁ := by
        simp only [World.onScheduledTick, h₁, h_kind]
      have h_e₂ : w₂.onScheduledTick id = w₂ := by
        simp only [World.onScheduledTick, h₂, h_kind]
      rw [h_e₁, h_e₂]
      exact h_nodes
    | observer =>
      have h_e₁ : w₁.onScheduledTick id =
          (w₁.updateNode id
            (fun nd' =>
              ({ nd' with sigLevel := 15 } : NodeData))).notifyOutputs id :=
        by simp only [World.onScheduledTick, h₁, h_kind]
      have h_e₂ : w₂.onScheduledTick id =
          (w₂.updateNode id
            (fun nd' =>
              ({ nd' with sigLevel := 15 } : NodeData))).notifyOutputs id :=
        by simp only [World.onScheduledTick, h₂, h_kind]
      rw [h_e₁, h_e₂, World.notifyOutputs_nodes, World.notifyOutputs_nodes]
      dsimp [World.updateNode]
      rw [h_nodes]
    | repeater d p =>
      have h_e₁ : w₁.onScheduledTick id =
          (w₁.updateNode id (fun nd' =>
            ({ nd' with
              sigLevel := if w₁.getInputSignal id > 0 then 15 else 0 } :
              NodeData))).notifyOutputs id := by
        simp only [World.onScheduledTick, h₁, h_kind]
      have h_e₂ : w₂.onScheduledTick id =
          (w₂.updateNode id (fun nd' =>
            ({ nd' with
              sigLevel := if w₂.getInputSignal id > 0 then 15 else 0 } :
              NodeData))).notifyOutputs id := by
        simp only [World.onScheduledTick, h₂, h_kind]
      have h_sig : w₁.getInputSignal id = w₂.getInputSignal id := by
        dsimp [World.getInputSignal, World.getNode]
        rw [h_nodes]
      have h_upd : (w₁.updateNode id (fun nd' =>
            ({ nd' with
              sigLevel := if w₂.getInputSignal id > 0 then 15 else 0 } :
              NodeData))).nodes =
          (w₂.updateNode id (fun nd' =>
            ({ nd' with
              sigLevel := if w₂.getInputSignal id > 0 then 15 else 0 } :
              NodeData))).nodes := by
        dsimp [World.updateNode]
        rw [h_nodes]
      rw [h_e₁, h_e₂, World.notifyOutputs_nodes, World.notifyOutputs_nodes,
        h_sig, h_upd]

/-- With no due events the spawn accumulator is empty. -/
private theorem popSpawnAcc_of_no_due (w : World) (fuel : Nat)
    (h_no : ∀ ev ∈ w.events, ev.targetTick ≠ w.tick) :
    World.popSpawnAcc w fuel = [] := by
  induction fuel with
  | zero => dsimp [World.popSpawnAcc]
  | succ fuel ih =>
    dsimp only [World.popSpawnAcc]
    rw [World.popNextEvent_none_of_no_due w h_no]

/-- The spawn accumulator splits over a fuel sum. -/
private theorem popSpawnAcc_concat (w : World) (a b : Nat) :
    World.popSpawnAcc w (a + b) =
      World.popSpawnAcc w a ++
        World.popSpawnAcc (World.popSeqWorldFuel w a) b := by
  induction a generalizing w b with
  | zero =>
    rw [Nat.zero_add]
    dsimp [World.popSpawnAcc, World.popSeqWorldFuel]
  | succ a ih =>
    rw [Nat.succ_add]
    cases h_pop : w.popNextEvent with
    | none =>
      have h_no : ∀ ev ∈ w.events, ev.targetTick ≠ w.tick :=
        popNextEvent_none_no_events w h_pop
      rw [popSpawnAcc_of_no_due w (a + b + 1) h_no]
      have h_acc : World.popSpawnAcc w (a + 1) = [] := by
        dsimp [World.popSpawnAcc]
        simp only [h_pop]
      have h_world : World.popSeqWorldFuel w (a + 1) = w := by
        dsimp [World.popSeqWorldFuel]
        simp only [h_pop]
      rw [h_acc, h_world, List.nil_append]
      exact (popSpawnAcc_of_no_due w b h_no).symm
    | some p =>
      rcases p with ⟨ev₀, w_pop⟩
      set w' := w_pop.onScheduledTick ev₀.nodeId
      have h_lhs : World.popSpawnAcc w (a + b + 1) =
          w'.events.drop w_pop.events.length ++ World.popSpawnAcc w' (a + b) :=
        by
        dsimp [World.popSpawnAcc, w']
        simp only [h_pop]
      have h_acc : World.popSpawnAcc w (a + 1) =
          w'.events.drop w_pop.events.length ++ World.popSpawnAcc w' a := by
        dsimp [World.popSpawnAcc, w']
        simp only [h_pop]
      have h_world : World.popSeqWorldFuel w (a + 1) =
          World.popSeqWorldFuel w' a := by
        dsimp [World.popSeqWorldFuel, w']
        simp only [h_pop]
      rw [h_lhs, h_acc, h_world, ih w' b, List.append_assoc]

/-- The spawn accumulator depends only on the tick, the node list, and
    the due filter. Two such worlds accumulate the same spawns. -/
private theorem popSpawnAcc_congr (w₁ w₂ : World)
    (h_tick : w₁.tick = w₂.tick)
    (h_filter : w₁.events.filter (fun e => e.targetTick == w₁.tick) =
        w₂.events.filter (fun e => e.targetTick == w₂.tick))
    (h_nodes : w₁.nodes = w₂.nodes) (fuel : Nat) :
    World.popSpawnAcc w₁ fuel = World.popSpawnAcc w₂ fuel := by
  induction fuel generalizing w₁ w₂ h_tick h_filter h_nodes with
  | zero => dsimp [World.popSpawnAcc]
  | succ fuel ih =>
    dsimp only [World.popSpawnAcc]
    cases h_pop₁ : w₁.popNextEvent with
    | none =>
      have h_pop₂ : w₂.popNextEvent = none := by
        by_contra h_ne
        cases h_pop₂ : w₂.popNextEvent with
        | none => exact h_ne h_pop₂
        | some q =>
          rcases q with ⟨ev, w_pop₂⟩
          obtain ⟨_, _, _, h_due, h_mem, _⟩ :=
            World.popNextEvent_eraseIdx w₂ ev w_pop₂ h_pop₂
          have h_ev_f : ev ∈
              w₂.events.filter (fun e => e.targetTick == w₂.tick) := by
            rw [List.mem_filter]
            exact ⟨h_mem, by rw [h_due]; simp⟩
          rw [← h_filter] at h_ev_f
          exact popNextEvent_none_no_events w₁ h_pop₁ ev
            (List.mem_filter.mp h_ev_f).1 (by
              simpa using (List.mem_filter.mp h_ev_f).2)
      simp only [h_pop₂]
    | some p =>
      rcases p with ⟨ev₀, w_pop₁⟩
      obtain ⟨w_pop₂, h_pop₂⟩ :=
        popNextEvent_same_of_same_filter w₁ w₂ h_tick h_filter ev₀ w_pop₁
          h_pop₁
      simp only [h_pop₂]
      set v₁ := w_pop₁.onScheduledTick ev₀.nodeId
      set v₂ := w_pop₂.onScheduledTick ev₀.nodeId
      have h_tick_pop : w_pop₁.tick = w_pop₂.tick := by
        rw [World.popNextEvent_tick w₁ ev₀ w_pop₁ h_pop₁,
          World.popNextEvent_tick w₂ ev₀ w_pop₂ h_pop₂, h_tick]
      have h_nodes_pop : w_pop₁.nodes = w_pop₂.nodes := by
        rw [World.popNextEvent_nodes w₁ ev₀ w_pop₁ h_pop₁,
          World.popNextEvent_nodes w₂ ev₀ w_pop₂ h_pop₂, h_nodes]
      -- both pops append the same spawn list
      have h_node_id : w_pop₁.getNode ev₀.nodeId =
          w_pop₂.getNode ev₀.nodeId := by
        dsimp [World.getNode]
        rw [h_nodes_pop]
      have h_kinds : ∀ nid,
          (w_pop₁.getNode nid).map (·.kind) =
            (w_pop₂.getNode nid).map (·.kind) := by
        intro nid
        dsimp [World.getNode]
        rw [h_nodes_pop]
      obtain ⟨new, h_new₁, h_new₂⟩ :=
        onScheduledTick_events_congr w_pop₁ w_pop₂ ev₀.nodeId h_tick_pop
          h_node_id h_kinds
      have h_drop : v₁.events.drop w_pop₁.events.length =
          v₂.events.drop w_pop₂.events.length := by
        dsimp only [v₁, v₂]
        rw [h_new₁, h_new₂, drop_append_self, drop_append_self]
      rw [h_drop]
      have h_tick_v : v₁.tick = v₂.tick := by
        dsimp only [v₁, v₂]
        rw [World.onScheduledTick_tick, World.onScheduledTick_tick,
          h_tick_pop]
      have h_filter_v :
          v₁.events.filter (fun e => e.targetTick == v₁.tick) =
            v₂.events.filter (fun e => e.targetTick == v₂.tick) := by
        dsimp only [v₁, v₂]
        rw [World.onScheduledTick_tick, World.onScheduledTick_tick]
        obtain ⟨new₁, h_app₁, h_fut₁⟩ :=
          World.onScheduledTick_appends_future w_pop₁ ev₀.nodeId
        obtain ⟨new₂, h_app₂, h_fut₂⟩ :=
          World.onScheduledTick_appends_future w_pop₂ ev₀.nodeId
        rw [h_app₁, h_app₂, List.filter_append, List.filter_append]
        have h_nil₁ :
            new₁.filter (fun e => e.targetTick == w_pop₁.tick) = [] := by
          apply filter_empty_of_none
          intro e h_e
          have h_gt := h_fut₁ e h_e
          exact nat_beq_false_of_ne e.targetTick w_pop₁.tick (by omega)
        have h_nil₂ :
            new₂.filter (fun e => e.targetTick == w_pop₂.tick) = [] := by
          apply filter_empty_of_none
          intro e h_e
          have h_gt := h_fut₂ e h_e
          exact nat_beq_false_of_ne e.targetTick w_pop₂.tick (by omega)
        rw [h_nil₁, h_nil₂, List.append_nil, List.append_nil]
        exact popNextEvent_filter_eq w₁ w₂ h_tick h_filter ev₀ w_pop₁
          w_pop₂ h_pop₁ h_pop₂
      have h_nodes_v : v₁.nodes = v₂.nodes :=
        onScheduledTick_nodes_of_nodes_eq w_pop₁ w_pop₂ ev₀.nodeId
          h_nodes_pop
      rw [ih v₁ v₂ h_tick_v h_filter_v h_nodes_v]

/-- Filter the post-burst queue to the non-due events of priority other
    than 0. The result is the old filtered queue plus the filtered spawn
    accumulator of the popped due events. The observer batches drop out
    of the filter. They all carry priority 0. -/
private theorem gSimBurst_filter_split (t : Nat)
    (obsAll : List (List Nat)) (withinOrd pos : Nat → List Nat)
    (w : World) (pairs : List (Nat × Nat)) :
    ∃ M,
      ((gSimBurst t obsAll withinOrd pos w pairs).events.filter
          (fun ev => ev.targetTick ≠ w.tick)).filter
        (fun ev => ev.priority ≠ (0 : Int)) =
        (w.events.filter (fun ev => ev.targetTick ≠ w.tick)).filter
          (fun ev => ev.priority ≠ (0 : Int)) ++
        (World.popSpawnAcc w M).filter
          (fun ev => ev.priority ≠ (0 : Int)) := by
  set pPri : ScheduledEvent → Bool :=
    fun ev => decide (ev.priority ≠ (0 : Int))
  induction pairs generalizing w with
  | nil =>
    refine ⟨0, ?_⟩
    dsimp [gSimBurst, World.popSpawnAcc]
    simp [pPri]
  | cons p ps ih =>
    rcases p with ⟨gi, k⟩
    dsimp only [gSimBurst, List.foldl_cons]
    set m := (pos t)[k]?.getD 0
    set ordered : List Nat := (withinOrd gi).foldl (fun acc ci =>
      match (obsAll[gi]?.getD [])[ci]? with
      | some oid => acc ++ [oid]
      | none => acc) []
    set Wp := processNEvents w m
    set W₁ := activateGroup Wp ordered
    obtain ⟨M', h_ih⟩ := ih W₁
    have h_tick_Wp : Wp.tick = w.tick := by
      dsimp [Wp]
      exact processNEvents_tick w m
    have h_tick_W₁ : W₁.tick = w.tick := by
      dsimp [W₁]
      rw [activateGroup_tick, h_tick_Wp]
    rw [h_tick_W₁] at h_ih
    -- the observer events appended by `activateGroup`
    set obsEv : List ScheduledEvent := ordered.map (fun nid =>
      ({ targetTick := Wp.tick + 2, priority := 0, nodeId := nid } :
        ScheduledEvent))
    have h_W₁_events : W₁.events = Wp.events ++ obsEv := by
      dsimp [W₁, obsEv]
      exact activateGroup_events_map Wp ordered
    have h_W₁_filter :
        (W₁.events.filter (fun ev => ev.targetTick ≠ w.tick)).filter pPri =
          (Wp.events.filter
            (fun ev => ev.targetTick ≠ w.tick)).filter pPri := by
      rw [h_W₁_events, List.filter_append, List.filter_append]
      have h_obs_nil :
          (obsEv.filter (fun ev => ev.targetTick ≠ w.tick)).filter pPri =
            [] := by
        apply filter_empty_of_none
        intro ev h_ev
        rcases List.mem_filter.mp h_ev with ⟨h_mem, _⟩
        dsimp [obsEv] at h_mem
        rcases List.mem_map.mp h_mem with ⟨nid, _, h_ev_eq⟩
        rw [← h_ev_eq]
        dsimp [pPri]
        exact decide_eq_false (by omega)
      rw [h_obs_nil, List.append_nil]
    have h_Wp_filter :
        (Wp.events.filter (fun ev => ev.targetTick ≠ w.tick)).filter pPri =
          (w.events.filter (fun ev => ev.targetTick ≠ w.tick)).filter pPri
            ++ (World.popSpawnAcc w m).filter pPri := by
      have h_f := (World.popSeqWorldFuel_filter_split w m).1
      rw [← processNEvents_eq_popSeqWorldFuel] at h_f
      dsimp [Wp]
      rw [h_f, List.filter_append]
    -- the accumulator does not see the appended observer events
    have h_acc : World.popSpawnAcc W₁ M' = World.popSpawnAcc Wp M' := by
      refine popSpawnAcc_congr W₁ Wp ?_ ?_ (activateGroup_nodes Wp ordered) M'
      · dsimp [W₁]
        exact activateGroup_tick Wp ordered
      · dsimp [W₁]
        rw [activateGroup_tick]
        exact activateGroup_due_filter Wp ordered
    refine ⟨m + M', ?_⟩
    change ((gSimBurst t obsAll withinOrd pos W₁ ps).events.filter
        (fun ev => ev.targetTick ≠ w.tick)).filter pPri =
      (w.events.filter (fun ev => ev.targetTick ≠ w.tick)).filter pPri ++
        (World.popSpawnAcc w (m + M')).filter pPri
    rw [h_ih, h_W₁_filter, h_acc, h_Wp_filter]
    rw [List.append_assoc, ← List.filter_append]
    congr 1
    rw [popSpawnAcc_concat w m M']
    have h_tail : World.popSpawnAcc Wp M' =
        World.popSpawnAcc (World.popSeqWorldFuel w m) M' := by
      congr 1
      dsimp [Wp]
      exact processNEvents_eq_popSeqWorldFuel w m
    rw [h_tail]

/-- The core of the converse spawn-origin fact. The event sits between
    the two spawned reference events in the spawn accumulator of `n`
    pops. The reference spawns force the reference pops into the pop
    sequence. The proof traces the event back to its parent pop. The
    middle-block invariant then classifies it. -/
private theorem converse_spawn_popSpawnAcc (groups : List GroupSpec)
    (actTick : Nat → Nat) (T : Nat) (w : World) (g₁ c₁ g₂ c₂ j n : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_layout : NodeLayoutOk groups w)
    (h_j₁ : j ≤ (chainAt groups g₁ c₁).middleDelays.length)
    (h_j₂ : j ≤ (chainAt groups g₂ c₂).middleDelays.length)
    (h_j_ge : 1 ≤ j)
    (h_due : w.tick = stageTarget actTick groups g₁ c₁ j)
    (h_tgt₂ : stageTarget actTick groups g₂ c₂ j =
        stageTarget actTick groups g₁ c₁ j)
    (h_nodup : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup)
    (h_mb : MiddleBlockOk groups actTick T
        (w.events.filter (fun e => e.targetTick == w.tick)) g₁ c₁ g₂ c₂ j)
    (h_stage : StageMemAt groups actTick w w.tick)
    (h_sA_absent : stageEvent actTick groups g₁ c₁ (j + 1) ∉ w.events)
    (h_sD_absent : stageEvent actTick groups g₂ c₂ (j + 1) ∉ w.events)
    (e : ScheduledEvent)
    (h_e_absent : e ∉ w.events)
    (h_b_left : evBefore (World.popSpawnAcc w n)
        (stageEvent actTick groups g₁ c₁ (j + 1)) e)
    (h_b_right : evBefore (World.popSpawnAcc w n) e
        (stageEvent actTick groups g₂ c₂ (j + 1))) :
    ∃ g c, g < groups.length ∧ c < (groupAt groups g).length ∧
      e = stageEvent actTick groups g c (j + 1) ∧
      evBefore (w.events.filter (fun ev => ev.targetTick == w.tick))
        (stageEvent actTick groups g₁ c₁ j)
        (stageEvent actTick groups g c j) ∧
      evBefore (w.events.filter (fun ev => ev.targetTick == w.tick))
        (stageEvent actTick groups g c j)
        (stageEvent actTick groups g₂ c₂ j) := by
  set A := stageEvent actTick groups g₁ c₁ j
  set D := stageEvent actTick groups g₂ c₂ j
  set sA := stageEvent actTick groups g₁ c₁ (j + 1)
  set sD := stageEvent actTick groups g₂ c₂ (j + 1)
  set due := w.events.filter (fun ev => ev.targetTick == w.tick)
  -- basic facts about the two reference events
  have hA_due : A.targetTick = w.tick := by
    dsimp [A, stageEvent]
    exact h_due.symm
  have hD_due : D.targetTick = w.tick := by
    dsimp [D, stageEvent]
    rw [h_tgt₂, h_due]
  have hA_pri : A.priority = (-3 : Int) := by
    dsimp [A, stageEvent]
    exact stagePri_middle groups g₁ c₁ j h_j_ge h_j₁
  have hD_pri : D.priority = (-3 : Int) := by
    dsimp [D, stageEvent]
    exact stagePri_middle groups g₂ c₂ j h_j_ge h_j₂
  have h_sA_gt : sA.targetTick > w.tick := by
    dsimp [sA, stageEvent]
    rw [h_due]
    exact stageTarget_lt_succ actTick groups g₁ c₁ j h_j₁
  have h_sD_gt : sD.targetTick > w.tick := by
    dsimp [sD, stageEvent]
    rw [h_due, ← h_tgt₂]
    exact stageTarget_lt_succ actTick groups g₂ c₂ j h_j₂
  have h_spawnA : ∀ (v : World), v.tick = w.tick → NodeLayoutOk groups v →
      (v.onScheduledTick A.nodeId).events = v.events ++ [sA] := by
    intro v h_v h_lay
    simpa [A, sA, stageEvent] using
      stage_spawn groups actTick v g₁ c₁ j h_g₁ h_c₁ h_j₁
        (h_v.trans h_due) h_lay
  have h_spawnD : ∀ (v : World), v.tick = w.tick → NodeLayoutOk groups v →
      (v.onScheduledTick D.nodeId).events = v.events ++ [sD] := by
    intro v h_v h_lay
    simpa [D, sD, stageEvent] using
      stage_spawn groups actTick v g₂ c₂ j h_g₂ h_c₂ h_j₂
        ((h_v.trans h_due).trans h_tgt₂.symm) h_lay
  -- every pop spawns at most one event
  have h_single : ∀ ev ∈ World.popSeqFuel w n, ∀ (v : World),
      v.tick = w.tick → NodeLayoutOk groups v →
      ∃ s, (v.onScheduledTick ev.nodeId).events = v.events ++ [s] ∨
        (v.onScheduledTick ev.nodeId).events = v.events := by
    intro ev h_ev v h_v h_lay
    have h_ev_w : ev ∈ w.events :=
      World.mem_popSeqFuel_mem_events w n ev h_ev
    obtain ⟨gi₀, ci₀, k₀, h_gi₀, h_ci₀, h_k₀, h_ev_eq₀, _, _⟩ :=
      h_stage ev h_ev_w
    by_cases h_last :
        k₀ = (chainAt groups gi₀ ci₀).middleDelays.length + 1
    · refine ⟨ev, Or.inr ?_⟩
      rw [h_ev_eq₀, h_last]
      exact lastStage_spawn_nil groups actTick v gi₀ ci₀ h_gi₀ h_ci₀ h_lay
    · refine ⟨stageEvent actTick groups gi₀ ci₀ (k₀ + 1), Or.inl ?_⟩
      have h_mid : k₀ ≤ (chainAt groups gi₀ ci₀).middleDelays.length := by
        omega
      have h_ev_due : ev.targetTick = w.tick :=
        World.mem_popSeqFuel_due w n ev h_ev
      have h_tick : v.tick = stageTarget actTick groups gi₀ ci₀ k₀ := by
        rw [h_v, ← h_ev_due]
        have := congr_arg ScheduledEvent.targetTick h_ev_eq₀
        dsimp [stageEvent] at this
        exact this
      rw [h_ev_eq₀]
      exact stage_spawn groups actTick v gi₀ ci₀ k₀ h_gi₀ h_ci₀ h_mid
        h_tick h_lay
  -- only A spawns sA
  have h_uniqueA : ∀ ev ∈ World.popSeqFuel w n, ∀ (v : World),
      v.tick = w.tick → NodeLayoutOk groups v → ∀ s,
      (v.onScheduledTick ev.nodeId).events = v.events ++ [s] →
      s = sA → ev = A := by
    intro ev h_ev v h_v h_lay s h_sp h_s
    have h_ev_w : ev ∈ w.events :=
      World.mem_popSeqFuel_mem_events w n ev h_ev
    obtain ⟨gi₀, ci₀, k₀, h_gi₀, h_ci₀, h_k₀, h_ev_eq₀, _, _⟩ :=
      h_stage ev h_ev_w
    by_cases h_last :
        k₀ = (chainAt groups gi₀ ci₀).middleDelays.length + 1
    · have h_nil : (v.onScheduledTick ev.nodeId).events = v.events := by
        rw [h_ev_eq₀, h_last]
        exact lastStage_spawn_nil groups actTick v gi₀ ci₀ h_gi₀ h_ci₀
          h_lay
      rw [h_nil] at h_sp
      have h_len := congrArg List.length h_sp
      simp at h_len
    · have h_mid : k₀ ≤ (chainAt groups gi₀ ci₀).middleDelays.length := by
        omega
      have h_ev_due : ev.targetTick = w.tick :=
        World.mem_popSeqFuel_due w n ev h_ev
      have h_tick : v.tick = stageTarget actTick groups gi₀ ci₀ k₀ := by
        rw [h_v, ← h_ev_due]
        have := congr_arg ScheduledEvent.targetTick h_ev_eq₀
        dsimp [stageEvent] at this
        exact this
      have h_sp' : (v.onScheduledTick ev.nodeId).events =
          v.events ++ [stageEvent actTick groups gi₀ ci₀ (k₀ + 1)] := by
        rw [h_ev_eq₀]
        exact stage_spawn groups actTick v gi₀ ci₀ k₀ h_gi₀ h_ci₀ h_mid
          h_tick h_lay
      rw [h_sp'] at h_sp
      have h_inj := append_left_cancel' v.events
        [stageEvent actTick groups gi₀ ci₀ (k₀ + 1)] [s] h_sp
      injection h_inj with h_one
      rw [h_s] at h_one
      obtain ⟨h_g_eq, h_c_eq, _⟩ :=
        stageEvent_injective actTick groups gi₀ ci₀ (k₀ + 1) g₁ c₁ (j + 1)
          h_gi₀ h_ci₀ h_g₁ h_c₁ (by omega) (by omega) h_one
      rw [h_ev_eq₀, h_g_eq, h_c_eq]
      dsimp [A]
      congr 1
      omega
  -- only D spawns sD
  have h_uniqueD : ∀ ev ∈ World.popSeqFuel w n, ∀ (v : World),
      v.tick = w.tick → NodeLayoutOk groups v → ∀ s,
      (v.onScheduledTick ev.nodeId).events = v.events ++ [s] →
      s = sD → ev = D := by
    intro ev h_ev v h_v h_lay s h_sp h_s
    have h_ev_w : ev ∈ w.events :=
      World.mem_popSeqFuel_mem_events w n ev h_ev
    obtain ⟨gi₀, ci₀, k₀, h_gi₀, h_ci₀, h_k₀, h_ev_eq₀, _, _⟩ :=
      h_stage ev h_ev_w
    by_cases h_last :
        k₀ = (chainAt groups gi₀ ci₀).middleDelays.length + 1
    · have h_nil : (v.onScheduledTick ev.nodeId).events = v.events := by
        rw [h_ev_eq₀, h_last]
        exact lastStage_spawn_nil groups actTick v gi₀ ci₀ h_gi₀ h_ci₀
          h_lay
      rw [h_nil] at h_sp
      have h_len := congrArg List.length h_sp
      simp at h_len
    · have h_mid : k₀ ≤ (chainAt groups gi₀ ci₀).middleDelays.length := by
        omega
      have h_ev_due : ev.targetTick = w.tick :=
        World.mem_popSeqFuel_due w n ev h_ev
      have h_tick : v.tick = stageTarget actTick groups gi₀ ci₀ k₀ := by
        rw [h_v, ← h_ev_due]
        have := congr_arg ScheduledEvent.targetTick h_ev_eq₀
        dsimp [stageEvent] at this
        exact this
      have h_sp' : (v.onScheduledTick ev.nodeId).events =
          v.events ++ [stageEvent actTick groups gi₀ ci₀ (k₀ + 1)] := by
        rw [h_ev_eq₀]
        exact stage_spawn groups actTick v gi₀ ci₀ k₀ h_gi₀ h_ci₀ h_mid
          h_tick h_lay
      rw [h_sp'] at h_sp
      have h_inj := append_left_cancel' v.events
        [stageEvent actTick groups gi₀ ci₀ (k₀ + 1)] [s] h_sp
      injection h_inj with h_one
      rw [h_s] at h_one
      obtain ⟨h_g_eq, h_c_eq, _⟩ :=
        stageEvent_injective actTick groups gi₀ ci₀ (k₀ + 1) g₂ c₂ (j + 1)
          h_gi₀ h_ci₀ h_g₂ h_c₂ (by omega) (by omega) h_one
      rw [h_ev_eq₀, h_g_eq, h_c_eq]
      dsimp [D]
      congr 1
      omega
  -- distinct pops spawn distinct events
  have h_distinct : ∀ ev₁ ∈ World.popSeqFuel w n,
      ∀ ev₂ ∈ World.popSeqFuel w n, ev₁ ≠ ev₂ →
      ∀ (v₁ v₂ : World), v₁.tick = w.tick → v₂.tick = w.tick →
      NodeLayoutOk groups v₁ → NodeLayoutOk groups v₂ →
      ∀ s₁ s₂, (v₁.onScheduledTick ev₁.nodeId).events = v₁.events ++ [s₁] →
      (v₂.onScheduledTick ev₂.nodeId).events = v₂.events ++ [s₂] →
      s₁ ≠ s₂ := by
    intro ev₁ h₁ ev₂ h₂ h_ne v₁ v₂ h_v₁ h_v₂ h_l₁ h_l₂ s₁ s₂ h_sp₁ h_sp₂
        h_s_eq
    obtain ⟨gi₁, ci₁, k₁, h_gi₁, h_ci₁, h_k₁, h_ev₁, _, _⟩ :=
      h_stage ev₁ (World.mem_popSeqFuel_mem_events w n ev₁ h₁)
    obtain ⟨gi₂, ci₂, k₂, h_gi₂, h_ci₂, h_k₂, h_ev₂, _, _⟩ :=
      h_stage ev₂ (World.mem_popSeqFuel_mem_events w n ev₂ h₂)
    have h_k₁_mid : k₁ ≤ (chainAt groups gi₁ ci₁).middleDelays.length := by
      by_contra h_last
      have h_last' :
          k₁ = (chainAt groups gi₁ ci₁).middleDelays.length + 1 := by omega
      have h_nil : (v₁.onScheduledTick ev₁.nodeId).events = v₁.events := by
        rw [h_ev₁, h_last']
        exact lastStage_spawn_nil groups actTick v₁ gi₁ ci₁ h_gi₁ h_ci₁
          h_l₁
      rw [h_nil] at h_sp₁
      have h_len := congrArg List.length h_sp₁
      simp at h_len
    have h_k₂_mid : k₂ ≤ (chainAt groups gi₂ ci₂).middleDelays.length := by
      by_contra h_last
      have h_last' :
          k₂ = (chainAt groups gi₂ ci₂).middleDelays.length + 1 := by omega
      have h_nil : (v₂.onScheduledTick ev₂.nodeId).events = v₂.events := by
        rw [h_ev₂, h_last']
        exact lastStage_spawn_nil groups actTick v₂ gi₂ ci₂ h_gi₂ h_ci₂
          h_l₂
      rw [h_nil] at h_sp₂
      have h_len := congrArg List.length h_sp₂
      simp at h_len
    have h_due₁ : ev₁.targetTick = w.tick :=
      World.mem_popSeqFuel_due w n ev₁ h₁
    have h_due₂ : ev₂.targetTick = w.tick :=
      World.mem_popSeqFuel_due w n ev₂ h₂
    have h_tick₁ : v₁.tick = stageTarget actTick groups gi₁ ci₁ k₁ := by
      rw [h_v₁, ← h_due₁]
      have := congr_arg ScheduledEvent.targetTick h_ev₁
      dsimp [stageEvent] at this
      exact this
    have h_tick₂ : v₂.tick = stageTarget actTick groups gi₂ ci₂ k₂ := by
      rw [h_v₂, ← h_due₂]
      have := congr_arg ScheduledEvent.targetTick h_ev₂
      dsimp [stageEvent] at this
      exact this
    have h_sp₁' : (v₁.onScheduledTick ev₁.nodeId).events =
        v₁.events ++ [stageEvent actTick groups gi₁ ci₁ (k₁ + 1)] := by
      rw [h_ev₁]
      exact stage_spawn groups actTick v₁ gi₁ ci₁ k₁ h_gi₁ h_ci₁ h_k₁_mid
        h_tick₁ h_l₁
    have h_sp₂' : (v₂.onScheduledTick ev₂.nodeId).events =
        v₂.events ++ [stageEvent actTick groups gi₂ ci₂ (k₂ + 1)] := by
      rw [h_ev₂]
      exact stage_spawn groups actTick v₂ gi₂ ci₂ k₂ h_gi₂ h_ci₂ h_k₂_mid
        h_tick₂ h_l₂
    rw [h_sp₁'] at h_sp₁
    rw [h_sp₂'] at h_sp₂
    have h_inj₁ := append_left_cancel' v₁.events
      [stageEvent actTick groups gi₁ ci₁ (k₁ + 1)] [s₁] h_sp₁
    have h_inj₂ := append_left_cancel' v₂.events
      [stageEvent actTick groups gi₂ ci₂ (k₂ + 1)] [s₂] h_sp₂
    injection h_inj₁ with h_s₁
    injection h_inj₂ with h_s₂
    rw [← h_s₁, ← h_s₂] at h_s_eq
    obtain ⟨h_g, h_c, h_k⟩ := stageEvent_injective actTick groups gi₁ ci₁
      (k₁ + 1) gi₂ ci₂ (k₂ + 1) h_gi₁ h_ci₁ h_gi₂ h_ci₂ (by omega)
      (by omega) h_s_eq
    rw [h_ev₁, h_ev₂, h_g, h_c] at h_ne
    exact h_ne (by congr 1; omega)
  -- the reference spawns force the reference pops into the pop sequence
  have hA_pop : A ∈ World.popSeqFuel w n := by
    have h_sA_acc : sA ∈ World.popSpawnAcc w n := evBefore.mem_left h_b_left
    obtain ⟨ev, h_ev, v, s, h_v, h_lay, h_sp, h_s⟩ :=
      mem_popSpawnAcc_singleton_spawn groups w n sA h_layout h_single
        h_sA_acc
    have h_ev_A : ev = A :=
      h_uniqueA ev h_ev v h_v h_lay s h_sp h_s.symm
    rwa [← h_ev_A]
  have hD_pop : D ∈ World.popSeqFuel w n := by
    have h_sD_acc : sD ∈ World.popSpawnAcc w n :=
      evBefore.mem_right h_b_right
    obtain ⟨ev, h_ev, v, s, h_v, h_lay, h_sp, h_s⟩ :=
      mem_popSpawnAcc_singleton_spawn groups w n sD h_layout h_single
        h_sD_acc
    have h_ev_D : ev = D :=
      h_uniqueD ev h_ev v h_v h_lay s h_sp h_s.symm
    rwa [← h_ev_D]
  -- the accumulator is duplicate-free, and e differs from sA and sD
  have h_acc_nd : (World.popSpawnAcc w n).Nodup :=
    popSpawnAcc_nodup groups w n h_layout h_nodup h_single h_distinct
  have h_e_ne_sA : e ≠ sA := by
    intro h_eq
    rw [h_eq] at h_b_left
    obtain ⟨l₁, l₂, l₃, h_two⟩ := evBefore_self_two_split h_b_left
    exact nodup_cons_append_not_mem (h_two ▸ h_acc_nd)
      (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
  have h_e_ne_sD : e ≠ sD := by
    intro h_eq
    rw [h_eq] at h_b_right
    obtain ⟨l₁, l₂, l₃, h_two⟩ := evBefore_self_two_split h_b_right
    exact nodup_cons_append_not_mem (h_two ▸ h_acc_nd)
      (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
  -- trace e back to its parent pops on both sides
  obtain ⟨eL, h_eL_pop, h_AeL, vL, h_vL_tick, h_vL_lay, h_eL_fire,
      h_eL_fresh⟩ :=
    popSpawnAcc_left_converse groups w n A sA e h_layout h_nodup hA_pop
      hA_due h_sA_absent h_sA_gt h_spawnA h_single h_uniqueA h_distinct
      h_e_absent h_e_ne_sA h_b_left
  obtain ⟨eR, h_eR_pop, h_eRD, vR, h_vR_tick, h_vR_lay, h_eR_fire,
      h_eR_fresh⟩ :=
    popSpawnAcc_right_converse groups w n D sD e h_layout h_nodup hD_pop
      hD_due h_sD_absent h_sD_gt h_spawnD h_single h_uniqueD h_e_absent
      h_e_ne_sD h_b_right
  -- decode the right parent: it is a middle-stage event
  have h_eR_w : eR ∈ w.events :=
    World.mem_popSeqFuel_mem_events w n eR h_eR_pop
  obtain ⟨gi, ci, k, h_gi, h_ci, h_k_le, h_eR_eq, _, _⟩ :=
    h_stage eR h_eR_w
  have h_eR_due : eR.targetTick = w.tick :=
    World.mem_popSeqFuel_due w n eR h_eR_pop
  have h_k_mid : k ≤ (chainAt groups gi ci).middleDelays.length := by
    by_contra h_last
    have h_last' :
        k = (chainAt groups gi ci).middleDelays.length + 1 := by omega
    have h_nil : (vR.onScheduledTick eR.nodeId).events = vR.events := by
      rw [h_eR_eq, h_last']
      exact lastStage_spawn_nil groups actTick vR gi ci h_gi h_ci h_vR_lay
    rw [h_nil] at h_eR_fire
    exact h_eR_fresh h_eR_fire
  have h_tick_R : vR.tick = stageTarget actTick groups gi ci k := by
    rw [h_vR_tick, ← h_eR_due]
    have := congr_arg ScheduledEvent.targetTick h_eR_eq
    dsimp [stageEvent] at this
    exact this
  have h_fire_R : (vR.onScheduledTick eR.nodeId).events =
      vR.events ++ [stageEvent actTick groups gi ci (k + 1)] := by
    rw [h_eR_eq]
    exact stage_spawn groups actTick vR gi ci k h_gi h_ci h_k_mid h_tick_R
      h_vR_lay
  have h_e_eq : e = stageEvent actTick groups gi ci (k + 1) := by
    rw [h_fire_R] at h_eR_fire
    rcases List.mem_append.mp h_eR_fire with h_mem | h_mem
    · exact absurd h_mem h_eR_fresh
    · simpa using h_mem
  -- decode the left parent and identify it with the right parent
  have h_eL_w : eL ∈ w.events :=
    World.mem_popSeqFuel_mem_events w n eL h_eL_pop
  obtain ⟨gi', ci', k', h_gi', h_ci', h_k_le', h_eL_eq, _, _⟩ :=
    h_stage eL h_eL_w
  have h_parent_eq : eL = eR := by
    by_cases h_k'_last :
        k' = (chainAt groups gi' ci').middleDelays.length + 1
    · have h_nil : (vL.onScheduledTick eL.nodeId).events = vL.events := by
        rw [h_eL_eq, h_k'_last]
        exact lastStage_spawn_nil groups actTick vL gi' ci' h_gi' h_ci'
          h_vL_lay
      rw [h_nil] at h_eL_fire
      exact absurd h_eL_fire h_eL_fresh
    · have h_k'_mid : k' ≤ (chainAt groups gi' ci').middleDelays.length := by
        omega
      have h_eL_due : eL.targetTick = w.tick :=
        World.mem_popSeqFuel_due w n eL h_eL_pop
      have h_tick_L : vL.tick = stageTarget actTick groups gi' ci' k' := by
        rw [h_vL_tick, ← h_eL_due]
        have := congr_arg ScheduledEvent.targetTick h_eL_eq
        dsimp [stageEvent] at this
        exact this
      have h_fire_L : (vL.onScheduledTick eL.nodeId).events =
          vL.events ++ [stageEvent actTick groups gi' ci' (k' + 1)] := by
        rw [h_eL_eq]
        exact stage_spawn groups actTick vL gi' ci' k' h_gi' h_ci' h_k'_mid
          h_tick_L h_vL_lay
      have h_e_eq_L : e = stageEvent actTick groups gi' ci' (k' + 1) := by
        rw [h_fire_L] at h_eL_fire
        rcases List.mem_append.mp h_eL_fire with h_mem | h_mem
        · exact absurd h_mem h_eL_fresh
        · simpa using h_mem
      obtain ⟨h_g_eq, h_c_eq, _⟩ :=
        stageEvent_injective actTick groups gi' ci' (k' + 1) gi ci (k + 1)
          h_gi' h_ci' h_gi h_ci (by omega) (by omega)
          (h_e_eq_L.symm.trans h_e_eq)
      rw [h_eL_eq, h_eR_eq, h_g_eq, h_c_eq]
      congr 1
      omega
  have h_AeR : evBefore (World.popSeqFuel w n) A eR := by
    rwa [← h_parent_eq]
  -- the parent carries the middle priority
  have h_pri_eR : eR.priority = (-3 : Int) := by
    have h_le₁ : A.priority ≤ eR.priority :=
      popSeqFuel_priority_mono w n A eR h_AeR
    have h_le₂ : eR.priority ≤ D.priority :=
      popSeqFuel_priority_mono w n eR D h_eRD
    rw [hA_pri] at h_le₁
    rw [hD_pri] at h_le₂
    omega
  -- transfer the pop order to the due-filter order
  have h_due_AeR : evBefore due A eR :=
    due_evBefore_of_popSeq_evBefore w n A eR hA_pop h_eR_pop hA_due
      h_eR_due (by rw [hA_pri, h_pri_eR]) h_nodup h_AeR
  have h_due_eRD : evBefore due eR D :=
    due_evBefore_of_popSeq_evBefore w n eR D h_eR_pop hD_pop h_eR_due
      hD_due (by rw [h_pri_eR, hD_pri]) h_nodup h_eRD
  -- the middle-block invariant classifies the parent
  have h_mb_eR : MiddleBlock groups actTick T g₁ c₁ j eR :=
    h_mb eR h_due_AeR h_due_eRD h_pri_eR (by
      rw [show eR.targetTick = w.tick from h_eR_due, h_due])
  rcases h_mb_eR with h_fin | h_mid
  · exfalso
    exact IsFinalEvent_priority_ne_middle groups actTick T eR h_fin h_pri_eR
  · obtain ⟨g, c, h_g, h_c, h_ev_eq, h_mb_pri, _, _⟩ := h_mid
    have h_mb_pri' : stagePri groups g c j = (-3 : Int) := by
      have h := congr_arg ScheduledEvent.priority h_ev_eq
      dsimp [stageEvent] at h
      rw [h_mb_pri] at h
      exact h.symm
    have h_j_bound : j ≤ (chainAt groups g c).middleDelays.length + 1 := by
      dsimp only [stagePri] at h_mb_pri'
      split_ifs at h_mb_pri' <;> omega
    obtain ⟨h_g_eq, h_c_eq, h_j_eq⟩ :=
      stageEvent_injective actTick groups g c j gi ci k h_g h_c h_gi h_ci
        h_j_bound (by omega) (h_ev_eq.symm.trans h_eR_eq)
    refine ⟨g, c, h_g, h_c, ?_, ?_, ?_⟩
    · rw [h_e_eq, h_g_eq, h_c_eq]
      congr 1
      omega
    · rw [← h_ev_eq]
      exact h_due_AeR
    · rw [← h_ev_eq]
      exact h_due_eRD

set_option linter.unusedVariables false in
/-- At the pop tick of stage `j`, two reference events spawn `sA` and
    `sD`. Take an event between `sA` and `sD` in the queue that
    `processNEvents w n` returns. It carries priority -3. It targets
    the stage-`j + 1` tick of the first chain. That event is the
    stage-`j + 1` event of some chain. The stage-`j` event of that
    chain sits between the two reference events in the due filter. -/
theorem converse_spawn_processNEvents (groups : List GroupSpec)
    (actTick : Nat → Nat) (T : Nat) (w : World) (n : Nat)
    (g₁ c₁ g₂ c₂ j : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_layout : NodeLayoutOk groups w)
    (h_j₁ : j ≤ (chainAt groups g₁ c₁).middleDelays.length)
    (h_j₂ : j ≤ (chainAt groups g₂ c₂).middleDelays.length)
    (h_j_ge : 1 ≤ j)
    (h_due : w.tick = stageTarget actTick groups g₁ c₁ j)
    (h_tgt₂ : stageTarget actTick groups g₂ c₂ j =
        stageTarget actTick groups g₁ c₁ j)
    (hA_mem : stageEvent actTick groups g₁ c₁ j ∈ w.events)
    (hD_mem : stageEvent actTick groups g₂ c₂ j ∈ w.events)
    (h_nodup : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup)
    (hAD : evBefore (w.events.filter (fun e => e.targetTick == w.tick))
        (stageEvent actTick groups g₁ c₁ j)
        (stageEvent actTick groups g₂ c₂ j))
    (h_mb : MiddleBlockOk groups actTick T
        (w.events.filter (fun e => e.targetTick == w.tick)) g₁ c₁ g₂ c₂ j)
    (h_stage : StageMemAt groups actTick w w.tick)
    (h_sA_absent : stageEvent actTick groups g₁ c₁ (j + 1) ∉ w.events)
    (h_sD_absent : stageEvent actTick groups g₂ c₂ (j + 1) ∉ w.events)
    (e : ScheduledEvent)
    (h_e_absent : e ∉ w.events)
    (h_b1 : evBefore (processNEvents w n).events
        (stageEvent actTick groups g₁ c₁ (j + 1)) e)
    (h_b2 : evBefore (processNEvents w n).events e
        (stageEvent actTick groups g₂ c₂ (j + 1)))
    (h_pri : e.priority = (-3 : Int))
    (h_tgt : e.targetTick = stageTarget actTick groups g₁ c₁ (j + 1)) :
    ∃ g c, g < groups.length ∧ c < (groupAt groups g).length ∧
      e = stageEvent actTick groups g c (j + 1) ∧
      evBefore (w.events.filter (fun ev => ev.targetTick == w.tick))
        (stageEvent actTick groups g₁ c₁ j)
        (stageEvent actTick groups g c j) ∧
      evBefore (w.events.filter (fun ev => ev.targetTick == w.tick))
        (stageEvent actTick groups g c j)
        (stageEvent actTick groups g₂ c₂ j) := by
  set sA := stageEvent actTick groups g₁ c₁ (j + 1)
  set sD := stageEvent actTick groups g₂ c₂ (j + 1)
  set W := processNEvents w n
  -- sA, e, sD all miss the tick of w
  have h_sA_nd : sA.targetTick ≠ w.tick := by
    dsimp [sA, stageEvent]
    rw [h_due]
    exact (stageTarget_lt_succ actTick groups g₁ c₁ j h_j₁).ne'
  have h_e_nd : e.targetTick ≠ w.tick := by
    rw [h_tgt, h_due]
    exact (stageTarget_lt_succ actTick groups g₁ c₁ j h_j₁).ne'
  have h_sD_nd : sD.targetTick ≠ w.tick := by
    dsimp [sD, stageEvent]
    rw [h_due, ← h_tgt₂]
    exact (stageTarget_lt_succ actTick groups g₂ c₂ j h_j₂).ne'
  -- keep only the events that miss the tick of w
  have h_b1_f :
      evBefore (W.events.filter (fun ev => ev.targetTick ≠ w.tick)) sA e :=
    evBefore.filter (fun ev => ev.targetTick ≠ w.tick)
      (by simp [h_sA_nd]) (by simp [h_e_nd]) h_b1
  have h_b2_f :
      evBefore (W.events.filter (fun ev => ev.targetTick ≠ w.tick)) e sD :=
    evBefore.filter (fun ev => ev.targetTick ≠ w.tick)
      (by simp [h_e_nd]) (by simp [h_sD_nd]) h_b2
  -- split the filtered queue into survivors and the spawn accumulator
  have h_split : W.events.filter (fun ev => ev.targetTick ≠ w.tick) =
      w.events.filter (fun ev => ev.targetTick ≠ w.tick) ++
        World.popSpawnAcc w n := by
    have h_f := (World.popSeqWorldFuel_filter_split w n).1
    rwa [← processNEvents_eq_popSeqWorldFuel] at h_f
  have h_surv_sA :
      sA ∉ w.events.filter (fun ev => ev.targetTick ≠ w.tick) :=
    fun h_mem => h_sA_absent (List.mem_filter.mp h_mem).1
  have h_b_left : evBefore (World.popSpawnAcc w n) sA e :=
    evBefore_append_left_absent h_surv_sA (by rwa [← h_split])
  have h_b_right : evBefore (World.popSpawnAcc w n) e sD := by
    have h_e_surv :
        e ∉ w.events.filter (fun ev => ev.targetTick ≠ w.tick) :=
      fun h_mem => h_e_absent (List.mem_filter.mp h_mem).1
    rw [h_split] at h_b2_f
    rcases evBefore_append_split_right h_b2_f with h_e_s | h_b
    · exact absurd h_e_s h_e_surv
    · exact h_b
  exact converse_spawn_popSpawnAcc groups actTick T w g₁ c₁ g₂ c₂ j n
    h_g₁ h_c₁ h_g₂ h_c₂ h_layout h_j₁ h_j₂ h_j_ge h_due h_tgt₂ h_nodup
    h_mb h_stage h_sA_absent h_sD_absent e h_e_absent h_b_left h_b_right

set_option linter.unusedVariables false in
/-- The converse spawn-origin fact for a burst phase. The burst phase
    appends observer events at the end of the queue. Those events carry
    priority 0. The priority filter in the proof drops them. The rest
    reduces to the spawn accumulator of the popped due events. -/
theorem converse_spawn_gSimBurst (groups : List GroupSpec)
    (actTick : Nat → Nat) (T : Nat) (t : Nat)
    (obsAll : List (List Nat)) (withinOrd pos : Nat → List Nat)
    (w : World) (pairs : List (Nat × Nat)) (g₁ c₁ g₂ c₂ j : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_layout : NodeLayoutOk groups w)
    (h_j₁ : j ≤ (chainAt groups g₁ c₁).middleDelays.length)
    (h_j₂ : j ≤ (chainAt groups g₂ c₂).middleDelays.length)
    (h_j_ge : 1 ≤ j)
    (h_due : w.tick = stageTarget actTick groups g₁ c₁ j)
    (h_tgt₂ : stageTarget actTick groups g₂ c₂ j =
        stageTarget actTick groups g₁ c₁ j)
    (hA_mem : stageEvent actTick groups g₁ c₁ j ∈ w.events)
    (hD_mem : stageEvent actTick groups g₂ c₂ j ∈ w.events)
    (h_nodup : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup)
    (hAD : evBefore (w.events.filter (fun e => e.targetTick == w.tick))
        (stageEvent actTick groups g₁ c₁ j)
        (stageEvent actTick groups g₂ c₂ j))
    (h_mb : MiddleBlockOk groups actTick T
        (w.events.filter (fun e => e.targetTick == w.tick)) g₁ c₁ g₂ c₂ j)
    (h_stage : StageMemAt groups actTick w w.tick)
    (h_sA_absent : stageEvent actTick groups g₁ c₁ (j + 1) ∉ w.events)
    (h_sD_absent : stageEvent actTick groups g₂ c₂ (j + 1) ∉ w.events)
    (e : ScheduledEvent)
    (h_e_absent : e ∉ w.events)
    (h_b1 : evBefore (gSimBurst t obsAll withinOrd pos w pairs).events
        (stageEvent actTick groups g₁ c₁ (j + 1)) e)
    (h_b2 : evBefore (gSimBurst t obsAll withinOrd pos w pairs).events e
        (stageEvent actTick groups g₂ c₂ (j + 1)))
    (h_pri : e.priority = (-3 : Int))
    (h_tgt : e.targetTick = stageTarget actTick groups g₁ c₁ (j + 1)) :
    ∃ g c, g < groups.length ∧ c < (groupAt groups g).length ∧
      e = stageEvent actTick groups g c (j + 1) ∧
      evBefore (w.events.filter (fun ev => ev.targetTick == w.tick))
        (stageEvent actTick groups g₁ c₁ j)
        (stageEvent actTick groups g c j) ∧
      evBefore (w.events.filter (fun ev => ev.targetTick == w.tick))
        (stageEvent actTick groups g c j)
        (stageEvent actTick groups g₂ c₂ j) := by
  set sA := stageEvent actTick groups g₁ c₁ (j + 1)
  set sD := stageEvent actTick groups g₂ c₂ (j + 1)
  set W_B := gSimBurst t obsAll withinOrd pos w pairs
  set pPri : ScheduledEvent → Bool :=
    fun ev => decide (ev.priority ≠ (0 : Int))
  -- sA, e, sD all miss the tick of w
  have h_sA_nd : sA.targetTick ≠ w.tick := by
    dsimp [sA, stageEvent]
    rw [h_due]
    exact (stageTarget_lt_succ actTick groups g₁ c₁ j h_j₁).ne'
  have h_e_nd : e.targetTick ≠ w.tick := by
    rw [h_tgt, h_due]
    exact (stageTarget_lt_succ actTick groups g₁ c₁ j h_j₁).ne'
  have h_sD_nd : sD.targetTick ≠ w.tick := by
    dsimp [sD, stageEvent]
    rw [h_due, ← h_tgt₂]
    exact (stageTarget_lt_succ actTick groups g₂ c₂ j h_j₂).ne'
  -- keep only the events that miss the tick of w
  have h_b1_f :
      evBefore (W_B.events.filter (fun ev => ev.targetTick ≠ w.tick))
        sA e :=
    evBefore.filter (fun ev => ev.targetTick ≠ w.tick)
      (by simp [h_sA_nd]) (by simp [h_e_nd]) h_b1
  have h_b2_f :
      evBefore (W_B.events.filter (fun ev => ev.targetTick ≠ w.tick))
        e sD :=
    evBefore.filter (fun ev => ev.targetTick ≠ w.tick)
      (by simp [h_e_nd]) (by simp [h_sD_nd]) h_b2
  -- sA, e, sD carry a priority other than 0
  have h_sA_ne₀ : sA.priority ≠ (0 : Int) := by
    dsimp [sA, stageEvent, stagePri]
    intro h_eq
    omega
  have h_sA_pri : decide (sA.priority ≠ (0 : Int)) = true := by
    simp [h_sA_ne₀]
  have h_sD_ne₀ : sD.priority ≠ (0 : Int) := by
    dsimp [sD, stageEvent, stagePri]
    intro h_eq
    omega
  have h_sD_pri : decide (sD.priority ≠ (0 : Int)) = true := by
    simp [h_sD_ne₀]
  have h_e_ne₀ : e.priority ≠ (0 : Int) := by
    rw [h_pri]
    intro h_eq
    omega
  have h_e_pri : decide (e.priority ≠ (0 : Int)) = true := by
    simp [h_e_ne₀]
  -- apply the burst split. The priority filter drops the observer
  -- batches.
  obtain ⟨M, h_split⟩ :=
    gSimBurst_filter_split t obsAll withinOrd pos w pairs
  have h_b1_ff : evBefore
      ((w.events.filter (fun ev => ev.targetTick ≠ w.tick)).filter pPri ++
        (World.popSpawnAcc w M).filter pPri) sA e := by
    have h := evBefore.filter pPri h_sA_pri h_e_pri h_b1_f
    rwa [h_split] at h
  have h_surv_sA :
      sA ∉ (w.events.filter (fun ev => ev.targetTick ≠ w.tick)).filter
        pPri :=
    fun h_mem =>
      h_sA_absent (List.mem_filter.mp (List.mem_filter.mp h_mem).1).1
  have h_b_left : evBefore (World.popSpawnAcc w M) sA e :=
    evBefore.of_filter pPri
      (evBefore_append_left_absent h_surv_sA h_b1_ff)
  have h_b_right : evBefore (World.popSpawnAcc w M) e sD := by
    have h_b2_ff : evBefore
        ((w.events.filter
            (fun ev => ev.targetTick ≠ w.tick)).filter pPri ++
          (World.popSpawnAcc w M).filter pPri) e sD := by
      have h := evBefore.filter pPri h_e_pri h_sD_pri h_b2_f
      rwa [h_split] at h
    have h_e_surv :
        e ∉ (w.events.filter (fun ev => ev.targetTick ≠ w.tick)).filter
          pPri :=
      fun h_mem =>
        h_e_absent (List.mem_filter.mp (List.mem_filter.mp h_mem).1).1
    rcases evBefore_append_split_right h_b2_ff with h_e_s | h_b
    · exact absurd h_e_s h_e_surv
    · exact evBefore.of_filter pPri h_b
  exact converse_spawn_popSpawnAcc groups actTick T w g₁ c₁ g₂ c₂ j M
    h_g₁ h_c₁ h_g₂ h_c₂ h_layout h_j₁ h_j₂ h_j_ge h_due h_tgt₂ h_nodup
    h_mb h_stage h_sA_absent h_sD_absent e h_e_absent h_b_left h_b_right
