import BasicProofs.PrefixChain.Part01


open BasicRedstoneSim

/-- Stronger: `setInput` new events have targetTick ≥ w.tick + 2. -/
theorem setInput_events_future_ge2 (w : World) (id level : Nat)
    (h_delay : ∀ nid nd, w.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2) :
    ∀ ev ∈ (w.setInput id level).events, ev ∉ w.events → ev.targetTick ≥ w.tick + 2 := by
  dsimp (config := { zeta := true }) [World.setInput, World.notifyOutputs]
  set w' := w.updateNode id (fun nd => { nd with sigLevel := level })
  have h_events' : w'.events = w.events := World.updateNode_events w id _
  have h_tick' : w'.tick = w.tick := World.updateNode_tick w id _
  cases h_getNode : w'.getNode id with
  | none =>
    simp [h_events']
    intro ev h h'; contradiction
  | some nd =>
    have h_delay' : ∀ nid nd, w'.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
      intro nid nd' h_nd' d p h_kind
      obtain ⟨nd_orig, h_getNode', h_kind_eq⟩ :=
        World.updateNode_getNode_kind w id nid
          (fun nd => { nd with sigLevel := level })
          (fun nd => rfl) nd' h_nd'
      rw [← h_kind_eq] at h_kind
      exact h_delay nid nd_orig h_getNode' d p h_kind
    simp only []
    have := foldl_onNeighborUpdate_events_future_ge2 nd.outputs w' h_delay'
    rw [h_tick'] at this
    intro ev h_ev h_notin
    rw [← h_events'] at h_notin
    exact this ev h_ev h_notin

/-- foldl `onNeighborUpdate` new events have targetTick % 2 = w.tick % 2. -/
theorem foldl_onNeighborUpdate_events_parity (l : List Nat) (w : World)
    (h_even : ∀ nid nd, w.getNode nid = some nd → ∀ d p,
        nd.kind = .repeater d p → (d : Nat) % 2 = 0) :
    ∀ ev ∈ (l.foldl (fun w' outId => w'.onNeighborUpdate outId) w).events,
    ev ∉ w.events → ev.targetTick % 2 = w.tick % 2 := by
  induction l generalizing w with
  | nil => simp; intro ev h h'; contradiction
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    have h_tick_hd : (w.onNeighborUpdate hd).tick = w.tick := World.onNeighborUpdate_tick w hd
    have h_even_hd : ∀ nid nd, (w.onNeighborUpdate hd).getNode nid = some nd → ∀ d p,
        nd.kind = .repeater d p → (d : Nat) % 2 = 0 := by
      intro nid nd h_nd d p h_kind
      have h_nd_w : w.getNode nid = some nd := by
        have := World.onNeighborUpdate_nodes w hd
        dsimp [World.getNode] at h_nd ⊢; rw [← this]; exact h_nd
      exact h_even nid nd h_nd_w d p h_kind
    intro ev h_ev h_new
    by_cases h_old_hd : ev ∈ w.events
    · exfalso; exact h_new h_old_hd
    · by_cases h_old_mid : ev ∈ (w.onNeighborUpdate hd).events
      · -- ev is new from onNeighborUpdate hd
        exact World.onNeighborUpdate_events_parity w hd
          (fun nd h_nd => h_even hd nd h_nd) ev h_old_mid h_old_hd
      · -- ev is new from the tail foldl
        have := ih (w.onNeighborUpdate hd) h_even_hd ev h_ev h_old_mid
        rwa [← h_tick_hd]

/-- `onScheduledTick` new events have targetTick % 2 = w.tick % 2 when delays are even. -/
theorem World.onScheduledTick_events_parity (w : World) (id : Nat)
    (h_even : ∀ nid nd, w.getNode nid = some nd → ∀ d p,
        nd.kind = .repeater d p → (d : Nat) % 2 = 0) :
    ∀ ev ∈ (w.onScheduledTick id).events, ev ∉ w.events → ev.targetTick % 2 = w.tick % 2 := by
  dsimp [World.onScheduledTick]
  split
  · intro ev h h'; contradiction
  · rename_i nd; split
    · rename_i delay priority
      set w' := w.updateNode id (fun nd' => { nd' with sigLevel := if w.getInputSignal id > 0 then 15 else 0 })
      have h_ev' : w'.events = w.events := World.updateNode_events w id _
      have h_tick' : w'.tick = w.tick := World.updateNode_tick w id _
      dsimp [World.notifyOutputs]
      cases h_go : w'.getNode id with
      | none => simp [h_ev']; intro ev h h'; contradiction
      | some nd' =>
        simp only []
        have h_even' : ∀ nid nd, w'.getNode nid = some nd → ∀ d p,
            nd.kind = .repeater d p → (d : Nat) % 2 = 0 := by
          intro nid nd'' h_nd'' d p h_kind
          obtain ⟨nd_orig, h_go', h_keq⟩ :=
            World.updateNode_getNode_kind w id nid
              (fun nd => { nd with sigLevel := if w.getInputSignal id > 0 then 15 else 0 })
              (fun nd => rfl) nd'' h_nd''
          rw [← h_keq] at h_kind
          exact h_even nid nd_orig h_go' d p h_kind
        intro ev h_ev h_new
        have h_parity := foldl_onNeighborUpdate_events_parity nd'.outputs w' h_even' ev h_ev
        have h_new' : ev ∉ w'.events := by rwa [h_ev']
        have := h_parity h_new'
        rwa [← h_tick']
    · set w' := w.updateNode id (fun nd' => { nd' with sigLevel := 15 })
      have h_ev' : w'.events = w.events := World.updateNode_events w id _
      have h_tick' : w'.tick = w.tick := World.updateNode_tick w id _
      dsimp [World.notifyOutputs]
      cases h_go : w'.getNode id with
      | none => simp [h_ev']; intro ev h h'; contradiction
      | some nd' =>
        simp only []
        have h_even' : ∀ nid nd, w'.getNode nid = some nd → ∀ d p,
            nd.kind = .repeater d p → (d : Nat) % 2 = 0 := by
          intro nid nd'' h_nd'' d p h_kind
          obtain ⟨nd_orig, h_go', h_keq⟩ :=
            World.updateNode_getNode_kind w id nid
              (fun nd => { nd with sigLevel := 15 }) (fun nd => rfl) nd'' h_nd''
          rw [← h_keq] at h_kind
          exact h_even nid nd_orig h_go' d p h_kind
        intro ev h_ev h_new
        have h_parity := foldl_onNeighborUpdate_events_parity nd'.outputs w' h_even' ev h_ev
        have h_new' : ev ∉ w'.events := by rwa [h_ev']
        have := h_parity h_new'
        rwa [← h_tick']
    · intro ev h h'; contradiction

/-- New events from `onNeighborUpdate` have nodeId = id. -/
theorem World.onNeighborUpdate_events_nodeId (w : World) (id : Nat) :
    ∀ ev ∈ (w.onNeighborUpdate id).events, ev ∉ w.events → ev.nodeId = id := by
  cases h_getNode : w.getNode id with
  | none => simp [World.onNeighborUpdate, h_getNode]; intro ev h h'; contradiction
  | some nd =>
    cases h_kind : nd.kind with
    | repeater delay priority =>
      simp [World.onNeighborUpdate, h_getNode, h_kind, World.scheduleEvent_events,
            List.mem_append]
      intro ev h_ev h_new
      cases h_ev with
      | inl h => contradiction
      | inr h => rw [h]
    | observer =>
      simp [World.onNeighborUpdate, h_getNode, h_kind, World.scheduleEvent_events,
            List.mem_append]
      intro ev h_ev h_new
      cases h_ev with
      | inl h => contradiction
      | inr h => rw [h]
    | output name =>
      simp [World.onNeighborUpdate, h_getNode, h_kind, World.logOutput_events]
      intro ev h h'; contradiction
    | input =>
      simp [World.onNeighborUpdate, h_getNode, h_kind]
      intro ev h h'; contradiction

/-- New events from `foldl onNeighborUpdate` have nodeId in the foldl list. -/
theorem foldl_onNeighborUpdate_nodeId_mem (l : List Nat) (w : World) :
    ∀ ev ∈ (l.foldl (fun w' outId => w'.onNeighborUpdate outId) w).events,
    ev ∉ w.events → ev.nodeId ∈ l := by
  induction l generalizing w with
  | nil => intro ev h h'; simp at h; contradiction
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    intro ev h_ev h_new
    by_cases h_old : ev ∈ w.events
    · exfalso; exact h_new h_old
    · by_cases h_mid : ev ∈ (w.onNeighborUpdate hd).events
      · -- New from onNeighborUpdate hd: nodeId = hd
        have h_nodeId := World.onNeighborUpdate_events_nodeId w hd ev h_mid h_old
        rw [h_nodeId]; exact List.mem_cons.mpr (Or.inl rfl)
      · -- New from tail foldl
        have := ih (w.onNeighborUpdate hd) ev h_ev h_mid
        exact List.mem_cons.mpr (Or.inr this)

/-! ### Layer 3: popNextEvent semantics -/

/-- `popNextEvent` selects an event at the current tick. -/
theorem popNextEvent_at_tick (w : World) (ev : ScheduledEvent) (w' : World)
    (h : w.popNextEvent = some (ev, w')) :
    ev.targetTick = w.tick := by
  unfold World.popNextEvent at h
  dsimp (config := { zeta := true }) at h
  set indexed := List.zip (List.range w.events.length) w.events
  set candidates := indexed.filter (fun (_, e) => e.targetTick == w.tick)
  set minPri := candidates.foldl (fun acc (_, e) => min acc e.priority) (100 : Int)
  split at h <;> try contradiction
  · split at h <;> try contradiction
    · rename_i idx ev_found h_find
      rw [Option.some_inj, Prod.mk.injEq] at h
      rcases h with ⟨rfl, _⟩
      -- ev_found ∈ candidates because find? returned it
      have h_mem := List.mem_of_find?_eq_some h_find
      -- candidates = filter (·.targetTick == w.tick) indexed, so ev_found.targetTick == w.tick
      dsimp [candidates] at h_mem
      rw [List.mem_filter] at h_mem
      exact Nat.eq_of_beq_eq_true (by simpa using h_mem.2)

/-- Swapping components of a zip gives the zip in the other order. -/
theorem List.zip_map_swap (l₁ : List α) (l₂ : List β) :
    (List.zip l₁ l₂).map Prod.swap = List.zip l₂ l₁ := by
  induction l₁ generalizing l₂ with
  | nil => simp [List.zip]
  | cons hd tl ih =>
    cases l₂ with
    | nil => simp [List.zip]
    | cons hd₂ tl₂ =>
      simp [List.zip, List.zipWith, Prod.swap] at ih ⊢
      exact ih tl₂

/-- The i-th element of `List.zip (List.range l.length) l` is `(i, l[i])`. -/
theorem mem_zip_range_self (l : List α) (i : Nat) (h : i < l.length) :
    (i, l[i]) ∈ List.zip (List.range l.length) l := by
  have h_eq : List.zip (List.range l.length) l = l.zipIdx.map Prod.swap := by
    rw [← List.zip_map_swap, List.zipIdx_eq_zip_range', List.range_eq_range']
  rw [h_eq, List.mem_map]
  use (l[i], i)
  constructor
  · -- (l[i], i) ∈ l.zipIdx
    have h_len : i < l.zipIdx.length := by simp [List.length_zipIdx, h]
    have h_elem : l.zipIdx[i] = (l[i], i) := by
      rw [List.getElem_zipIdx (by simp [List.length_zipIdx, h])]
      simp
    rw [← h_elem]; exact List.getElem_mem h_len
  · rfl

/-- The foldl-min is ≤ the initial value. -/
theorem foldl_min_le_init (l : List (Nat × ScheduledEvent)) (init : Int) :
    l.foldl (fun acc (_, e) => min acc e.priority) init ≤ init := by
  induction l generalizing init with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    exact le_trans (ih (min init hd.2.priority)) (min_le_left _ _)

/-- The foldl-min is ≤ every element's priority. -/
theorem foldl_min_le_all (l : List (Nat × ScheduledEvent)) (init : Int) :
    ∀ x ∈ l, l.foldl (fun acc (_, e) => min acc e.priority) init ≤ x.2.priority := by
  induction l generalizing init with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.mem_cons]
    intro x hx
    cases hx with
    | inl h => rw [h]; exact le_trans (foldl_min_le_init tl _) (min_le_right _ _)
    | inr h => exact ih _ x h

/-- If `find?` returns `some a`, then `a` satisfies the predicate. -/
theorem find?_eq_some_imp_pred {α : Type} (p : α → Bool) :
    ∀ (l : List α) (a : α), l.find? p = some a → p a = true := by
  intro l
  induction l with
  | nil => intro a h; contradiction
  | cons hd tl ih =>
    intro a h
    dsimp [List.find?] at h
    split at h
    · injection h with h_eq; subst h_eq; assumption
    · exact ih a h

/-- `popNextEvent` selects the event with minimum priority among all
candidates at the current tick. -/
theorem popNextEvent_min_priority (w : World) (ev : ScheduledEvent) (w' : World)
    (h : w.popNextEvent = some (ev, w')) :
    ∀ ev' ∈ w.events, ev'.targetTick = w.tick → ev.priority ≤ ev'.priority := by
  unfold World.popNextEvent at h
  dsimp (config := { zeta := true }) at h
  set indexed := List.zip (List.range w.events.length) w.events
  set candidates := indexed.filter (fun (_, e) => e.targetTick == w.tick)
  set initPri := candidates.head?.map (fun (_, e) => e.priority) |>.getD 0
  set minPri := candidates.foldl (fun acc (_, e) => min acc e.priority) initPri
  split at h
  · intro ev' _ _; cases h
  · split at h
    · intro ev' _ _; cases h
    · rename_i idx ev_found h_find
      rw [Option.some_inj, Prod.mk.injEq] at h
      rcases h with ⟨rfl, _⟩
      -- ev_found.priority == minPri (from find? predicate)
      have h_pri : (ev_found.priority == minPri) = true :=
        find?_eq_some_imp_pred (fun (x : Nat × ScheduledEvent) => x.2.priority == minPri)
          candidates (idx, ev_found) h_find
      intro ev' h_ev' h_tick
      -- ev' is a candidate: (idx', ev') ∈ candidates for some idx'
      have h_beq : (ev'.targetTick == w.tick) = true := by simp [h_tick]
      obtain ⟨idx', h_lt, h_eq⟩ := List.getElem_of_mem h_ev'
      have h_cand : (idx', ev') ∈ candidates := by
        dsimp [candidates, indexed]
        rw [List.mem_filter]
        constructor
        · simpa [h_eq] using mem_zip_range_self w.events idx' h_lt
        · exact h_beq
      have h_le := foldl_min_le_all candidates initPri (idx', ev') h_cand
      -- h_le : minPri ≤ ev'.priority, h_pri : (ev_found.priority == minPri) = true
      have h_ev_pri : (ev_found.priority : Int) = minPri := of_decide_eq_true h_pri
      linarith

/-! ### Layer 4: stepUntilNextTick exhaustion -/

/-- The foldl-min is either the initial value or some element's priority. -/
theorem foldl_min_mem (l : List (Nat × ScheduledEvent)) (init : Int) :
    l.foldl (fun acc (_, e) => min acc e.priority) init = init ∨
    ∃ x ∈ l, l.foldl (fun acc (_, e) => min acc e.priority) init = x.2.priority := by
  induction l generalizing init with
  | nil => left; rfl
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    by_cases h : hd.2.priority < init
    · have h_min : min init hd.2.priority = hd.2.priority := by omega
      rw [h_min]
      have ih' := ih hd.2.priority
      cases ih' with
      | inl h' => right; exact ⟨hd, by simp, h'⟩
      | inr h' => right; rcases h' with ⟨x, hx, hx'⟩; exact ⟨x, by simp [hx], hx'⟩
    · have h_min : min init hd.2.priority = init := by omega
      rw [h_min]
      have ih' := ih init
      cases ih' with
      | inl h' => left; exact h'
      | inr h' => right; rcases h' with ⟨x, hx, hx'⟩; exact ⟨x, by simp [hx], hx'⟩

/-- If `popNextEvent = none`, no events target the current tick. -/
theorem popNextEvent_none_no_events (w : World)
    (h_pop : w.popNextEvent = none) :
    ∀ ev ∈ w.events, ev.targetTick ≠ w.tick := by
  intro ev h_ev h_tick
  -- ev is a candidate at the current tick, so candidates is non-empty
  obtain ⟨i, h_lt, h_eq⟩ := List.mem_iff_getElem.mp h_ev
  have h_zip := mem_zip_range_self w.events i h_lt
  rw [h_eq] at h_zip
  -- Show popNextEvent w ≠ none by showing candidates is non-empty and find? succeeds
  unfold World.popNextEvent at h_pop
  dsimp (config := { zeta := true }) at h_pop
  set candidates := (List.zip (List.range w.events.length) w.events).filter
      (fun (_, e) => e.targetTick == w.tick) with h_cands_def
  set init := candidates.head?.map (fun (_, e) => e.priority) |>.getD 0 with h_init_def
  set minPri := candidates.foldl (fun acc (_, e) => min acc e.priority) init with h_minPri_def
  -- (i, ev) ∈ candidates since ev.targetTick = w.tick
  have h_cand : (i, ev) ∈ candidates := by
    dsimp [candidates]; rw [List.mem_filter]; exact ⟨h_zip, by simp [h_tick]⟩
  have h_ne : candidates ≠ [] := by intro h; rw [h] at h_cand; contradiction
  have h_not_empty : ¬candidates.isEmpty := by intro h; apply h_ne; simpa using h
  simp [h_not_empty] at h_pop
  split at h_pop
  · -- find? returned none → contradiction via foldl_min_mem
    rename_i h_find
    rw [List.find?_eq_none] at h_find
    have h_mem := foldl_min_mem candidates init
    cases h_mem with
    | inl h_eq_init =>
      -- minPri = init; candidates ≠ [] so candidates = hd :: tl
      obtain ⟨hd, tl, h_cons⟩ := List.exists_cons_of_ne_nil h_ne
      have hd_in : hd ∈ candidates := by rw [h_cons]; simp
      have h_init_eq : init = hd.2.priority := by dsimp [init]; rw [h_cons]; simp
      have h_pred : (hd.2.priority == minPri) = true := by
        dsimp [minPri]; rw [h_eq_init, h_init_eq]; simp
      have h_contra := h_find hd hd_in
      rw [h_pred] at h_contra; contradiction
    | inr h_exists =>
      obtain ⟨x, hx, hx'⟩ := h_exists
      have h_pred : (x.2.priority == minPri) = true := by
        dsimp [minPri]; rw [hx']; simp
      have h_contra := h_find x hx
      rw [h_pred] at h_contra; contradiction
  · -- find? returned some → contradiction with h_pop
    contradiction

/-- `popNextEvent` removes an event via `eraseIdx`. -/
theorem List.snd_mem_of_mem_zip {α β : Type} (l₁ : List α) (l₂ : List β) (a : α) (b : β) :
    (a, b) ∈ List.zip l₁ l₂ → b ∈ l₂ := by
  intro h
  induction l₁ generalizing l₂ a b with
  | nil => simp [List.zip] at h
  | cons hd tl ih =>
    cases l₂ with
    | nil => simp [List.zip] at h
    | cons hd₂ tl₂ =>
      simp [List.zip] at h ⊢
      cases h with
      | inl h_1 => simp_all only [true_or]
      | inr h_2 =>
        apply Or.inr
        apply ih
        · exact h_2

theorem List.fst_mem_of_mem_zip {α β : Type} (l₁ : List α) (l₂ : List β) (a : α) (b : β) :
    (a, b) ∈ List.zip l₁ l₂ → a ∈ l₁ := by
  intro h
  induction l₁ generalizing l₂ a b with
  | nil => simp [List.zip] at h
  | cons hd tl ih =>
    cases l₂ with
    | nil => simp [List.zip] at h
    | cons hd₂ tl₂ =>
      simp [List.zip] at h ⊢
      cases h with
      | inl h => left; exact h.1
      | inr h => right; exact ih _ _ _ h

theorem getElem_append_of_lt {α : Type} (l r : List α) (i : Nat) (h : i < l.length) :
    (l ++ r)[i]'(by simp []; omega) = l[i] := by
  revert i h
  induction l with
  | nil => intro i h; simp [List.length] at h
  | cons hd tl ih =>
    intro i h
    cases i with
    | zero => rfl
    | succ i' =>
      have h' : i' < tl.length := by simpa [List.length] using h
      simpa [List.length, List.cons_append] using ih i' h'

theorem getElem_append_right_eq {α : Type} (l : List α) (a b : α) :
    (l ++ [a, b])[l.length]'(by simp [List.length]) = a ∧
    (l ++ [a, b])[l.length + 1]'(by simp [List.length]) = b := by
  induction l with
  | nil => constructor <;> rfl
  | cons hd tl ih =>
    simp [List.length, List.cons_append]

theorem eraseIdx_append_two {α : Type} (l : List α) (a b : α) :
    (l ++ [a, b]).eraseIdx l.length = l ++ [b] := by
  induction l with
  | nil => simp []
  | cons hd tl ih =>
    simp only [List.length, List.cons_append, List.eraseIdx]
    exact congrArg (List.cons hd) ih

theorem eraseIdx_append_two_right {α : Type} (l : List α) (a b : α) :
    (l ++ [a, b]).eraseIdx (l.length + 1) = l ++ [a] := by
  induction l with
  | nil => simp [List.eraseIdx]
  | cons hd tl ih =>
    simp only [List.length, List.cons_append, List.eraseIdx]
    exact congrArg (List.cons hd) ih

theorem eraseIdx_append_two_mid {α : Type} (l r : List α) (a b : α) :
    (l ++ [a, b] ++ r).eraseIdx l.length = l ++ [b] ++ r := by
  induction l with
  | nil => simp []
  | cons hd tl ih =>
    simp only [List.length, List.cons_append, List.eraseIdx]
    exact congrArg (List.cons hd) ih

theorem eraseIdx_append_two_mid_right {α : Type} (l r : List α) (a b : α) :
    (l ++ [a, b] ++ r).eraseIdx (l.length + 1) = l ++ [a] ++ r := by
  induction l with
  | nil => simp [List.eraseIdx]
  | cons hd tl ih =>
    simp only [List.length, List.cons_append, List.eraseIdx]
    exact congrArg (List.cons hd) ih

/-- If `a ∉ l`, `a ∉ r`, `a ≠ b`, and `(l ++ [a, b] ++ r)[i] = a`, then `i = l.length`. -/
theorem getElem_eq_of_not_mem_append_two {α : Type} [DecidableEq α]
    (l r : List α) (a b : α)
    (h_not_l : a ∉ l) (h_not_r : a ∉ r) (h_ne : a ≠ b)
    (i : Nat) (h_lt : i < (l ++ [a, b] ++ r).length)
    (h_getElem : (l ++ [a, b] ++ r)[i]'h_lt = a) :
    i = l.length := by
  have h_len_ab : (l ++ [a, b]).length = l.length + 2 := by rw [List.length_append]; rfl
  have h_len_abr : (l ++ [a, b] ++ r).length = l.length + 2 + r.length := by rw [List.length_append, List.length_append]; rfl
  have h_ge : l.length ≤ i := by
    by_contra h
    have h_lt_i : i < l.length := by omega
    have h_lt_assoc : i < (l ++ ([a, b] ++ r)).length := by
      have h : (l ++ ([a, b] ++ r)).length = (l ++ [a, b] ++ r).length := by
        simp [List.length_append]
      rw [h]; exact h_lt
    have h_getElem' : (l ++ ([a, b] ++ r))[i]'h_lt_assoc = a := by
      simpa [List.append_assoc] using h_getElem
    have h_app := getElem_append_of_lt l ([a, b] ++ r) i h_lt_i
    exact h_not_l (by rw [← h_app.symm.trans h_getElem']; exact List.getElem_mem h_lt_i)
  have h_le : i ≤ l.length := by
    by_contra h
    have h_gt : i ≥ l.length + 1 := by omega
    by_cases h_eq : i = l.length + 1
    · subst h_eq
      have h_b : (l ++ [a, b] ++ r)[l.length + 1]'(by omega) = b := by
        have h_app := getElem_append_of_lt (l ++ [a, b]) r (l.length + 1) (by omega)
        exact h_app.trans (getElem_append_right_eq l a b).2
      exact h_ne (h_b.symm.trans h_getElem).symm
    · have h_ge' : i ≥ l.length + 2 := by omega
      have h_mem_r : a ∈ r := by
        have h_getElem' : ((l ++ [a, b]) ++ r)[i]'h_lt = a := by
          simpa [List.append_assoc] using h_getElem
        set j := i - (l.length + 2) with hj_def
        have hj_lt : j < r.length := by dsimp [j]; omega
        have hj_eq : i = l.length + 2 + j := by dsimp [j]; omega
        have h_app_right := @List.getElem_append_right α (l ++ [a, b]) r ((l ++ [a, b]).length + j) (by omega)
        have h_r : r[j]'hj_lt = a := by
          have h_getElem'' : ((l ++ [a, b]) ++ r)[(l ++ [a, b]).length + j]'(by omega) = a := by
            simpa [← hj_eq, h_len_ab] using h_getElem'
          have h_app := @List.getElem_append_right α (l ++ [a, b]) r ((l ++ [a, b]).length + j) (by omega)
          convert h_app.symm.trans h_getElem'' using 2
          omega
        rw [← h_r]; exact List.getElem_mem hj_lt
      exact h_not_r h_mem_r
  omega

/-- If `a ∉ l`, `a ∉ r`, `a ≠ b`, and `(l ++ [b, a] ++ r)[i] = a`, then `i = l.length + 1`. -/
theorem getElem_eq_of_not_mem_append_two_right {α : Type} [DecidableEq α]
    (l r : List α) (a b : α)
    (h_not_l : a ∉ l) (h_not_r : a ∉ r) (h_ne : a ≠ b)
    (i : Nat) (h_lt : i < (l ++ [b, a] ++ r).length)
    (h_getElem : (l ++ [b, a] ++ r)[i]'h_lt = a) :
    i = l.length + 1 := by
  have h_len_ba : (l ++ [b, a]).length = l.length + 2 := by rw [List.length_append]; rfl
  have h_len_bar : (l ++ [b, a] ++ r).length = l.length + 2 + r.length := by rw [List.length_append, List.length_append]; rfl
  have h_ge : l.length + 1 ≤ i := by
    by_contra h
    have h_lt_i : i ≤ l.length := by omega
    by_cases h_eq : i = l.length
    · subst h_eq
      have h_b : (l ++ [b, a] ++ r)[l.length]'(by omega) = b := by
        have h_app := getElem_append_of_lt (l ++ [b, a]) r l.length (by omega)
        exact h_app.trans (getElem_append_right_eq l b a).1
      exact h_ne ((h_b.symm.trans h_getElem).symm)
    · have h_lt_i' : i < l.length := by omega
      have h_lt_assoc : i < (l ++ ([b, a] ++ r)).length := by
        have h : (l ++ ([b, a] ++ r)).length = (l ++ [b, a] ++ r).length := by
          simp [List.length_append]
        rw [h]; exact h_lt
      have h_getElem' : (l ++ ([b, a] ++ r))[i]'h_lt_assoc = a := by
        simpa [List.append_assoc] using h_getElem
      have h_app := getElem_append_of_lt l ([b, a] ++ r) i h_lt_i'
      exact h_not_l (by rw [← h_app.symm.trans h_getElem']; exact List.getElem_mem h_lt_i')
  have h_le : i ≤ l.length + 1 := by
    by_contra h
    have h_ge' : i ≥ l.length + 2 := by omega
    have h_mem_r : a ∈ r := by
      have h_getElem' : ((l ++ [b, a]) ++ r)[i]'h_lt = a := by
        simpa [List.append_assoc] using h_getElem
      set j := i - (l.length + 2) with hj_def
      have hj_lt : j < r.length := by dsimp [j]; omega
      have hj_eq : i = l.length + 2 + j := by dsimp [j]; omega
      have h_app_right := @List.getElem_append_right α (l ++ [b, a]) r ((l ++ [b, a]).length + j) (by omega)
      have h_r : r[j]'hj_lt = a := by
        have h_getElem'' : ((l ++ [b, a]) ++ r)[(l ++ [b, a]).length + j]'(by omega) = a := by
          simpa [← hj_eq, h_len_ba] using h_getElem'
        have h_app := @List.getElem_append_right α (l ++ [b, a]) r ((l ++ [b, a]).length + j) (by omega)
        convert h_app.symm.trans h_getElem'' using 2
        omega
      rw [← h_r]; exact List.getElem_mem hj_lt
    exact h_not_r h_mem_r
  omega

theorem World.popNextEvent_eraseIdx (w : World) (ev : ScheduledEvent) (w' : World)
    (h : w.popNextEvent = some (ev, w')) :
    ∃ (idx : Nat) (h_idx : idx < w.events.length),
    w'.events = w.events.eraseIdx idx ∧
    ev.targetTick = w.tick ∧ ev ∈ w.events ∧ w.events[idx] = ev := by
  unfold World.popNextEvent at h
  dsimp (config := { zeta := true }) at h
  split at h <;> try contradiction
  · split at h <;> try contradiction
    · rename_i idx ev_found h_find
      rw [Option.some_inj, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      have h_mem := List.mem_of_find?_eq_some h_find
      rw [List.mem_filter] at h_mem
      have h_tick : ev_found.targetTick = w.tick :=
        Nat.eq_of_beq_eq_true (by simpa using h_mem.2)
      have h_ev_mem : ev_found ∈ w.events :=
        List.snd_mem_of_mem_zip (List.range w.events.length) w.events idx ev_found h_mem.1
      have h_idx_lt : idx < w.events.length := by
        obtain ⟨j, h_j_lt, h_j_eq⟩ := List.mem_iff_getElem.mp h_mem.1
        simp [List.zip, List.getElem_zipWith, List.getElem_range] at h_j_lt h_j_eq
        omega
      have h_getElem : w.events[idx] = ev_found := by
        obtain ⟨j, h_j_lt, h_j_eq⟩ := List.mem_iff_getElem.mp h_mem.1
        simp [List.zip, List.getElem_zipWith, List.getElem_range] at h_j_lt h_j_eq
        exact h_j_eq.1.symm ▸ h_j_eq.2
      exact ⟨idx, h_idx_lt, rfl, h_tick, h_ev_mem, h_getElem⟩

/-- Stronger version of `popNextEvent_eraseIdx`: the index is the `find?` result. -/
theorem World.popNextEvent_eraseIdx_find (w : World) (ev : ScheduledEvent) (w' : World)
    (h : w.popNextEvent = some (ev, w')) :
    ∃ (idx : Nat) (h_idx : idx < w.events.length),
    w'.events = w.events.eraseIdx idx ∧
    ev.targetTick = w.tick ∧ w.events[idx] = ev ∧
    ((List.zip (List.range w.events.length) w.events).filter
      (fun x => x.2.targetTick == w.tick)).find?
      (fun x => x.2.priority ==
        ((List.zip (List.range w.events.length) w.events).filter
          (fun x => x.2.targetTick == w.tick)).foldl
          (fun acc x => min acc x.2.priority)
          (((List.zip (List.range w.events.length) w.events).filter
            (fun x => x.2.targetTick == w.tick)).head?.map (fun x => x.2.priority) |>.getD 0))
      = some (idx, ev) := by
  unfold World.popNextEvent at h
  dsimp (config := { zeta := true }) at h
  split at h <;> try contradiction
  · split at h <;> try contradiction
    · rename_i idx ev_found h_find
      rw [Option.some_inj, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      have h_mem := List.mem_of_find?_eq_some h_find
      rw [List.mem_filter] at h_mem
      have h_tick : ev_found.targetTick = w.tick :=
        Nat.eq_of_beq_eq_true (by simpa using h_mem.2)
      have h_idx_lt : idx < w.events.length := by
        obtain ⟨j, h_j_lt, h_j_eq⟩ := List.mem_iff_getElem.mp h_mem.1
        simp [List.zip, List.getElem_zipWith, List.getElem_range] at h_j_lt h_j_eq
        omega
      have h_getElem : w.events[idx] = ev_found := by
        obtain ⟨j, h_j_lt, h_j_eq⟩ := List.mem_iff_getElem.mp h_mem.1
        simp [List.zip, List.getElem_zipWith, List.getElem_range] at h_j_lt h_j_eq
        exact h_j_eq.1.symm ▸ h_j_eq.2
      exact ⟨idx, h_idx_lt, rfl, h_tick, h_getElem, h_find⟩

/-- If no events target `w.tick`, then `processNEvents w n = w`. -/
theorem processNEvents_eq_of_no_events (w : World) (n : Nat)
    (h_no : ∀ ev ∈ w.events, ev.targetTick ≠ w.tick) :
    processNEvents w n = w := by
  induction n generalizing w with
  | zero => rfl
  | succ n' ih =>
    dsimp [processNEvents]
    have h_pop : w.popNextEvent = none := by
      by_contra h_pop_ne
      obtain ⟨⟨ev, w'⟩, h_pop⟩ := Option.ne_none_iff_exists.mp h_pop_ne
      obtain ⟨_, _, _, h_tick, h_mem, _⟩ := World.popNextEvent_eraseIdx w ev w' h_pop.symm
      exact h_no ev h_mem h_tick
    rw [show w.step = none by unfold World.step; rw [h_pop]]

/-- `onNeighborUpdate` new events have priority < 100, given repeater priorities < 100. -/
theorem World.onNeighborUpdate_events_pri (w : World) (id : Nat)
    (h_np : ∀ nd, w.getNode id = some nd → ∀ d p, nd.kind = .repeater d p → p < 100) :
    ∀ ev ∈ (w.onNeighborUpdate id).events, ev ∉ w.events → ev.priority < 100 := by
  cases h_getNode : w.getNode id with
  | none => simp [World.onNeighborUpdate, h_getNode]; intro ev h h'; contradiction
  | some nd =>
    cases h_kind : nd.kind with
    | repeater delay priority =>
      simp [World.onNeighborUpdate, h_getNode, h_kind, World.scheduleEvent_events,
            List.mem_append]
      intro ev h_ev h_new
      cases h_ev with
      | inl h => contradiction
      | inr h =>
        have h_pri : ev.priority = priority := by rw [h]
        rw [h_pri]
        exact h_np nd h_getNode delay priority h_kind
    | observer =>
      simp [World.onNeighborUpdate, h_getNode, h_kind, World.scheduleEvent_events,
            List.mem_append]
      intro ev h_ev h_new
      cases h_ev with
      | inl h => contradiction
      | inr h =>
        have h_pri : ev.priority = 0 := by rw [h]
        omega
    | output name =>
      simp [World.onNeighborUpdate, h_getNode, h_kind, World.logOutput_events]
      intro ev h h'; contradiction
    | input =>
      simp [World.onNeighborUpdate, h_getNode, h_kind]
      intro ev h h'; contradiction

/-- foldl of `onNeighborUpdate`: new events have priority < 100. -/
theorem foldl_onNeighborUpdate_events_pri (l : List Nat) (w : World)
    (h_np : ∀ nid nd, w.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 100) :
    ∀ ev ∈ (l.foldl (fun w' outId => w'.onNeighborUpdate outId) w).events,
      ev ∉ w.events → ev.priority < 100 := by
  induction l generalizing w with
  | nil => intro ev h h'; contradiction
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    set w' := w.onNeighborUpdate hd
    have h_np' : ∀ nid nd, w'.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 100 := by
      intro nid nd h_nd d p h_kind
      rw [World.onNeighborUpdate_getNode] at h_nd
      exact h_np nid nd h_nd d p h_kind
    have h_new := World.onNeighborUpdate_events_pri w hd
      (fun nd h_nd d p h_kind => h_np hd nd h_nd d p h_kind)
    have h_ih := ih w' h_np'
    intro ev h_ev h_notin
    by_cases h_mid : ev ∈ w'.events
    · exact h_new ev h_mid h_notin
    · exact h_ih ev h_ev h_mid

/-- All events in `w.setInput id level` have priority < 100, given that all events in `w`
and all repeater priorities in `w` are < 100. -/
theorem setInput_events_pri (w : World) (id level : Nat)
    (h_pri : ∀ ev ∈ w.events, ev.priority < 100)
    (h_np : ∀ nid nd, w.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 100) :
    ∀ ev ∈ (w.setInput id level).events, ev.priority < 100 := by
  intro ev h_ev
  dsimp (config := { zeta := true }) [World.setInput, World.notifyOutputs] at h_ev
  set w' := w.updateNode id (fun nd => { nd with sigLevel := level })
  have h_events' : w'.events = w.events := World.updateNode_events w id _
  cases h_getNode : w'.getNode id with
  | none =>
    simp [h_getNode, h_events'] at h_ev; exact h_pri ev h_ev
  | some nd =>
    simp only [h_getNode] at h_ev
    have h_np' : ∀ nid nd, w'.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 100 := by
      intro nid nd' h_nd' d p h_kind
      obtain ⟨nd_orig, h_getNode', h_kind_eq⟩ :=
        World.updateNode_getNode_kind w id nid
          (fun nd => { nd with sigLevel := level })
          (fun nd => rfl) nd' h_nd'
      rw [← h_kind_eq] at h_kind
      exact h_np nid nd_orig h_getNode' d p h_kind
    by_cases h_old : ev ∈ w'.events
    · rw [h_events'] at h_old; exact h_pri ev h_old
    · exact foldl_onNeighborUpdate_events_pri nd.outputs w' h_np' ev h_ev h_old

/-- `popNextEvent` preserves the node list. -/
theorem World.popNextEvent_nodes (w : World) :
    ∀ ev w', w.popNextEvent = some (ev, w') → w'.nodes = w.nodes := by
  intro ev w' h
  unfold World.popNextEvent at h
  dsimp (config := { zeta := true }) at h
  split at h <;> try contradiction
  · split at h <;> try contradiction
    · rw [Option.some_inj, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩; rfl

/-- `onScheduledTick`: new events have priority < 100 and target future ticks. -/
theorem World.onScheduledTick_new_events (w : World) (id : Nat)
    (h_np : ∀ nid nd, w.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 100)
    (h_delay : ∀ nid nd, w.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2) :
    (∀ ev ∈ (w.onScheduledTick id).events, ev ∉ w.events → ev.priority < 100) ∧
    (∀ ev ∈ (w.onScheduledTick id).events, ev ∉ w.events → ev.targetTick > w.tick) := by
  dsimp [World.onScheduledTick]
  split
  · exact ⟨by (intro ev h h'; contradiction), by (intro ev h h'; contradiction)⟩
  · rename_i nd; split
    · -- repeater
      rename_i delay priority
      set w' := w.updateNode id (fun nd' => { nd' with sigLevel := if w.getInputSignal id > 0 then 15 else 0 })
      have h_ev' : w'.events = w.events := World.updateNode_events w id _
      have h_tick' : w'.tick = w.tick := World.updateNode_tick w id _
      dsimp [World.notifyOutputs]
      cases h_go : w'.getNode id with
      | none =>
        simp [h_ev']
        exact ⟨by (intro ev h h'; contradiction), by (intro ev h h'; contradiction)⟩
      | some nd' =>
        simp only []
        have h_np' : ∀ nid nd, w'.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 100 := by
          intro nid nd'' h_nd'' d p h_kind
          obtain ⟨nd_orig, h_go', h_keq⟩ :=
            World.updateNode_getNode_kind w id nid (fun nd => { nd with sigLevel := if w.getInputSignal id > 0 then 15 else 0 })
              (fun nd => rfl) nd'' h_nd''
          rw [← h_keq] at h_kind
          exact h_np nid nd_orig h_go' d p h_kind
        have h_delay' : ∀ nid nd, w'.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
          intro nid nd'' h_nd'' d p h_kind
          obtain ⟨nd_orig, h_go', h_keq⟩ :=
            World.updateNode_getNode_kind w id nid (fun nd => { nd with sigLevel := if w.getInputSignal id > 0 then 15 else 0 })
              (fun nd => rfl) nd'' h_nd''
          rw [← h_keq] at h_kind
          exact h_delay nid nd_orig h_go' d p h_kind
        constructor
        · have := foldl_onNeighborUpdate_events_pri nd'.outputs w' h_np'
          rw [h_ev'] at this
          intro ev h_ev h_notin
          exact this ev h_ev h_notin
        · have := foldl_onNeighborUpdate_events_future nd'.outputs w' h_delay'
          rw [h_tick'] at this
          intro ev h_ev h_notin
          rw [← h_ev'] at h_notin
          exact this ev h_ev h_notin
    · -- observer
      set w' := w.updateNode id (fun nd' => { nd' with sigLevel := 15 })
      have h_ev' : w'.events = w.events := World.updateNode_events w id _
      have h_tick' : w'.tick = w.tick := World.updateNode_tick w id _
      dsimp [World.notifyOutputs]
      cases h_go : w'.getNode id with
      | none =>
        simp [h_ev']
        exact ⟨by (intro ev h h'; contradiction), by (intro ev h h'; contradiction)⟩
      | some nd' =>
        simp only []
        have h_np' : ∀ nid nd, w'.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 100 := by
          intro nid nd'' h_nd'' d p h_kind
          obtain ⟨nd_orig, h_go', h_keq⟩ :=
            World.updateNode_getNode_kind w id nid (fun nd => { nd with sigLevel := 15 })
              (fun nd => rfl) nd'' h_nd''
          rw [← h_keq] at h_kind
          exact h_np nid nd_orig h_go' d p h_kind
        have h_delay' : ∀ nid nd, w'.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
          intro nid nd'' h_nd'' d p h_kind
          obtain ⟨nd_orig, h_go', h_keq⟩ :=
            World.updateNode_getNode_kind w id nid (fun nd => { nd with sigLevel := 15 })
              (fun nd => rfl) nd'' h_nd''
          rw [← h_keq] at h_kind
          exact h_delay nid nd_orig h_go' d p h_kind
        constructor
        · have := foldl_onNeighborUpdate_events_pri nd'.outputs w' h_np'
          rw [h_ev'] at this
          intro ev h_ev h_notin
          exact this ev h_ev h_notin
        · have := foldl_onNeighborUpdate_events_future nd'.outputs w' h_delay'
          rw [h_tick'] at this
          intro ev h_ev h_notin
          rw [← h_ev'] at h_notin
          exact this ev h_ev h_notin
    · -- output or input: onScheduledTick returns w unchanged
      exact ⟨by (intro ev h h'; contradiction), by (intro ev h h'; contradiction)⟩

/-- `onNeighborUpdate` appends at most one event at a future tick. -/
theorem World.onNeighborUpdate_events_append (w : World) (id : Nat)
    (h_delay : ∀ nd, w.getNode id = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2) :
    ∃ new_events, (w.onNeighborUpdate id).events = w.events ++ new_events ∧
    ∀ ev ∈ new_events, ev.targetTick > w.tick := by
  cases h_getNode : w.getNode id with
  | none => exact ⟨[], by simp [World.onNeighborUpdate, h_getNode], by simp⟩
  | some nd =>
    cases h_kind : nd.kind with
    | repeater delay priority =>
      unfold World.onNeighborUpdate
      simp only [h_getNode, h_kind, World.scheduleEvent_events]
      have hd_ge2 : delay ≥ 2 := h_delay nd h_getNode delay priority h_kind
      use ([{ targetTick := w.tick + delay, priority := priority, nodeId := id }] : List ScheduledEvent)
      constructor
      · rfl
      · intro ev h_ev; simp [] at h_ev; subst h_ev
        exact Nat.lt_add_of_pos_right (PNat.pos delay)
    | observer =>
      unfold World.onNeighborUpdate
      simp only [h_getNode, h_kind, World.scheduleEvent_events]
      use ([{ targetTick := w.tick + 2, priority := 0, nodeId := id }] : List ScheduledEvent)
      constructor
      · rfl
      · intro ev h_ev; simp [] at h_ev; subst h_ev
        change w.tick + 2 > w.tick; omega
    | output name =>
      unfold World.onNeighborUpdate
      simp only [h_getNode, h_kind, World.logOutput_events]
      use []; constructor <;> simp
    | input =>
      unfold World.onNeighborUpdate
      simp only [h_getNode, h_kind]
      use []; constructor <;> simp

/-- foldl of `onNeighborUpdate` appends events at future ticks. -/
theorem foldl_onNeighborUpdate_events_append (l : List Nat) (w : World)
    (h_delay : ∀ nid nd, w.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2) :
    ∃ new_events, (l.foldl (fun w' outId => w'.onNeighborUpdate outId) w).events = w.events ++ new_events ∧
    ∀ ev ∈ new_events, ev.targetTick > w.tick := by
  induction l generalizing w with
  | nil => exact ⟨[], by simp, by simp⟩
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    have h_delay' : ∀ nid nd, (w.onNeighborUpdate hd).getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
      intro nid nd h_nd d p h_kind
      rw [World.onNeighborUpdate_getNode] at h_nd
      exact h_delay nid nd h_nd d p h_kind
    obtain ⟨new_hd, h_app_hd, h_fut_hd⟩ := World.onNeighborUpdate_events_append w hd
      (fun nd h_nd d p h_kind => h_delay hd nd h_nd d p h_kind)
    obtain ⟨new_tl, h_app_tl, h_fut_tl⟩ := ih (w.onNeighborUpdate hd) h_delay'
    refine ⟨new_hd ++ new_tl, ?_, ?_⟩
    · rw [h_app_tl, h_app_hd, List.append_assoc]
    · intro ev h_ev
      simp [List.mem_append] at h_ev
      cases h_ev with
      | inl h => exact h_fut_hd ev h
      | inr h =>
        have h_tick := World.onNeighborUpdate_tick w hd
        rw [h_tick] at h_fut_tl
        exact h_fut_tl ev h
