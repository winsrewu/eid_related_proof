import BasicProofs.PrefixChain.Part09


open BasicRedstoneSim

/-- If two worlds have the same tick and the same events at the current tick (as a list),
then `popNextEvent` pops the same event from both. -/
theorem popNextEvent_same_of_same_filter (w₁ w₂ : World)
    (h_tick : w₁.tick = w₂.tick)
    (h_filter : w₁.events.filter (fun e => e.targetTick == w₁.tick) =
        w₂.events.filter (fun e => e.targetTick == w₂.tick))
    (ev : ScheduledEvent) (w₁' : World)
    (h_pop₁ : w₁.popNextEvent = some (ev, w₁')) :
    ∃ w₂', w₂.popNextEvent = some (ev, w₂') := by
  unfold World.popNextEvent at h_pop₁ ⊢
  dsimp (config := { zeta := true }) at h_pop₁ ⊢
  set c₁ := (List.zip (List.range w₁.events.length) w₁.events).filter
    (fun x => x.2.targetTick == w₁.tick)
  set c₂ := (List.zip (List.range w₂.events.length) w₂.events).filter
    (fun x => x.2.targetTick == w₂.tick)
  have h_c₁_snd : c₁.map Prod.snd = w₁.events.filter (fun e => e.targetTick == w₁.tick) := by
    dsimp [c₁]
    convert zip_filter_map_snd_eq (List.range w₁.events.length) w₁.events w₁.tick (by simp) using 2
  have h_c₂_snd : c₂.map Prod.snd = w₂.events.filter (fun e => e.targetTick == w₂.tick) := by
    dsimp [c₂]
    convert zip_filter_map_snd_eq (List.range w₂.events.length) w₂.events w₂.tick (by simp) using 2
  have h_c_snd : c₁.map Prod.snd = c₂.map Prod.snd := by
    rw [h_c₁_snd, h_c₂_snd]
    exact h_filter
  -- c₁ ≠ [] because popNextEvent returned some
  have h_c₁_ne : c₁ ≠ [] := by
    intro h
    rw [h] at h_pop₁
    simp only [List.isEmpty, ↓reduceIte] at h_pop₁
    cases h_pop₁
  -- c₂ ≠ [] because c₁.map Prod.snd = c₂.map Prod.snd and c₁ ≠ []
  have h_c₂_ne : c₂ ≠ [] := by
    intro h
    have : c₁.map Prod.snd = [] := by rw [h_c_snd, h]; rfl
    exact h_c₁_ne (List.eq_nil_of_map_eq_nil this)
  -- Helper: find? commutes with map Prod.snd when predicate only depends on snd
  have h_find_map : ∀ (l : List (Nat × ScheduledEvent)) (p : ScheduledEvent → Bool),
      (l.find? (fun x => p x.2)).map Prod.snd = (l.map Prod.snd).find? p := by
    intro l p
    induction l with
    | nil => rfl
    | cons hd tl ih =>
      rw [List.find?_cons, List.map_cons, List.find?_cons]
      split <;> simp_all
  -- foldl-min gives same result for any init (proved on arbitrary lists)
  have h_fold_aux : ∀ (l₁ l₂ : List (Nat × ScheduledEvent)),
      l₁.map Prod.snd = l₂.map Prod.snd →
      ∀ init : Int,
      l₁.foldl (fun acc x => min acc x.2.priority) init =
      l₂.foldl (fun acc x => min acc x.2.priority) init := by
    intro l₁
    induction l₁ with
    | nil =>
      intro l₂ h_map init
      cases l₂ with
      | nil => rfl
      | cons hd tl =>
        rw [List.map_nil, List.map_cons] at h_map
        injection h_map
    | cons hd₁ tl₁ ih =>
      intro l₂ h_map init
      cases l₂ with
      | nil =>
        rw [List.map_cons, List.map_nil] at h_map
        injection h_map
      | cons hd₂ tl₂ =>
        rw [List.map_cons] at h_map
        have h_hd : hd₁.2 = hd₂.2 := by injection h_map with h_hd _
        have h_tl : tl₁.map Prod.snd = tl₂.map Prod.snd := by injection h_map with _ h_tl
        rw [List.foldl_cons, List.foldl_cons, h_hd]
        exact ih tl₂ h_tl (min init hd₂.2.priority)
  have h_fold := h_fold_aux c₁ c₂ h_c_snd
  -- head? gives same priority (proved on arbitrary lists)
  have h_head_aux : ∀ (l₁ l₂ : List (Nat × ScheduledEvent)),
      l₁.map Prod.snd = l₂.map Prod.snd →
      l₁.head?.map (fun x => x.2.priority) = l₂.head?.map (fun x => x.2.priority) := by
    intro l₁
    induction l₁ with
    | nil =>
      intro l₂ h_map
      cases l₂ with
      | nil => rfl
      | cons hd tl =>
        rw [List.map_nil, List.map_cons] at h_map
        injection h_map
    | cons hd₁ tl₁ ih =>
      intro l₂ h_map
      cases l₂ with
      | nil =>
        rw [List.map_cons, List.map_nil] at h_map
        injection h_map
      | cons hd₂ tl₂ =>
        rw [List.map_cons] at h_map
        injection h_map with h_hd h_tl
        simp [h_hd]
  have h_head := h_head_aux c₁ c₂ h_c_snd
  have h_minPri : c₁.foldl (fun acc x => min acc x.2.priority)
      (c₁.head?.map (fun x => x.2.priority) |>.getD 0) =
      c₂.foldl (fun acc x => min acc x.2.priority)
      (c₂.head?.map (fun x => x.2.priority) |>.getD 0) := by
    rw [h_head]; apply h_fold
  -- find? gives same event component
  have h_find_snd : (c₁.find? (fun x => x.2.priority ==
      c₁.foldl (fun acc x => min acc x.2.priority)
        (c₁.head?.map (fun x => x.2.priority) |>.getD 0))).map Prod.snd =
      (c₂.find? (fun x => x.2.priority ==
        c₂.foldl (fun acc x => min acc x.2.priority)
          (c₂.head?.map (fun x => x.2.priority) |>.getD 0))).map Prod.snd := by
    rw [h_minPri]
    set minPri := c₂.foldl (fun acc x => min acc x.2.priority)
      (c₂.head?.map (fun x => x.2.priority) |>.getD 0)
    rw [h_find_map c₁ (fun e => e.priority == minPri)]
    rw [h_find_map c₂ (fun e => e.priority == minPri)]
    rw [h_c_snd]
  -- Now extract from h_pop₁
  have h_c₁_not_empty : ¬c₁.isEmpty = true := by
    intro h_empty; cases c₁ <;> simp_all [List.isEmpty]
  simp only [h_c₁_not_empty] at h_pop₁
  split at h_pop₁
  · cases h_pop₁
  · -- isEmpty ≠ true, so the match result determines the output
    split at h_pop₁ <;> try { cases h_pop₁ }
    -- some (idx₁, ev₁) case
    rename_i idx₁ ev₁ h_find₁
    -- h_pop₁ : some (ev₁, ...) = some (ev, w₁')
    have h_ev_eq : ev₁ = ev := by
      injection h_pop₁ with h_pair
      injection h_pair with h_ev _
    rw [h_ev_eq] at h_find₁
    -- h_find₁ now mentions ev instead of ev₁
    have h_find₂_ev : ∃ idx₂,
          c₂.find? (fun x => x.2.priority ==
            c₂.foldl (fun acc x => min acc x.2.priority)
              (c₂.head?.map (fun x => x.2.priority) |>.getD 0)) =
            some (idx₂, ev) := by
        have h_map_eq : (c₁.find? (fun x => x.2.priority ==
            c₁.foldl (fun acc x => min acc x.2.priority)
              (c₁.head?.map (fun x => x.2.priority) |>.getD 0))).map Prod.snd = some ev := by
          rw [h_find₁]; rfl
        have h_c₂_map : (c₂.find? (fun x => x.2.priority ==
            c₂.foldl (fun acc x => min acc x.2.priority)
              (c₂.head?.map (fun x => x.2.priority) |>.getD 0))).map Prod.snd = some ev := by
          rw [← h_find_snd, h_map_eq]
        cases h_f₂ : c₂.find? (fun x => x.2.priority ==
            c₂.foldl (fun acc x => min acc x.2.priority)
              (c₂.head?.map (fun x => x.2.priority) |>.getD 0)) with
        | none => simp [h_f₂] at h_c₂_map
        | some p =>
          rcases p with ⟨idx₂, ev₂⟩
          rw [h_f₂] at h_c₂_map
          simp at h_c₂_map
          -- h_c₂_map : ev₂ = ev; goal generalized to ∃ idx₂, some (idx₂, ev₂) = some (idx₂, ev)
          rw [h_c₂_map]
          exact ⟨idx₂, rfl⟩
    obtain ⟨idx₂, h_f₂⟩ := h_find₂_ev
    simp only [h_f₂]
    by_cases h_empty : c₂.isEmpty = true
    · exfalso
      apply h_c₂_ne
      rw [← List.isEmpty_iff]
      exact h_empty
    · exact ⟨{w₂ with events := w₂.events.eraseIdx idx₂}, by simp [h_empty]⟩

/-- Filtering commutes with eraseIdx: erasing an element that passes the filter
and then filtering equals filtering and then erasing at the corresponding position. -/
theorem List.filter_eraseIdx_comm {α : Type} (l : List α) (p : α → Bool)
    (i : Nat) (h_i : i < l.length) (h_p : p l[i] = true) :
    (l.eraseIdx i).filter p = (l.filter p).eraseIdx ((l.take i).filter p).length := by
  revert i h_i h_p
  induction l with
  | nil => intro i h_i; simp at h_i
  | cons hd tl ih =>
    intro i h_i h_p
    cases i with
    | zero =>
      have h_hd : p hd = true := by simpa using h_p
      simp [List.eraseIdx, List.filter, h_hd, List.take]
    | succ i' =>
      have h_i' : i' < tl.length := by simp at h_i; omega
      have h_p' : p tl[i'] = true := by simpa using h_p
      have h_ih := ih i' h_i' h_p'
      by_cases h_hd : p hd = true
      · simp [List.eraseIdx, List.filter, h_hd, List.take, h_ih]
      · simp [List.eraseIdx, List.filter, h_hd, List.take, h_ih]

/-- If two lists have the same filter, and we erase elements that pass the filter
at positions with the same take-filter length, the resulting filters are equal. -/
theorem List.filter_eraseIdx_same {α : Type} (l₁ l₂ : List α) (p : α → Bool)
    (i₁ i₂ : Nat) (h_filter : l₁.filter p = l₂.filter p)
    (h_i₁ : i₁ < l₁.length) (h_i₂ : i₂ < l₂.length)
    (h_p₁ : p l₁[i₁] = true) (h_p₂ : p l₂[i₂] = true)
    (h_len : ((l₁.take i₁).filter p).length = ((l₂.take i₂).filter p).length) :
    (l₁.eraseIdx i₁).filter p = (l₂.eraseIdx i₂).filter p := by
  rw [List.filter_eraseIdx_comm l₁ p i₁ h_i₁ h_p₁,
      List.filter_eraseIdx_comm l₂ p i₂ h_i₂ h_p₂,
      h_filter, h_len]

/-- The element at position `i` in `l` appears at position `((l.take i).filter p).length` in `l.filter p`. -/
theorem filter_getElem_of_take_filter_length {α : Type} (l : List α) (p : α → Bool) (i : Nat)
    (h_i : i < l.length) (h_p : p l[i] = true) :
    ∃ h : ((l.take i).filter p).length < (l.filter p).length,
    (l.filter p)[((l.take i).filter p).length] = l[i] := by
  revert i h_i h_p
  induction l with
  | nil => intro i h_i; simp at h_i
  | cons hd tl ih =>
    intro i h_i h_p
    cases i with
    | zero =>
      have h_hd : p hd = true := by simpa using h_p
      have h_f : (hd :: tl).filter p = hd :: tl.filter p := by simp [List.filter, h_hd]
      have h_lt : (((hd :: tl).take 0).filter p).length < ((hd :: tl).filter p).length := by
        have : (hd :: tl).take 0 = ([] : List α) := rfl
        simp [this, h_f]
      refine ⟨h_lt, ?_⟩
      simp [List.take, h_f]
    | succ i' =>
      have h_i' : i' < tl.length := by simp at h_i; omega
      have h_p' : p tl[i'] = true := by simpa using h_p
      obtain ⟨h_ih_lt, h_ih_eq⟩ := ih i' h_i' h_p'
      by_cases h_hd : p hd = true
      · have h_f : (hd :: tl).filter p = hd :: tl.filter p := by simp [List.filter, h_hd]
        have h_take_f : ((hd :: tl).take (i' + 1)).filter p = hd :: (tl.take i').filter p := by
          simp [List.take, h_hd]
        have h_lt : (((hd :: tl).take (i' + 1)).filter p).length < ((hd :: tl).filter p).length := by
          rw [h_f, h_take_f]; simp; omega
        refine ⟨h_lt, ?_⟩
        simp_all [List.getElem_cons_succ]
      · have h_f : (hd :: tl).filter p = tl.filter p := by simp [List.filter, h_hd]
        have h_take_f : ((hd :: tl).take (i' + 1)).filter p = (tl.take i').filter p := by
          simp [List.take, h_hd]
        have h_lt : (((hd :: tl).take (i' + 1)).filter p).length < ((hd :: tl).filter p).length := by
          rw [h_f, h_take_f]; exact h_ih_lt
        refine ⟨h_lt, ?_⟩
        simp_all [List.getElem_cons_succ]

/-- The position of `(i, l[i])` in the zip-filter equals the take-filter length. -/
theorem zip_filter_position_eq_take_filter_length (l : List ScheduledEvent) (t : Nat) (i : Nat)
    (h_i : i < l.length) (h_t : (l[i].targetTick == t) = true) :
    let c := (List.zip (List.range l.length) l).filter (fun x => x.2.targetTick == t)
    let k := ((l.take i).filter (fun e => e.targetTick == t)).length
    ∃ h : k < c.length, c[k] = (i, l[i]) := by
  set q := fun x : Nat × ScheduledEvent => x.2.targetTick == t
  set p := fun e : ScheduledEvent => e.targetTick == t
  set zl := List.zip (List.range l.length) l
  have h_zl_len : zl.length = l.length := by dsimp [zl]; simp
  -- zl[i] = (i, l[i])
  have h_zl_get : zl[i] = (i, l[i]) := by
    dsimp [zl]; simp [List.getElem_range]
  -- q (zl[i]) = true
  have h_q : q (zl[i]) = true := by rw [h_zl_get]; simpa [q] using h_t
  -- zl.take i = zip (range i) (l.take i)
  have h_zip_take : zl.take i = List.zip (List.range i) (l.take i) := by
    dsimp [zl]
    ext n
    by_cases hn : n < i <;> by_cases hn' : n < l.length <;>
      simp [List.getElem_take, List.getElem_range, hn, hn']
  -- ((zl.take i).filter q).length = ((l.take i).filter p).length
  have h_take_filter_len : ((zl.take i).filter q).length = ((l.take i).filter p).length := by
    rw [h_zip_take]
    have h_map := zip_filter_map_snd_eq (List.range i) (l.take i) t
      (by simp [List.length_range, List.length_take]; omega)
    have h_eq : ((List.zip (List.range i) (l.take i)).filter q).map Prod.snd =
        (l.take i).filter p := by simpa [q, p] using h_map
    rw [← List.length_map, h_eq]
  -- Apply filter_getElem_of_take_filter_length to zl with q
  have h_k := filter_getElem_of_take_filter_length zl q i (by rw [h_zl_len]; exact h_i) h_q
  obtain ⟨h_k_lt, h_k_get⟩ := h_k
  have h_k_lt' : ((l.take i).filter p).length < (zl.filter q).length := by
    rwa [← h_take_filter_len]
  have h_k_get' : (zl.filter q)[((l.take i).filter p).length] = zl[i] := by
    simpa [h_take_filter_len.symm] using h_k_get
  exact ⟨h_k_lt', by rwa [h_zl_get] at h_k_get'⟩
/-- Popping the same event from worlds with the same current-tick filter
    gives worlds with the same current-tick filter. -/
theorem popNextEvent_filter_eq (w₁ w₂ : World)
    (h_tick : w₁.tick = w₂.tick)
    (h_filter : w₁.events.filter (fun e => e.targetTick == w₁.tick) =
        w₂.events.filter (fun e => e.targetTick == w₂.tick))
    (ev : ScheduledEvent) (w₁' w₂' : World)
    (h_pop₁ : w₁.popNextEvent = some (ev, w₁'))
    (h_pop₂ : w₂.popNextEvent = some (ev, w₂')) :
    w₁'.events.filter (fun e => e.targetTick == w₁'.tick) =
    w₂'.events.filter (fun e => e.targetTick == w₂'.tick) := by
  have h_tick₁ : w₁'.tick = w₁.tick := World.popNextEvent_tick _ _ _ h_pop₁
  have h_tick₂ : w₂'.tick = w₂.tick := World.popNextEvent_tick _ _ _ h_pop₂
  rw [h_tick₁, h_tick₂, h_tick]
  obtain ⟨idx₁, h_idx₁, h_erase₁, h_tick_ev₁, h_get₁, h_find₁⟩ :=
    World.popNextEvent_eraseIdx_find w₁ ev w₁' h_pop₁
  obtain ⟨idx₂, h_idx₂, h_erase₂, h_tick_ev₂, h_get₂, h_find₂⟩ :=
    World.popNextEvent_eraseIdx_find w₂ ev w₂' h_pop₂
  set p := (fun e : ScheduledEvent => e.targetTick == w₁.tick)
  have h_p₁ : p w₁.events[idx₁] = true := by dsimp [p]; simp [h_get₁, h_tick_ev₁]
  have h_p₂ : p w₂.events[idx₂] = true := by dsimp [p]; simp [h_get₂, h_tick_ev₂, h_tick]
  have h_filter_p : w₁.events.filter p = w₂.events.filter p := by
    dsimp [p]; convert h_filter using 2 ; ext e ; simp [h_tick]
  -- Prove take-filter lengths are equal via find? uniqueness
  have h_k_eq : ((w₁.events.take idx₁).filter p).length = ((w₂.events.take idx₂).filter p).length := by
    set k₁ := ((w₁.events.take idx₁).filter p).length
    set k₂ := ((w₂.events.take idx₂).filter p).length
    -- Set up zip-filters
    set c₁ := (List.zip (List.range w₁.events.length) w₁.events).filter
      (fun x => x.2.targetTick == w₁.tick)
    set c₂ := (List.zip (List.range w₂.events.length) w₂.events).filter
      (fun x => x.2.targetTick == w₂.tick)
    set minPri₁ := c₁.foldl (fun acc x => min acc x.2.priority)
      (c₁.head?.map (fun x => x.2.priority) |>.getD 0)
    set minPri₂ := c₂.foldl (fun acc x => min acc x.2.priority)
      (c₂.head?.map (fun x => x.2.priority) |>.getD 0)
    have h_find₁' : c₁.find? (fun x => x.2.priority == minPri₁) = some (idx₁, ev) := by
      rw [← h_find₁]
    have h_find₂' : c₂.find? (fun x => x.2.priority == minPri₂) = some (idx₂, ev) := by
      rw [← h_find₂]
    -- c₁.map Prod.snd = c₂.map Prod.snd
    have h_c₁_snd : c₁.map Prod.snd = w₁.events.filter p := by
      dsimp [c₁, p]; convert zip_filter_map_snd_eq (List.range w₁.events.length) w₁.events w₁.tick (by simp) using 2
    have h_c₂_snd : c₂.map Prod.snd = w₂.events.filter (fun e => e.targetTick == w₂.tick) := by
      dsimp [c₂]; convert zip_filter_map_snd_eq (List.range w₂.events.length) w₂.events w₂.tick (by simp) using 2
    have h_snd_eq : c₁.map Prod.snd = c₂.map Prod.snd := by
      rw [h_c₁_snd, h_c₂_snd]; dsimp [p]; convert h_filter using 2
    -- minPri₁ = minPri₂ (foldl depends only on second components)
    have h_minPri_eq : minPri₁ = minPri₂ := by
      dsimp [minPri₁, minPri₂]
      -- First prove foldl agrees for any init
      have h_fold_same : ∀ (l₁ l₂ : List (Nat × ScheduledEvent)) (init : Int),
          l₁.map Prod.snd = l₂.map Prod.snd →
          l₁.foldl (fun acc x => min acc x.2.priority) init =
          l₂.foldl (fun acc x => min acc x.2.priority) init := by
        intro l₁
        induction l₁ with
        | nil =>
          intro l₂ init h
          cases l₂ with
          | nil => simp
          | cons => simp [List.map] at h
        | cons hd₁ tl₁ ih =>
          intro l₂ init h
          cases l₂ with
          | nil => simp [List.map] at h
          | cons hd₂ tl₂ =>
            simp [List.map] at h
            have h_hd : hd₁.2 = hd₂.2 := by simpa using h.1
            show tl₁.foldl _ (min init hd₁.2.priority) = tl₂.foldl _ (min init hd₂.2.priority)
            rw [h_hd]
            exact ih tl₂ _ (by simpa using h.2)
      -- head? also agrees
      have h_head_same : c₁.head?.map (fun x => x.2.priority) = c₂.head?.map (fun x => x.2.priority) := by
        revert h_snd_eq
        cases c₁ <;> cases c₂ <;> intro h <;> simp at h ⊢ ; (cases h ; simp_all)
      have h_fold := h_fold_same c₁ c₂ (c₁.head?.map (fun x => x.2.priority) |>.getD 0) h_snd_eq
      rw [h_fold, congrArg (·.getD 0) h_head_same]
    -- find? positions are the same
    obtain ⟨f₁, h_f₁_lt, h_f₁_get, h_f₁_first⟩ :=
      List.find?_eq_some_getElem (fun x => x.2.priority == minPri₁) c₁ (idx₁, ev) h_find₁'
    obtain ⟨f₂, h_f₂_lt, h_f₂_get, h_f₂_first⟩ :=
      List.find?_eq_some_getElem (fun x => x.2.priority == minPri₂) c₂ (idx₂, ev) h_find₂'
    -- f₁ = f₂: predicates agree at corresponding positions
    have h_f_eq : f₁ = f₂ := by
      have h_len_eq : c₁.length = c₂.length := by
        have h₁ := List.length_map (f := Prod.snd) (as := c₁)
        have h₂ := List.length_map (f := Prod.snd) (as := c₂)
        rw [← h₁, ← h₂, h_snd_eq]
      have h_pred_agree : ∀ (i : Nat) (hi₁ : i < c₁.length) (hi₂ : i < c₂.length),
          (c₁[i].2.priority == minPri₁) = (c₂[i].2.priority == minPri₂) := by
        intro i hi₁ hi₂
        have h_snd : c₁[i].2 = c₂[i].2 := by
          have hi₁' : i < (c₁.map Prod.snd).length := by rw [List.length_map]; exact hi₁
          have hi₂' : i < (c₂.map Prod.snd).length := by rw [List.length_map]; exact hi₂
          have h₁ := @List.getElem_map _ _ Prod.snd c₁ i hi₁'
          have h₂ := @List.getElem_map _ _ Prod.snd c₂ i hi₂'
          rw [← h₁, ← h₂]
          simp [h_snd_eq]
        rw [h_minPri_eq, h_snd]
      by_contra h_ne
      have h_lt : f₁ < f₂ ∨ f₂ < f₁ := by omega
      cases h_lt with
      | inl h_lt =>
        -- f₁ < f₂: c₁[f₁] satisfies pred, so c₂[f₁] does too, contradicting h_f₂_first
        have h_f₁_pred : (c₁[f₁].2.priority == minPri₁) = true := by
          rw [h_f₁_get]; simpa using List.find?_predicate_true _ _ _ h_find₁'
        have h_f₁_lt₂ : f₁ < c₂.length := by rw [← h_len_eq]; exact h_f₁_lt
        have h_f₂_at_f₁ : (c₂[f₁].2.priority == minPri₂) = true := by
          have := h_pred_agree f₁ h_f₁_lt h_f₁_lt₂
          rwa [← this]
        have := h_f₂_first f₁ (by omega)
        rw [h_f₂_at_f₁] at this; contradiction
      | inr h_lt =>
        -- f₂ < f₁: c₂[f₂] satisfies pred, so c₁[f₂] does too, contradicting h_f₁_first
        have h_f₂_pred : (c₂[f₂].2.priority == minPri₂) = true := by
          rw [h_f₂_get]; simpa using List.find?_predicate_true _ _ _ h_find₂'
        have h_f₂_lt₁ : f₂ < c₁.length := by rw [h_len_eq]; exact h_f₂_lt
        have h_f₁_at_f₂ : (c₁[f₂].2.priority == minPri₁) = true := by
          have := h_pred_agree f₂ h_f₂_lt₁ h_f₂_lt
          rwa [this]
        have := h_f₁_first f₂ (by omega)
        rw [h_f₁_at_f₂] at this; contradiction
    -- k₁ = f₁ and k₂ = f₂ via zip_filter_position_eq_take_filter_length
    have h_p₁' : (w₁.events[idx₁].targetTick == w₁.tick) = true := by simpa [p] using h_p₁
    have h_p₂' : (w₂.events[idx₂].targetTick == w₂.tick) = true := by simpa [p, h_tick] using h_p₂
    obtain ⟨h_k₁_lt, h_k₁_get⟩ := zip_filter_position_eq_take_filter_length w₁.events w₁.tick idx₁ h_idx₁ h_p₁'
    obtain ⟨h_k₂_lt, h_k₂_get⟩ := zip_filter_position_eq_take_filter_length w₂.events w₂.tick idx₂ h_idx₂ h_p₂'
    -- f₁ = k₁ and f₂ = k₂ via Nodup
    have h_f₁_eq_k₁ : f₁ = k₁ := by
      have h_nodup : (c₁.map Prod.fst).Nodup := by
        dsimp [c₁]
        have h_sub := (List.filter_sublist (p := fun x : Nat × ScheduledEvent =>
          x.2.targetTick == w₁.tick) (l := List.zip (List.range w₁.events.length) w₁.events)).map Prod.fst
        have h_eq : (List.zip (List.range w₁.events.length) w₁.events).map Prod.fst =
            List.range w₁.events.length := by
          ext i
          by_cases h : i < w₁.events.length
          · simp [h]
          · simp [h]
        rw [h_eq] at h_sub; exact h_sub.nodup List.nodup_range
      have h_k₁_lt' : k₁ < c₁.length := by dsimp [k₁, c₁]; exact h_k₁_lt
      have h_c₁_k₁ : c₁[k₁]'h_k₁_lt' = (idx₁, w₁.events[idx₁]) := by
        dsimp [c₁, k₁] at h_k₁_get ⊢; simpa using h_k₁_get
      have hf₁ : f₁ < (c₁.map Prod.fst).length := by rw [List.length_map]; exact h_f₁_lt
      have hk₁ : k₁ < (c₁.map Prod.fst).length := by rw [List.length_map]; exact h_k₁_lt'
      have h_eq : (c₁.map Prod.fst)[f₁]'hf₁ = (c₁.map Prod.fst)[k₁]'hk₁ := by
        have := @List.getElem_map _ _ Prod.fst c₁ f₁ hf₁
        have := @List.getElem_map _ _ Prod.fst c₁ k₁ hk₁
        simp_all
      exact (List.Nodup.getElem_inj_iff h_nodup).mp h_eq
    have h_f₂_eq_k₂ : f₂ = k₂ := by
      have h_nodup : (c₂.map Prod.fst).Nodup := by
        dsimp [c₂]
        have h_sub := (List.filter_sublist (p := fun x : Nat × ScheduledEvent =>
          x.2.targetTick == w₂.tick) (l := List.zip (List.range w₂.events.length) w₂.events)).map Prod.fst
        have h_eq : (List.zip (List.range w₂.events.length) w₂.events).map Prod.fst =
            List.range w₂.events.length := by
          ext i
          by_cases h : i < w₂.events.length
          · simp [h]
          · simp [h]
        rw [h_eq] at h_sub; exact h_sub.nodup List.nodup_range
      have h_k₂_lt' : k₂ < c₂.length := by dsimp [k₂, c₂, p]; simpa [h_tick] using h_k₂_lt
      have h_c₂_k₂ : c₂[k₂]'h_k₂_lt' = (idx₂, w₂.events[idx₂]) := by
        dsimp [c₂, k₂, p] at h_k₂_get ⊢; simpa [h_tick] using h_k₂_get
      have hf₂ : f₂ < (c₂.map Prod.fst).length := by rw [List.length_map]; exact h_f₂_lt
      have hk₂ : k₂ < (c₂.map Prod.fst).length := by rw [List.length_map]; exact h_k₂_lt'
      have h_eq : (c₂.map Prod.fst)[f₂]'hf₂ = (c₂.map Prod.fst)[k₂]'hk₂ := by
        have := @List.getElem_map _ _ Prod.fst c₂ f₂ hf₂
        have := @List.getElem_map _ _ Prod.fst c₂ k₂ hk₂
        simp_all
      exact (List.Nodup.getElem_inj_iff h_nodup).mp h_eq
    rw [← h_f₁_eq_k₁, ← h_f₂_eq_k₂, h_f_eq]
  have h_congr := List.filter_eraseIdx_same w₁.events w₂.events p idx₁ idx₂ h_filter_p
    h_idx₁ h_idx₂ h_p₁ h_p₂ h_k_eq
  rw [h_erase₁, h_erase₂]
  dsimp [p] at h_congr ⊢
  convert h_congr using 2 <;> ext e <;> simp [h_tick]


/-- If two worlds have the same nodes, same tick, and same events at the current tick,
then `stepUntilNextTick` gives the same nodes. -/
theorem stepUntilNextTick_nodes_congr (w₁ w₂ : World)
    (h_nodes : w₁.nodes = w₂.nodes)
    (h_tick : w₁.tick = w₂.tick)
    (h_filter : w₁.events.filter (fun e => e.targetTick == w₁.tick) =
        w₂.events.filter (fun e => e.targetTick == w₂.tick))
    (h_delay : ∀ nid nd, w₁.getNode nid = some nd → ∀ d p,
        nd.kind = .repeater d p → d ≥ 2) :
    w₁.stepUntilNextTick.nodes = w₂.stepUntilNextTick.nodes := by
  revert h_delay h_filter h_tick h_nodes w₂
  induction w₁ using World.stepUntilNextTick.induct with
  | case1 w₁ h_step₁ =>
    intro w₂ h_nodes h_tick h_filter h_delay
    have h_pop₁ : w₁.popNextEvent = none := by
      dsimp [World.step] at h_step₁
      cases h_pop : w₁.popNextEvent with
      | none => rfl
      | some p => simp [h_pop] at h_step₁
    have h_no₁ : ∀ ev ∈ w₁.events, ev.targetTick ≠ w₁.tick :=
      popNextEvent_none_no_events w₁ h_pop₁
    have h_no₂ : ∀ ev ∈ w₂.events, ev.targetTick ≠ w₂.tick := by
      intro ev h_ev h_eq
      have h_in : ev ∈ w₂.events.filter (fun e => e.targetTick == w₂.tick) := by
        simp [List.mem_filter, h_ev, h_eq]
      have h_in' : ev ∈ w₁.events.filter (fun e => e.targetTick == w₁.tick) := by
        rwa [← h_filter] at h_in
      have h_eq' : ev.targetTick = w₁.tick := by rwa [h_tick]
      exact h_no₁ ev (List.mem_of_mem_filter h_in') h_eq'
    have h_step₂ : w₂.step = none := by
      dsimp [World.step]
      cases h_pop : w₂.popNextEvent with
      | none => rfl
      | some p =>
        rcases p with ⟨ev, w'⟩
        have := popNextEvent_at_tick w₂ ev w' h_pop
        obtain ⟨_, _, _, _, h_mem, _⟩ := World.popNextEvent_eraseIdx w₂ ev w' h_pop
        exfalso; exact h_no₂ ev h_mem this
    rw [stepUntilNextTick_of_step_none w₁ h_step₁, stepUntilNextTick_of_step_none w₂ h_step₂]
    exact h_nodes
  | case2 w₁ w₁' h_step₁ ih =>
    intro w₂ h_nodes h_tick h_filter h_delay
    have h_sunt₁ : w₁.stepUntilNextTick = w₁'.stepUntilNextTick := by
      rw [World.stepUntilNextTick, h_step₁]
    rw [h_sunt₁]
    dsimp [World.step] at h_step₁
    cases h_pop₁ : w₁.popNextEvent with
    | none => simp [h_pop₁] at h_step₁
    | some p =>
      rcases p with ⟨ev, w₁_pop⟩
      simp [h_pop₁] at h_step₁
      subst h_step₁
      -- w₁' = w₁_pop.onScheduledTick ev.nodeId
      obtain ⟨w₂_pop, h_pop₂⟩ := popNextEvent_same_of_same_filter w₁ w₂ h_tick h_filter ev w₁_pop h_pop₁
      have h_step₂ : w₂.step = some (w₂_pop.onScheduledTick ev.nodeId) := by
        dsimp [World.step]; rw [h_pop₂]
      have h_sunt₂ : w₂.stepUntilNextTick = (w₂_pop.onScheduledTick ev.nodeId).stepUntilNextTick := by
        rw [World.stepUntilNextTick, h_step₂]
      rw [h_sunt₂]
      -- Show nodes equal after onScheduledTick
      have h_pop_nodes₁ : w₁_pop.nodes = w₁.nodes := World.popNextEvent_nodes w₁ ev w₁_pop h_pop₁
      have h_pop_nodes₂ : w₂_pop.nodes = w₂.nodes := World.popNextEvent_nodes w₂ ev w₂_pop h_pop₂
      have h_nodes_pop : w₁_pop.nodes = w₂_pop.nodes := by rw [h_pop_nodes₁, h_pop_nodes₂, h_nodes]
      have h_tick_pop : w₁_pop.tick = w₂_pop.tick := by
        rw [World.popNextEvent_tick w₁ ev w₁_pop h_pop₁,
            World.popNextEvent_tick w₂ ev w₂_pop h_pop₂, h_tick]
      have h_getNode_all : ∀ nid, w₁_pop.getNode nid = w₂_pop.getNode nid := by
        intro nid; dsimp [World.getNode]; rw [h_nodes_pop]
      have h_nodes' : (w₁_pop.onScheduledTick ev.nodeId).nodes =
          (w₂_pop.onScheduledTick ev.nodeId).nodes := by
        dsimp [World.onScheduledTick]
        rw [h_getNode_all ev.nodeId]
        split
        · exact h_nodes_pop
        · rename_i nd; split
          · -- repeater
            have h_gis : w₁_pop.getInputSignal ev.nodeId = w₂_pop.getInputSignal ev.nodeId := by
              dsimp [World.getInputSignal]
              rw [h_getNode_all ev.nodeId]
              split
              · rfl
              · rename_i nd'
                congr 1
                ext maxSig inputId
                rw [h_getNode_all inputId]
            rw [h_gis]
            rw [World.notifyOutputs_nodes, World.notifyOutputs_nodes]
            dsimp [World.updateNode]; rw [h_nodes_pop]
          · -- observer
            rw [World.notifyOutputs_nodes, World.notifyOutputs_nodes]
            dsimp [World.updateNode]; rw [h_nodes_pop]
          · -- output/input
            exact h_nodes_pop
      have h_tick' : (w₁_pop.onScheduledTick ev.nodeId).tick =
          (w₂_pop.onScheduledTick ev.nodeId).tick := by
        rw [World.onScheduledTick_tick, World.onScheduledTick_tick, h_tick_pop]
      -- Filter equality after onScheduledTick
      have h_filter' : (w₁_pop.onScheduledTick ev.nodeId).events.filter
          (fun e => e.targetTick == (w₁_pop.onScheduledTick ev.nodeId).tick) =
          (w₂_pop.onScheduledTick ev.nodeId).events.filter
          (fun e => e.targetTick == (w₂_pop.onScheduledTick ev.nodeId).tick) := by
        rw [h_tick']
        have h_delay_pop₁ : ∀ nid nd, w₁_pop.getNode nid = some nd → ∀ d p,
            nd.kind = .repeater d p → d ≥ 2 := by
          intro nid nd h_nd
          have : w₁.getNode nid = some nd := by
            dsimp [World.getNode, World.popNextEvent] at h_nd ⊢
            rwa [← h_pop_nodes₁]
          exact h_delay nid nd this
        have h_delay_pop₂ : ∀ nid nd, w₂_pop.getNode nid = some nd → ∀ d p,
            nd.kind = .repeater d p → d ≥ 2 := by
          intro nid nd h_nd
          have : w₁.getNode nid = some nd := by
            dsimp [World.getNode] at h_nd ⊢
            rw [← h_pop_nodes₁, h_nodes_pop]
            exact h_nd
          exact h_delay nid nd this
        obtain ⟨new₁, h_app₁, h_fut₁⟩ := World.onScheduledTick_events_append w₁_pop ev.nodeId h_delay_pop₁
        obtain ⟨new₂, h_app₂, h_fut₂⟩ := World.onScheduledTick_events_append w₂_pop ev.nodeId h_delay_pop₂
        rw [h_app₁, h_app₂, List.filter_append, List.filter_append]
        have h_tick₂ : (w₂_pop.onScheduledTick ev.nodeId).tick = w₂_pop.tick :=
          World.onScheduledTick_tick _ _
        simp only [h_tick₂]
        have h_e₁ : new₁.filter (fun e => e.targetTick == w₂_pop.tick) = [] := by
          apply List.filter_eq_nil_iff.mpr; intro e he; have := h_fut₁ e he
          rw [← h_tick_pop]; simp; omega
        have h_e₂ : new₂.filter (fun e => e.targetTick == w₂_pop.tick) = [] := by
          apply List.filter_eq_nil_iff.mpr; intro e he; have := h_fut₂ e he; simp; omega
        rw [h_e₁, h_e₂, List.append_nil, List.append_nil]
        -- w₁_pop.events.filter (...) = w₂_pop.events.filter (...)
        -- Both popped the same event from worlds with the same filter
        -- Use filter_eraseIdx_comm + filter_eraseIdx_same
        have h_tw : w₂_pop.tick = w₁.tick := by
          rw [World.popNextEvent_tick w₂ ev w₂_pop h_pop₂, h_tick]
        set p := (fun e : ScheduledEvent => e.targetTick == w₁.tick)
        obtain ⟨idx₁, h_idx₁, h_erase₁, h_tick_ev₁, h_get₁, h_find₁_full⟩ := World.popNextEvent_eraseIdx_find w₁ ev w₁_pop h_pop₁
        obtain ⟨idx₂, h_idx₂, h_erase₂, h_tick_ev₂, h_get₂, h_find₂_full⟩ := World.popNextEvent_eraseIdx_find w₂ ev w₂_pop h_pop₂
        have h_p₁ : p w₁.events[idx₁] = true := by dsimp [p]; simp [h_get₁, h_tick_ev₁]
        have h_p₂ : p w₂.events[idx₂] = true := by dsimp [p]; simp [h_get₂, h_tick_ev₂, h_tick]
        have h_filter_p : w₁.events.filter p = w₂.events.filter p := by
          dsimp [p]; convert h_filter using 2 ; ext e ; simp [h_tick]
        -- Show take-filter lengths are the same
        -- Both equal the position of ev in the filter
        obtain ⟨h_k₁_lt, h_k₁_eq⟩ := filter_getElem_of_take_filter_length w₁.events p idx₁ h_idx₁ h_p₁
        rw [h_get₁] at h_k₁_eq -- h_k₁_eq : (w₁.events.filter p)[k₁] = ev
        obtain ⟨h_k₂_lt, h_k₂_eq⟩ := filter_getElem_of_take_filter_length w₂.events p idx₂ h_idx₂ h_p₂
        rw [h_get₂] at h_k₂_eq -- h_k₂_eq : (w₂.events.filter p)[k₂] = ev
        -- ev has minimum priority among all events at current tick
        have h_min₁ := popNextEvent_min_priority w₁ ev w₁_pop h_pop₁
        have h_min₂ := popNextEvent_min_priority w₂ ev w₂_pop h_pop₂
        -- Show k₁ = k₂: both are the position of ev in the same filter
        -- ev is the first event with minimum priority (by find? in popNextEvent)
        have h_k_eq : ((w₁.events.take idx₁).filter p).length = ((w₂.events.take idx₂).filter p).length := by
          set k₁ := ((w₁.events.take idx₁).filter p).length
          set k₂ := ((w₂.events.take idx₂).filter p).length
          by_contra h_ne
          have h_lt : k₁ < k₂ ∨ k₂ < k₁ := by omega
          cases h_lt with
          | inl h_lt =>
            -- k₁ < k₂: show contradiction
            -- (w₂.events.filter p)[k₁] = ev (from h_filter_p and h_k₁_eq)
            have h_at_k₁ : (w₂.events.filter p)[k₁] = ev := by
              simpa [h_filter_p.symm] using h_k₁_eq
            -- ev.priority ≤ all priorities in filter (by h_min₂)
            -- ev is the FIRST with min priority in w₂'s filter (by find? in popNextEvent)
            -- Extract find? result from h_pop₂
            have h_pop₂_orig : World.popNextEvent w₂ = some (ev, w₂_pop) := h_pop₂
            unfold World.popNextEvent at h_pop₂
            dsimp (config := { zeta := true }) at h_pop₂
            set c₂ := (List.zip (List.range w₂.events.length) w₂.events).filter
              (fun x => x.2.targetTick == w₂.tick)
            set minPri₂ := c₂.foldl (fun acc x => min acc x.2.priority)
              (c₂.head?.map (fun x => x.2.priority) |>.getD 0)
            split at h_pop₂ <;> try contradiction
            split at h_pop₂ <;> try contradiction
            rename_i idx₂' ev₂' h_find₂
            rw [Option.some_inj, Prod.mk.injEq] at h_pop₂
            rcases h_pop₂ with ⟨h_ev₂', _⟩
            have h_ev₂'_eq : ev₂' = ev := h_ev₂'
            -- h_find₂ : c₂.find? (fun x => x.2.priority == minPri₂) = some (idx₂', ev)
            -- ev.priority == minPri₂
            have h_ev_pri : ev.priority == minPri₂ := by
              have h_pred := List.find?_predicate_true
                (fun x : Nat × ScheduledEvent => x.2.priority == minPri₂) c₂ (idx₂', ev₂') h_find₂
              simpa [h_ev₂'_eq] using h_pred
            -- c₂.map Prod.snd = w₂.events.filter (fun e => e.targetTick == w₂.tick)
            have h_c₂_snd : c₂.map Prod.snd = w₂.events.filter (fun e => e.targetTick == w₂.tick) := by
              dsimp [c₂]
              convert zip_filter_map_snd_eq (List.range w₂.events.length) w₂.events w₂.tick (by simp) using 2
            -- The find? returns the first with min priority
            -- So no element before the find? position in c₂ has priority == minPri₂
            -- The find? position in c₂ is k₂ (because c₂.map Prod.snd = filter and (filter)[k₂] = ev)
            -- So no element before k₂ in c₂.map Prod.snd has priority == minPri₂
            -- So no element before k₂ in w₂.events.filter p' has priority == minPri₂
            -- But (w₂.events.filter p')[k₁] = ev has priority == minPri₂ and k₁ < k₂
            -- Contradiction
            -- To show: the find? position in c₂ is k₂
            -- c₂.map Prod.snd = w₂.events.filter p' and (w₂.events.filter p')[k₂] = ev
            -- And c₂[k₂].2 = (c₂.map Prod.snd)[k₂] = ev
            -- And find? returned (idx₂', ev) which is at some position in c₂
            -- The position of (idx₂', ev) in c₂ is the find? index
            -- And c₂[find?_index] = (idx₂', ev)
            -- And c₂[find?_index].2 = ev = c₂[k₂].2
            -- But this doesn't directly give find?_index = k₂
            -- However, find? returns the FIRST with min priority
            -- And c₂[k₂].2 = ev has min priority
            -- So find?_index ≤ k₂
            -- And no element before find?_index has min priority
            -- And c₂[k₁].2 = (c₂.map Prod.snd)[k₁] = (w₂.events.filter p')[k₁] = ev has min priority
            -- So find?_index ≤ k₁
            -- And k₁ < k₂
            -- So find?_index ≤ k₁ < k₂
            -- But c₂[k₂].2 = ev has min priority and find?_index ≤ k₁ < k₂
            -- This is consistent (find?_index could be ≤ k₁)
            -- But we also know that (w₂.events.filter p')[k₂] = ev
            -- And c₂.map Prod.snd = w₂.events.filter p'
            -- So c₂[k₂].2 = ev
            -- And find? returned (idx₂', ev) at position find?_index
            -- And c₂[find?_index].2 = ev
            -- But there might be multiple positions with ev
            -- However, find? returns the FIRST with min priority
            -- So find?_index is the first position with min priority
            -- And k₁ is a position with min priority (because c₂[k₁].2 = ev has min priority)
            -- So find?_index ≤ k₁
            -- And k₂ is also a position with min priority
            -- So find?_index ≤ k₂
            -- But this doesn't give a contradiction
            -- I need to show that k₂ is the find? position
            -- And this requires showing that k₂ = find?_index
            -- Which requires showing that the find? result is at position k₂ in c₂
            -- And this follows from the take-filter length being the position
            -- Use zip_filter_position_eq_take_filter_length to show c₂[k₂] = (idx₂, ev)
            have h_p₂' : (w₂.events[idx₂].targetTick == w₂.tick) = true := by
              simpa [p, h_tick] using h_p₂
            have h_k₂_pos := zip_filter_position_eq_take_filter_length w₂.events w₂.tick idx₂ h_idx₂ h_p₂'
            obtain ⟨h_k₂_lt_raw, h_k₂_get⟩ := h_k₂_pos
            have h_k₂_lt : k₂ < c₂.length := by
              dsimp [k₂, c₂, p] at h_k₂_lt_raw ⊢
              simpa [h_tick] using h_k₂_lt_raw
            -- idx₂' = idx₂: both are the find? index from popNextEvent
            have h_idx_eq : idx₂' = idx₂ := by
              have h₂ := h_find₂
              dsimp [c₂, minPri₂] at h₂
              rw [h_ev₂'_eq] at h₂
              have h_eq : some (idx₂, ev) = some (idx₂', ev) := by
                rw [← h_find₂_full]
                exact h₂
              injection h_eq with h_pair
              injection h_pair with h_idx _
              exact h_idx.symm
            -- find? position in c₂ is k₂; no element before k₂ has min priority
            have h_find₂' : c₂.find? (fun x => x.2.priority == minPri₂) = some (idx₂, ev) := by
              simpa [h_idx_eq, h_ev₂'_eq] using h_find₂
            obtain ⟨f₂, h_f₂_lt, h_f₂_get, h_f₂_first⟩ :=
              List.find?_eq_some_getElem (fun x => x.2.priority == minPri₂) c₂ (idx₂, ev) h_find₂'
            -- c₂[k₂] = (idx₂, ev) from zip_filter_position
            have h_c₂_k₂ : c₂[k₂] = (idx₂, ev) := by
              dsimp [c₂, k₂, p] at h_k₂_get ⊢
              simpa [h_get₂, h_tick] using h_k₂_get
            -- f₂ = k₂ because c₂ has unique first components (from zip range)
            have h_f₂_eq_k₂ : f₂ = k₂ := by
              have h_nodup : (c₂.map Prod.fst).Nodup := by
                dsimp [c₂]
                have h_sub := (List.filter_sublist (p := fun x : Nat × ScheduledEvent =>
                  x.2.targetTick == w₂.tick) (l := List.zip (List.range w₂.events.length) w₂.events)).map Prod.fst
                have h_eq : (List.zip (List.range w₂.events.length) w₂.events).map Prod.fst =
                    List.range w₂.events.length := by
                  ext i
                  by_cases h : i < w₂.events.length
                  · simp [h]
                  · simp [h]
                rw [h_eq] at h_sub
                exact h_sub.nodup List.nodup_range
              have h_f₂_map : f₂ < (c₂.map Prod.fst).length := by
                rw [List.length_map]; exact h_f₂_lt
              have h_k₂_map : k₂ < (c₂.map Prod.fst).length := by
                rw [List.length_map]; exact h_k₂_lt
              have h_eq : (c₂.map Prod.fst)[f₂] = (c₂.map Prod.fst)[k₂] := by
                rw [List.getElem_map, List.getElem_map, h_f₂_get, h_c₂_k₂]
              exact (List.Nodup.getElem_inj_iff h_nodup).mp h_eq
            -- No element before k₂ satisfies the predicate
            have h_no_before : ∀ j (h_j : j < k₂), (c₂[j].2.priority == minPri₂) = false := by
              intro j h_j
              have h_j' : j < f₂ := by rw [h_f₂_eq_k₂]; exact h_j
              exact h_f₂_first j h_j'
            -- c₂[k₁].2 = ev has min priority
            have h_c₂_k₁_snd : c₂[k₁].2 = ev := by
              have h_map : c₂.map Prod.snd = w₂.events.filter p := by
                dsimp [c₂, p]
                convert zip_filter_map_snd_eq (List.range w₂.events.length) w₂.events w₂.tick (by simp) using 2
                ; ext ⟨i, e⟩ ; simp [h_tick]
              have h_k₁_lt' : k₁ < c₂.length := by
                have := List.length_map (f := Prod.snd) (as := c₂)
                rw [h_map] at this
                omega
              have h_map_lt₁ : k₁ < (c₂.map Prod.snd).length := by rw [List.length_map]; exact h_k₁_lt'
              have h₁ : c₂[k₁].2 = (c₂.map Prod.snd)[k₁] := by rw [List.getElem_map]
              have h₂ : (c₂.map Prod.snd)[k₁] = ev := by
                simpa [h_map] using h_at_k₁
              rw [h₁, h₂]
            have h_k₁_pred : (c₂[k₁].2.priority == minPri₂) = true := by
              rw [h_c₂_k₁_snd]; exact h_ev_pri
            -- Contradiction: k₁ < k₂ but no element before k₂ satisfies predicate
            have h_k₁_lt_c₂ : k₁ < c₂.length := by
              have h_map : c₂.map Prod.snd = w₂.events.filter p := by
                dsimp [c₂, p]
                convert zip_filter_map_snd_eq (List.range w₂.events.length) w₂.events w₂.tick (by simp) using 2
                ; ext ⟨i, e⟩ ; simp [h_tick]
              have := List.length_map (f := Prod.snd) (as := c₂)
              rw [h_map] at this
              omega
            have := h_no_before k₁ (by omega)
            rw [h_k₁_pred] at this; contradiction
          | inr h_lt =>
            -- Symmetric case: k₂ < k₁ — use h_find₁_full for w₁
            set c₁ := (List.zip (List.range w₁.events.length) w₁.events).filter
              (fun x => x.2.targetTick == w₁.tick)
            set minPri₁ := c₁.foldl (fun acc x => min acc x.2.priority)
              (c₁.head?.map (fun x => x.2.priority) |>.getD 0)
            have h_find₁' : c₁.find? (fun x => x.2.priority == minPri₁) = some (idx₁, ev) := by
              simpa [c₁, minPri₁] using h_find₁_full
            obtain ⟨f₁, h_f₁_lt, h_f₁_get, h_f₁_first⟩ :=
              List.find?_eq_some_getElem (fun x => x.2.priority == minPri₁) c₁ (idx₁, ev) h_find₁'
            -- c₁[k₁] = (idx₁, ev) from zip_filter_position
            have h_p₁' : (w₁.events[idx₁].targetTick == w₁.tick) = true := by simpa [p] using h_p₁
            have h_k₁_pos := zip_filter_position_eq_take_filter_length w₁.events w₁.tick idx₁ h_idx₁ h_p₁'
            obtain ⟨h_k₁_lt_raw, h_k₁_get'⟩ := h_k₁_pos
            have h_k₁_lt' : k₁ < c₁.length := by
              dsimp [k₁, c₁, p] at h_k₁_lt_raw ⊢
              exact h_k₁_lt_raw
            have h_c₁_k₁ : c₁[k₁] = (idx₁, ev) := by
              dsimp [c₁] at h_k₁_get' ⊢; simpa [h_get₁] using h_k₁_get'
            -- f₁ = k₁
            have h_f₁_eq_k₁ : f₁ = k₁ := by
              have h_nodup : (c₁.map Prod.fst).Nodup := by
                dsimp [c₁]
                have h_sub := (List.filter_sublist (p := fun x : Nat × ScheduledEvent =>
                  x.2.targetTick == w₁.tick) (l := List.zip (List.range w₁.events.length) w₁.events)).map Prod.fst
                have h_eq : (List.zip (List.range w₁.events.length) w₁.events).map Prod.fst =
                    List.range w₁.events.length := by
                  ext i
                  by_cases h : i < w₁.events.length
                  · simp [h]
                  · simp [h]
                rw [h_eq] at h_sub
                exact h_sub.nodup List.nodup_range
              have h_f₁_map : f₁ < (c₁.map Prod.fst).length := by
                rw [List.length_map]; exact h_f₁_lt
              have h_k₁_map : k₁ < (c₁.map Prod.fst).length := by
                rw [List.length_map]; exact h_k₁_lt'
              have h_eq : (c₁.map Prod.fst)[f₁] = (c₁.map Prod.fst)[k₁] := by
                rw [List.getElem_map, List.getElem_map, h_f₁_get, h_c₁_k₁]
              exact (List.Nodup.getElem_inj_iff h_nodup).mp h_eq
            -- No element before k₁ satisfies the predicate
            have h_no_before : ∀ j (h_j : j < k₁), (c₁[j].2.priority == minPri₁) = false := by
              intro j h_j
              have h_j' : j < f₁ := by rw [h_f₁_eq_k₁]; exact h_j
              exact h_f₁_first j h_j'
            -- c₁[k₂].2 = ev has min priority
            have h_c₁_k₂_snd : c₁[k₂].2 = ev := by
              have h_map : c₁.map Prod.snd = w₁.events.filter p := by
                dsimp [c₁, p]
                convert zip_filter_map_snd_eq (List.range w₁.events.length) w₁.events w₁.tick (by simp) using 2
              have h_k₂_lt' : k₂ < c₁.length := by
                have := List.length_map (f := Prod.snd) (as := c₁)
                rw [h_map, h_filter_p] at this
                omega
              have h_map_lt₂ : k₂ < (c₁.map Prod.snd).length := by rw [List.length_map]; exact h_k₂_lt'
              have h₁ : c₁[k₂].2 = (c₁.map Prod.snd)[k₂] := by rw [List.getElem_map]
              have h₂ : (c₁.map Prod.snd)[k₂] = ev := by
                simpa [h_map, h_filter_p] using h_k₂_eq
              rw [h₁, h₂]
            have h_ev_pri₁ : (ev.priority == minPri₁) = true := by
              have := List.find?_predicate_true
                (fun x : Nat × ScheduledEvent => x.2.priority == minPri₁) c₁ (idx₁, ev) h_find₁'
              simpa using this
            have h_k₂_pred : (c₁[k₂].2.priority == minPri₁) = true := by
              rw [h_c₁_k₂_snd]; exact h_ev_pri₁
            have h_k₂_lt' : k₂ < c₁.length := by
              have h_map : c₁.map Prod.snd = w₁.events.filter p := by
                dsimp [c₁, p]
                convert zip_filter_map_snd_eq (List.range w₁.events.length) w₁.events w₁.tick (by simp) using 2
              have := List.length_map (f := Prod.snd) (as := c₁)
              rw [h_map] at this
              omega
            have := h_no_before k₂ (by omega)
            rw [h_k₂_pred] at this; contradiction
        -- Now use filter_eraseIdx_same
        have h_congr := List.filter_eraseIdx_same w₁.events w₂.events p idx₁ idx₂ h_filter_p
          h_idx₁ h_idx₂ h_p₁ h_p₂ h_k_eq
        -- h_congr : (w₁.events.eraseIdx idx₁).filter p = (w₂.events.eraseIdx idx₂).filter p
        -- w₁_pop.events = w₁.events.eraseIdx idx₁
        -- w₂_pop.events = w₂.events.eraseIdx idx₂
        have h_pred_goal : p = (fun e : ScheduledEvent => e.targetTick == w₂_pop.tick) := by
          dsimp [p]; ext e; simp [h_tw]
        rw [h_pred_goal] at h_congr
        rw [h_erase₁, h_erase₂]
        exact h_congr
      -- Delay property preserved
      have h_delay' : ∀ nid nd, (w₁_pop.onScheduledTick ev.nodeId).getNode nid = some nd →
          ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
        intro nid nd h_nd d p h_kind
        obtain ⟨nd₀, h_nd₀, h_kind_eq⟩ := World.onScheduledTick_kind_preserved w₁_pop ev.nodeId nid nd h_nd
        rw [h_kind_eq] at h_kind
        have h_nd₀' : w₁.getNode nid = some nd₀ := by
          dsimp [World.getNode]; rw [← h_pop_nodes₁]; exact h_nd₀
        exact h_delay nid nd₀ h_nd₀' d p h_kind
      exact ih (w₂_pop.onScheduledTick ev.nodeId) h_nodes' h_tick' h_filter' h_delay'
