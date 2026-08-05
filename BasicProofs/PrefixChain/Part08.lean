import BasicProofs.PrefixChain.Part07


open BasicRedstoneSim

/-- `stepUntilNextTick` produces equal results for worlds that share the same
nodes/tick/outputLog/nextId, have permuted event lists with the same "future"
sublist, unique priorities at the current tick, and sufficient fuel. -/
theorem stepUntilNextTick_perm_eq (w₁ w₂ : World)
    (h_nodes : w₁.nodes = w₂.nodes)
    (h_tick : w₁.tick = w₂.tick)
    (h_log : w₁.outputLog = w₂.outputLog)
    (h_nextId : w₁.nextId = w₂.nextId)
    (h_perm : List.Perm w₁.events w₂.events)
    (h_future : w₁.events.filter (fun e => e.targetTick ≠ w₁.tick) =
        w₂.events.filter (fun e => e.targetTick ≠ w₂.tick))
    (h_unique : ∀ ev₁ ∈ w₁.events, ∀ ev₂ ∈ w₁.events,
        ev₁.targetTick = w₁.tick → ev₂.targetTick = w₁.tick → ev₁ ≠ ev₂ →
        ev₁.priority ≠ ev₂.priority)
    (h_pri : ∀ ev ∈ w₁.events, ev.priority < 100)
    (h_delay : ∀ nid nd, w₁.getNode nid = some nd → ∀ d p,
        nd.kind = .repeater d p → d ≥ 2)
    (h_new_pri : ∀ nid nd, w₁.getNode nid = some nd → ∀ d p,
        nd.kind = .repeater d p → p < 100) :
    w₁.stepUntilNextTick = w₂.stepUntilNextTick := by
  suffices ∀ (w₁ w₂ : World), w₁.nodes = w₂.nodes → w₁.tick = w₂.tick →
      w₁.outputLog = w₂.outputLog → w₁.nextId = w₂.nextId →
      List.Perm w₁.events w₂.events →
      (w₁.events.filter (fun e => e.targetTick ≠ w₁.tick) =
        w₂.events.filter (fun e => e.targetTick ≠ w₂.tick)) →
      (∀ ev ∈ w₁.events, ∀ ev' ∈ w₂.events, ev.targetTick = w₁.tick → ev'.targetTick = w₂.tick →
        ev ≠ ev' → ev.priority ≠ ev'.priority) →
      (∀ ev ∈ w₁.events, ev.targetTick > w₁.tick → ev ∈ w₂.events) →
      (∀ ev₁ ∈ w₁.events, ∀ ev₂ ∈ w₁.events,
        ev₁.targetTick = w₁.tick → ev₂.targetTick = w₁.tick → ev₁ ≠ ev₂ →
        ev₁.priority ≠ ev₂.priority) →
      (∀ ev ∈ w₁.events, ev.priority < 100) →
      (∀ nid nd, w₁.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2) →
      (∀ nid nd, w₁.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 100) →
      w₁.stepUntilNextTick = w₂.stepUntilNextTick from by
    have h_cross : ∀ ev ∈ w₁.events, ∀ ev' ∈ w₂.events, ev.targetTick = w₁.tick →
        ev'.targetTick = w₂.tick → ev ≠ ev' → ev.priority ≠ ev'.priority := by
      intro ev h_ev ev' h_ev' h_tick_ev h_tick_ev' h_ne
      have h_ev'_in₁ : ev' ∈ w₁.events := h_perm.symm.subperm.subset h_ev'
      rw [← h_tick] at h_tick_ev'
      exact (h_unique ev' h_ev'_in₁ ev h_ev h_tick_ev' h_tick_ev (Ne.symm h_ne)).symm
    have h_fut_mem : ∀ ev ∈ w₁.events, ev.targetTick > w₁.tick → ev ∈ w₂.events := by
      intro ev h_ev h_gt
      have h_ne : ev.targetTick ≠ w₁.tick := by omega
      have h_in_filter : ev ∈ w₁.events.filter (fun e => e.targetTick ≠ w₁.tick) := by
        simp [List.mem_filter, h_ev, h_ne]
      rw [h_future] at h_in_filter
      simp [List.mem_filter] at h_in_filter
      exact h_in_filter.1
    exact this w₁ w₂ h_nodes h_tick h_log h_nextId h_perm h_future h_cross h_fut_mem h_unique h_pri h_delay h_new_pri
  intro w₁
  induction w₁ using World.stepUntilNextTick.induct with
  | case1 w₁ h_step₁ =>
    intro w₂ h_nodes h_tick h_log h_nextId h_perm h_future h_cross h_fut_mem h_unique h_pri h_delay h_new_pri
    -- h_step₁ : w₁.step = none
    have h_no₁ : ∀ ev ∈ w₁.events, ev.targetTick ≠ w₁.tick := by
      dsimp [World.step] at h_step₁
      cases h_pop : w₁.popNextEvent with
      | none => exact popNextEvent_none_no_events w₁ h_pop
      | some p => simp [h_pop] at h_step₁
    have h_no₂ : ∀ ev ∈ w₂.events, ev.targetTick ≠ w₂.tick := by
      intro ev h_ev; rw [← h_tick]; intro h_eq
      exact h_no₁ ev (h_perm.symm.subperm.subset h_ev) h_eq
    have h_evts : w₁.events = w₂.events := by
      have h₁ : w₁.events.filter (fun e => e.targetTick ≠ w₁.tick) = w₁.events :=
        List.filter_eq_self.mpr (fun ev h_ev => by simp [h_no₁ ev h_ev])
      have h₂ : w₂.events.filter (fun e => e.targetTick ≠ w₂.tick) = w₂.events :=
        List.filter_eq_self.mpr (fun ev h_ev => by simp [h_no₂ ev h_ev])
      rw [← h₁, ← h₂, h_future]
    have h_step₂ : w₂.step = none := by
      dsimp [World.step]
      cases h_pop : w₂.popNextEvent with
      | none => rfl
      | some p =>
        rcases p with ⟨ev, w'⟩
        have h_ev_tick := popNextEvent_at_tick w₂ ev w' h_pop
        obtain ⟨_, _, _, _, h_mem_ev, _⟩ := World.popNextEvent_eraseIdx w₂ ev w' h_pop
        exfalso; exact h_no₂ ev h_mem_ev h_ev_tick
    rw [stepUntilNextTick_of_step_none w₁ h_step₁, stepUntilNextTick_of_step_none w₂ h_step₂]
    simp [h_evts, h_nodes, h_tick, h_log, h_nextId]
  | case2 w₁ w₁' h_step₁ ih =>
    intro w₂ h_nodes h_tick h_log h_nextId h_perm h_future h_cross h_fut_mem h_unique h_pri h_delay h_new_pri
    -- h_step₁ : w₁.step = some w₁'
    have h_sunt : w₁.stepUntilNextTick = w₁'.stepUntilNextTick := by
      rw [World.stepUntilNextTick, h_step₁]
    rw [h_sunt]
    -- w₂.step ≠ none as well
    have h_step₂' : w₂.step ≠ none := by
      intro h_contra
      dsimp [World.step] at h_contra
      cases h_pop : w₂.popNextEvent with
      | none =>
        have h_no₂ : ∀ ev ∈ w₂.events, ev.targetTick ≠ w₂.tick :=
          popNextEvent_none_no_events w₂ h_pop
        dsimp [World.step] at h_step₁
        cases h_pop₁ : w₁.popNextEvent with
        | none => simp [h_pop₁] at h_step₁
        | some p =>
          rcases p with ⟨ev, w'⟩
          have h_ev_tick := popNextEvent_at_tick w₁ ev w' h_pop₁
          have h_ev_in₂ : ev ∈ w₂.events := by
            obtain ⟨_, _, _, _, h_mem, _⟩ := World.popNextEvent_eraseIdx w₁ ev w' h_pop₁
            exact h_perm.subperm.subset h_mem
          exact h_no₂ ev h_ev_in₂ (h_ev_tick.trans h_tick)
      | some p => simp [h_pop] at h_contra
    -- Both steps are some
    cases h_s₂ : w₂.step with
    | none => contradiction
    | some w₂' =>
      have h_step₂_eq : w₂.step = some w₂' := h_s₂
      -- Unfold step to get popNextEvent structure
      dsimp [World.step] at h_step₁ h_s₂
      cases h_pop₁ : w₁.popNextEvent with
      | none => simp [h_pop₁] at h_step₁
      | some p₁ =>
        rcases p₁ with ⟨ev₁, w₁_pop⟩
        simp only [h_pop₁] at h_step₁
        injection h_step₁ with h_w₁'
        cases h_pop₂ : w₂.popNextEvent with
            | none => simp [h_pop₂] at h_s₂
            | some p₂ =>
              rcases p₂ with ⟨ev₂, w₂_pop⟩
              simp only [h_pop₂] at h_s₂
              injection h_s₂ with h_w₂'
              -- Both pop events at current tick
              have h_ev₁_tick : ev₁.targetTick = w₁.tick := popNextEvent_at_tick w₁ ev₁ w₁_pop h_pop₁
              have h_ev₂_tick : ev₂.targetTick = w₂.tick := popNextEvent_at_tick w₂ ev₂ w₂_pop h_pop₂
              obtain ⟨idx₁, h_idx₁, h_erase₁, _, h_mem₁, h_get₁⟩ := World.popNextEvent_eraseIdx w₁ ev₁ w₁_pop h_pop₁
              obtain ⟨idx₂, h_idx₂, h_erase₂, _, h_mem₂, h_get₂⟩ := World.popNextEvent_eraseIdx w₂ ev₂ w₂_pop h_pop₂
              have h_ev₁_in₂ : ev₁ ∈ w₂.events := h_perm.subperm.subset h_mem₁
              have h_ev₂_in₁ : ev₂ ∈ w₁.events := h_perm.symm.subperm.subset h_mem₂
              -- Both have minimum priority → ev₁ = ev₂
              have h_min₁ := popNextEvent_min_priority w₁ ev₁ w₁_pop h_pop₁
              have h_min₂ := popNextEvent_min_priority w₂ ev₂ w₂_pop h_pop₂
              have h_ev_eq : ev₁ = ev₂ := by
                have h_le₁ : ev₁.priority ≤ ev₂.priority :=
                  h_min₁ ev₂ h_ev₂_in₁ (h_ev₂_tick.trans h_tick.symm)
                have h_le₂ : ev₂.priority ≤ ev₁.priority :=
                  h_min₂ ev₁ h_ev₁_in₂ (h_ev₁_tick.trans h_tick)
                by_cases h_eq : ev₁ = ev₂
                · exact h_eq
                · exfalso
                  have h_ne := h_unique ev₁ h_mem₁
                    ev₂ h_ev₂_in₁ h_ev₁_tick (by rwa [h_tick]) h_eq
                  omega
              rw [← h_ev_eq] at h_pop₂ h_w₂' h_ev₂_tick h_get₂
              -- After popping same event, remaining events are permuted
              have h_perm_pop : List.Perm w₁_pop.events w₂_pop.events := by
                rw [h_erase₁, h_erase₂]
                -- Use perm_cons_eraseIdx: l[i] :: l.eraseIdx i ~ l
                have hp₁ : List.Perm (ev₁ :: w₁.events.eraseIdx idx₁) w₁.events := by
                  rw [← h_get₁]; exact List.perm_cons_eraseIdx h_idx₁
                have hp₂ : List.Perm (ev₁ :: w₂.events.eraseIdx idx₂) w₂.events := by
                  rw [← h_get₂]; exact List.perm_cons_eraseIdx h_idx₂
                -- Chain: ev₁ :: eraseIdx idx₁ ~ w₁.events ~ w₂.events ~ ev₁ :: eraseIdx idx₂
                -- Then remove common head ev₁
                exact List.Perm.cons_inv (hp₁.trans (h_perm.trans hp₂.symm))
              -- Popped worlds share fields
              have h_nodes_pop : w₁_pop.nodes = w₂_pop.nodes := by
                rw [World.popNextEvent_nodes w₁ ev₁ w₁_pop h_pop₁,
                    World.popNextEvent_nodes w₂ ev₁ w₂_pop h_pop₂, h_nodes]
              have h_tick_pop : w₁_pop.tick = w₂_pop.tick := by
                rw [World.popNextEvent_tick w₁ ev₁ w₁_pop h_pop₁,
                    World.popNextEvent_tick w₂ ev₁ w₂_pop h_pop₂, h_tick]
              have h_log_pop : w₁_pop.outputLog = w₂_pop.outputLog := by
                rw [World.popNextEvent_outputLog w₁ ev₁ w₁_pop h_pop₁,
                    World.popNextEvent_outputLog w₂ ev₁ w₂_pop h_pop₂, h_log]
              -- Use onScheduledTick_congr_fields for the heavy lifting
              have h_nextId_pop : w₁_pop.nextId = w₂_pop.nextId := by
                rw [World.popNextEvent_nextId w₁ ev₁ w₁_pop h_pop₁,
                    World.popNextEvent_nextId w₂ ev₁ w₂_pop h_pop₂, h_nextId]
              obtain ⟨h_nodes_st, h_tick_st, h_log_st, h_nextId_st, new, h_app₁, h_app₂⟩ :=
                World.onScheduledTick_congr_fields w₁_pop w₂_pop ev₁.nodeId
                  h_nodes_pop h_tick_pop h_log_pop h_nextId_pop
              have h_w₁'_eq : w₁' = w₁_pop.onScheduledTick ev₁.nodeId := by rw [← h_w₁']
              have h_w₂'_eq : w₂' = w₂_pop.onScheduledTick ev₁.nodeId := by rw [← h_w₂']
              -- Field equalities for w₁' and w₂'
              have h_nodes' : w₁'.nodes = w₂'.nodes := by rw [h_w₁'_eq, h_w₂'_eq]; exact h_nodes_st
              have h_tick' : w₁'.tick = w₂'.tick := by rw [h_w₁'_eq, h_w₂'_eq]; exact h_tick_st
              have h_log' : w₁'.outputLog = w₂'.outputLog := by rw [h_w₁'_eq, h_w₂'_eq]; exact h_log_st
              have h_nextId' : w₁'.nextId = w₂'.nextId := by rw [h_w₁'_eq, h_w₂'_eq]; exact h_nextId_st
              -- Permuted events after onScheduledTick
              have h_perm' : List.Perm w₁'.events w₂'.events := by
                rw [h_w₁'_eq, h_w₂'_eq, h_app₁, h_app₂]
                exact List.Perm.append h_perm_pop (List.Perm.refl new)
              -- Helper lemma: erasing an element that fails the predicate doesn't change filter
              have h_filter_eraseIdx_lemma : ∀ (l : List ScheduledEvent) (i : Nat) (t : Nat)
                  (h_lt : i < l.length), (getElem l i h_lt).targetTick = t →
                  (l.eraseIdx i).filter (fun e => e.targetTick ≠ t) = l.filter (fun e => e.targetTick ≠ t) := by
                intro l
                induction l with
                | nil => simp
                | cons hd tl ih' =>
                  intro i t h_lt h_tick
                  cases i with
                  | zero =>
                    simp only [List.eraseIdx, List.filter, List.getElem_cons_zero] at h_tick ⊢
                    simp [h_tick]
                  | succ i' =>
                    simp only [List.eraseIdx_cons_succ, List.filter, List.getElem_cons_succ] at h_tick ⊢
                    have h_lt' : i' < tl.length := by simp [List.length] at h_lt; omega
                    have h_ih := ih' i' t h_lt' h_tick
                    rw [h_ih]
              have h_erase_filter₁ : w₁_pop.events.filter (fun e => e.targetTick ≠ w₁_pop.tick) =
                  w₁.events.filter (fun e => e.targetTick ≠ w₁.tick) := by
                rw [World.popNextEvent_tick w₁ ev₁ w₁_pop h_pop₁, h_erase₁]
                exact h_filter_eraseIdx_lemma w₁.events idx₁ w₁.tick h_idx₁ (by rw [h_get₁]; exact h_ev₁_tick)
              have h_erase_filter₂ : w₂_pop.events.filter (fun e => e.targetTick ≠ w₂_pop.tick) =
                  w₂.events.filter (fun e => e.targetTick ≠ w₂.tick) := by
                rw [World.popNextEvent_tick w₂ ev₁ w₂_pop h_pop₂, h_erase₂]
                exact h_filter_eraseIdx_lemma w₂.events idx₂ w₂.tick h_idx₂ (by rw [h_get₂]; exact h_ev₂_tick)
              -- Future filter equality for popped worlds
              have h_future_pop : w₁_pop.events.filter (fun e => e.targetTick ≠ w₁_pop.tick) =
                  w₂_pop.events.filter (fun e => e.targetTick ≠ w₂_pop.tick) := by
                rw [h_erase_filter₁, h_erase_filter₂, h_future]
              -- New events are at future ticks
              have h_delay_pop : ∀ nid nd, w₁_pop.getNode nid = some nd → ∀ d p,
                  nd.kind = .repeater d p → d ≥ 2 := by
                intro nid nd h_nd d p h_kind
                apply h_delay nid nd _ d p h_kind
                dsimp [World.getNode]; rw [← (World.popNextEvent_nodes w₁ ev₁ w₁_pop h_pop₁)]
                exact h_nd
              obtain ⟨new₁, h_app₁', h_fut₁⟩ := World.onScheduledTick_events_append w₁_pop ev₁.nodeId h_delay_pop
              -- Prove new = new₁ by append cancellation
              have h_new_eq : new = new₁ := by
                have h : w₁_pop.events ++ new = w₁_pop.events ++ new₁ := by
                  rw [← h_app₁, ← h_app₁']
                revert h
                induction w₁_pop.events with
                | nil => simp
                | cons hd tl ih' =>
                  intro h
                  have h' : tl ++ new = tl ++ new₁ := by
                    simpa [List.cons_append] using h
                  exact ih' h'
              have h_new_future : ∀ ev ∈ new, ev.targetTick ≠ w₁_pop.tick := by
                intro ev h_ev; rw [h_new_eq] at h_ev; have := h_fut₁ ev h_ev; omega
              -- Future filter for w₁' and w₂'
              have h_future' : w₁'.events.filter (fun e => e.targetTick ≠ w₁'.tick) =
                  w₂'.events.filter (fun e => e.targetTick ≠ w₂'.tick) := by
                rw [h_w₁'_eq, h_w₂'_eq, h_app₁, h_app₂]
                rw [List.filter_append, List.filter_append]
                -- Simplify ticks: onScheduledTick preserves tick
                simp only [World.onScheduledTick_tick]
                -- new events all pass the future filter
                have h_new_f₁ : new.filter (fun e => e.targetTick ≠ w₁_pop.tick) = new := by
                  apply List.filter_eq_self.mpr
                  intro ev h_ev; simpa using h_new_future ev h_ev
                have h_new_f₂ : new.filter (fun e => e.targetTick ≠ w₂_pop.tick) = new := by
                  apply List.filter_eq_self.mpr
                  intro ev h_ev
                  simpa [h_tick_pop] using h_new_future ev h_ev
                rw [h_new_f₁, h_new_f₂, h_future_pop]
              -- Unique priorities preserved
              have h_tick_w₁'_orig : w₁'.tick = w₁.tick := by
                rw [h_w₁'_eq, World.onScheduledTick_tick,
                    World.popNextEvent_tick w₁ ev₁ w₁_pop h_pop₁]
              have h_unique' : ∀ ev₁ ∈ w₁'.events, ∀ ev₂ ∈ w₁'.events,
                  ev₁.targetTick = w₁'.tick → ev₂.targetTick = w₁'.tick → ev₁ ≠ ev₂ →
                  ev₁.priority ≠ ev₂.priority := by
                intro ev₁' h_ev₁' ev₂' h_ev₂' h_tick₁' h_tick₂' h_ne'
                rw [h_w₁'_eq, h_app₁] at h_ev₁' h_ev₂'
                simp [List.mem_append] at h_ev₁' h_ev₂'
                rcases h_ev₁' with h_ev₁' | h_ev₁' <;> rcases h_ev₂' with h_ev₂' | h_ev₂'
                · -- Both in w₁_pop.events ⊆ w₁.events
                  have h_ev₁_orig : ev₁' ∈ w₁.events := by
                    rw [h_erase₁] at h_ev₁'; exact List.eraseIdx_subset' w₁.events idx₁ h_ev₁'
                  have h_ev₂_orig : ev₂' ∈ w₁.events := by
                    rw [h_erase₁] at h_ev₂'; exact List.eraseIdx_subset' w₁.events idx₁ h_ev₂'
                  exact h_unique ev₁' h_ev₁_orig ev₂' h_ev₂_orig
                    (by rw [h_tick_w₁'_orig] at h_tick₁'; exact h_tick₁')
                    (by rw [h_tick_w₁'_orig] at h_tick₂'; exact h_tick₂') h_ne'
                · have := h_new_future ev₂' h_ev₂'
                  rw [h_tick_w₁'_orig] at h_tick₂'
                  have : w₁_pop.tick = w₁.tick := World.popNextEvent_tick w₁ ev₁ w₁_pop h_pop₁
                  omega
                · have := h_new_future ev₁' h_ev₁'
                  rw [h_tick_w₁'_orig] at h_tick₁'
                  have : w₁_pop.tick = w₁.tick := World.popNextEvent_tick w₁ ev₁ w₁_pop h_pop₁
                  omega
                · have h₁ := h_new_future ev₁' h_ev₁'
                  have h₂ := h_new_future ev₂' h_ev₂'
                  rw [h_tick_w₁'_orig] at h_tick₁' h_tick₂'
                  have : w₁_pop.tick = w₁.tick := World.popNextEvent_tick w₁ ev₁ w₁_pop h_pop₁
                  omega
              -- All priorities < 100
              have h_new_pri_pop : ∀ nid nd, w₁_pop.getNode nid = some nd → ∀ d p,
                  nd.kind = .repeater d p → p < 100 := by
                intro nid nd h_nd d p h_kind
                apply h_new_pri nid nd _ d p h_kind
                dsimp [World.getNode]; rw [← (World.popNextEvent_nodes w₁ ev₁ w₁_pop h_pop₁)]
                exact h_nd
              have h_pri' : ∀ ev ∈ w₁'.events, ev.priority < 100 := by
                intro ev h_ev
                rw [h_w₁'_eq, h_app₁] at h_ev
                simp [List.mem_append] at h_ev
                rcases h_ev with h_ev | h_ev
                · -- In w₁_pop.events ⊆ w₁.events
                  have h_in_orig : ev ∈ w₁.events := by
                    rw [h_erase₁] at h_ev; exact List.eraseIdx_subset' w₁.events idx₁ h_ev
                  exact h_pri ev h_in_orig
                · -- In new: use onScheduledTick_new_events
                  by_cases h_in_pop : ev ∈ w₁_pop.events
                  · have h_in_orig : ev ∈ w₁.events := by
                      rw [h_erase₁] at h_in_pop; exact List.eraseIdx_subset' w₁.events idx₁ h_in_pop
                    exact h_pri ev h_in_orig
                  · have h_new_ev := (World.onScheduledTick_new_events w₁_pop ev₁.nodeId h_new_pri_pop h_delay_pop).1
                    have h_ev_st : ev ∈ (w₁_pop.onScheduledTick ev₁.nodeId).events := by
                      rw [h_app₁]; exact List.mem_append_right _ h_ev
                    exact h_new_ev ev h_ev_st h_in_pop
              -- Delays preserved
              have h_delay' : ∀ nid nd, w₁'.getNode nid = some nd → ∀ d p,
                  nd.kind = .repeater d p → d ≥ 2 := by
                intro nid nd h_nd d p h_kind
                rw [h_w₁'_eq] at h_nd
                obtain ⟨nd₀, h_nd₀, h_keq⟩ := World.onScheduledTick_getNode_kind w₁_pop ev₁.nodeId nid nd h_nd
                rw [← h_keq] at h_kind
                exact h_delay_pop nid nd₀ h_nd₀ d p h_kind
              -- Repeater priorities preserved
              have h_new_pri' : ∀ nid nd, w₁'.getNode nid = some nd → ∀ d p,
                  nd.kind = .repeater d p → p < 100 := by
                intro nid nd h_nd d p h_kind
                rw [h_w₁'_eq] at h_nd
                obtain ⟨nd₀, h_nd₀, h_keq⟩ := World.onScheduledTick_getNode_kind w₁_pop ev₁.nodeId nid nd h_nd
                rw [← h_keq] at h_kind
                exact h_new_pri_pop nid nd₀ h_nd₀ d p h_kind
              -- Cross-uniqueness for w₁' and w₂'
              have h_cross' : ∀ ev ∈ w₁'.events, ∀ ev' ∈ w₂'.events, ev.targetTick = w₁'.tick →
                  ev'.targetTick = w₂'.tick → ev ≠ ev' → ev.priority ≠ ev'.priority := by
                intro ev₁' h_ev₁' ev₂' h_ev₂' h_tick₁' h_tick₂' h_ne'
                rw [h_w₁'_eq, h_app₁] at h_ev₁'
                rw [h_w₂'_eq, h_app₂] at h_ev₂'
                simp [List.mem_append] at h_ev₁' h_ev₂'
                rcases h_ev₁' with h_ev₁' | h_ev₁' <;> rcases h_ev₂' with h_ev₂' | h_ev₂'
                · have h₁ : ev₁' ∈ w₁.events := by
                    rw [h_erase₁] at h_ev₁'; exact List.eraseIdx_subset' w₁.events idx₁ h_ev₁'
                  have h₂ : ev₂' ∈ w₂.events := by
                    rw [h_erase₂] at h_ev₂'; exact List.eraseIdx_subset' w₂.events idx₂ h_ev₂'
                  have h_t1 : ev₁'.targetTick = w₁.tick := by rw [h_tick₁', h_tick_w₁'_orig]
                  have h_t2 : ev₂'.targetTick = w₂.tick := by
                    rw [h_tick₂', ← h_tick', h_tick_w₁'_orig, h_tick]
                  exact h_cross ev₁' h₁ ev₂' h₂ h_t1 h_t2 h_ne'
                · exfalso; have h_nf := h_new_future ev₂' h_ev₂'
                  have : ev₂'.targetTick = w₁_pop.tick := by
                    rw [h_tick₂', ← h_tick', h_tick_w₁'_orig]
                    exact (World.popNextEvent_tick w₁ ev₁ w₁_pop h_pop₁).symm
                  contradiction
                · exfalso; have h_nf := h_new_future ev₁' h_ev₁'
                  have : ev₁'.targetTick = w₁_pop.tick := by
                    rw [h_tick₁', h_tick_w₁'_orig]
                    exact (World.popNextEvent_tick w₁ ev₁ w₁_pop h_pop₁).symm
                  contradiction
                · exfalso; have h₁ := h_new_future ev₁' h_ev₁'
                  have h₂ := h_new_future ev₂' h_ev₂'
                  have ht1 : ev₁'.targetTick = w₁_pop.tick := by
                    rw [h_tick₁', h_tick_w₁'_orig]
                    exact (World.popNextEvent_tick w₁ ev₁ w₁_pop h_pop₁).symm
                  have ht2 : ev₂'.targetTick = w₁_pop.tick := by
                    rw [h_tick₂', ← h_tick', h_tick_w₁'_orig]
                    exact (World.popNextEvent_tick w₁ ev₁ w₁_pop h_pop₁).symm
                  contradiction
              -- Future membership for w₁' events in w₂'
              have h_fut_mem' : ∀ ev ∈ w₁'.events, ev.targetTick > w₁'.tick → ev ∈ w₂'.events := by
                intro ev h_ev h_gt
                rw [h_w₁'_eq, h_app₁] at h_ev
                simp [List.mem_append] at h_ev
                rcases h_ev with h_ev | h_ev
                · -- In w₁_pop.events ⊆ w₁.events
                  have h_in₁ : ev ∈ w₁.events := by
                    rw [h_erase₁] at h_ev; exact List.eraseIdx_subset' w₁.events idx₁ h_ev
                  have h_gt₁ : ev.targetTick > w₁.tick := by rwa [h_tick_w₁'_orig] at h_gt
                  have h_in₂ : ev ∈ w₂.events := h_fut_mem ev h_in₁ h_gt₁
                  have h_ne_idx : ev ≠ ev₁ := by
                    intro h_eq; rw [h_eq] at h_gt₁
                    have := h_ev₁_tick; omega
                  have h_in₂_pop : ev ∈ w₂_pop.events := by
                    rw [h_erase₂]
                    have h_ne' : ev ≠ w₂.events[idx₂] := by rwa [h_get₂]
                    exact List.mem_eraseIdx_of_mem_ne w₂.events idx₂ ev h_idx₂ h_in₂ h_ne'
                  rw [h_w₂'_eq, h_app₂]
                  exact List.mem_append_left _ h_in₂_pop
                · -- In new: shared between w₁' and w₂'
                  rw [h_w₂'_eq, h_app₂]
                  exact List.mem_append_right _ h_ev
              have h_sunt₂ : w₂.stepUntilNextTick = w₂'.stepUntilNextTick := by
                rw [World.stepUntilNextTick, h_step₂_eq]
              rw [h_sunt₂]
              exact ih w₂' h_nodes' h_tick' h_log' h_nextId' h_perm' h_future'
                h_cross' h_fut_mem' h_unique' h_pri' h_delay' h_new_pri'

/-- `stepUntilNextTick` produces permuted event lists for worlds that share the
same nodes/tick/outputLog/nextId and have permuted event lists with unique
priorities at the current tick. (Weaker than `stepUntilNextTick_perm_eq`:
the future-event sublists need only be permuted, not literally equal.) -/
theorem stepUntilNextTick_perm_events (w₁ w₂ : World)
    (h_nodes : w₁.nodes = w₂.nodes)
    (h_tick : w₁.tick = w₂.tick)
    (h_log : w₁.outputLog = w₂.outputLog)
    (h_nextId : w₁.nextId = w₂.nextId)
    (h_perm : List.Perm w₁.events w₂.events)
    (h_unique : ∀ ev₁ ∈ w₁.events, ∀ ev₂ ∈ w₁.events,
        ev₁.targetTick = w₁.tick → ev₂.targetTick = w₁.tick → ev₁ ≠ ev₂ →
        ev₁.priority ≠ ev₂.priority)
    (h_pri : ∀ ev ∈ w₁.events, ev.priority < 100)
    (h_delay : ∀ nid nd, w₁.getNode nid = some nd → ∀ d p,
        nd.kind = .repeater d p → d ≥ 2)
    (h_new_pri : ∀ nid nd, w₁.getNode nid = some nd → ∀ d p,
        nd.kind = .repeater d p → p < 100) :
    List.Perm w₁.stepUntilNextTick.events w₂.stepUntilNextTick.events := by
  suffices ∀ (w₁ w₂ : World), w₁.nodes = w₂.nodes → w₁.tick = w₂.tick →
      w₁.outputLog = w₂.outputLog → w₁.nextId = w₂.nextId →
      List.Perm w₁.events w₂.events →
      (∀ ev₁ ∈ w₁.events, ∀ ev₂ ∈ w₁.events,
        ev₁.targetTick = w₁.tick → ev₂.targetTick = w₁.tick → ev₁ ≠ ev₂ →
        ev₁.priority ≠ ev₂.priority) →
      (∀ ev ∈ w₁.events, ev.priority < 100) →
      (∀ nid nd, w₁.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2) →
      (∀ nid nd, w₁.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 100) →
      List.Perm w₁.stepUntilNextTick.events w₂.stepUntilNextTick.events from
    this w₁ w₂ h_nodes h_tick h_log h_nextId h_perm h_unique h_pri h_delay h_new_pri
  intro w₁
  induction w₁ using World.stepUntilNextTick.induct with
  | case1 w₁ h_step₁ =>
    intro w₂ h_nodes h_tick h_log h_nextId h_perm h_unique h_pri h_delay h_new_pri
    -- h_step₁ : w₁.step = none
    have h_no₁ : ∀ ev ∈ w₁.events, ev.targetTick ≠ w₁.tick := by
      dsimp [World.step] at h_step₁
      cases h_pop : w₁.popNextEvent with
      | none => exact popNextEvent_none_no_events w₁ h_pop
      | some p => simp [h_pop] at h_step₁
    have h_no₂ : ∀ ev ∈ w₂.events, ev.targetTick ≠ w₂.tick := by
      intro ev h_ev; rw [← h_tick]; intro h_eq
      exact h_no₁ ev (h_perm.symm.subperm.subset h_ev) h_eq
    have h_step₂ : w₂.step = none := by
      dsimp [World.step]
      cases h_pop : w₂.popNextEvent with
      | none => rfl
      | some p =>
        rcases p with ⟨ev, w'⟩
        have h_ev_tick := popNextEvent_at_tick w₂ ev w' h_pop
        obtain ⟨_, _, _, _, h_mem_ev, _⟩ := World.popNextEvent_eraseIdx w₂ ev w' h_pop
        exfalso; exact h_no₂ ev h_mem_ev h_ev_tick
    rw [stepUntilNextTick_of_step_none w₁ h_step₁, stepUntilNextTick_of_step_none w₂ h_step₂]
    exact h_perm
  | case2 w₁ w₁' h_step₁ ih =>
    intro w₂ h_nodes h_tick h_log h_nextId h_perm h_unique h_pri h_delay h_new_pri
    -- h_step₁ : w₁.step = some w₁'
    have h_sunt : w₁.stepUntilNextTick = w₁'.stepUntilNextTick := by
      rw [World.stepUntilNextTick, h_step₁]
    rw [h_sunt]
    -- w₂.step ≠ none as well
    have h_step₂' : w₂.step ≠ none := by
      intro h_contra
      dsimp [World.step] at h_contra
      cases h_pop : w₂.popNextEvent with
      | none =>
        have h_no₂ : ∀ ev ∈ w₂.events, ev.targetTick ≠ w₂.tick :=
          popNextEvent_none_no_events w₂ h_pop
        dsimp [World.step] at h_step₁
        cases h_pop₁ : w₁.popNextEvent with
        | none => simp [h_pop₁] at h_step₁
        | some p =>
          rcases p with ⟨ev, w'⟩
          have h_ev_tick := popNextEvent_at_tick w₁ ev w' h_pop₁
          have h_ev_in₂ : ev ∈ w₂.events := by
            obtain ⟨_, _, _, _, h_mem, _⟩ := World.popNextEvent_eraseIdx w₁ ev w' h_pop₁
            exact h_perm.subperm.subset h_mem
          exact h_no₂ ev h_ev_in₂ (h_ev_tick.trans h_tick)
      | some p => simp [h_pop] at h_contra
    cases h_s₂ : w₂.step with
    | none => contradiction
    | some w₂' =>
      have h_step₂_eq : w₂.step = some w₂' := h_s₂
      dsimp [World.step] at h_step₁ h_s₂
      cases h_pop₁ : w₁.popNextEvent with
      | none => simp [h_pop₁] at h_step₁
      | some p₁ =>
        rcases p₁ with ⟨ev₁, w₁_pop⟩
        simp only [h_pop₁] at h_step₁
        injection h_step₁ with h_w₁'
        cases h_pop₂ : w₂.popNextEvent with
        | none => simp [h_pop₂] at h_s₂
        | some p₂ =>
          rcases p₂ with ⟨ev₂, w₂_pop⟩
          simp only [h_pop₂] at h_s₂
          injection h_s₂ with h_w₂'
          have h_ev₁_tick : ev₁.targetTick = w₁.tick := popNextEvent_at_tick w₁ ev₁ w₁_pop h_pop₁
          have h_ev₂_tick : ev₂.targetTick = w₂.tick := popNextEvent_at_tick w₂ ev₂ w₂_pop h_pop₂
          obtain ⟨idx₁, h_idx₁, h_erase₁, _, h_mem₁, h_get₁⟩ := World.popNextEvent_eraseIdx w₁ ev₁ w₁_pop h_pop₁
          obtain ⟨idx₂, h_idx₂, h_erase₂, _, h_mem₂, h_get₂⟩ := World.popNextEvent_eraseIdx w₂ ev₂ w₂_pop h_pop₂
          have h_ev₁_in₂ : ev₁ ∈ w₂.events := h_perm.subperm.subset h_mem₁
          have h_ev₂_in₁ : ev₂ ∈ w₁.events := h_perm.symm.subperm.subset h_mem₂
          -- Both have minimum priority → ev₁ = ev₂
          have h_min₁ := popNextEvent_min_priority w₁ ev₁ w₁_pop h_pop₁
          have h_min₂ := popNextEvent_min_priority w₂ ev₂ w₂_pop h_pop₂
          have h_ev_eq : ev₁ = ev₂ := by
            have h_le₁ : ev₁.priority ≤ ev₂.priority :=
              h_min₁ ev₂ h_ev₂_in₁ (h_ev₂_tick.trans h_tick.symm)
            have h_le₂ : ev₂.priority ≤ ev₁.priority :=
              h_min₂ ev₁ h_ev₁_in₂ (h_ev₁_tick.trans h_tick)
            by_cases h_eq : ev₁ = ev₂
            · exact h_eq
            · exfalso
              have h_ne := h_unique ev₁ h_mem₁
                ev₂ h_ev₂_in₁ h_ev₁_tick (by rwa [h_tick]) h_eq
              omega
          rw [← h_ev_eq] at h_pop₂ h_w₂' h_ev₂_tick h_get₂
          -- After popping same event, remaining events are permuted
          have h_perm_pop : List.Perm w₁_pop.events w₂_pop.events := by
            rw [h_erase₁, h_erase₂]
            have hp₁ : List.Perm (ev₁ :: w₁.events.eraseIdx idx₁) w₁.events := by
              rw [← h_get₁]; exact List.perm_cons_eraseIdx h_idx₁
            have hp₂ : List.Perm (ev₁ :: w₂.events.eraseIdx idx₂) w₂.events := by
              rw [← h_get₂]; exact List.perm_cons_eraseIdx h_idx₂
            exact List.Perm.cons_inv (hp₁.trans (h_perm.trans hp₂.symm))
          -- Popped worlds share fields
          have h_nodes_pop : w₁_pop.nodes = w₂_pop.nodes := by
            rw [World.popNextEvent_nodes w₁ ev₁ w₁_pop h_pop₁,
                World.popNextEvent_nodes w₂ ev₁ w₂_pop h_pop₂, h_nodes]
          have h_tick_pop : w₁_pop.tick = w₂_pop.tick := by
            rw [World.popNextEvent_tick w₁ ev₁ w₁_pop h_pop₁,
                World.popNextEvent_tick w₂ ev₁ w₂_pop h_pop₂, h_tick]
          have h_log_pop : w₁_pop.outputLog = w₂_pop.outputLog := by
            rw [World.popNextEvent_outputLog w₁ ev₁ w₁_pop h_pop₁,
                World.popNextEvent_outputLog w₂ ev₁ w₂_pop h_pop₂, h_log]
          have h_nextId_pop : w₁_pop.nextId = w₂_pop.nextId := by
            rw [World.popNextEvent_nextId w₁ ev₁ w₁_pop h_pop₁,
                World.popNextEvent_nextId w₂ ev₁ w₂_pop h_pop₂, h_nextId]
          obtain ⟨h_nodes_st, h_tick_st, h_log_st, h_nextId_st, new, h_app₁, h_app₂⟩ :=
            World.onScheduledTick_congr_fields w₁_pop w₂_pop ev₁.nodeId
              h_nodes_pop h_tick_pop h_log_pop h_nextId_pop
          have h_w₁'_eq : w₁' = w₁_pop.onScheduledTick ev₁.nodeId := by rw [← h_w₁']
          have h_w₂'_eq : w₂' = w₂_pop.onScheduledTick ev₁.nodeId := by rw [← h_w₂']
          have h_nodes' : w₁'.nodes = w₂'.nodes := by rw [h_w₁'_eq, h_w₂'_eq]; exact h_nodes_st
          have h_tick' : w₁'.tick = w₂'.tick := by rw [h_w₁'_eq, h_w₂'_eq]; exact h_tick_st
          have h_log' : w₁'.outputLog = w₂'.outputLog := by rw [h_w₁'_eq, h_w₂'_eq]; exact h_log_st
          have h_nextId' : w₁'.nextId = w₂'.nextId := by rw [h_w₁'_eq, h_w₂'_eq]; exact h_nextId_st
          -- Permuted events after onScheduledTick
          have h_perm' : List.Perm w₁'.events w₂'.events := by
            rw [h_w₁'_eq, h_w₂'_eq, h_app₁, h_app₂]
            exact List.Perm.append h_perm_pop (List.Perm.refl new)
          -- New events are at future ticks
          have h_delay_pop : ∀ nid nd, w₁_pop.getNode nid = some nd → ∀ d p,
              nd.kind = .repeater d p → d ≥ 2 := by
            intro nid nd h_nd d p h_kind
            apply h_delay nid nd _ d p h_kind
            dsimp [World.getNode]; rw [← (World.popNextEvent_nodes w₁ ev₁ w₁_pop h_pop₁)]
            exact h_nd
          obtain ⟨new₁, h_app₁', h_fut₁⟩ := World.onScheduledTick_events_append w₁_pop ev₁.nodeId h_delay_pop
          have h_new_eq : new = new₁ := by
            have h : w₁_pop.events ++ new = w₁_pop.events ++ new₁ := by
              rw [← h_app₁, ← h_app₁']
            revert h
            induction w₁_pop.events with
            | nil => simp
            | cons hd tl ih' =>
              intro h
              have h' : tl ++ new = tl ++ new₁ := by
                simpa [List.cons_append] using h
              exact ih' h'
          have h_new_future : ∀ ev ∈ new, ev.targetTick ≠ w₁_pop.tick := by
            intro ev h_ev; rw [h_new_eq] at h_ev; have := h_fut₁ ev h_ev; omega
          -- Unique priorities preserved
          have h_tick_w₁'_orig : w₁'.tick = w₁.tick := by
            rw [h_w₁'_eq, World.onScheduledTick_tick,
                World.popNextEvent_tick w₁ ev₁ w₁_pop h_pop₁]
          have h_unique' : ∀ ev₁ ∈ w₁'.events, ∀ ev₂ ∈ w₁'.events,
              ev₁.targetTick = w₁'.tick → ev₂.targetTick = w₁'.tick → ev₁ ≠ ev₂ →
              ev₁.priority ≠ ev₂.priority := by
            intro ev₁' h_ev₁' ev₂' h_ev₂' h_tick₁' h_tick₂' h_ne'
            rw [h_w₁'_eq, h_app₁] at h_ev₁' h_ev₂'
            simp [List.mem_append] at h_ev₁' h_ev₂'
            rcases h_ev₁' with h_ev₁' | h_ev₁' <;> rcases h_ev₂' with h_ev₂' | h_ev₂'
            · -- Both in w₁_pop.events ⊆ w₁.events
              have h_ev₁_orig : ev₁' ∈ w₁.events := by
                rw [h_erase₁] at h_ev₁'; exact List.eraseIdx_subset' w₁.events idx₁ h_ev₁'
              have h_ev₂_orig : ev₂' ∈ w₁.events := by
                rw [h_erase₁] at h_ev₂'; exact List.eraseIdx_subset' w₁.events idx₁ h_ev₂'
              exact h_unique ev₁' h_ev₁_orig ev₂' h_ev₂_orig
                (by rw [h_tick_w₁'_orig] at h_tick₁'; exact h_tick₁')
                (by rw [h_tick_w₁'_orig] at h_tick₂'; exact h_tick₂') h_ne'
            · have := h_new_future ev₂' h_ev₂'
              rw [h_tick_w₁'_orig] at h_tick₂'
              have : w₁_pop.tick = w₁.tick := World.popNextEvent_tick w₁ ev₁ w₁_pop h_pop₁
              omega
            · have := h_new_future ev₁' h_ev₁'
              rw [h_tick_w₁'_orig] at h_tick₁'
              have : w₁_pop.tick = w₁.tick := World.popNextEvent_tick w₁ ev₁ w₁_pop h_pop₁
              omega
            · have h₁ := h_new_future ev₁' h_ev₁'
              have h₂ := h_new_future ev₂' h_ev₂'
              rw [h_tick_w₁'_orig] at h_tick₁' h_tick₂'
              have : w₁_pop.tick = w₁.tick := World.popNextEvent_tick w₁ ev₁ w₁_pop h_pop₁
              omega
          -- All priorities < 100
          have h_new_pri_pop : ∀ nid nd, w₁_pop.getNode nid = some nd → ∀ d p,
              nd.kind = .repeater d p → p < 100 := by
            intro nid nd h_nd d p h_kind
            apply h_new_pri nid nd _ d p h_kind
            dsimp [World.getNode]; rw [← (World.popNextEvent_nodes w₁ ev₁ w₁_pop h_pop₁)]
            exact h_nd
          have h_pri' : ∀ ev ∈ w₁'.events, ev.priority < 100 := by
            intro ev h_ev
            rw [h_w₁'_eq, h_app₁] at h_ev
            simp [List.mem_append] at h_ev
            rcases h_ev with h_ev | h_ev
            · have h_in_orig : ev ∈ w₁.events := by
                rw [h_erase₁] at h_ev; exact List.eraseIdx_subset' w₁.events idx₁ h_ev
              exact h_pri ev h_in_orig
            · by_cases h_in_pop : ev ∈ w₁_pop.events
              · have h_in_orig : ev ∈ w₁.events := by
                  rw [h_erase₁] at h_in_pop; exact List.eraseIdx_subset' w₁.events idx₁ h_in_pop
                exact h_pri ev h_in_orig
              · have h_new_ev := (World.onScheduledTick_new_events w₁_pop ev₁.nodeId h_new_pri_pop h_delay_pop).1
                have h_ev_st : ev ∈ (w₁_pop.onScheduledTick ev₁.nodeId).events := by
                  rw [h_app₁]; exact List.mem_append_right _ h_ev
                exact h_new_ev ev h_ev_st h_in_pop
          -- Delays preserved
          have h_delay' : ∀ nid nd, w₁'.getNode nid = some nd → ∀ d p,
              nd.kind = .repeater d p → d ≥ 2 := by
            intro nid nd h_nd d p h_kind
            rw [h_w₁'_eq] at h_nd
            obtain ⟨nd₀, h_nd₀, h_keq⟩ := World.onScheduledTick_getNode_kind w₁_pop ev₁.nodeId nid nd h_nd
            rw [← h_keq] at h_kind
            exact h_delay_pop nid nd₀ h_nd₀ d p h_kind
          -- Repeater priorities preserved
          have h_new_pri' : ∀ nid nd, w₁'.getNode nid = some nd → ∀ d p,
              nd.kind = .repeater d p → p < 100 := by
            intro nid nd h_nd d p h_kind
            rw [h_w₁'_eq] at h_nd
            obtain ⟨nd₀, h_nd₀, h_keq⟩ := World.onScheduledTick_getNode_kind w₁_pop ev₁.nodeId nid nd h_nd
            rw [← h_keq] at h_kind
            exact h_new_pri_pop nid nd₀ h_nd₀ d p h_kind
          have h_sunt₂ : w₂.stepUntilNextTick = w₂'.stepUntilNextTick := by
            rw [World.stepUntilNextTick, h_step₂_eq]
          rw [h_sunt₂]
          exact ih w₂' h_nodes' h_tick' h_log' h_nextId' h_perm'
            h_unique' h_pri' h_delay' h_new_pri'

/-- When `w.tick > t₂`, the foldl is independent of `pos`. -/
theorem foldl_simBody_pos_indep_from (t1 t2 pos pos' in1 in2 : Nat) (w : World) (n : Nat)
    (h_tick : w.tick > t2) :
    (List.range n).foldl (simBody t1 t2 pos in1 in2) w =
    (List.range n).foldl (simBody t1 t2 pos' in1 in2) w := by
  induction n generalizing w with
  | zero => rfl
  | succ n' ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [ih w h_tick]
    apply simBody_pos_indep
    rw [simFoldl_tick w t1 t2 pos' in1 in2 n']
    omega

/-- The foldl in `connectChain` preserves node kinds. -/
theorem foldl_updateNode_kind (w₀ : World) :
    ∀ (pairs : List (Nat × Nat)) (w : World),
    (∀ nid nd, w.getNode nid = some nd → ∃ nd₀, w₀.getNode nid = some nd₀ ∧ nd₀.kind = nd.kind) →
    ∀ nid nd, (pairs.foldl (fun w' x =>
      (w'.updateNode x.2 (fun nd => { nd with inputs := nd.inputs ++ [x.1] })).updateNode x.1
        (fun nd => { nd with outputs := nd.outputs ++ [x.2] })
    ) w).getNode nid = some nd →
    ∃ nd₀, w₀.getNode nid = some nd₀ ∧ nd₀.kind = nd.kind
  | [], w, h_pres, nid, nd, h_get => h_pres nid nd h_get
  | ⟨prev, curr⟩ :: ps, w, h_pres, nid, nd, h_get => by
    dsimp [List.foldl] at h_get
    set w₁ := (w.updateNode curr (fun nd => { nd with inputs := nd.inputs ++ [prev] })).updateNode prev
      (fun nd => { nd with outputs := nd.outputs ++ [curr] })
    have h_get' : (ps.foldl (fun w' x =>
        (w'.updateNode x.2 (fun nd => { nd with inputs := nd.inputs ++ [x.1] })).updateNode x.1
          (fun nd => { nd with outputs := nd.outputs ++ [x.2] })
      ) w₁).getNode nid = some nd := h_get
    obtain ⟨nd₁, h_nd₁, h_kind₁⟩ := foldl_updateNode_kind w₀ ps w₁
      (fun nid' nd' h_get' => by
        obtain ⟨nd₂, h_nd₂, h_kind₂⟩ := World.updateNode_getNode_kind
          (w.updateNode curr (fun nd => { nd with inputs := nd.inputs ++ [prev] }))
          prev nid' (fun nd => { nd with outputs := nd.outputs ++ [curr] })
          (fun nd => rfl) nd' h_get'
        obtain ⟨nd₃, h_nd₃, h_kind₃⟩ := World.updateNode_getNode_kind
          w curr nid' (fun nd => { nd with inputs := nd.inputs ++ [prev] })
          (fun nd => rfl) nd₂ h_nd₂
        obtain ⟨nd₀, h_nd₀, h_kind₀⟩ := h_pres nid' nd₃ h_nd₃
        exact ⟨nd₀, h_nd₀, h_kind₀.trans (h_kind₃.trans h_kind₂)⟩)
      nid nd h_get'
    exact ⟨nd₁, h_nd₁, h_kind₁⟩

/-- `connectChain` preserves node kinds. -/
theorem connectChain_kind_preserved (w : World) (ids : List Nat) :
    ∀ nid nd, (connectChain w ids).getNode nid = some nd →
    ∃ nd₀, w.getNode nid = some nd₀ ∧ nd₀.kind = nd.kind := by
  dsimp [connectChain]
  exact foldl_updateNode_kind w (ids.zip (ids.drop 1)) w
    (fun nid nd h_get => ⟨nd, h_get, rfl⟩)

/-- `addNode` preserves "all repeaters have delay ≥ 2", given the new node also satisfies it. -/
theorem addNode_preserves_delay_ge2 (w : World) (nd : NodeData)
    (h_w : ∀ nid nd, w.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2)
    (h_nd : ∀ d p, nd.kind = .repeater d p → d ≥ 2)
    (h_fresh : w.getNode w.nextId = none) :
    ∀ nid nd', (w.addNode nd).2.getNode nid = some nd' →
    ∀ d p, nd'.kind = .repeater d p → d ≥ 2 := by
  intro nid nd' h_get d p h_kind
  by_cases h_eq : nid = w.nextId
  · subst h_eq
    have h_new := World.addNode_getNode_fresh w nd h_fresh
    have h_eq_nd : nd' = nd := by
      have h : some nd' = some nd := h_get.symm.trans h_new
      injection h
    subst h_eq_nd
    exact h_nd d p h_kind
  · have h_old := World.addNode_getNode_old w nd nid h_eq
    rw [h_old] at h_get
    exact h_w nid nd' h_get d p h_kind

/-- The `repFoldlStep` foldl preserves "all repeaters have delay ≥ 2". -/
theorem repFoldl_preserves_delay_ge2 (delays : List PNat) :
    ∀ (acc : List Nat × World),
    (∀ nid nd, acc.2.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2) →
    (∀ d ∈ delays, d ≥ 2) →
    (∀ p ∈ acc.2.nodes, p.1 < acc.2.nextId) →
    ∀ nid nd, (delays.foldl repFoldlStep acc).2.getNode nid = some nd →
    ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
  induction delays with
  | nil =>
    intro acc h_acc h_delays h_ids nid nd h_get d p h_kind
    dsimp [List.foldl] at h_get
    exact h_acc nid nd h_get d p h_kind
  | cons d ds ih =>
    intro acc h_acc h_delays h_ids nid nd h_get d' p' h_kind
    dsimp [List.foldl] at h_get
    have h_d_ge2 : d ≥ 2 := h_delays d (by simp)
    have h_fresh : acc.2.getNode acc.2.nextId = none := World.getNode_nextId_none acc.2 h_ids
    have h_step : ∀ nid' nd', (repFoldlStep acc d).2.getNode nid' = some nd' →
        ∀ d'' p'', nd'.kind = .repeater d'' p'' → d'' ≥ 2 := by
      dsimp [repFoldlStep]
      exact addNode_preserves_delay_ge2 acc.2 (mkRepNode d) h_acc
        (by dsimp [mkRepNode]; intro d'' p'' h; injection h with h_d; subst h_d; exact h_d_ge2)
        h_fresh
    have h_ids' : ∀ p ∈ (repFoldlStep acc d).2.nodes, p.1 < (repFoldlStep acc d).2.nextId := by
      dsimp [repFoldlStep]
      exact World.addNode_ids_lt_nextId acc.2 (mkRepNode d) h_ids
    exact ih (repFoldlStep acc d) h_step
      (fun d'' h_mem => h_delays d'' (List.mem_cons_of_mem d h_mem))
      h_ids' nid nd h_get d' p' h_kind

/-- `connectChain` preserves events. -/
theorem connectChain_events (w : World) (ids : List Nat) :
    (connectChain w ids).events = w.events := by
  dsimp [connectChain]
  induction ids.zip (ids.drop 1) generalizing w with
  | nil => rfl
  | cons p ps ih =>
    dsimp only [List.foldl]
    rcases p with ⟨prev, curr⟩
    rw [ih, World.updateNode_events, World.updateNode_events]

/-- `buildChain` preserves events. -/
theorem buildChain_events (w : World) (name : String) (c : ChainSpec) :
    (buildChain w name c).2.events = w.events := by
  dsimp [buildChain]
  rw [connectChain_events]
  dsimp [buildChainPre]
  have h_add : ∀ (w : World) (nd : NodeData), (w.addNode nd).2.events = w.events := by
    intro w nd; dsimp [World.addNode]
  have h_rep : ∀ (acc : List Nat × World) (d : PNat),
      (repFoldlStep acc d).2.events = acc.2.events := by
    intro acc d; dsimp [repFoldlStep]; exact h_add acc.2 (mkRepNode d)
  have h_foldl : ∀ (l : List PNat) (acc : List Nat × World),
      (l.foldl repFoldlStep acc).2.events = acc.2.events := by
    intro l
    induction l with
    | nil => intro acc; rfl
    | cons d ds ih =>
      intro acc
      dsimp [List.foldl]
      rw [ih, h_rep]
  simp [h_add, h_foldl]

/-- `buildChain` preserves "no events". -/
theorem buildChain_no_events (w : World) (name : String) (c : ChainSpec)
    (h : w.events = []) : (buildChain w name c).2.events = [] := by
  rw [buildChain_events, h]

/-- The initial world (two chains built from empty) has no events. -/
theorem w0_events_empty (c1 c2 : ChainSpec) :
    (buildChain (buildChain World.empty "A" c1).2 "B" c2).2.events = [] := by
  rw [buildChain_events, buildChain_events]; rfl

/-- The initial world has tick 0. -/
theorem w0_tick (c1 c2 : ChainSpec) :
    (buildChain (buildChain World.empty "A" c1).2 "B" c2).2.tick = 0 := by
  dsimp (config := { zeta := true }) [buildChain, buildChainPre]
  suffices h_ct : ∀ w ids, (connectChain w ids).tick = w.tick by
    rw [h_ct]
    suffices h_fl : ∀ (d : List PNat) (ids : List Nat) (w : World),
        ((d.foldl repFoldlStep (ids, w)).2 : World).tick = w.tick by
      simp [World.addNode, World.empty, h_fl, h_ct]
    intro d ids w; induction d generalizing ids w with
    | nil => rfl
    | cons _ rest ih =>
      simp only [List.foldl_cons, repFoldlStep]
      rw [ih]; simp [World.addNode]
  intro w ids; dsimp [connectChain]
  induction ids.zip (ids.drop 1) generalizing w with
  | nil => rfl
  | cons p rest ih => cases p; simp [List.foldl_cons, ih]

/-- Before setInput in1 fires (ticks 0..t₂-1 when t₂ ≤ t₁), no events exist. -/
theorem simFoldl_no_events_before_activation (c1 c2 : ChainSpec) (t1 t2 pos' : Nat)
    (h_ge : t2 ≤ t1) :
    ∀ k, k ≤ t2 → ((List.range k).foldl (simBody t1 t2 pos'
      (buildChain World.empty "A" c1).1
      (buildChain (buildChain World.empty "A" c1).2 "B" c2).1)
      (buildChain (buildChain World.empty "A" c1).2 "B" c2).2).events = [] := by
  intro k hk
  induction k with
  | zero => simp [List.range_zero, List.foldl_nil]; exact w0_events_empty c1 c2
  | succ k' ih =>
    have hk' : k' ≤ t2 := by omega
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    have h_ih := ih hk'
    have h_tick : ((List.range k').foldl (simBody t1 t2 pos'
        (buildChain World.empty "A" c1).1
        (buildChain (buildChain World.empty "A" c1).2 "B" c2).1)
        (buildChain (buildChain World.empty "A" c1).2 "B" c2).2).tick = k' := by
      have := simFoldl_tick (buildChain (buildChain World.empty "A" c1).2 "B" c2).2 t1 t2 pos'
        (buildChain World.empty "A" c1).1
        (buildChain (buildChain World.empty "A" c1).2 "B" c2).1 k'
      rw [w0_tick c1 c2] at this; omega
    have h_ne_t1 : k' ≠ t1 := by omega
    have h_ne_t2 : k' ≠ t2 := by omega
    dsimp (config := { zeta := true }) [simBody]
    simp only [h_tick]
    have h_beq1 : (k' == t1) = false := by
      cases h : k' == t1 <;> simp_all
    have h_beq2 : (k' == t2) = false := by
      cases h : k' == t2 <;> simp_all
    simp only [h_beq1]
    set w_log := ((List.range k').foldl (simBody t1 t2 pos'
        (buildChain World.empty "A" c1).1
        (buildChain (buildChain World.empty "A" c1).2 "B" c2).1)
        (buildChain (buildChain World.empty "A" c1).2 "B" c2).2).logOutput s!"tick {k'}"
    have h_no_at_tick : ∀ ev ∈ w_log.events, ev.targetTick ≠ w_log.tick := by
      dsimp [w_log]; simp [h_ih]
    simp only [Bool.false_eq_true, ite_false]
    dsimp [w_log]
    simp only [h_tick, h_beq2, Bool.false_eq_true, ite_false]
    rw [stepUntilNextTick_events_eq_of_no_events _ h_no_at_tick]
    rw [World.logOutput_events, h_ih]
