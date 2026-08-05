import BasicProofs.PrefixChain.Part02


open BasicRedstoneSim

/-- `onScheduledTick` appends events at future ticks. -/
theorem World.onScheduledTick_events_append (w : World) (id : Nat)
    (h_delay : ∀ nid nd, w.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2) :
    ∃ new_events, (w.onScheduledTick id).events = w.events ++ new_events ∧
    ∀ ev ∈ new_events, ev.targetTick > w.tick := by
  dsimp [World.onScheduledTick]
  split
  · exact ⟨[], by simp, by simp⟩
  · rename_i nd; split
    · rename_i delay priority
      set w' := w.updateNode id (fun nd' => { nd' with sigLevel := if w.getInputSignal id > 0 then 15 else 0 })
      have h_ev' : w'.events = w.events := World.updateNode_events w id _
      have h_tick' : w'.tick = w.tick := World.updateNode_tick w id _
      dsimp [World.notifyOutputs]
      cases h_go : w'.getNode id with
      | none => exact ⟨[], by simp [h_ev'], by simp⟩
      | some nd' =>
        have h_delay' : ∀ nid nd, w'.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
          intro nid nd'' h_nd'' d p h_kind
          obtain ⟨nd_orig, h_go', h_keq⟩ :=
            World.updateNode_getNode_kind w id nid (fun nd => { nd with sigLevel := if w.getInputSignal id > 0 then 15 else 0 })
              (fun nd => rfl) nd'' h_nd''
          rw [← h_keq] at h_kind
          exact h_delay nid nd_orig h_go' d p h_kind
        obtain ⟨new_ev, h_app, h_fut⟩ := foldl_onNeighborUpdate_events_append nd'.outputs w' h_delay'
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
        have h_delay' : ∀ nid nd, w'.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
          intro nid nd'' h_nd'' d p h_kind
          obtain ⟨nd_orig, h_go', h_keq⟩ :=
            World.updateNode_getNode_kind w id nid (fun nd => { nd with sigLevel := 15 })
              (fun nd => rfl) nd'' h_nd''
          rw [← h_keq] at h_kind
          exact h_delay nid nd_orig h_go' d p h_kind
        obtain ⟨new_ev, h_app, h_fut⟩ := foldl_onNeighborUpdate_events_append nd'.outputs w' h_delay'
        refine ⟨new_ev, ?_, ?_⟩
        · rw [h_app, h_ev']
        · intro ev h_ev
          rw [h_tick'] at h_fut
          exact h_fut ev h_ev
    · exact ⟨[], by simp, by simp⟩

/-- `onScheduledTick` only appends events; existing events are preserved. -/
theorem World.onScheduledTick_events_subset (w : World) (id : Nat) :
    w.events ⊆ (w.onScheduledTick id).events := by
  have h_foldl : ∀ (l : List Nat) (w : World) (ev : ScheduledEvent), ev ∈ w.events →
      ev ∈ (l.foldl (fun w' outId => w'.onNeighborUpdate outId) w).events := by
    intro l; induction l with
    | nil => intro w ev h; exact h
    | cons hd tl ih =>
      intro w ev h
      simp only [List.foldl_cons]
      apply ih
      dsimp [World.onNeighborUpdate]
      split
      · exact h
      · split
        · rw [World.scheduleEvent_events]; exact List.mem_append_left _ h
        · rw [World.scheduleEvent_events]; exact List.mem_append_left _ h
        · rw [World.logOutput_events]; exact h
        · exact h
  dsimp [World.onScheduledTick]
  split
  · exact fun _ h => h
  · rename_i nd; split
    · -- repeater
      intro ev h_ev
      dsimp [World.notifyOutputs]
      cases h_go : (w.updateNode id (fun nd' => { nd' with sigLevel := if w.getInputSignal id > 0 then 15 else 0 })).getNode id with
      | none => simp [World.updateNode_events]; exact h_ev
      | some nd' =>
        have h_ev' : ev ∈ (w.updateNode id (fun nd' => { nd' with sigLevel := if w.getInputSignal id > 0 then 15 else 0 })).events := by
          simp [World.updateNode_events]; exact h_ev
        exact h_foldl nd'.outputs _ ev h_ev'
    · -- observer
      intro ev h_ev
      dsimp [World.notifyOutputs]
      cases h_go : (w.updateNode id (fun nd' => { nd' with sigLevel := 15 })).getNode id with
      | none => simp [World.updateNode_events]; exact h_ev
      | some nd' =>
        have h_ev' : ev ∈ (w.updateNode id (fun nd' => { nd' with sigLevel := 15 })).events := by
          simp [World.updateNode_events]; exact h_ev
        exact h_foldl nd'.outputs _ ev h_ev'
    · -- output/input
      exact fun _ h => h

/-- Erasing an element satisfying `p` decreases the filter count by exactly 1. -/
theorem List.eraseIdx_subset' {α : Type} (l : List α) (i : Nat) : l.eraseIdx i ⊆ l := by
  induction l generalizing i with
  | nil => simp [List.eraseIdx]
  | cons hd tl ih =>
    cases i with
    | zero => simp [List.eraseIdx]
    | succ i' =>
      simp only [List.eraseIdx]
      intro x hx
      rw [List.mem_cons] at hx ⊢
      rcases hx with rfl | hx
      · left; rfl
      · right; exact ih i' hx

theorem List.filter_eraseIdx_length {α : Type} (l : List α) (i : Nat) (p : α → Bool)
    (h_lt : i < l.length) (h_p : p l[i] = true) :
    ((l.eraseIdx i).filter p).length + 1 = (l.filter p).length := by
  revert i h_lt h_p
  induction l with
  | nil => intro i h_lt; simp [List.length] at h_lt
  | cons hd tl ih =>
    intro i h_lt h_p
    cases i with
    | zero =>
      have h_p' : p hd = true := by simpa using h_p
      have h_f : (hd :: tl).filter p = hd :: tl.filter p := by simp [List.filter, h_p']
      simp [List.eraseIdx, h_f]
    | succ i' =>
      have h_lt' : i' < tl.length := by simp [List.length] at h_lt; omega
      have h_p' : p tl[i'] = true := by simpa using h_p
      have h_ih := ih i' h_lt' h_p'
      by_cases h_hd : p hd = true
      · simp [List.eraseIdx]
        have h1 : (hd :: tl).filter p = hd :: tl.filter p := by simp [List.filter, h_hd]
        have h2 : (hd :: tl.eraseIdx i').filter p = hd :: (tl.eraseIdx i').filter p := by
          simp [List.filter, h_hd]
        rw [h2, h1]
        simp [List.length]
        omega
      · simp [List.eraseIdx]
        have h1 : (hd :: tl).filter p = tl.filter p := by simp [List.filter, h_hd]
        have h2 : (hd :: tl.eraseIdx i').filter p = (tl.eraseIdx i').filter p := by
          simp [List.filter, h_hd]
        rw [h2, h1]
        exact h_ih

/-- After `stepUntilNextTick`, no events at the old tick remain in the queue. -/
theorem stepUntilNextTick_no_events_at_tick (w : World) :
    ∀ ev ∈ (w.stepUntilNextTick).events, ev.targetTick ≠ w.tick := by
  induction w using World.stepUntilNextTick.induct with
  | case1 w h =>
    rw [stepUntilNextTick_of_step_none w h]
    intro ev h_ev h_tick
    dsimp [World.step] at h
    cases h_pop : w.popNextEvent with
    | some p => simp [h_pop] at h
    | none => exact popNextEvent_none_no_events w h_pop ev h_ev h_tick
  | case2 w w' h_step ih =>
    have h_sunt : w.stepUntilNextTick = w'.stepUntilNextTick := by
      rw [World.stepUntilNextTick, h_step]
    rw [h_sunt]
    have h_tick' : w'.tick = w.tick := World.step_tick w w' h_step
    intro ev h_ev h_tick
    have h_eq : ev.targetTick = w'.tick := by rw [h_tick, ← h_tick']
    exact ih ev h_ev h_eq

/-! ### Layer 5: Two-element queue order independence -/

/-- `processNEvents` is the identity when `step = none`. -/
theorem processNEvents_of_step_none (w : World) (n : Nat) (h : w.step = none) :
    processNEvents w n = w := by
  induction n with
  | zero => rfl
  | succ n' ih => simp [processNEvents, h]

/-- `popNextEvent` preserves `nextId`. -/
theorem World.popNextEvent_nextId (w : World) :
    ∀ ev w', w.popNextEvent = some (ev, w') → w'.nextId = w.nextId := by
  intro ev w' h
  unfold World.popNextEvent at h
  dsimp (config := { zeta := true }) at h
  split at h <;> try contradiction
  · split at h <;> try contradiction
    · injection h with h_pair; rcases h_pair with ⟨rfl, rfl⟩; rfl

/-- `popNextEvent` preserves `outputLog`. -/
theorem World.popNextEvent_outputLog (w : World) :
    ∀ ev w', w.popNextEvent = some (ev, w') → w'.outputLog = w.outputLog := by
  intro ev w' h
  unfold World.popNextEvent at h
  dsimp (config := { zeta := true }) at h
  split at h <;> try contradiction
  · split at h <;> try contradiction
    · injection h with h_pair; rcases h_pair with ⟨rfl, rfl⟩; rfl

/-- `popNextEvent` on `[ev₁, ev₂]` with `ev₁.priority < ev₂.priority` pops `ev₁`, leaves `[ev₂]`. -/
theorem popNextEvent_two_first (w : World) (ev₁ ev₂ : ScheduledEvent)
    (h_tick₁ : ev₁.targetTick = w.tick)
    (_ : ev₂.targetTick = w.tick)
    (h_pri : ev₁.priority < ev₂.priority)
    (h_pri₁ : ev₁.priority < (100 : Int))
    (h_pri₂ : ev₂.priority < (100 : Int))
    (h_events : w.events = [ev₁, ev₂]) :
    w.popNextEvent = some (ev₁, {w with events := [ev₂]}) := by
  cases h_pop : w.popNextEvent with
  | none =>
    have h_pri' : ∀ ev ∈ w.events, ev.priority < 100 := by
      intro ev h
      have h' : ev ∈ [ev₁, ev₂] := by rw [← h_events]; exact h
      obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp h'
      have : i < 2 := by simpa using hi
      interval_cases i
      · change ev₁ = ev at heq; exact heq ▸ h_pri₁
      · change ev₂ = ev at heq; exact heq ▸ h_pri₂
    have h_mem : ev₁ ∈ w.events := by
      rw [h_events]
      exact List.mem_iff_getElem.mpr ⟨0, by norm_num, rfl⟩
    exact False.elim (popNextEvent_none_no_events w h_pop ev₁ h_mem h_tick₁)
  | some p =>
    rcases p with ⟨ev, w'⟩
    obtain ⟨idx, h_idx_lt, h_erase, h_ev_tick, h_ev_mem, h_getElem⟩ := World.popNextEvent_eraseIdx w ev w' h_pop
    have h_min := popNextEvent_min_priority w ev w' h_pop
    -- ev = ev₁
    have h_ev_eq : ev = ev₁ := by
      have h_ev_mem' : ev ∈ [ev₁, ev₂] := by rw [← h_events]; exact h_ev_mem
      obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp h_ev_mem'
      have : i < 2 := by simpa using hi
      interval_cases i
      · change ev₁ = ev at heq; exact heq.symm
      · change ev₂ = ev at heq
        have := h_min ev₁ (by rw [h_events]; exact List.mem_iff_getElem.mpr ⟨0, by norm_num, rfl⟩) h_tick₁
        rw [← heq] at this; omega
    -- idx = 0
    have h_ne₁₂ : ev₁ ≠ ev₂ := by intro h; rw [h] at h_pri; omega
    have h_idx₀ : idx = 0 := by
      have h_lt₂ : idx < 2 := by rw [h_events] at h_idx_lt; simpa using h_idx_lt
      interval_cases idx
      · rfl
      · exfalso
        have h₁ := h_getElem.trans h_ev_eq
        have : ev₂ = ev₁ := by simpa [h_events] using h₁
        exact h_ne₁₂ this.symm
    -- w'.events = [ev₂]
    have h_w'_ev : w'.events = [ev₂] := by rw [h_erase, h_events, h_idx₀]; rfl
    -- w' = {w with events := [ev₂]}
    have h_pop_saved := h_pop
    have h_w'_eq : w' = {w with events := [ev₂]} := by
      have h_nodes := World.popNextEvent_nodes w ev w' h_pop
      have h_tick := World.popNextEvent_tick w ev w' h_pop
      have h_nextId := World.popNextEvent_nextId w ev w' h_pop
      have h_log := World.popNextEvent_outputLog w ev w' h_pop
      ext <;> simp_all
    rw [← h_ev_eq, ← h_w'_eq]

/-- `popNextEvent` on `[ev₂, ev₁]` with `ev₁.priority < ev₂.priority` pops `ev₁`, leaves `[ev₂]`. -/
theorem popNextEvent_two_second (w : World) (ev₁ ev₂ : ScheduledEvent)
    (h_tick₁ : ev₁.targetTick = w.tick)
    (_ : ev₂.targetTick = w.tick)
    (h_pri : ev₁.priority < ev₂.priority)
    (h_pri₁ : ev₁.priority < (100 : Int))
    (h_pri₂ : ev₂.priority < (100 : Int))
    (h_events : w.events = [ev₂, ev₁]) :
    w.popNextEvent = some (ev₁, {w with events := [ev₂]}) := by
  cases h_pop : w.popNextEvent with
  | none =>
    have h_pri' : ∀ ev ∈ w.events, ev.priority < 100 := by
      intro ev h
      have h' : ev ∈ [ev₂, ev₁] := by rw [← h_events]; exact h
      obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp h'
      have : i < 2 := by simpa using hi
      interval_cases i
      · change ev₂ = ev at heq; exact heq ▸ h_pri₂
      · change ev₁ = ev at heq; exact heq ▸ h_pri₁
    have h_mem : ev₁ ∈ w.events := by
      rw [h_events]
      exact List.mem_iff_getElem.mpr ⟨1, by norm_num, rfl⟩
    exact False.elim (popNextEvent_none_no_events w h_pop ev₁ h_mem h_tick₁)
  | some p =>
    rcases p with ⟨ev, w'⟩
    obtain ⟨idx, h_idx_lt, h_erase, h_ev_tick, h_ev_mem, h_getElem⟩ := World.popNextEvent_eraseIdx w ev w' h_pop
    have h_min := popNextEvent_min_priority w ev w' h_pop
    -- ev = ev₁
    have h_ev_eq : ev = ev₁ := by
      have h_ev_mem' : ev ∈ [ev₂, ev₁] := by rw [← h_events]; exact h_ev_mem
      obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp h_ev_mem'
      have : i < 2 := by simpa using hi
      interval_cases i
      · change ev₂ = ev at heq
        have := h_min ev₁ (by rw [h_events]; exact List.mem_iff_getElem.mpr ⟨1, by norm_num, rfl⟩) h_tick₁
        rw [← heq] at this; omega
      · change ev₁ = ev at heq; exact heq.symm
    -- idx = 1
    have h_ne₁₂ : ev₁ ≠ ev₂ := by intro h; rw [h] at h_pri; omega
    have h_idx₁ : idx = 1 := by
      have h_lt₂ : idx < 2 := by rw [h_events] at h_idx_lt; simpa using h_idx_lt
      interval_cases idx
      · exfalso
        have h₁ := h_getElem.trans h_ev_eq
        have h₂ : w.events[0] = ev₂ := by simp [h_events]
        exact h_ne₁₂ (h₁.symm.trans h₂)
      · rfl
    -- w'.events = [ev₂]
    have h_w'_ev : w'.events = [ev₂] := by rw [h_erase, h_events, h_idx₁]; simp [List.eraseIdx]
    -- w' = {w with events := [ev₂]}
    have h_pop_saved := h_pop
    have h_w'_eq : w' = {w with events := [ev₂]} := by
      have h_nodes := World.popNextEvent_nodes w ev w' h_pop
      have h_tick := World.popNextEvent_tick w ev w' h_pop
      have h_nextId := World.popNextEvent_nextId w ev w' h_pop
      have h_log := World.popNextEvent_outputLog w ev w' h_pop
      ext <;> simp_all
    rw [← h_ev_eq, ← h_w'_eq]

/-- `stepUntilNextTick` is independent of queue order for two events with distinct priorities.
After one step, both orderings converge to the same world (ev₁ is always popped first). -/
theorem stepUntilNextTick_swap_two (w : World) (ev₁ ev₂ : ScheduledEvent)
    (h_tick₁ : ev₁.targetTick = w.tick)
    (h_tick₂ : ev₂.targetTick = w.tick)
    (h_pri : ev₁.priority < ev₂.priority)
    (h_pri₁ : ev₁.priority < (100 : Int))
    (h_pri₂ : ev₂.priority < (100 : Int)) :
    ({w with events := [ev₁, ev₂]} : World).stepUntilNextTick =
    ({w with events := [ev₂, ev₁]} : World).stepUntilNextTick := by
  set w₁ := {w with events := [ev₁, ev₂]}
  set w₂ := {w with events := [ev₂, ev₁]}
  have h_pop₁ : w₁.popNextEvent = some (ev₁, {w with events := [ev₂]}) :=
    popNextEvent_two_first w₁ ev₁ ev₂
      (by simp [w₁, h_tick₁]) (by simp [w₁, h_tick₂]) h_pri h_pri₁ h_pri₂ rfl
  have h_pop₂ : w₂.popNextEvent = some (ev₁, {w with events := [ev₂]}) :=
    popNextEvent_two_second w₂ ev₁ ev₂
      (by simp [w₂, h_tick₁]) (by simp [w₂, h_tick₂]) h_pri h_pri₁ h_pri₂ rfl
  have h_step₁ : w₁.step = some (({w with events := [ev₂]} : World).onScheduledTick ev₁.nodeId) := by
    unfold World.step; rw [h_pop₁]
  have h_step₂ : w₂.step = some (({w with events := [ev₂]} : World).onScheduledTick ev₁.nodeId) := by
    unfold World.step; rw [h_pop₂]
  rw [World.stepUntilNextTick, h_step₁, World.stepUntilNextTick, h_step₂]

/-- `stepUntilNextTick` is invariant under swapping two events at the end of the event list
when they have different priorities and no other events in the prefix are at the current tick. -/
theorem stepUntilNextTick_swap_end (w : World) (l : List ScheduledEvent)
    (ev₁ ev₂ : ScheduledEvent)
    (h_tick₁ : ev₁.targetTick = w.tick)
    (_ : ev₂.targetTick = w.tick)
    (h_pri : ev₁.priority < ev₂.priority)
    (h_pri₁ : ev₁.priority < (100 : Int))
    (h_pri₂ : ev₂.priority < (100 : Int))
    (h_pri_l : ∀ ev ∈ l, ev.priority < 100)
    (h_no_other : ∀ ev ∈ l, ev.targetTick ≠ w.tick) :
    ({w with events := l ++ [ev₁, ev₂]} : World).stepUntilNextTick =
    ({w with events := l ++ [ev₂, ev₁]} : World).stepUntilNextTick := by
  set w₁ := {w with events := l ++ [ev₁, ev₂]}
  set w₂ := {w with events := l ++ [ev₂, ev₁]}
  have h_pri_w₁ : ∀ ev ∈ w₁.events, ev.priority < 100 := by
    intro ev h_ev; dsimp [w₁] at h_ev
    have : ev ∈ l ∨ ev = ev₁ ∨ ev = ev₂ := by simpa using h_ev
    rcases this with h | h | h
    · exact h_pri_l ev h
    · rwa [h]
    · rwa [h]
  have h_pri_w₂ : ∀ ev ∈ w₂.events, ev.priority < 100 := by
    intro ev h_ev; dsimp [w₂] at h_ev
    have : ev ∈ l ∨ ev = ev₂ ∨ ev = ev₁ := by simpa using h_ev
    rcases this with h | h | h
    · exact h_pri_l ev h
    · rwa [h]
    · rwa [h]
  -- Both worlds pop ev₁ first (lowest priority at current tick)
  have h_w₁_tick : w₁.tick = w.tick := rfl
  have h_w₂_tick : w₂.tick = w.tick := rfl
  have h_pop₁ : w₁.popNextEvent = some (ev₁, {w with events := l ++ [ev₂]}) := by
    cases h_pop : w₁.popNextEvent with
    | none =>
      exfalso
      have h_mem : ev₁ ∈ w₁.events := by dsimp [w₁]; simp
      exact popNextEvent_none_no_events w₁ h_pop ev₁ h_mem (h_tick₁.trans rfl)
    | some p =>
      rcases p with ⟨ev, w'⟩
      have h_ev_tick : ev.targetTick = w₁.tick := popNextEvent_at_tick w₁ ev w' h_pop
      have h_ev_eq : ev = ev₁ := by
        obtain ⟨idx, _, h_erase, _, h_mem, _⟩ := World.popNextEvent_eraseIdx w₁ ev w' h_pop
        have : ev ∈ l ∨ ev = ev₁ ∨ ev = ev₂ := by dsimp [w₁] at h_mem; simpa using h_mem
        rcases this with h_in_l | h | h
        · exfalso; exact h_no_other ev h_in_l (h_ev_tick.trans rfl)
        · exact h
        · exfalso
          have h_min := popNextEvent_min_priority w₁ ev w' h_pop
          have h_min₁ := h_min ev₁ (by dsimp [w₁]; simp) (h_tick₁.trans rfl)
          rw [h] at h_min₁; omega
      rw [h_ev_eq] at h_pop
      obtain ⟨idx, h_idx_lt, h_erase, _, _, h_getElem⟩ := World.popNextEvent_eraseIdx w₁ ev₁ w' h_pop
      have h_idx : idx = l.length := by
        dsimp [w₁] at h_idx_lt
        by_contra h_ne
        have h_range : idx < l.length ∨ idx = l.length + 1 := by
          simp [List.length] at h_idx_lt; omega
        rcases h_range with h_lt | h_eq
        · have h_app := getElem_append_of_lt l [ev₁, ev₂] idx h_lt
          have h_l_eq : l[idx] = ev₁ := h_app.symm.trans h_getElem
          have h_mem_l : ev₁ ∈ l := by rw [← h_l_eq]; exact List.getElem_mem h_lt
          exact h_no_other ev₁ h_mem_l (by rw [← h_ev_eq]; exact h_ev_tick.trans rfl)
        · subst h_eq
          have h_ev₂ := (getElem_append_right_eq l ev₁ ev₂).2
          have h_l_eq : ev₂ = ev₁ := h_ev₂.symm.trans h_getElem
          rw [h_l_eq] at h_pri; omega
      have h_nodes := World.popNextEvent_nodes w₁ ev₁ w' h_pop
      have h_tick := World.popNextEvent_tick w₁ ev₁ w' h_pop
      have h_nextId := World.popNextEvent_nextId w₁ ev₁ w' h_pop
      have h_log := World.popNextEvent_outputLog w₁ ev₁ w' h_pop
      have h_evts : w'.events = l ++ [ev₂] := by
        rw [h_erase, h_idx]; dsimp [w₁]; exact eraseIdx_append_two l ev₁ ev₂
      have h_w'_eq : w' = {w with events := l ++ [ev₂]} := by
        ext <;> simp_all [w₁]
      rw [← h_w'_eq, h_ev_eq]
  have h_pop₂ : w₂.popNextEvent = some (ev₁, {w with events := l ++ [ev₂]}) := by
    cases h_pop : w₂.popNextEvent with
    | none =>
      exfalso
      have h_mem : ev₁ ∈ w₂.events := by dsimp [w₂]; simp
      exact popNextEvent_none_no_events w₂ h_pop ev₁ h_mem (h_tick₁.trans rfl)
    | some p =>
      rcases p with ⟨ev, w'⟩
      have h_ev_tick : ev.targetTick = w₂.tick := popNextEvent_at_tick w₂ ev w' h_pop
      have h_ev_eq : ev = ev₁ := by
        obtain ⟨idx, _, h_erase, _, h_mem, _⟩ := World.popNextEvent_eraseIdx w₂ ev w' h_pop
        have : ev ∈ l ∨ ev = ev₂ ∨ ev = ev₁ := by dsimp [w₂] at h_mem; simpa using h_mem
        rcases this with h_in_l | h | h
        · exfalso; exact h_no_other ev h_in_l (h_ev_tick.trans rfl)
        · exfalso
          have h_min := popNextEvent_min_priority w₂ ev w' h_pop
          have h_min₁ := h_min ev₁ (by dsimp [w₂]; simp) (h_tick₁.trans rfl)
          rw [h] at h_min₁; omega
        · exact h
      rw [h_ev_eq] at h_pop
      obtain ⟨idx, h_idx_lt, h_erase, _, _, h_getElem⟩ := World.popNextEvent_eraseIdx w₂ ev₁ w' h_pop
      have h_idx : idx = l.length + 1 := by
        dsimp [w₂] at h_idx_lt
        by_contra h_ne
        have h_range : idx < l.length ∨ idx = l.length := by
          simp [List.length] at h_idx_lt; omega
        rcases h_range with h_lt | h_eq
        · have h_app := getElem_append_of_lt l [ev₂, ev₁] idx h_lt
          have h_l_eq : l[idx] = ev₁ := h_app.symm.trans h_getElem
          have h_mem_l : ev₁ ∈ l := by rw [← h_l_eq]; exact List.getElem_mem h_lt
          exact h_no_other ev₁ h_mem_l (by rw [← h_ev_eq]; exact h_ev_tick.trans rfl)
        · subst h_eq
          have h_ev₂ := (getElem_append_right_eq l ev₂ ev₁).1
          have h_l_eq : ev₂ = ev₁ := h_ev₂.symm.trans h_getElem
          rw [h_l_eq] at h_pri; omega
      have h_nodes := World.popNextEvent_nodes w₂ ev₁ w' h_pop
      have h_tick := World.popNextEvent_tick w₂ ev₁ w' h_pop
      have h_nextId := World.popNextEvent_nextId w₂ ev₁ w' h_pop
      have h_log := World.popNextEvent_outputLog w₂ ev₁ w' h_pop
      have h_evts : w'.events = l ++ [ev₂] := by
        rw [h_erase, h_idx]; dsimp [w₂]; exact eraseIdx_append_two_right l ev₂ ev₁
      have h_w'_eq : w' = {w with events := l ++ [ev₂]} := by
        ext <;> simp_all [w₂]
      rw [← h_w'_eq, h_ev_eq]
  have h_step₁ : w₁.step = some (({w with events := l ++ [ev₂]} : World).onScheduledTick ev₁.nodeId) := by
    unfold World.step; rw [h_pop₁]
  have h_step₂ : w₂.step = some (({w with events := l ++ [ev₂]} : World).onScheduledTick ev₁.nodeId) := by
    unfold World.step; rw [h_pop₂]
  rw [World.stepUntilNextTick, h_step₁, World.stepUntilNextTick, h_step₂]

/-- `stepUntilNextTick` is invariant under swapping two events with different priorities
in the event list, when no other events in the prefix/suffix target the current tick.
Both worlds pop ev₁ first (lowest priority), leaving identical remaining worlds. -/
theorem stepUntilNextTick_swap_mid (w : World) (l r : List ScheduledEvent)
    (ev₁ ev₂ : ScheduledEvent)
    (h_tick₁ : ev₁.targetTick = w.tick)
    (_ : ev₂.targetTick = w.tick)
    (h_pri : ev₁.priority < ev₂.priority)
    (h_pri₁ : ev₁.priority < (100 : Int))
    (h_pri₂ : ev₂.priority < (100 : Int))
    (h_pri_lr : ∀ ev ∈ l ++ r, ev.priority < 100)
    (h_no_other : ∀ ev ∈ l ++ r, ev.targetTick ≠ w.tick) :
    ({w with events := l ++ [ev₁, ev₂] ++ r} : World).stepUntilNextTick =
    ({w with events := l ++ [ev₂, ev₁] ++ r} : World).stepUntilNextTick := by
  set w₁ := {w with events := l ++ [ev₁, ev₂] ++ r}
  set w₂ := {w with events := l ++ [ev₂, ev₁] ++ r}
  have h_pri_w₁ : ∀ ev ∈ w₁.events, ev.priority < 100 := by
    intro ev h_ev; dsimp [w₁] at h_ev
    have : ev ∈ l ∨ ev = ev₁ ∨ ev = ev₂ ∨ ev ∈ r := by simpa [List.mem_append] using h_ev
    rcases this with h | h | h | h
    · have := h_pri_lr ev (by simp [List.mem_append, h]); exact this
    · rwa [h]
    · rwa [h]
    · have := h_pri_lr ev (by simp [List.mem_append, h]); exact this
  have h_pri_w₂ : ∀ ev ∈ w₂.events, ev.priority < 100 := by
    intro ev h_ev; dsimp [w₂] at h_ev
    have : ev ∈ l ∨ ev = ev₂ ∨ ev = ev₁ ∨ ev ∈ r := by simpa [List.mem_append] using h_ev
    rcases this with h | h | h | h
    · have := h_pri_lr ev (by simp [List.mem_append, h]); exact this
    · rwa [h]
    · rwa [h]
    · have := h_pri_lr ev (by simp [List.mem_append, h]); exact this
  have h_no_l : ∀ ev ∈ l, ev.targetTick ≠ w.tick := fun ev h => h_no_other ev (by simp [List.mem_append, h])
  have h_no_r : ∀ ev ∈ r, ev.targetTick ≠ w.tick := fun ev h => h_no_other ev (by simp [List.mem_append, h])
  -- w₁ pops ev₁ at index |l|
  have h_pop₁ : w₁.popNextEvent = some (ev₁, {w with events := l ++ [ev₂] ++ r}) := by
    cases h_pop : w₁.popNextEvent with
    | none =>
      exfalso
      exact popNextEvent_none_no_events w₁ h_pop ev₁ (by dsimp [w₁]; simp) (h_tick₁.trans rfl)
    | some p =>
      rcases p with ⟨ev, w'⟩
      have h_ev_tick : ev.targetTick = w₁.tick := popNextEvent_at_tick w₁ ev w' h_pop
      have h_ev_eq : ev = ev₁ := by
        obtain ⟨idx, _, _, _, h_mem, _⟩ := World.popNextEvent_eraseIdx w₁ ev w' h_pop
        have : ev ∈ l ∨ ev = ev₁ ∨ ev = ev₂ ∨ ev ∈ r := by dsimp [w₁] at h_mem; simpa [List.mem_append] using h_mem
        rcases this with h_in_l | h | h | h_in_r
        · exfalso; exact h_no_l ev h_in_l (h_ev_tick.trans rfl)
        · exact h
        · exfalso
          have h_min := popNextEvent_min_priority w₁ ev w' h_pop
          have := h_min ev₁ (by dsimp [w₁]; simp) (h_tick₁.trans rfl)
          rw [h] at this; omega
        · exfalso; exact h_no_r ev h_in_r (h_ev_tick.trans rfl)
      rw [h_ev_eq] at h_pop
      obtain ⟨idx, h_idx_lt, h_erase, _, _, h_getElem⟩ := World.popNextEvent_eraseIdx w₁ ev₁ w' h_pop
      have h_idx : idx = l.length :=
        getElem_eq_of_not_mem_append_two l r ev₁ ev₂
          (fun h => h_no_l ev₁ h (h_tick₁.trans rfl))
          (fun h => h_no_r ev₁ h (h_tick₁.trans rfl))
          (fun h => by rw [h] at h_pri; omega)
          idx h_idx_lt h_getElem
      have h_nodes := World.popNextEvent_nodes w₁ ev₁ w' h_pop
      have h_tick := World.popNextEvent_tick w₁ ev₁ w' h_pop
      have h_nextId := World.popNextEvent_nextId w₁ ev₁ w' h_pop
      have h_log := World.popNextEvent_outputLog w₁ ev₁ w' h_pop
      have h_evts : w'.events = l ++ [ev₂] ++ r := by
        rw [h_erase, h_idx]; dsimp [w₁]; exact eraseIdx_append_two_mid l r ev₁ ev₂
      have h_w'_eq : w' = {w with events := l ++ [ev₂] ++ r} := by
        ext <;> simp_all [w₁]
      rw [← h_w'_eq, h_ev_eq]
  -- w₂ pops ev₁ at index |l|+1
  have h_pop₂ : w₂.popNextEvent = some (ev₁, {w with events := l ++ [ev₂] ++ r}) := by
    cases h_pop : w₂.popNextEvent with
    | none =>
      exfalso
      exact popNextEvent_none_no_events w₂ h_pop ev₁ (by dsimp [w₂]; simp) (h_tick₁.trans rfl)
    | some p =>
      rcases p with ⟨ev, w'⟩
      have h_ev_tick : ev.targetTick = w₂.tick := popNextEvent_at_tick w₂ ev w' h_pop
      have h_ev_eq : ev = ev₁ := by
        obtain ⟨idx, _, _, _, h_mem, _⟩ := World.popNextEvent_eraseIdx w₂ ev w' h_pop
        have : ev ∈ l ∨ ev = ev₂ ∨ ev = ev₁ ∨ ev ∈ r := by dsimp [w₂] at h_mem; simpa [List.mem_append] using h_mem
        rcases this with h_in_l | h | h | h_in_r
        · exfalso; exact h_no_l ev h_in_l (h_ev_tick.trans rfl)
        · exfalso
          have h_min := popNextEvent_min_priority w₂ ev w' h_pop
          have := h_min ev₁ (by dsimp [w₂]; simp) (h_tick₁.trans rfl)
          rw [h] at this; omega
        · exact h
        · exfalso; exact h_no_r ev h_in_r (h_ev_tick.trans rfl)
      rw [h_ev_eq] at h_pop
      obtain ⟨idx, h_idx_lt, h_erase, _, _, h_getElem⟩ := World.popNextEvent_eraseIdx w₂ ev₁ w' h_pop
      have h_idx : idx = l.length + 1 :=
        getElem_eq_of_not_mem_append_two_right l r ev₁ ev₂
          (fun h => h_no_l ev₁ h (h_tick₁.trans rfl))
          (fun h => h_no_r ev₁ h (h_tick₁.trans rfl))
          (fun h => by rw [h] at h_pri; omega)
          idx h_idx_lt h_getElem
      have h_nodes := World.popNextEvent_nodes w₂ ev₁ w' h_pop
      have h_tick := World.popNextEvent_tick w₂ ev₁ w' h_pop
      have h_nextId := World.popNextEvent_nextId w₂ ev₁ w' h_pop
      have h_log := World.popNextEvent_outputLog w₂ ev₁ w' h_pop
      have h_evts : w'.events = l ++ [ev₂] ++ r := by
        rw [h_erase, h_idx]; dsimp [w₂]; exact eraseIdx_append_two_mid_right l r ev₂ ev₁
      have h_w'_eq : w' = {w with events := l ++ [ev₂] ++ r} := by
        ext <;> simp_all [w₂]
      rw [← h_w'_eq, h_ev_eq]
  have h_step₁ : w₁.step = some (({w with events := l ++ [ev₂] ++ r} : World).onScheduledTick ev₁.nodeId) := by
    unfold World.step; rw [h_pop₁]
  have h_step₂ : w₂.step = some (({w with events := l ++ [ev₂] ++ r} : World).onScheduledTick ev₁.nodeId) := by
    unfold World.step; rw [h_pop₂]
  rw [World.stepUntilNextTick, h_step₁, World.stepUntilNextTick, h_step₂]

/-- `stepUntilNextTick` is invariant under swapping two events where only the first targets
the current tick.  Popping ev₁ leaves the same remaining list `l ++ [ev₂] ++ r` in both cases. -/
theorem stepUntilNextTick_swap_future (w : World) (l r : List ScheduledEvent)
    (ev₁ ev₂ : ScheduledEvent)
    (h_tick₁ : ev₁.targetTick = w.tick)
    (h_tick₂ : ev₂.targetTick ≠ w.tick)
    (h_pri₁ : ev₁.priority < (100 : Int))
    (h_pri₂ : ev₂.priority < (100 : Int))
    (h_pri_lr : ∀ ev ∈ l ++ r, ev.priority < 100)
    (h_no_other : ∀ ev ∈ l ++ r, ev.targetTick ≠ w.tick) :
    ({w with events := l ++ [ev₁, ev₂] ++ r} : World).stepUntilNextTick =
    ({w with events := l ++ [ev₂, ev₁] ++ r} : World).stepUntilNextTick := by
  set w₁ := {w with events := l ++ [ev₁, ev₂] ++ r}
  set w₂ := {w with events := l ++ [ev₂, ev₁] ++ r}
  have h_pri_w₁ : ∀ ev ∈ w₁.events, ev.priority < 100 := by
    intro ev h_ev; dsimp [w₁] at h_ev
    have : ev ∈ l ∨ ev = ev₁ ∨ ev = ev₂ ∨ ev ∈ r := by simpa [List.mem_append] using h_ev
    rcases this with h | h | h | h
    · exact h_pri_lr ev (by simp [List.mem_append, h])
    · rwa [h]
    · rwa [h]
    · exact h_pri_lr ev (by simp [List.mem_append, h])
  have h_pri_w₂ : ∀ ev ∈ w₂.events, ev.priority < 100 := by
    intro ev h_ev; dsimp [w₂] at h_ev
    have : ev ∈ l ∨ ev = ev₂ ∨ ev = ev₁ ∨ ev ∈ r := by simpa [List.mem_append] using h_ev
    rcases this with h | h | h | h
    · exact h_pri_lr ev (by simp [List.mem_append, h])
    · rwa [h]
    · rwa [h]
    · exact h_pri_lr ev (by simp [List.mem_append, h])
  have h_no_l : ∀ ev ∈ l, ev.targetTick ≠ w.tick := fun ev h => h_no_other ev (by simp [List.mem_append, h])
  have h_no_r : ∀ ev ∈ r, ev.targetTick ≠ w.tick := fun ev h => h_no_other ev (by simp [List.mem_append, h])
  -- w₁ pops ev₁ at index |l|
  have h_pop₁ : w₁.popNextEvent = some (ev₁, {w with events := l ++ [ev₂] ++ r}) := by
    cases h_pop : w₁.popNextEvent with
    | none =>
      exfalso
      exact popNextEvent_none_no_events w₁ h_pop ev₁ (by dsimp [w₁]; simp) (h_tick₁.trans rfl)
    | some p =>
      rcases p with ⟨ev, w'⟩
      have h_ev_tick : ev.targetTick = w₁.tick := popNextEvent_at_tick w₁ ev w' h_pop
      have h_ev_eq : ev = ev₁ := by
        obtain ⟨idx, _, _, _, h_mem, _⟩ := World.popNextEvent_eraseIdx w₁ ev w' h_pop
        have : ev ∈ l ∨ ev = ev₁ ∨ ev = ev₂ ∨ ev ∈ r := by dsimp [w₁] at h_mem; simpa [List.mem_append] using h_mem
        rcases this with h_in_l | h | h | h_in_r
        · exfalso; exact h_no_l ev h_in_l (h_ev_tick.trans rfl)
        · exact h
        · exfalso; exact h_tick₂ (by subst h; simpa [w₁] using h_ev_tick)
        · exfalso; exact h_no_r ev h_in_r (h_ev_tick.trans rfl)
      rw [h_ev_eq] at h_pop
      obtain ⟨idx, h_idx_lt, h_erase, _, _, h_getElem⟩ := World.popNextEvent_eraseIdx w₁ ev₁ w' h_pop
      have h_idx : idx = l.length :=
        getElem_eq_of_not_mem_append_two l r ev₁ ev₂
          (fun h => h_no_l ev₁ h (h_tick₁.trans rfl))
          (fun h => h_no_r ev₁ h (h_tick₁.trans rfl))
          (fun h => h_tick₂ (by rw [← h, h_tick₁]))
          idx h_idx_lt h_getElem
      have h_nodes := World.popNextEvent_nodes w₁ ev₁ w' h_pop
      have h_tick := World.popNextEvent_tick w₁ ev₁ w' h_pop
      have h_nextId := World.popNextEvent_nextId w₁ ev₁ w' h_pop
      have h_log := World.popNextEvent_outputLog w₁ ev₁ w' h_pop
      have h_w'_eq : w' = {w with events := l ++ [ev₂] ++ r} := by
        have h_evts : w'.events = l ++ [ev₂] ++ r := by
          rw [h_erase, h_idx]; dsimp [w₁]; exact eraseIdx_append_two_mid l r ev₁ ev₂
        ext <;> simp_all [w₁]
      rw [h_w'_eq, h_ev_eq]
  -- w₂ pops ev₁ at index |l| + 1
  have h_pop₂ : w₂.popNextEvent = some (ev₁, {w with events := l ++ [ev₂] ++ r}) := by
    cases h_pop : w₂.popNextEvent with
    | none =>
      exfalso
      exact popNextEvent_none_no_events w₂ h_pop ev₁ (by dsimp [w₂]; simp [List.mem_append]) (h_tick₁.trans rfl)
    | some p =>
      rcases p with ⟨ev, w'⟩
      have h_ev_tick : ev.targetTick = w₂.tick := popNextEvent_at_tick w₂ ev w' h_pop
      have h_ev_eq : ev = ev₁ := by
        obtain ⟨idx, _, _, _, h_mem, _⟩ := World.popNextEvent_eraseIdx w₂ ev w' h_pop
        have : ev ∈ l ∨ ev = ev₂ ∨ ev = ev₁ ∨ ev ∈ r := by dsimp [w₂] at h_mem; simpa [List.mem_append] using h_mem
        rcases this with h_in_l | h | h | h_in_r
        · exfalso; exact h_no_l ev h_in_l (h_ev_tick.trans rfl)
        · exfalso; exact h_tick₂ (by subst h; simpa [w₂] using h_ev_tick)
        · exact h
        · exfalso; exact h_no_r ev h_in_r (h_ev_tick.trans rfl)
      rw [h_ev_eq] at h_pop
      obtain ⟨idx, h_idx_lt, h_erase, _, _, h_getElem⟩ := World.popNextEvent_eraseIdx w₂ ev₁ w' h_pop
      have h_idx : idx = l.length + 1 :=
        getElem_eq_of_not_mem_append_two_right l r ev₁ ev₂
          (fun h => h_no_l ev₁ h (h_tick₁.trans rfl))
          (fun h => h_no_r ev₁ h (h_tick₁.trans rfl))
          (fun h => h_tick₂ (by rw [← h, h_tick₁]))
          idx h_idx_lt h_getElem
      have h_nodes := World.popNextEvent_nodes w₂ ev₁ w' h_pop
      have h_tick := World.popNextEvent_tick w₂ ev₁ w' h_pop
      have h_nextId := World.popNextEvent_nextId w₂ ev₁ w' h_pop
      have h_log := World.popNextEvent_outputLog w₂ ev₁ w' h_pop
      have h_w'_eq : w' = {w with events := l ++ [ev₂] ++ r} := by
        have h_evts : w'.events = l ++ [ev₂] ++ r := by
          rw [h_erase, h_idx]; dsimp [w₂]; exact eraseIdx_append_two_mid_right l r ev₂ ev₁
        ext <;> simp_all [w₂]
      rw [h_w'_eq, h_ev_eq]
  have h_step₁ : w₁.step = some (({w with events := l ++ [ev₂] ++ r} : World).onScheduledTick ev₁.nodeId) := by
    unfold World.step; rw [h_pop₁]
  have h_step₂ : w₂.step = some (({w with events := l ++ [ev₂] ++ r} : World).onScheduledTick ev₁.nodeId) := by
    unfold World.step; rw [h_pop₂]
  rw [World.stepUntilNextTick, h_step₁, World.stepUntilNextTick, h_step₂]

/-! ### Layer 6: Structural properties of buildChain / connectChain -/

/-- `updateNode` does not change `getNode` for a different node ID. -/
theorem World.updateNode_getNode_ne (w : World) (id₁ id₂ : Nat) (f : NodeData → NodeData)
    (h : id₁ ≠ id₂) :
    (w.updateNode id₁ f).getNode id₂ = w.getNode id₂ := by
  dsimp [World.updateNode, World.getNode]
  set g := fun (x : Nat × NodeData) => if x.1 == id₁ then (x.1, f x.2) else x
  have h_inv : ∀ x, (fun (p : Nat × NodeData) => p.1 == id₂) (g x) =
      (fun (p : Nat × NodeData) => p.1 == id₂) x := by
    intro x; dsimp [g]; split <;> rfl
  rw [List.find?_map_invariant w.nodes g (fun x => x.1 == id₂) h_inv]
  cases h_opt : w.nodes.find? (fun (nid, _) => nid == id₂) with
  | none => rfl
  | some q =>
    rcases q with ⟨nid, nd⟩
    have h_pred : (nid == id₂) = true :=
      find?_eq_some_imp_pred (fun (x : Nat × NodeData) => x.1 == id₂) w.nodes (nid, nd) h_opt
    have h_ne : ¬(nid == id₁) := by
      intro h'
      have h₁ : nid = id₁ := by simpa using h'
      have h₂ : nid = id₂ := by simpa using h_pred
      exact h (h₁.symm.trans h₂)
    dsimp [g]; simp [h_ne]

/-- `updateNode` on a non-existent node preserves `getNode = none`. -/
theorem World.updateNode_getNode_none (w : World) (id : Nat) (f : NodeData → NodeData)
    (h : w.getNode id = none) :
    (w.updateNode id f).getNode id = none := by
  dsimp [World.updateNode, World.getNode] at h ⊢
  set g := fun (x : Nat × NodeData) => if x.1 == id then (x.1, f x.2) else x
  have h_inv : ∀ x, (fun (p : Nat × NodeData) => p.1 == id) (g x) =
      (fun (p : Nat × NodeData) => p.1 == id) x := by
    intro x; dsimp [g]; split <;> rfl
  rw [List.find?_map_invariant w.nodes g (fun x => x.1 == id) h_inv]
  have h_none : w.nodes.find? (fun (nid, _) => nid == id) = none := by
    cases h_opt : w.nodes.find? (fun (nid, _) => nid == id) with
    | none => rfl
    | some q => rcases q with ⟨nid', nd'⟩; simp [h_opt] at h
  simp [h_none]

/-- `updateNode` applies `f` to the target node's data (when it exists). -/
theorem World.updateNode_getNode_eq (w : World) (id : Nat) (f : NodeData → NodeData)
    (nd : NodeData) (h : w.getNode id = some nd) :
    (w.updateNode id f).getNode id = some (f nd) := by
  dsimp [World.updateNode, World.getNode] at h ⊢
  set g := fun (x : Nat × NodeData) => if x.1 == id then (x.1, f x.2) else x
  have h_inv : ∀ x, (fun (p : Nat × NodeData) => p.1 == id) (g x) =
      (fun (p : Nat × NodeData) => p.1 == id) x := by
    intro x; dsimp [g]; split <;> rfl
  rw [List.find?_map_invariant w.nodes g (fun x => x.1 == id) h_inv]
  cases h_opt : w.nodes.find? (fun (nid, _) => nid == id) with
  | none => simp [h_opt] at h
  | some q =>
    rcases q with ⟨nid', nd'⟩
    have h_pred : (nid' == id) = true :=
      find?_eq_some_imp_pred (fun (x : Nat × NodeData) => x.1 == id) w.nodes (nid', nd') h_opt
    rw [h_opt] at h
    dsimp at h
    injection h with h_nd
    simp only [Option.map]
    dsimp [g]; simp [h_pred, h_nd]

/-- The second component of a pair in `zip l₁ l₂` is in `l₂`. -/
theorem snd_mem_zip {α β : Type} (l₁ : List α) (l₂ : List β) (a : α) (b : β)
    (h : (a, b) ∈ List.zip l₁ l₂) : b ∈ l₂ :=
  List.snd_mem_of_mem_zip l₁ l₂ a b h

/-- An element of `l.drop n` is in `l`. -/
theorem mem_of_mem_drop {α : Type} (l : List α) (n : Nat) (x : α)
    (h : x ∈ l.drop n) : x ∈ l := by
  induction l generalizing n with
  | nil => simp at h
  | cons hd tl ih =>
    cases n with
    | zero => simp [List.drop] at h ⊢; exact h
    | succ n' =>
      simp only [List.drop] at h ⊢
      exact List.mem_cons_of_mem hd (ih n' h)

/-- After `connectChain w ids`, every output of every node is either in `ids`
    or was already an output of that node in `w`. -/
theorem connectChain_outputs_subset (ids : List Nat) :
    ∀ (w : World) id nd, (connectChain w ids).getNode id = some nd →
    ∀ out ∈ nd.outputs, out ∈ ids ∨ ∃ nd₀, w.getNode id = some nd₀ ∧ out ∈ nd₀.outputs := by
  induction ids with
  | nil =>
    intro w id nd h_getNode out h_out
    dsimp [connectChain] at h_getNode
    right; exact ⟨nd, h_getNode, h_out⟩
  | cons hd tl ih =>
    cases tl with
    | nil =>
      intro w id nd h_getNode out h_out
      dsimp [connectChain] at h_getNode
      right; exact ⟨nd, h_getNode, h_out⟩
    | cons hd₂ tl₂ =>
      intro w id nd h_getNode out h_out
      set w₁ := (w.updateNode hd₂ (fun nd => { nd with inputs := nd.inputs ++ [hd] })).updateNode hd
        (fun nd => { nd with outputs := nd.outputs ++ [hd₂] })
      have h_decomp : connectChain w (hd :: hd₂ :: tl₂) = connectChain w₁ (hd₂ :: tl₂) := by
        dsimp [connectChain, w₁]
      rw [h_decomp] at h_getNode
      have h_ih := ih w₁ id nd h_getNode out h_out
      cases h_ih with
      | inl h_in_tl =>
        -- out ∈ hd₂ :: tl₂ ⊆ hd :: hd₂ :: tl₂
        left; exact List.mem_cons_of_mem hd h_in_tl
      | inr h_in_w₁ =>
        rcases h_in_w₁ with ⟨nd₁, h_getNode₁, h_out₁⟩
        -- out is an output of id in w₁. Show: out ∈ ids or output in w.
        by_cases h_id_hd : id = hd
        · -- id = hd: w₁ appends [hd₂] to hd's outputs
          cases h_orig : w.getNode hd with
          | none =>
            have h₂ : w₁.getNode hd = none := by
              dsimp [w₁]
              by_cases h_eq : hd = hd₂
              · cases h_eq -- hd₂ becomes hd
                have h₃ : (w.updateNode hd (fun nd => { nd with inputs := nd.inputs ++ [hd] })).getNode hd = none :=
                  World.updateNode_getNode_none w hd _ h_orig
                exact World.updateNode_getNode_none _ hd _ h₃
              · have h₃ : (w.updateNode hd₂ (fun nd => { nd with inputs := nd.inputs ++ [hd] })).getNode hd = none := by
                  rw [World.updateNode_getNode_ne w hd₂ hd _ (by omega)]; exact h_orig
                exact World.updateNode_getNode_none _ hd _ h₃
            rw [h_id_hd] at h_getNode₁; rw [h₂] at h_getNode₁; contradiction
          | some nd₀ =>
            have h_outputs : nd₁.outputs = nd₀.outputs ++ [hd₂] := by
              rw [h_id_hd] at h_getNode₁
              dsimp [w₁] at h_getNode₁
              by_cases h_eq : hd = hd₂
              · cases h_eq -- hd₂ becomes hd
                have h₁ := World.updateNode_getNode_eq w hd
                  (fun nd => { nd with inputs := nd.inputs ++ [hd] }) nd₀ h_orig
                have h₂ := World.updateNode_getNode_eq _ hd
                  (fun nd => { nd with outputs := nd.outputs ++ [hd] }) _ h₁
                have h_eq₂ := h₂.symm.trans h_getNode₁
                injection h_eq₂ with h_nd; cases h_nd; rfl
              · have h₁ : (w.updateNode hd₂ (fun nd => { nd with inputs := nd.inputs ++ [hd] })).getNode hd =
                    some nd₀ := by
                  rw [World.updateNode_getNode_ne w hd₂ hd _ (by omega)]; exact h_orig
                have h₂ := World.updateNode_getNode_eq _ hd
                  (fun nd => { nd with outputs := nd.outputs ++ [hd₂] }) nd₀ h₁
                have h_eq₂ := h₂.symm.trans h_getNode₁
                injection h_eq₂ with h_nd; cases h_nd; rfl
            have h_out' : out ∈ nd₀.outputs ∨ out = hd₂ := by
              rw [h_outputs] at h_out₁
              simp [List.mem_append] at h_out₁ ⊢; exact h_out₁
            cases h_out' with
            | inl h_old => right; exact ⟨nd₀, by rw [h_id_hd]; exact h_orig, h_old⟩
            | inr h_eq => left; rw [h_eq]; simp
        · -- id ≠ hd
          by_cases h_id_hd₂ : id = hd₂
          · -- id = hd₂: w₁ changes hd₂'s inputs, not outputs
            cases h_orig : w.getNode hd₂ with
            | none =>
              have h₁ : (w.updateNode hd₂ (fun nd => { nd with inputs := nd.inputs ++ [hd] })).getNode hd₂ = none :=
                World.updateNode_getNode_none w hd₂ _ h_orig
              have h₂ : w₁.getNode hd₂ = none := by
                dsimp [w₁]
                rw [World.updateNode_getNode_ne _ hd hd₂ _ (by omega)]
                exact h₁
              rw [h_id_hd₂] at h_getNode₁; rw [h₂] at h_getNode₁; contradiction
            | some nd₀ =>
              have h₁ : (w.updateNode hd₂ (fun nd => { nd with inputs := nd.inputs ++ [hd] })).getNode hd₂ =
                  some ({ nd₀ with inputs := nd₀.inputs ++ [hd] } : NodeData) :=
                World.updateNode_getNode_eq w hd₂ _ nd₀ h_orig
              have h₂ : w₁.getNode hd₂ =
                  some ({ nd₀ with inputs := nd₀.inputs ++ [hd] } : NodeData) := by
                dsimp [w₁]
                rw [World.updateNode_getNode_ne _ hd hd₂ _ (by omega)]
                exact h₁
              rw [h_id_hd₂] at h_getNode₁
              dsimp [w₁] at h_getNode₁
              have h_eq₂ := h₂.symm.trans h_getNode₁
              injection h_eq₂ with h_nd
              have h_out' : out ∈ nd₀.outputs := by
                have : nd₁.outputs = nd₀.outputs := by cases h_nd; rfl
                rw [this] at h_out₁; exact h_out₁
              right; exact ⟨nd₀, by rw [h_id_hd₂]; exact h_orig, h_out'⟩
          · -- id ≠ hd and id ≠ hd₂: w₁.getNode id = w.getNode id
            have h₁ : w₁.getNode id = w.getNode id := by
              dsimp [w₁]
              rw [World.updateNode_getNode_ne _ hd id _ (by omega)]
              exact World.updateNode_getNode_ne w hd₂ id _ (by omega)
            rw [h₁] at h_getNode₁
            right; exact ⟨nd₁, h_getNode₁, h_out₁⟩
