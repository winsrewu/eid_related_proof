import BasicProofs.PrefixChain.Part04


open BasicRedstoneSim

/-- If all events have `nodeId < N` and all nodes < N have outputs < N,
    then `stepUntilNextTick` preserves `nodeId < N`. -/
theorem stepUntilNextTick_nodeId_lt (w : World) (N : Nat)
    (h_events : ∀ ev ∈ w.events, ev.nodeId < N)
    (h_outputs : ∀ nid nd, w.getNode nid = some nd → nid < N → ∀ out ∈ nd.outputs, out < N)
    (h_delay : ∀ nid nd, w.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2) :
    ∀ ev ∈ w.stepUntilNextTick.events, ev.nodeId < N := by
  revert N h_events h_outputs h_delay
  induction w using World.stepUntilNextTick.induct with
  | case1 w h_step =>
    intro N h_events h_outputs h_delay
    rw [stepUntilNextTick_of_step_none w h_step]
    intro ev h_ev
    simp only at h_ev
    exact h_events ev h_ev
  | case2 w w' h_step ih =>
    intro N h_events h_outputs h_delay
    have h_sunt : w.stepUntilNextTick = w'.stepUntilNextTick := by
      rw [World.stepUntilNextTick, h_step]
    rw [h_sunt]
    dsimp [World.step] at h_step
    cases h_pop : w.popNextEvent with
    | none => simp [h_pop] at h_step
    | some p =>
      rcases p with ⟨ev, w_pop⟩
      simp [h_pop] at h_step
      subst h_step
      obtain ⟨idx, h_idx, h_erase, h_tick_ev, h_mem, h_get⟩ := World.popNextEvent_eraseIdx w ev w_pop h_pop
      have h_ev_nodeId : ev.nodeId < N := h_events ev h_mem
      have h_pop_events : ∀ ev' ∈ w_pop.events, ev'.nodeId < N := by
        intro ev' h_ev'
        rw [h_erase] at h_ev'
        exact h_events ev' (List.mem_of_mem_eraseIdx h_ev')
      have h_pop_nodes : w_pop.nodes = w.nodes := World.popNextEvent_nodes w ev w_pop h_pop
      have h_pop_outputs : ∀ nid nd, w_pop.getNode nid = some nd → nid < N → ∀ out ∈ nd.outputs, out < N := by
        intro nid nd h_nd h_lt out h_out
        have h_nd' : w.getNode nid = some nd := by
          dsimp [World.getNode] at h_nd ⊢; rw [← h_pop_nodes]; exact h_nd
        exact h_outputs nid nd h_nd' h_lt out h_out
      have h_pop_delay : ∀ nid nd, w_pop.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
        intro nid nd h_nd d p h_kind
        have h_nd' : w.getNode nid = some nd := by
          dsimp [World.getNode] at h_nd ⊢; rw [← h_pop_nodes]; exact h_nd
        exact h_delay nid nd h_nd' d p h_kind
      apply ih
      · intro ev' h_ev'
        obtain ⟨new_ev, h_app, h_fut⟩ := World.onScheduledTick_events_append w_pop ev.nodeId h_pop_delay
        rw [h_app] at h_ev'
        simp [List.mem_append] at h_ev'
        cases h_ev' with
        | inl h_old => exact h_pop_events ev' h_old
        | inr h_new =>
          have h_or := World.onScheduledTick_events_nodeId_mem_or w_pop ev.nodeId ev'
            (by rw [h_app]; exact List.mem_append_right _ h_new)
          cases h_or with
          | inl h_mem =>
            obtain ⟨nd, h_nd, h_out⟩ := h_mem
            exact h_pop_outputs ev.nodeId nd h_nd h_ev_nodeId ev'.nodeId h_out
          | inr h_old => exact h_pop_events ev' h_old
      · intro nid nd h_nd h_lt out h_out
        obtain ⟨nd₀, h_nd₀, h_kind_eq⟩ := World.onScheduledTick_kind_preserved w_pop ev.nodeId nid nd h_nd
        obtain ⟨nd₀', h_nd₀', h_inputs_eq, h_outputs_eq⟩ := World.onScheduledTick_inputs_preserved w_pop ev.nodeId nid nd h_nd
        have h_nd₀_eq : nd₀' = nd₀ := by
          apply Option.some_inj.mp; rw [← h_nd₀', h_nd₀]
        rw [h_nd₀_eq] at h_outputs_eq
        rw [h_outputs_eq] at h_out
        exact h_pop_outputs nid nd₀ h_nd₀ h_lt out h_out
      · intro nid nd h_nd d p h_kind
        obtain ⟨nd₀, h_nd₀, h_kind_eq⟩ := World.onScheduledTick_kind_preserved w_pop ev.nodeId nid nd h_nd
        rw [h_kind_eq] at h_kind
        exact h_pop_delay nid nd₀ h_nd₀ d p h_kind

/-- `processNEvents` preserves "all events have nodeId < N". -/
theorem processNEvents_nodeId_lt (w : World) (n : Nat) (N : Nat)
    (h_events : ∀ ev ∈ w.events, ev.nodeId < N)
    (h_outputs : ∀ nid nd, w.getNode nid = some nd → nid < N → ∀ out ∈ nd.outputs, out < N)
    (h_delay : ∀ nid nd, w.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2) :
    ∀ ev ∈ (processNEvents w n).events, ev.nodeId < N := by
  induction n generalizing w with
  | zero => simpa [processNEvents] using h_events
  | succ n' ih =>
    dsimp [processNEvents]
    cases h_step : w.step with
    | none => simpa [h_step] using h_events
    | some w' =>
      simp only []
      apply ih
      · -- Events in w' have nodeId < N
        dsimp [World.step] at h_step
        cases h_pop : w.popNextEvent with
        | none => simp [h_pop] at h_step
        | some p =>
          rcases p with ⟨ev, w_pop⟩
          simp only [h_pop] at h_step
          injection h_step with h_w'
          subst h_w'
          obtain ⟨idx, h_idx, h_erase, h_tick_ev, h_mem, h_get⟩ := World.popNextEvent_eraseIdx w ev w_pop h_pop
          have h_ev_nodeId : ev.nodeId < N := h_events ev h_mem
          have h_pop_events : ∀ ev' ∈ w_pop.events, ev'.nodeId < N := by
            intro ev' h_ev'
            rw [h_erase] at h_ev'
            exact h_events ev' (List.mem_of_mem_eraseIdx h_ev')
          have h_pop_nodes : w_pop.nodes = w.nodes := World.popNextEvent_nodes w ev w_pop h_pop
          have h_pop_outputs : ∀ nid nd, w_pop.getNode nid = some nd → nid < N → ∀ out ∈ nd.outputs, out < N := by
            intro nid nd h_nd h_lt out h_out
            have h_nd' : w.getNode nid = some nd := by
              dsimp [World.getNode] at h_nd ⊢; rw [← h_pop_nodes]; exact h_nd
            exact h_outputs nid nd h_nd' h_lt out h_out
          have h_pop_delay : ∀ nid nd, w_pop.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
            intro nid nd h_nd d p h_kind
            have h_nd' : w.getNode nid = some nd := by
              dsimp [World.getNode] at h_nd ⊢; rw [← h_pop_nodes]; exact h_nd
            exact h_delay nid nd h_nd' d p h_kind
          intro ev' h_ev'
          obtain ⟨new_ev, h_app, h_fut⟩ := World.onScheduledTick_events_append w_pop ev.nodeId h_pop_delay
          rw [h_app] at h_ev'
          simp [List.mem_append] at h_ev'
          cases h_ev' with
          | inl h_old => exact h_pop_events ev' h_old
          | inr h_new =>
            have h_or := World.onScheduledTick_events_nodeId_mem_or w_pop ev.nodeId ev'
              (by rw [h_app]; exact List.mem_append_right _ h_new)
            cases h_or with
            | inl h_mem =>
              obtain ⟨nd, h_nd, h_out⟩ := h_mem
              exact h_pop_outputs ev.nodeId nd h_nd h_ev_nodeId ev'.nodeId h_out
            | inr h_old => exact h_pop_events ev' h_old
      · -- Outputs property for w'
        intro nid nd h_nd h_lt out h_out
        dsimp [World.step] at h_step
        cases h_pop : w.popNextEvent with
        | none => simp [h_pop] at h_step
        | some p =>
          rcases p with ⟨ev, w_pop⟩
          simp only [h_pop] at h_step
          injection h_step with h_w'
          subst h_w'
          obtain ⟨nd₀, h_nd₀, h_kind_eq⟩ := World.onScheduledTick_kind_preserved w_pop ev.nodeId nid nd h_nd
          obtain ⟨nd₀', h_nd₀', h_inputs_eq, h_outputs_eq⟩ := World.onScheduledTick_inputs_preserved w_pop ev.nodeId nid nd h_nd
          have h_nd₀_eq : nd₀' = nd₀ := by
            apply Option.some_inj.mp; rw [← h_nd₀', h_nd₀]
          rw [h_nd₀_eq] at h_outputs_eq
          rw [h_outputs_eq] at h_out
          have h_pop_nodes : w_pop.nodes = w.nodes := World.popNextEvent_nodes w ev w_pop h_pop
          have h_nd₀' : w.getNode nid = some nd₀ := by
            dsimp [World.getNode] at h_nd₀ ⊢; rw [← h_pop_nodes]; exact h_nd₀
          exact h_outputs nid nd₀ h_nd₀' h_lt out h_out
      · -- Delay property for w'
        intro nid nd h_nd d p h_kind
        dsimp [World.step] at h_step
        cases h_pop : w.popNextEvent with
        | none => simp [h_pop] at h_step
        | some p =>
          rcases p with ⟨ev, w_pop⟩
          simp only [h_pop] at h_step
          injection h_step with h_w'
          subst h_w'
          obtain ⟨nd₀, h_nd₀, h_kind_eq⟩ := World.onScheduledTick_kind_preserved w_pop ev.nodeId nid nd h_nd
          rw [h_kind_eq] at h_kind
          have h_pop_nodes : w_pop.nodes = w.nodes := World.popNextEvent_nodes w ev w_pop h_pop
          have h_nd₀' : w.getNode nid = some nd₀ := by
            dsimp [World.getNode] at h_nd₀ ⊢; rw [← h_pop_nodes]; exact h_nd₀
          exact h_delay nid nd₀ h_nd₀' d p h_kind

/-- `stepUntilNextTick` preserves "no event targets node M". -/
theorem stepUntilNextTick_nodeId_ne (w : World) (M : Nat)
    (h_events : ∀ ev ∈ w.events, ev.nodeId ≠ M)
    (h_outputs : ∀ nid nd, w.getNode nid = some nd → ∀ out ∈ nd.outputs, out ≠ M)
    (h_delay : ∀ nid nd, w.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2) :
    ∀ ev ∈ w.stepUntilNextTick.events, ev.nodeId ≠ M := by
  revert M h_events h_outputs h_delay
  induction w using World.stepUntilNextTick.induct with
  | case1 w h_step =>
    intro M h_events h_outputs h_delay
    rw [stepUntilNextTick_of_step_none w h_step]
    intro ev h_ev
    simp only at h_ev
    exact h_events ev h_ev
  | case2 w w' h_step ih =>
    intro M h_events h_outputs h_delay
    have h_sunt : w.stepUntilNextTick = w'.stepUntilNextTick := by
      rw [World.stepUntilNextTick, h_step]
    rw [h_sunt]
    dsimp [World.step] at h_step
    cases h_pop : w.popNextEvent with
    | none => simp [h_pop] at h_step
    | some p =>
      rcases p with ⟨ev, w_pop⟩
      simp [h_pop] at h_step
      subst h_step
      obtain ⟨idx, h_idx, h_erase, h_tick_ev, h_mem, h_get⟩ := World.popNextEvent_eraseIdx w ev w_pop h_pop
      have h_pop_events : ∀ ev' ∈ w_pop.events, ev'.nodeId ≠ M := by
        intro ev' h_ev'
        rw [h_erase] at h_ev'
        exact h_events ev' (List.mem_of_mem_eraseIdx h_ev')
      have h_pop_nodes : w_pop.nodes = w.nodes := World.popNextEvent_nodes w ev w_pop h_pop
      have h_pop_outputs : ∀ nid nd, w_pop.getNode nid = some nd → ∀ out ∈ nd.outputs, out ≠ M := by
        intro nid nd h_nd out h_out
        have h_nd' : w.getNode nid = some nd := by
          dsimp [World.getNode] at h_nd ⊢; rw [← h_pop_nodes]; exact h_nd
        exact h_outputs nid nd h_nd' out h_out
      have h_pop_delay : ∀ nid nd, w_pop.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
        intro nid nd h_nd d p h_kind
        have h_nd' : w.getNode nid = some nd := by
          dsimp [World.getNode] at h_nd ⊢; rw [← h_pop_nodes]; exact h_nd
        exact h_delay nid nd h_nd' d p h_kind
      apply ih
      · intro ev' h_ev'
        obtain ⟨new_ev, h_app, h_fut⟩ := World.onScheduledTick_events_append w_pop ev.nodeId h_pop_delay
        rw [h_app] at h_ev'
        simp [List.mem_append] at h_ev'
        cases h_ev' with
        | inl h_old => exact h_pop_events ev' h_old
        | inr h_new =>
          have h_or := World.onScheduledTick_events_nodeId_mem_or w_pop ev.nodeId ev'
            (by rw [h_app]; exact List.mem_append_right _ h_new)
          cases h_or with
          | inl h_mem' =>
            obtain ⟨nd, h_nd, h_out⟩ := h_mem'
            exact h_pop_outputs ev.nodeId nd h_nd ev'.nodeId h_out
          | inr h_old => exact h_pop_events ev' h_old
      · intro nid nd h_nd out h_out
        obtain ⟨nd₀, h_nd₀, h_kind_eq⟩ := World.onScheduledTick_kind_preserved w_pop ev.nodeId nid nd h_nd
        obtain ⟨nd₀', h_nd₀', h_inputs_eq, h_outputs_eq⟩ := World.onScheduledTick_inputs_preserved w_pop ev.nodeId nid nd h_nd
        have h_nd₀_eq : nd₀' = nd₀ := by
          apply Option.some_inj.mp; rw [← h_nd₀', h_nd₀]
        rw [h_nd₀_eq] at h_outputs_eq
        rw [h_outputs_eq] at h_out
        exact h_pop_outputs nid nd₀ h_nd₀ out h_out
      · intro nid nd h_nd d p h_kind
        obtain ⟨nd₀, h_nd₀, h_kind_eq⟩ := World.onScheduledTick_kind_preserved w_pop ev.nodeId nid nd h_nd
        rw [h_kind_eq] at h_kind
        exact h_pop_delay nid nd₀ h_nd₀ d p h_kind

/-- `processNEvents` preserves "no event targets node M". -/
theorem processNEvents_nodeId_ne (w : World) (n : Nat) (M : Nat)
    (h_events : ∀ ev ∈ w.events, ev.nodeId ≠ M)
    (h_outputs : ∀ nid nd, w.getNode nid = some nd → ∀ out ∈ nd.outputs, out ≠ M)
    (h_delay : ∀ nid nd, w.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2) :
    ∀ ev ∈ (processNEvents w n).events, ev.nodeId ≠ M := by
  induction n generalizing w with
  | zero => simpa [processNEvents] using h_events
  | succ n' ih =>
    dsimp [processNEvents]
    cases h_step : w.step with
    | none => simpa [h_step] using h_events
    | some w' =>
      simp only []
      apply ih
      · dsimp [World.step] at h_step
        cases h_pop : w.popNextEvent with
        | none => simp [h_pop] at h_step
        | some p =>
          rcases p with ⟨ev, w_pop⟩
          simp only [h_pop] at h_step
          injection h_step with h_w'
          subst h_w'
          obtain ⟨idx, h_idx, h_erase, h_tick_ev, h_mem, h_get⟩ := World.popNextEvent_eraseIdx w ev w_pop h_pop
          have h_pop_events : ∀ ev' ∈ w_pop.events, ev'.nodeId ≠ M := by
            intro ev' h_ev'
            rw [h_erase] at h_ev'
            exact h_events ev' (List.mem_of_mem_eraseIdx h_ev')
          have h_pop_nodes : w_pop.nodes = w.nodes := World.popNextEvent_nodes w ev w_pop h_pop
          have h_pop_outputs : ∀ nid nd, w_pop.getNode nid = some nd → ∀ out ∈ nd.outputs, out ≠ M := by
            intro nid nd h_nd out h_out
            have h_nd' : w.getNode nid = some nd := by
              dsimp [World.getNode] at h_nd ⊢; rw [← h_pop_nodes]; exact h_nd
            exact h_outputs nid nd h_nd' out h_out
          have h_pop_delay : ∀ nid nd, w_pop.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
            intro nid nd h_nd d p h_kind
            have h_nd' : w.getNode nid = some nd := by
              dsimp [World.getNode] at h_nd ⊢; rw [← h_pop_nodes]; exact h_nd
            exact h_delay nid nd h_nd' d p h_kind
          intro ev' h_ev'
          obtain ⟨new_ev, h_app, h_fut⟩ := World.onScheduledTick_events_append w_pop ev.nodeId h_pop_delay
          rw [h_app] at h_ev'
          simp [List.mem_append] at h_ev'
          cases h_ev' with
          | inl h_old => exact h_pop_events ev' h_old
          | inr h_new =>
            have h_or := World.onScheduledTick_events_nodeId_mem_or w_pop ev.nodeId ev'
              (by rw [h_app]; exact List.mem_append_right _ h_new)
            cases h_or with
            | inl h_mem =>
              obtain ⟨nd, h_nd, h_out⟩ := h_mem
              exact h_pop_outputs ev.nodeId nd h_nd ev'.nodeId h_out
            | inr h_old => exact h_pop_events ev' h_old
      · intro nid nd h_nd out h_out
        dsimp [World.step] at h_step
        cases h_pop : w.popNextEvent with
        | none => simp [h_pop] at h_step
        | some p =>
          rcases p with ⟨ev, w_pop⟩
          simp only [h_pop] at h_step
          injection h_step with h_w'
          subst h_w'
          obtain ⟨nd₀, h_nd₀, h_kind_eq⟩ := World.onScheduledTick_kind_preserved w_pop ev.nodeId nid nd h_nd
          obtain ⟨nd₀', h_nd₀', h_inputs_eq, h_outputs_eq⟩ := World.onScheduledTick_inputs_preserved w_pop ev.nodeId nid nd h_nd
          have h_nd₀_eq : nd₀' = nd₀ := by
            apply Option.some_inj.mp; rw [← h_nd₀', h_nd₀]
          rw [h_nd₀_eq] at h_outputs_eq
          rw [h_outputs_eq] at h_out
          have h_pop_nodes : w_pop.nodes = w.nodes := World.popNextEvent_nodes w ev w_pop h_pop
          have h_nd₀'' : w.getNode nid = some nd₀ := by
            dsimp [World.getNode] at h_nd₀ ⊢; rw [← h_pop_nodes]; exact h_nd₀
          exact h_outputs nid nd₀ h_nd₀'' out h_out
      · intro nid nd h_nd d p h_kind
        dsimp [World.step] at h_step
        cases h_pop : w.popNextEvent with
        | none => simp [h_pop] at h_step
        | some p =>
          rcases p with ⟨ev, w_pop⟩
          simp only [h_pop] at h_step
          injection h_step with h_w'
          subst h_w'
          obtain ⟨nd₀, h_nd₀, h_kind_eq⟩ := World.onScheduledTick_kind_preserved w_pop ev.nodeId nid nd h_nd
          rw [h_kind_eq] at h_kind
          have h_pop_nodes : w_pop.nodes = w.nodes := World.popNextEvent_nodes w ev w_pop h_pop
          have h_nd₀'' : w.getNode nid = some nd₀ := by
            dsimp [World.getNode] at h_nd₀ ⊢; rw [← h_pop_nodes]; exact h_nd₀
          exact h_delay nid nd₀ h_nd₀'' d p h_kind

/-- `World.step` preserves node kind. -/
theorem World.step_kind_preserved (w : World) :
    ∀ w', w.step = some w' →
    ∀ nid nd, w'.getNode nid = some nd →
    ∃ nd₀, w.getNode nid = some nd₀ ∧ nd.kind = nd₀.kind := by
  intro w' h_step nid nd h
  unfold World.step at h_step
  cases h_pop : w.popNextEvent with
  | none => simp [h_pop] at h_step
  | some p =>
    rcases p with ⟨ev, w_pop⟩
    rw [h_pop] at h_step
    dsimp at h_step
    injection h_step with h_w'
    subst h_w'
    have h_nodes : w_pop.nodes = w.nodes := World.popNextEvent_nodes w ev w_pop h_pop
    have h_getNode_pop : w_pop.getNode nid = w.getNode nid := by
      dsimp [World.getNode]; rw [h_nodes]
    obtain ⟨nd₀, h₀, hk⟩ := World.onScheduledTick_kind_preserved w_pop ev.nodeId nid nd h
    exact ⟨nd₀, by rwa [← h_getNode_pop], hk⟩

/-- `stepUntilNextTick` preserves node kind. -/
theorem World.stepUntilNextTick_kind_preserved (w : World) :
    ∀ nid nd, (w.stepUntilNextTick).getNode nid = some nd →
    ∃ nd₀, w.getNode nid = some nd₀ ∧ nd.kind = nd₀.kind := by
  induction w using World.stepUntilNextTick.induct with
  | case1 w h_step =>
    intro nid nd h
    rw [stepUntilNextTick_of_step_none w h_step] at h
    exact ⟨nd, h, rfl⟩
  | case2 w w' h_step' ih =>
    intro nid nd h
    have h_sunt : w.stepUntilNextTick = w'.stepUntilNextTick := by
      rw [World.stepUntilNextTick, h_step']
    rw [h_sunt] at h
    obtain ⟨nd₁, h₁, hk₁⟩ := ih nid nd h
    obtain ⟨nd₀, h₀, hk₀⟩ := World.step_kind_preserved w w' h_step' nid nd₁ h₁
    exact ⟨nd₀, h₀, hk₁.trans hk₀⟩

/-- `processNEvents` preserves node kind. -/
theorem processNEvents_kind_preserved (w : World) (n : Nat) :
    ∀ nid nd, (processNEvents w n).getNode nid = some nd →
    ∃ nd₀, w.getNode nid = some nd₀ ∧ nd.kind = nd₀.kind := by
  induction n generalizing w with
  | zero => intro nid nd h; exact ⟨nd, h, rfl⟩
  | succ n' ih =>
    intro nid nd h
    dsimp [processNEvents] at h
    cases h_step : w.step with
    | none =>
      simp [h_step] at h
      exact ⟨nd, h, rfl⟩
    | some w' =>
      simp [h_step] at h
      obtain ⟨nd₁, h₁, hk₁⟩ := ih w' nid nd h
      obtain ⟨nd₀, h₀, hk₀⟩ := World.step_kind_preserved w w' h_step nid nd₁ h₁
      exact ⟨nd₀, h₀, hk₁.trans hk₀⟩

/-- `simBody` preserves node kind. -/
theorem simBody_kind_preserved (t1 t2 pos in1 in2 : Nat) (w : World) (i : Nat) :
    ∀ nid nd, (simBody t1 t2 pos in1 in2 w i).getNode nid = some nd →
    ∃ nd₀, w.getNode nid = some nd₀ ∧ nd.kind = nd₀.kind := by
  intro nid nd h
  dsimp (config := { zeta := true }) [simBody] at h
  split_ifs at h with h_t1 h_t2
  · obtain ⟨nd₁, h₁, hk₁⟩ := World.stepUntilNextTick_kind_preserved _ nid nd h
    obtain ⟨nd₂, h₂, hk₂⟩ := World.setInput_kind_preserved _ in2 15 nid nd₁ h₁
    obtain ⟨nd₃, h₃, hk₃⟩ := processNEvents_kind_preserved _ pos nid nd₂ h₂
    obtain ⟨nd₄, h₄, hk₄⟩ := World.setInput_kind_preserved _ in1 15 nid nd₃ h₃
    obtain ⟨nd₅, h₅, hk₅⟩ := World.logOutput_kind_preserved w _ nid nd₄ h₄
    exact ⟨nd₅, h₅, hk₁.trans (hk₂.trans (hk₃.trans (hk₄.trans hk₅)))⟩
  · obtain ⟨nd₁, h₁, hk₁⟩ := World.stepUntilNextTick_kind_preserved _ nid nd h
    obtain ⟨nd₂, h₂, hk₂⟩ := World.setInput_kind_preserved _ in1 15 nid nd₁ h₁
    obtain ⟨nd₃, h₃, hk₃⟩ := World.logOutput_kind_preserved w _ nid nd₂ h₂
    exact ⟨nd₃, h₃, hk₁.trans (hk₂.trans hk₃)⟩
  · obtain ⟨nd₁, h₁, hk₁⟩ := World.stepUntilNextTick_kind_preserved _ nid nd h
    obtain ⟨nd₂, h₂, hk₂⟩ := World.setInput_kind_preserved _ in2 15 nid nd₁ h₁
    obtain ⟨nd₃, h₃, hk₃⟩ := processNEvents_kind_preserved _ pos nid nd₂ h₂
    obtain ⟨nd₄, h₄, hk₄⟩ := World.logOutput_kind_preserved w _ nid nd₃ h₃
    exact ⟨nd₄, h₄, hk₁.trans (hk₂.trans (hk₃.trans hk₄))⟩
  · obtain ⟨nd₁, h₁, hk₁⟩ := World.stepUntilNextTick_kind_preserved _ nid nd h
    obtain ⟨nd₂, h₂, hk₂⟩ := World.logOutput_kind_preserved w _ nid nd₁ h₁
    exact ⟨nd₂, h₂, hk₁.trans hk₂⟩

/-- `simFoldl` preserves node kind. -/
theorem simFoldl_kind_preserved (w : World) (t1 t2 pos in1 in2 : Nat) (n : Nat) :
    ∀ nid nd, ((List.range n).foldl (simBody t1 t2 pos in1 in2) w).getNode nid = some nd →
    ∃ nd₀, w.getNode nid = some nd₀ ∧ nd.kind = nd₀.kind := by
  induction n generalizing w with
  | zero => intro nid nd h; simp at h; exact ⟨nd, h, rfl⟩
  | succ n' ih =>
    intro nid nd h
    rw [List.range_succ, List.foldl_append] at h
    simp only [List.foldl_cons, List.foldl_nil] at h
    set w_mid := (List.range n').foldl (simBody t1 t2 pos in1 in2) w
    obtain ⟨nd₁, h₁, hk₁⟩ := simBody_kind_preserved t1 t2 pos in1 in2 w_mid n' nid nd h
    obtain ⟨nd₀, h₀, hk₀⟩ := ih w nid nd₁ h₁
    exact ⟨nd₀, h₀, hk₁.trans hk₀⟩

/-- `stepUntilNextTick` preserves event target tick parity when all delays are even. -/
theorem stepUntilNextTick_parity (w : World) (p : Nat)
    (h_parity : ∀ ev ∈ w.events, ev.targetTick % 2 = p)
    (h_even : ∀ nid nd, w.getNode nid = some nd → ∀ d pr,
        nd.kind = .repeater d pr → (d : Nat) % 2 = 0) :
    ∀ ev ∈ (w.stepUntilNextTick).events, ev.targetTick % 2 = p := by
  induction w using World.stepUntilNextTick.induct generalizing p with
  | case1 w h =>
    rw [stepUntilNextTick_of_step_none w h]
    exact h_parity
  | case2 w w' h_step ih =>
    have h_sunt : w.stepUntilNextTick = w'.stepUntilNextTick := by
      rw [World.stepUntilNextTick, h_step]
    rw [h_sunt]
    dsimp [World.step] at h_step
    cases h_pop : w.popNextEvent with
    | none => simp [h_pop] at h_step
    | some pp =>
      cases pp with | mk ev_pop w_pop =>
      simp only [h_pop] at h_step
      injection h_step with h_w'_eq
      apply ih
      · -- Events in w' have parity p
        rw [← h_w'_eq]
        obtain ⟨_, _, h_erase, h_ev_tick, h_ev_mem, _⟩ :=
          World.popNextEvent_eraseIdx w ev_pop w_pop h_pop
        have h_tick_p : w.tick % 2 = p := by
          rw [← h_ev_tick]; exact h_parity ev_pop h_ev_mem
        intro ev h_ev
        by_cases h_old : ev ∈ w_pop.events
        · have h_mem : ev ∈ w.events := by
            rw [h_erase] at h_old; exact List.mem_of_mem_eraseIdx h_old
          exact h_parity ev h_mem
        · have h_even_pop : ∀ nid nd, w_pop.getNode nid = some nd → ∀ d pr,
              nd.kind = .repeater d pr → (d : Nat) % 2 = 0 := by
            intro nid nd h_nd d pr h_kind
            have h_nodes : w_pop.nodes = w.nodes := World.popNextEvent_nodes w ev_pop w_pop h_pop
            have h_nd_w : w.getNode nid = some nd := by
              dsimp [World.getNode] at h_nd ⊢; rw [← h_nodes]; exact h_nd
            exact h_even nid nd h_nd_w d pr h_kind
          have h_new := World.onScheduledTick_events_parity w_pop ev_pop.nodeId h_even_pop ev h_ev h_old
          have h_tick_pop : w_pop.tick = w.tick := World.popNextEvent_tick w ev_pop w_pop h_pop
          rw [h_tick_pop, h_tick_p] at h_new
          exact h_new
      · -- w' has even delays
        intro nid nd h_nd d pr h_kind
        rw [← h_w'_eq] at h_nd
        obtain ⟨nd₀, h_nd₀, h_keq⟩ := World.onScheduledTick_kind_preserved w_pop ev_pop.nodeId nid nd h_nd
        rw [h_keq] at h_kind
        have h_nodes : w_pop.nodes = w.nodes := World.popNextEvent_nodes w ev_pop w_pop h_pop
        have h_nd_w : w.getNode nid = some nd₀ := by
          dsimp [World.getNode] at h_nd₀ ⊢; rw [← h_nodes]; exact h_nd₀
        exact h_even nid nd₀ h_nd_w d pr h_kind

/-- `setInput` new events have targetTick % 2 = w.tick % 2 when delays are even. -/
theorem setInput_events_parity (w : World) (id level : Nat)
    (h_even : ∀ nid nd, w.getNode nid = some nd → ∀ d p,
        nd.kind = .repeater d p → (d : Nat) % 2 = 0) :
    ∀ ev ∈ (w.setInput id level).events, ev ∉ w.events → ev.targetTick % 2 = w.tick % 2 := by
  dsimp [World.setInput]
  have h_ev' : (w.updateNode id (fun nd => { nd with sigLevel := level })).events = w.events := by
    simp [World.updateNode]
  have h_tick' : (w.updateNode id (fun nd => { nd with sigLevel := level })).tick = w.tick := by
    simp [World.updateNode]
  dsimp [World.notifyOutputs]
  cases h_go : (w.updateNode id (fun nd => { nd with sigLevel := level })).getNode id with
  | none => simp []; intro ev h h'; contradiction
  | some nd =>
    simp only []
    have h_even' : ∀ nid nd, (w.updateNode id (fun nd => { nd with sigLevel := level })).getNode nid = some nd →
        ∀ d p, nd.kind = .repeater d p → (d : Nat) % 2 = 0 := by
      intro nid nd' h_nd' d p h_kind
      obtain ⟨nd₀, h₀, hkeq⟩ := World.updateNode_getNode_kind w id nid
        (fun nd => { nd with sigLevel := level }) (fun nd => rfl) nd' h_nd'
      rw [← hkeq] at h_kind
      exact h_even nid nd₀ h₀ d p h_kind
    intro ev h_ev h_new
    have := foldl_onNeighborUpdate_events_parity nd.outputs
      (w.updateNode id (fun nd => { nd with sigLevel := level })) h_even' ev h_ev
    have h_new' : ev ∉ (w.updateNode id (fun nd => { nd with sigLevel := level })).events := by
      rwa [h_ev']
    have := this h_new'
    rwa [← h_tick']

/-- `simBody` preserves event target tick parity (when tick ≠ t₂, so no processNEvents/setInput in2). -/
theorem simBody_parity (t1 t2 pos in1 in2 : Nat) (w : World) (i : Nat) (p : Nat)
    (h_parity : ∀ ev ∈ w.events, ev.targetTick % 2 = p)
    (h_even : ∀ nid nd, w.getNode nid = some nd → ∀ d pr,
        nd.kind = .repeater d pr → (d : Nat) % 2 = 0)
    (h_tick : w.tick ≠ t2)
    (h_tick_p : w.tick = t1 → w.tick % 2 = p) :
    ∀ ev ∈ (simBody t1 t2 pos in1 in2 w i).events, ev.targetTick % 2 = p := by
  by_cases h_t1 : w.tick = t1
  · -- tick = t1 (and ≠ t2): simBody = (logOutput + setInput in1).stepUntilNextTick
    have h_eq : simBody t1 t2 pos in1 in2 w i =
        ((w.logOutput s!"tick {w.tick}").setInput in1 15).stepUntilNextTick := by
      unfold simBody
      dsimp (config := { zeta := true })
      split_ifs <;> simp_all [World.logOutput_tick, World.setInput_tick, beq_iff_eq]
    rw [h_eq]
    apply stepUntilNextTick_parity _ p
    · intro ev h_ev
      by_cases h_old : ev ∈ (w.logOutput s!"tick {w.tick}").events
      · have h_old_w : ev ∈ w.events := by dsimp [World.logOutput] at h_old; exact h_old
        exact h_parity ev h_old_w
      · have h_new := setInput_events_parity (w.logOutput s!"tick {w.tick}") in1 15
          (fun nid nd h_nd d pr h_kind => by
            obtain ⟨nd₀, h₀, hkeq⟩ := World.logOutput_kind_preserved w s!"tick {w.tick}" nid nd h_nd
            rw [hkeq] at h_kind
            exact h_even nid nd₀ h₀ d pr h_kind)
          ev h_ev h_old
        rw [World.logOutput_tick] at h_new
        rwa [h_tick_p h_t1] at h_new
    · intro nid nd h_nd d pr h_kind
      obtain ⟨nd₁, h₁, hk₁⟩ := World.setInput_kind_preserved (w.logOutput s!"tick {w.tick}") in1 15 nid nd h_nd
      rw [hk₁] at h_kind
      obtain ⟨nd₀, h₀, hk₀⟩ := World.logOutput_kind_preserved w s!"tick {w.tick}" nid nd₁ h₁
      rw [hk₀] at h_kind
      exact h_even nid nd₀ h₀ d pr h_kind
  · -- tick ≠ t1 (and ≠ t2): simBody = (logOutput).stepUntilNextTick
    have h_eq : simBody t1 t2 pos in1 in2 w i =
        (w.logOutput s!"tick {w.tick}").stepUntilNextTick := by
      unfold simBody
      dsimp (config := { zeta := true })
      split_ifs <;> simp_all [World.logOutput_tick, beq_iff_eq]
    rw [h_eq]
    apply stepUntilNextTick_parity _ p
    · intro ev h_ev; dsimp [World.logOutput] at h_ev; exact h_parity ev h_ev
    · intro nid nd h_nd d pr h_kind
      obtain ⟨nd₀, h₀, hk⟩ := World.logOutput_kind_preserved w s!"tick {w.tick}" nid nd h_nd
      rw [hk] at h_kind
      exact h_even nid nd₀ h₀ d pr h_kind

/-- `simBody` preserves "all events have nodeId < N" (when tick ≠ t₂). -/
theorem simBody_nodeId_lt (t1 t2 pos in1 in2 : Nat) (w : World) (i : Nat) (N : Nat)
    (h_events : ∀ ev ∈ w.events, ev.nodeId < N)
    (h_outputs : ∀ nid nd, w.getNode nid = some nd → nid < N → ∀ out ∈ nd.outputs, out < N)
    (h_delay : ∀ nid nd, w.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2)
    (_ : in1 < N)
    (h_in1_outputs : ∀ nd, w.getNode in1 = some nd → ∀ out ∈ nd.outputs, out < N)
    (h_tick_ne : w.tick ≠ t2) :
    ∀ ev ∈ (simBody t1 t2 pos in1 in2 w i).events, ev.nodeId < N := by
  by_cases h_t1 : w.tick = t1
  · -- tick = t1 (and ≠ t2): simBody = (logOutput + setInput in1).stepUntilNextTick
    have h_eq : simBody t1 t2 pos in1 in2 w i =
        ((w.logOutput s!"tick {w.tick}").setInput in1 15).stepUntilNextTick := by
      unfold simBody
      dsimp (config := { zeta := true })
      split_ifs <;> simp_all [World.logOutput_tick, World.setInput_tick, beq_iff_eq]
    rw [h_eq]
    apply stepUntilNextTick_nodeId_lt _ N
    · intro ev h_ev
      by_cases h_old : ev ∈ (w.logOutput s!"tick {w.tick}").events
      · have : (w.logOutput s!"tick {w.tick}").events = w.events := by simp
        rw [this] at h_old
        exact h_events ev h_old
      · obtain ⟨nd, h_nd, h_out⟩ := setInput_nodeId_mem (w.logOutput s!"tick {w.tick}") in1 15 ev h_ev h_old
        -- h_nd : ((w.logOutput ...).updateNode in1 ...).getNode in1 = some nd
        -- Need: w.getNode in1 = some nd₀ with ev.nodeId ∈ nd₀.outputs
        -- Since updateNode only changes sigLevel, nd.outputs = nd₀.outputs
        have h_nd₀ : ∃ nd₀, w.getNode in1 = some nd₀ ∧ ev.nodeId ∈ nd₀.outputs := by
          have h_log : (w.logOutput s!"tick {w.tick}").getNode in1 = w.getNode in1 := by
            simp [World.logOutput, World.getNode]
          by_cases h_none : w.getNode in1 = none
          · exfalso
            have h_none' : (w.logOutput s!"tick {w.tick}").getNode in1 = none := by rw [h_log, h_none]
            have h_none'' := World.updateNode_getNode_none (w.logOutput s!"tick {w.tick}") in1
              (fun nd => { nd with sigLevel := 15 }) h_none'
            rw [h_none''] at h_nd
            cases h_nd
          · obtain ⟨nd₀, h_nd₀⟩ := Option.ne_none_iff_exists'.mp h_none
            refine ⟨nd₀, h_nd₀, ?_⟩
            have h_eq : nd.outputs = nd₀.outputs := by
              have h_gn := World.updateNode_getNode_eq (w.logOutput s!"tick {w.tick}") in1
                (fun nd => { nd with sigLevel := 15 }) nd₀ (by rwa [h_log])
              have : nd = { nd₀ with sigLevel := 15 } := by
                apply Option.some_inj.mp; rw [← h_nd, h_gn]
              simp [this]
            rw [← h_eq]; exact h_out
        obtain ⟨nd₀, h_nd₀, h_out₀⟩ := h_nd₀
        exact h_in1_outputs nd₀ h_nd₀ ev.nodeId h_out₀
    · intro nid nd h_nd h_lt out h_out
      obtain ⟨nd₀, h₀, h_inp, h_outp⟩ := World.setInput_inputs_preserved (w.logOutput s!"tick {w.tick}") in1 15 nid nd h_nd
      rw [h_outp] at h_out
      have h₀' : w.getNode nid = some nd₀ := by
        have : (w.logOutput s!"tick {w.tick}").getNode nid = w.getNode nid := by simp [World.logOutput, World.getNode]
        rwa [this] at h₀
      exact h_outputs nid nd₀ h₀' h_lt out h_out
    · intro nid nd h_nd d p h_kind
      obtain ⟨nd₀, h₀, hk⟩ := World.setInput_kind_preserved (w.logOutput s!"tick {w.tick}") in1 15 nid nd h_nd
      rw [hk] at h_kind
      have h₀' : w.getNode nid = some nd₀ := by
        have : (w.logOutput s!"tick {w.tick}").getNode nid = w.getNode nid := by simp [World.logOutput, World.getNode]
        rwa [this] at h₀
      exact h_delay nid nd₀ h₀' d p h_kind
  · -- tick ≠ t1 (and ≠ t2): simBody = (logOutput).stepUntilNextTick
    have h_eq : simBody t1 t2 pos in1 in2 w i =
        (w.logOutput s!"tick {w.tick}").stepUntilNextTick := by
      unfold simBody
      dsimp (config := { zeta := true })
      split_ifs <;> simp_all [World.logOutput_tick, beq_iff_eq]
    rw [h_eq]
    apply stepUntilNextTick_nodeId_lt _ N
    · intro ev h_ev
      have : (w.logOutput s!"tick {w.tick}").events = w.events := by simp
      rw [this] at h_ev
      exact h_events ev h_ev
    · intro nid nd h_nd
      have : (w.logOutput s!"tick {w.tick}").getNode nid = w.getNode nid := by simp [World.logOutput, World.getNode]
      rw [this] at h_nd
      exact h_outputs nid nd h_nd
    · intro nid nd h_nd
      have : (w.logOutput s!"tick {w.tick}").getNode nid = w.getNode nid := by simp [World.logOutput, World.getNode]
      rw [this] at h_nd
      exact h_delay nid nd h_nd

/-- `simFoldl` preserves "all events have nodeId < N" (for ticks < t₂, with setInput in1 only). -/
theorem simFoldl_nodeId_lt (w : World) (t1 t2 pos in1 in2 : Nat) (n : Nat) (N : Nat)
    (h_events : ∀ ev ∈ w.events, ev.nodeId < N)
    (h_outputs : ∀ nid nd, w.getNode nid = some nd → nid < N → ∀ out ∈ nd.outputs, out < N)
    (h_delay : ∀ nid nd, w.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2)
    (h_in1 : in1 < N)
    (h_in1_outputs : ∀ nd, w.getNode in1 = some nd → ∀ out ∈ nd.outputs, out < N)
    (h_tick_ne : ∀ k < n, ((List.range k).foldl (simBody t1 t2 pos in1 in2) w).tick ≠ t2) :
    ∀ ev ∈ ((List.range n).foldl (simBody t1 t2 pos in1 in2) w).events, ev.nodeId < N := by
  induction n generalizing w with
  | zero => simpa using h_events
  | succ n' ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    set w_mid := (List.range n').foldl (simBody t1 t2 pos in1 in2) w
    have h_events_mid : ∀ ev ∈ w_mid.events, ev.nodeId < N :=
      ih w h_events h_outputs h_delay h_in1_outputs (fun k hk => h_tick_ne k (by omega))
    have h_outputs_mid : ∀ nid nd, w_mid.getNode nid = some nd → nid < N → ∀ out ∈ nd.outputs, out < N := by
      intro nid nd h_nd h_lt out h_out
      obtain ⟨nd₀, h₀, h_inp, h_outp⟩ := simFoldl_inputs_preserved w t1 t2 pos in1 in2 n' nid nd h_nd
      rw [h_outp] at h_out
      exact h_outputs nid nd₀ h₀ h_lt out h_out
    have h_delay_mid : ∀ nid nd, w_mid.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
      intro nid nd h_nd d p h_kind
      obtain ⟨nd₀, h₀, hk⟩ := simFoldl_kind_preserved w t1 t2 pos in1 in2 n' nid nd h_nd
      rw [hk] at h_kind
      exact h_delay nid nd₀ h₀ d p h_kind
    have h_in1_mid : in1 < N := h_in1
    have h_in1_outputs_mid : ∀ nd, w_mid.getNode in1 = some nd → ∀ out ∈ nd.outputs, out < N := by
      intro nd h_nd out h_out
      obtain ⟨nd₀, h₀, h_inp, h_outp⟩ := simFoldl_inputs_preserved w t1 t2 pos in1 in2 n' in1 nd h_nd
      rw [h_outp] at h_out
      exact h_in1_outputs nd₀ h₀ out h_out
    have h_tick_ne_mid : w_mid.tick ≠ t2 := h_tick_ne n' (by omega)
    exact simBody_nodeId_lt t1 t2 pos in1 in2 w_mid n' N
      h_events_mid h_outputs_mid h_delay_mid h_in1 h_in1_outputs_mid h_tick_ne_mid

/-- `simBody` preserves "no event targets node M" (for ticks ≠ t₂). -/
theorem simBody_nodeId_ne (t1 t2 pos in1 in2 : Nat) (w : World) (i : Nat) (M : Nat)
    (h_events : ∀ ev ∈ w.events, ev.nodeId ≠ M)
    (h_outputs : ∀ nid nd, w.getNode nid = some nd → ∀ out ∈ nd.outputs, out ≠ M)
    (h_delay : ∀ nid nd, w.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2)
    (h_tick_ne : w.tick ≠ t2) :
    ∀ ev ∈ (simBody t1 t2 pos in1 in2 w i).events, ev.nodeId ≠ M := by
  by_cases h_t1 : w.tick = t1
  · -- tick = t1 (and ≠ t2): simBody = (logOutput + setInput in1).stepUntilNextTick
    have h_eq : simBody t1 t2 pos in1 in2 w i =
        ((w.logOutput s!"tick {w.tick}").setInput in1 15).stepUntilNextTick := by
      unfold simBody
      dsimp (config := { zeta := true })
      split_ifs <;> simp_all [World.logOutput_tick, World.setInput_tick, beq_iff_eq]
    rw [h_eq]
    apply stepUntilNextTick_nodeId_ne _ M
    · intro ev h_ev
      by_cases h_old : ev ∈ (w.logOutput s!"tick {w.tick}").events
      · have : (w.logOutput s!"tick {w.tick}").events = w.events := by simp
        rw [this] at h_old
        exact h_events ev h_old
      · obtain ⟨nd, h_nd, h_out⟩ := setInput_nodeId_mem (w.logOutput s!"tick {w.tick}") in1 15 ev h_ev h_old
        have h_nd₀ : ∃ nd₀, w.getNode in1 = some nd₀ ∧ ev.nodeId ∈ nd₀.outputs := by
          have h_log : (w.logOutput s!"tick {w.tick}").getNode in1 = w.getNode in1 := by
            simp [World.logOutput, World.getNode]
          by_cases h_none : w.getNode in1 = none
          · exfalso
            have h_none' : (w.logOutput s!"tick {w.tick}").getNode in1 = none := by rw [h_log, h_none]
            have h_none'' := World.updateNode_getNode_none (w.logOutput s!"tick {w.tick}") in1
              (fun nd => { nd with sigLevel := 15 }) h_none'
            rw [h_none''] at h_nd
            cases h_nd
          · obtain ⟨nd₀, h_nd₀⟩ := Option.ne_none_iff_exists'.mp h_none
            refine ⟨nd₀, h_nd₀, ?_⟩
            have h_eq : nd.outputs = nd₀.outputs := by
              have h_gn := World.updateNode_getNode_eq (w.logOutput s!"tick {w.tick}") in1
                (fun nd => { nd with sigLevel := 15 }) nd₀ (by rwa [h_log])
              have : nd = { nd₀ with sigLevel := 15 } := by
                apply Option.some_inj.mp; rw [← h_nd, h_gn]
              simp [this]
            rw [← h_eq]; exact h_out
        obtain ⟨nd₀, h_nd₀, h_out₀⟩ := h_nd₀
        exact h_outputs in1 nd₀ h_nd₀ ev.nodeId h_out₀
    · intro nid nd h_nd out h_out
      obtain ⟨nd₀, h₀, h_inp, h_outp⟩ := World.setInput_inputs_preserved (w.logOutput s!"tick {w.tick}") in1 15 nid nd h_nd
      rw [h_outp] at h_out
      have h₀' : w.getNode nid = some nd₀ := by
        have : (w.logOutput s!"tick {w.tick}").getNode nid = w.getNode nid := by simp [World.logOutput, World.getNode]
        rwa [this] at h₀
      exact h_outputs nid nd₀ h₀' out h_out
    · intro nid nd h_nd d p h_kind
      obtain ⟨nd₀, h₀, hk⟩ := World.setInput_kind_preserved (w.logOutput s!"tick {w.tick}") in1 15 nid nd h_nd
      rw [hk] at h_kind
      have h₀' : w.getNode nid = some nd₀ := by
        have : (w.logOutput s!"tick {w.tick}").getNode nid = w.getNode nid := by simp [World.logOutput, World.getNode]
        rwa [this] at h₀
      exact h_delay nid nd₀ h₀' d p h_kind
  · -- tick ≠ t1 (and ≠ t2): simBody = (logOutput).stepUntilNextTick
    have h_eq : simBody t1 t2 pos in1 in2 w i =
        (w.logOutput s!"tick {w.tick}").stepUntilNextTick := by
      unfold simBody
      dsimp (config := { zeta := true })
      split_ifs <;> simp_all [World.logOutput_tick, beq_iff_eq]
    rw [h_eq]
    apply stepUntilNextTick_nodeId_ne _ M
    · intro ev h_ev
      have : (w.logOutput s!"tick {w.tick}").events = w.events := by simp
      rw [this] at h_ev
      exact h_events ev h_ev
    · intro nid nd h_nd out h_out
      have : (w.logOutput s!"tick {w.tick}").getNode nid = w.getNode nid := by simp [World.logOutput, World.getNode]
      rw [this] at h_nd
      exact h_outputs nid nd h_nd out h_out
    · intro nid nd h_nd d p h_kind
      have : (w.logOutput s!"tick {w.tick}").getNode nid = w.getNode nid := by simp [World.logOutput, World.getNode]
      rw [this] at h_nd
      exact h_delay nid nd h_nd d p h_kind

/-- `simFoldl` preserves "no event targets node M" (for ticks ≠ t₂). -/
theorem simFoldl_nodeId_ne (w : World) (t1 t2 pos in1 in2 : Nat) (n : Nat) (M : Nat)
    (h_events : ∀ ev ∈ w.events, ev.nodeId ≠ M)
    (h_outputs : ∀ nid nd, w.getNode nid = some nd → ∀ out ∈ nd.outputs, out ≠ M)
    (h_delay : ∀ nid nd, w.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2)
    (h_tick_ne : ∀ k < n, ((List.range k).foldl (simBody t1 t2 pos in1 in2) w).tick ≠ t2) :
    ∀ ev ∈ ((List.range n).foldl (simBody t1 t2 pos in1 in2) w).events, ev.nodeId ≠ M := by
  induction n generalizing w with
  | zero => simpa using h_events
  | succ n' ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    set w_mid := (List.range n').foldl (simBody t1 t2 pos in1 in2) w
    have h_events_mid : ∀ ev ∈ w_mid.events, ev.nodeId ≠ M :=
      ih w h_events h_outputs h_delay (fun k hk => h_tick_ne k (by omega))
    have h_outputs_mid : ∀ nid nd, w_mid.getNode nid = some nd → ∀ out ∈ nd.outputs, out ≠ M := by
      intro nid nd h_nd out h_out
      obtain ⟨nd₀, h₀, h_inp, h_outp⟩ := simFoldl_inputs_preserved w t1 t2 pos in1 in2 n' nid nd h_nd
      rw [h_outp] at h_out
      exact h_outputs nid nd₀ h₀ out h_out
    have h_delay_mid : ∀ nid nd, w_mid.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
      intro nid nd h_nd d p h_kind
      obtain ⟨nd₀, h₀, hk⟩ := simFoldl_kind_preserved w t1 t2 pos in1 in2 n' nid nd h_nd
      rw [hk] at h_kind
      exact h_delay nid nd₀ h₀ d p h_kind
    have h_tick_ne_mid : w_mid.tick ≠ t2 := h_tick_ne n' (by omega)
    exact simBody_nodeId_ne t1 t2 pos in1 in2 w_mid n' M
      h_events_mid h_outputs_mid h_delay_mid h_tick_ne_mid

/-- `simFoldl` preserves event target tick parity (for ticks < t₂). -/
theorem simFoldl_parity (w : World) (t1 t2 pos in1 in2 : Nat) (n : Nat) (p : Nat)
    (h_parity : ∀ ev ∈ w.events, ev.targetTick % 2 = p)
    (h_even : ∀ nid nd, w.getNode nid = some nd → ∀ d pr,
        nd.kind = .repeater d pr → (d : Nat) % 2 = 0)
    (h_tick_ne : ∀ k < n, ((List.range k).foldl (simBody t1 t2 pos in1 in2) w).tick ≠ t2)
    (h_t1_p : t1 % 2 = p) :
    ∀ ev ∈ ((List.range n).foldl (simBody t1 t2 pos in1 in2) w).events, ev.targetTick % 2 = p := by
  induction n generalizing w with
  | zero => simpa using h_parity
  | succ n' ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    set w_mid := (List.range n').foldl (simBody t1 t2 pos in1 in2) w
    have h_parity_mid : ∀ ev ∈ w_mid.events, ev.targetTick % 2 = p :=
      ih w h_parity h_even (fun k hk => h_tick_ne k (by omega))
    have h_even_mid : ∀ nid nd, w_mid.getNode nid = some nd → ∀ d pr,
        nd.kind = .repeater d pr → (d : Nat) % 2 = 0 := by
      intro nid nd h_nd d pr h_kind
      obtain ⟨nd₀, h₀, hk⟩ := simFoldl_kind_preserved w t1 t2 pos in1 in2 n' nid nd h_nd
      rw [hk] at h_kind
      exact h_even nid nd₀ h₀ d pr h_kind
    have h_tick_ne_mid : w_mid.tick ≠ t2 := h_tick_ne n' (by omega)
    have h_tick_p : w_mid.tick = t1 → w_mid.tick % 2 = p := by
      intro h_eq; rw [h_eq, h_t1_p]
    exact simBody_parity t1 t2 pos in1 in2 w_mid n' p h_parity_mid h_even_mid h_tick_ne_mid h_tick_p

/-- `processNEvents` preserves event target tick parity. -/
theorem processNEvents_parity (w : World) (n : Nat) (p : Nat)
    (h_parity : ∀ ev ∈ w.events, ev.targetTick % 2 = p)
    (h_even : ∀ nid nd, w.getNode nid = some nd → ∀ d pr,
        nd.kind = .repeater d pr → (d : Nat) % 2 = 0) :
    ∀ ev ∈ (processNEvents w n).events, ev.targetTick % 2 = p := by
  induction n generalizing w with
  | zero => simpa [processNEvents] using h_parity
  | succ n' ih =>
    dsimp [processNEvents]
    cases h_step : w.step with
    | none => simpa [h_step] using h_parity
    | some w' =>
      simp []
      -- w' has parity p (from step)
      have h_parity' : ∀ ev ∈ w'.events, ev.targetTick % 2 = p := by
        dsimp [World.step] at h_step
        cases h_pop : w.popNextEvent with
        | none => simp [h_pop] at h_step
        | some pp =>
          cases pp with | mk ev_pop w_pop =>
          simp only [h_pop] at h_step
          injection h_step with h_w'_eq
          rw [← h_w'_eq]
          obtain ⟨_, _, h_erase, h_ev_tick, h_ev_mem, _⟩ :=
            World.popNextEvent_eraseIdx w ev_pop w_pop h_pop
          intro ev h_ev
          by_cases h_old : ev ∈ w_pop.events
          · have h_mem : ev ∈ w.events := by
              rw [h_erase] at h_old; exact List.mem_of_mem_eraseIdx h_old
            exact h_parity ev h_mem
          · have h_even_pop : ∀ nid nd, w_pop.getNode nid = some nd → ∀ d pr,
                nd.kind = .repeater d pr → (d : Nat) % 2 = 0 := by
              intro nid nd h_nd d pr h_kind
              have h_nodes : w_pop.nodes = w.nodes := World.popNextEvent_nodes w ev_pop w_pop h_pop
              have h_nd_w : w.getNode nid = some nd := by
                dsimp [World.getNode] at h_nd ⊢; rw [← h_nodes]; exact h_nd
              exact h_even nid nd h_nd_w d pr h_kind
            have h_new := World.onScheduledTick_events_parity w_pop ev_pop.nodeId h_even_pop ev h_ev h_old
            have h_tick_pop : w_pop.tick = w.tick := World.popNextEvent_tick w ev_pop w_pop h_pop
            have h_tick_p : w.tick % 2 = p := by
              rw [← h_ev_tick]; exact h_parity ev_pop h_ev_mem
            rw [h_tick_pop, h_tick_p] at h_new
            exact h_new
      -- Even delays preserved through step
      have h_even' : ∀ nid nd, w'.getNode nid = some nd → ∀ d pr,
          nd.kind = .repeater d pr → (d : Nat) % 2 = 0 := by
        intro nid nd h_nd d pr h_kind
        obtain ⟨nd₀, h₀, hk⟩ := World.step_kind_preserved w w' h_step nid nd h_nd
        rw [hk] at h_kind
        exact h_even nid nd₀ h₀ d pr h_kind
      exact ih w' h_parity' h_even'
