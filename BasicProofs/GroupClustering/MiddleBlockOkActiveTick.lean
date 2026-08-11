import BasicProofs.GroupClustering.MiddleBlockOkTicks
import BasicProofs.GroupClustering.BackwardTransport
import BasicProofs.GroupClustering.CrossPriorityPopDiscipline
import BasicProofs.GroupClustering.StageInductionSideFacts
import BasicProofs.GroupClustering.ConverseStageJ

open BasicRedstoneSim List

/-! # Group clustering — MiddleBlockOk across an active tick, general fates

One `gSimBody` tick at an activating moment runs `gSimBurst` and then
`stepUntilNextTick`. MiddleBlockOkTicks's `MiddleBlockOk_gSimBody_step_burst` proves
the middle-block step under the extra hypothesis that both
stage-`(j + 1)` reference events survive the burst into the burst
result. Those survival hypotheses are not provable in general: a
reference successor may be spawned by the drain instead of the burst.

This file removes exactly those two premises. The burst phase still
advances the invariant to stage `j + 1` on the post-burst queue
(`MiddleBlockOk_step_gSimBurst`, MiddleBlockPopStep). The drain step then carries
the stage-`(j + 1)` invariant through `stepUntilNextTick` for every
fate combination of the two reference events and the interloper:
survivor or spawn of the burst or of the drain. The drain splits the
post-drain queue into survivors (old non-due events) followed by the
chronological spawn accumulator, and every survivor precedes every
spawn. That structural fact alone discharges the mixed survivor/spawn
contradictions; the all-spawn and mixed-spawn cases trace the interloper
back to its parent pop.
-/

/-! ## Private helpers -/

/-- A list of length zero is empty. -/
private theorem list_nil_of_length_zero' {α : Type} (l : List α)
    (h : l.length = 0) : l = [] := by
  cases l with
  | nil => rfl
  | cons _ _ => simp at h

/-- Erasing an in-range element removes exactly one position. -/
private theorem length_eraseIdx_of_lt' {α : Type} (l : List α) (i : Nat)
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
      omega

/-- A filter keeps a list unchanged when the predicate holds
    everywhere. -/
private theorem filter_eq_self_of_forall'' {α : Type} (p : α → Bool)
    (l : List α) (h : ∀ x ∈ l, p x = true) : l.filter p = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have h_x := h x (List.mem_cons.mpr (Or.inl rfl))
    simp [List.filter, h_x,
      ih (fun y hy => h y (List.mem_cons.mpr (Or.inr hy)))]

/-- One pop removes the popped event from the due filter. -/
private theorem due_tail_eq_eraseIdx' (w : World) (ev₀ : ScheduledEvent)
    (w_pop : World) (h_pop : w.popNextEvent = some (ev₀, w_pop)) :
    ∃ j, j < (w.events.filter (fun e => e.targetTick == w.tick)).length ∧
      (w_pop.onScheduledTick ev₀.nodeId).events.filter
          (fun e => e.targetTick == w.tick) =
        (w.events.filter (fun e => e.targetTick == w.tick)).eraseIdx j := by
  obtain ⟨idx, h_idx, h_erase, h_tick_ev, _, h_get⟩ :=
    World.popNextEvent_eraseIdx w ev₀ w_pop h_pop
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

/-- A full drain of the due events leaves no event at the tick. -/
private theorem drain_due_filter' (w : World) :
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
      apply list_nil_of_length_zero'
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
          apply List.filter_eq_nil_iff.mpr
          intro ev h_ev
          by_cases h_be : ev.targetTick = w.tick
          · exact (popNextEvent_none_no_events w h_pop ev h_ev h_be).elim
          · simp [h_be]
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
            obtain ⟨j, hj, h_eq⟩ := due_tail_eq_eraseIdx' w ev₀ w_pop h_pop
            rw [h_tick, h_eq, length_eraseIdx_of_lt' _ _ hj]
            omega
          have h_tick_w' : w'.tick = w.tick := by
            rw [← h_w', World.onScheduledTick_tick,
              World.popNextEvent_tick w ev₀ w_pop h_pop]
          rw [← h_tick_w']
          exact ih w' h_len'
  exact h_gen w _ (by omega)

/-- `(l₁ ++ l₂).drop l₁.length = l₂`. -/
private theorem drop_append_self' {α : Type} (l₁ l₂ : List α) :
    (l₁ ++ l₂).drop l₁.length = l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a l ih => simp [ih]

/-- Append cancellation on the left. -/
private theorem append_left_cancel'' {α : Type} (l l₁ l₂ : List α)
    (h : l ++ l₁ = l ++ l₂) : l₁ = l₂ := by
  induction l generalizing l₁ l₂ with
  | nil => simpa using h
  | cons a l ih =>
    simp only [List.cons_append] at h
    exact ih l₁ l₂ (by simpa using congrArg List.tail h)

/-- In a split `l ++ r = p ++ s` with `p` at least as long as `l`, the
    prefix `p` starts with `l`. -/
private theorem append_prefix_of_length_le' {α : Type} (l r p s : List α)
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
private theorem mem_left_of_short_prefix_split' {α : Type}
    (l r p q : List α) (x : α) (h_eq : l ++ r = p ++ x :: q)
    (h_lt : p.length < l.length) : x ∈ l := by
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

/-- If the left anchor is absent from `l`, then `evBefore (l ++ r) x y`
    already holds in `r`. -/
private theorem evBefore_append_left_absent' {l r : List ScheduledEvent}
    {x y : ScheduledEvent} (h_x : x ∉ l) (h : evBefore (l ++ r) x y) :
    evBefore r x y := by
  obtain ⟨p, q, h_eq, h_y⟩ := h
  have h_len : l.length ≤ p.length := by
    by_contra h_lt
    exact h_x (mem_left_of_short_prefix_split' l r p q x h_eq (by omega))
  obtain ⟨p₁, _, h_r⟩ := append_prefix_of_length_le' l r p (x :: q) h_eq h_len
  exact ⟨p₁, q, h_r, h_y⟩

/-- With `y` in the split of `evBefore (l ++ r) x y`, either `x` lies in
    `l` or the betweenness already holds in `r`. -/
private theorem evBefore_append_split_right' {l r : List ScheduledEvent}
    {x y : ScheduledEvent} (h : evBefore (l ++ r) x y) :
    x ∈ l ∨ evBefore r x y := by
  obtain ⟨p, q, h_eq, h_yq⟩ := h
  by_cases h_lt : p.length < l.length
  · exact Or.inl (mem_left_of_short_prefix_split' l r p q x h_eq h_lt)
  · obtain ⟨p₁, _, h_r⟩ :=
      append_prefix_of_length_le' l r p (x :: q) h_eq (by omega)
    exact Or.inr ⟨p₁, q, h_r, h_yq⟩

/-- `evBefore l x x` splits the list around two copies of `x`. -/
private theorem evBefore_self_two_split' {l : List ScheduledEvent}
    {x : ScheduledEvent} (h : evBefore l x x) :
    ∃ l₁ l₂ l₃, l = l₁ ++ x :: (l₂ ++ x :: l₃) := by
  obtain ⟨p, q, h_eq, h_x⟩ := h
  obtain ⟨p₂, q₂, h_q⟩ := mem_split_append q x h_x
  refine ⟨p, p₂, q₂, ?_⟩
  rw [h_eq, h_q]

/-- A due event is always popped by a drain with fuel equal to the due
    count. -/
private theorem due_mem_popSeqFuel_drain' (w : World) (x : ScheduledEvent)
    (h_x : x ∈ w.events) (h_due : x.targetTick = w.tick) :
    x ∈ World.popSeqFuel w
      ((w.events.filter (fun e => e.targetTick == w.tick)).length) := by
  have h_gen : ∀ (w : World) (n : Nat),
      (w.events.filter (fun e => e.targetTick == w.tick)).length = n →
      ∀ x ∈ w.events, x.targetTick = w.tick → x ∈ World.popSeqFuel w n := by
    intro w n
    induction n generalizing w with
    | zero =>
      intro h_len x h_x h_due
      have h_mem : x ∈ w.events.filter (fun e => e.targetTick == w.tick) :=
        by
        rw [List.mem_filter]
        exact ⟨h_x, by rw [h_due]; simp⟩
      have h_nil : w.events.filter (fun e => e.targetTick == w.tick) = [] :=
        list_nil_of_length_zero' _ h_len
      rw [h_nil] at h_mem
      cases h_mem
    | succ n ih =>
      intro h_len x h_x h_due
      cases h_pop : w.popNextEvent with
      | none =>
        exact (popNextEvent_none_no_events w h_pop x h_x h_due).elim
      | some p =>
        rcases p with ⟨ev₀, w_pop⟩
        dsimp only [World.popSeqFuel]
        rw [h_pop]
        by_cases h_ev_x : ev₀ = x
        · rw [h_ev_x]
          exact List.mem_cons.mpr (Or.inl rfl)
        · obtain ⟨idx, h_idx, h_erase, _, _, h_get_idx⟩ :=
            World.popNextEvent_eraseIdx w ev₀ w_pop h_pop
          have h_x_pop : x ∈ w_pop.events := by
            rw [h_erase]
            exact mem_eraseIdx_of_ne w.events idx h_idx ev₀ x h_get_idx
              h_x (Ne.symm h_ev_x)
          have h_tick_pop : w_pop.tick = w.tick :=
            World.popNextEvent_tick w ev₀ w_pop h_pop
          set w' := w_pop.onScheduledTick ev₀.nodeId
          have h_x_w' : x ∈ w'.events := by
            dsimp only [w']
            obtain ⟨new, h_app, _⟩ :=
              World.onScheduledTick_appends_future w_pop ev₀.nodeId
            rw [h_app]
            exact List.mem_append_left _ h_x_pop
          have h_due_w' : x.targetTick = w'.tick := by
            dsimp only [w']
            rw [World.onScheduledTick_tick, h_tick_pop]
            exact h_due
          have h_len' : (w'.events.filter
              (fun e => e.targetTick == w'.tick)).length = n := by
            dsimp only [w']
            obtain ⟨j, hj, h_eq⟩ := due_tail_eq_eraseIdx' w ev₀ w_pop h_pop
            rw [World.onScheduledTick_tick, h_tick_pop, h_eq,
              length_eraseIdx_of_lt' _ _ hj]
            omega
          exact List.mem_cons.mpr (Or.inr
            (ih w' h_len' x h_x_w' h_due_w'))
  exact h_gen w _ rfl x h_x h_due

/-- `onScheduledTick` preserves the chain-node layout: only signal
    levels change. -/
private theorem NodeLayoutOk_onScheduledTick' (groups : List GroupSpec)
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
      obtain ⟨nd, h₁, hk₁, ho₁⟩ := h_keep (chainBaseId groups gi ci +
          (chainAt groups gi ci).middleDelays.length + 2) nd₀ h₀
      exact ⟨nd, h₁, by rw [hk₁, hk], by rw [ho₁, ho]⟩
    · intro gi ci h_gi h_ci
      obtain ⟨nd₀, h₀, hk, ho⟩ := hOut gi ci h_gi h_ci
      obtain ⟨nd, h₁, hk₁, ho₁⟩ := h_keep (chainBaseId groups gi ci +
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
    · rw [World.notifyOutputs_getNode]
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
    · rw [World.notifyOutputs_getNode]
      by_cases h_eq : nid = id
      · have h_gid₀ : w.getNode id = some nd₀ := by rwa [← h_eq]
        refine ⟨{ nd₀ with sigLevel := 15 }, ?_, rfl, rfl⟩
        rw [h_eq]
        exact World.updateNode_getNode_eq w id
          (fun nd' => { nd' with sigLevel := 15 }) nd₀ h_gid₀
      · refine ⟨nd₀, ?_, rfl, rfl⟩
        rw [World.updateNode_getNode_ne w id nid
          (fun nd' => { nd' with sigLevel := 15 }) (Ne.symm h_eq), h₀]
    · exact ⟨nd₀, h₀, rfl, rfl⟩

/-- A due event popped during a full drain deposits its spawn in the
    drain's spawn accumulator. -/
private theorem drain_spawn_mem' (groups : List GroupSpec) (w : World)
    (X sX : ScheduledEvent)
    (h_X : X ∈ w.events) (h_X_due : X.targetTick = w.tick)
    (h_spawn : ∀ (v : World), v.tick = w.tick → NodeLayoutOk groups v →
        (v.onScheduledTick X.nodeId).events = v.events ++ [sX])
    (h_layout : NodeLayoutOk groups w) :
    sX ∈ World.popSpawnAcc w
      ((w.events.filter (fun e => e.targetTick == w.tick)).length) := by
  have h_gen : ∀ (w : World) (n : Nat),
      (w.events.filter (fun e => e.targetTick == w.tick)).length = n →
      NodeLayoutOk groups w →
      ∀ (X : ScheduledEvent), X ∈ w.events → X.targetTick = w.tick →
      (∀ (v : World), v.tick = w.tick → NodeLayoutOk groups v →
        (v.onScheduledTick X.nodeId).events = v.events ++ [sX]) →
      sX ∈ World.popSpawnAcc w n := by
    intro w n
    induction n generalizing w with
    | zero =>
      intro h_len h_lay X h_X h_due _
      exfalso
      have h_mem : X ∈ w.events.filter
          (fun e => e.targetTick == w.tick) := by
        rw [List.mem_filter]
        exact ⟨h_X, by rw [h_due]; simp⟩
      have h_nil : w.events.filter (fun e => e.targetTick == w.tick) = [] :=
        list_nil_of_length_zero' _ h_len
      rw [h_nil] at h_mem
      cases h_mem
    | succ n ih =>
      intro h_len h_lay X h_X h_due h_spawn
      cases h_pop : w.popNextEvent with
      | none =>
        exfalso
        exact popNextEvent_none_no_events w h_pop X h_X h_due
      | some p =>
        rcases p with ⟨ev₀, w_pop⟩
        dsimp only [World.popSpawnAcc]
        rw [h_pop]
        dsimp only
        obtain ⟨idx, h_idx, h_erase, _, _, h_get_idx⟩ :=
          World.popNextEvent_eraseIdx w ev₀ w_pop h_pop
        have h_tick_pop : w_pop.tick = w.tick :=
          World.popNextEvent_tick w ev₀ w_pop h_pop
        set w' := w_pop.onScheduledTick ev₀.nodeId
        obtain ⟨new₀, h_app₀, h_fut₀⟩ :=
          World.onScheduledTick_appends_future w_pop ev₀.nodeId
        rw [h_app₀, drop_append_self']
        by_cases h_ev_X : ev₀ = X
        · -- X pops now: its spawn is appended in this step
          have h_new_X : sX ∈ new₀ := by
            have h_lay_pop : NodeLayoutOk groups w_pop :=
              NodeLayoutOk_of_nodes_eq groups w w_pop
                (World.popNextEvent_nodes w ev₀ w_pop h_pop) h_lay
            have h_sp := h_spawn w_pop h_tick_pop h_lay_pop
            have h_eq : w_pop.events ++ [sX] = w_pop.events ++ new₀ := by
              rw [← h_sp, ← h_ev_X]
              exact h_app₀
            have h_new₀ : new₀ = [sX] :=
              (append_left_cancel'' w_pop.events [sX] new₀ h_eq).symm
            rw [h_new₀]
            simp
          exact List.mem_append.mpr (Or.inl h_new_X)
        · -- some other event pops: X survives; recurse into the tail
          have h_X_pop : X ∈ w_pop.events := by
            rw [h_erase]
            exact mem_eraseIdx_of_ne w.events idx h_idx ev₀ X h_get_idx
              h_X (Ne.symm h_ev_X)
          have h_X_w' : X ∈ w'.events := by
            dsimp only [w']
            rw [h_app₀]
            exact List.mem_append_left _ h_X_pop
          have h_tick_w' : w'.tick = w.tick := by
            dsimp only [w']
            rw [World.onScheduledTick_tick, h_tick_pop]
          have h_due_w' : X.targetTick = w'.tick := by
            rw [h_tick_w']
            exact h_due
          have h_lay_w' : NodeLayoutOk groups w' := by
            dsimp only [w']
            have h_lay_pop : NodeLayoutOk groups w_pop :=
              NodeLayoutOk_of_nodes_eq groups w w_pop
                (World.popNextEvent_nodes w ev₀ w_pop h_pop) h_lay
            exact NodeLayoutOk_onScheduledTick' groups w_pop ev₀.nodeId
              h_lay_pop
          have h_len' : (w'.events.filter
              (fun e => e.targetTick == w'.tick)).length = n := by
            dsimp only [w']
            obtain ⟨j, hj, h_eq⟩ := due_tail_eq_eraseIdx' w ev₀ w_pop h_pop
            rw [World.onScheduledTick_tick, h_tick_pop, h_eq,
              length_eraseIdx_of_lt' _ _ hj]
            omega
          exact List.mem_append.mpr (Or.inr
            (ih w' h_len' h_lay_w' X h_X_w' h_due_w' (fun v h_v h_lay =>
              h_spawn v (by rw [h_v, h_tick_w']) h_lay)))
  exact h_gen w _ rfl h_layout X h_X h_X_due h_spawn

/-! ## The burst pop machinery

The burst phase interleaves `processNEvents` pop phases with
`activateGroup` appends. The appended observer events target tick
`+ 2` and carry priority `0`, so they never disturb the due-filter
dynamics at the burst tick. The filtered event split below makes this
precise: through the priority-`≠ 0` filter, the burst result is the old
filtered queue plus the filtered spawn accumulator of all burst pops. -/

/-- A filter is empty when no member satisfies the predicate. -/
private theorem filter_empty_of_none' {α : Type} (p : α → Bool)
    (l : List α) (h : ∀ x ∈ l, p x = false) : l.filter p = [] := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp [List.filter, h x (List.mem_cons.mpr (Or.inl rfl)),
      ih (fun y hy => h y (List.mem_cons.mpr (Or.inr hy)))]

/-- A Nat inequality decides the `==` comparison to false. -/
private theorem nat_beq_false_of_ne' (a b : Nat) (h : a ≠ b) :
    (a == b) = false := by
  simp [h]

/-- Equal node lists give equal node lists after one
    `onScheduledTick`. Only signal levels change. -/
private theorem onScheduledTick_nodes_of_nodes_eq' (w₁ w₂ : World)
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
private theorem popSpawnAcc_of_no_due' (w : World) (fuel : Nat)
    (h_no : ∀ ev ∈ w.events, ev.targetTick ≠ w.tick) :
    World.popSpawnAcc w fuel = [] := by
  induction fuel with
  | zero => dsimp [World.popSpawnAcc]
  | succ fuel ih =>
    dsimp only [World.popSpawnAcc]
    rw [World.popNextEvent_none_of_no_due w h_no]

/-- The spawn accumulator splits over a fuel sum. -/
private theorem popSpawnAcc_concat' (w : World) (a b : Nat) :
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
      rw [popSpawnAcc_of_no_due' w (a + b + 1) h_no]
      have h_acc : World.popSpawnAcc w (a + 1) = [] := by
        dsimp [World.popSpawnAcc]
        simp only [h_pop]
      have h_world : World.popSeqWorldFuel w (a + 1) = w := by
        dsimp [World.popSeqWorldFuel]
        simp only [h_pop]
      rw [h_acc, h_world, List.nil_append]
      exact (popSpawnAcc_of_no_due' w b h_no).symm
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
private theorem popSpawnAcc_congr' (w₁ w₂ : World)
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
        rw [h_new₁, h_new₂, drop_append_self', drop_append_self']
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
          apply filter_empty_of_none'
          intro e h_e
          have h_gt := h_fut₁ e h_e
          exact nat_beq_false_of_ne' e.targetTick w_pop₁.tick (by omega)
        have h_nil₂ :
            new₂.filter (fun e => e.targetTick == w_pop₂.tick) = [] := by
          apply filter_empty_of_none'
          intro e h_e
          have h_gt := h_fut₂ e h_e
          exact nat_beq_false_of_ne' e.targetTick w_pop₂.tick (by omega)
        rw [h_nil₁, h_nil₂, List.append_nil, List.append_nil]
        exact popNextEvent_filter_eq w₁ w₂ h_tick h_filter ev₀ w_pop₁
          w_pop₂ h_pop₁ h_pop₂
      have h_nodes_v : v₁.nodes = v₂.nodes :=
        onScheduledTick_nodes_of_nodes_eq' w_pop₁ w_pop₂ ev₀.nodeId
          h_nodes_pop
      rw [ih v₁ v₂ h_tick_v h_filter_v h_nodes_v]

/-- Total pop fuel spent by the `processNEvents` phases of a burst. -/
private def burstFuel' (t : Nat) (pos : Nat → List Nat) :
    List (Nat × Nat) → Nat
  | [] => 0
  | (_, k) :: ps => (pos t)[k]?.getD 0 + burstFuel' t pos ps

/-- The non-due, non-zero-priority part of the burst result: the old
    filtered queue plus the filtered spawn accumulator of the popped
    due events. The observer batches drop out of the filter. -/
private theorem gSimBurst_filter_split' (t : Nat)
    (obsAll : List (List Nat)) (withinOrd pos : Nat → List Nat)
    (w : World) (pairs : List (Nat × Nat)) :
    ((gSimBurst t obsAll withinOrd pos w pairs).events.filter
        (fun ev => ev.targetTick ≠ w.tick)).filter
      (fun ev => decide (ev.priority ≠ (0 : Int))) =
      (w.events.filter (fun ev => ev.targetTick ≠ w.tick)).filter
        (fun ev => decide (ev.priority ≠ (0 : Int))) ++
      (World.popSpawnAcc w (burstFuel' t pos pairs)).filter
        (fun ev => decide (ev.priority ≠ (0 : Int))) := by
  set pPri : ScheduledEvent → Bool :=
    fun ev => decide (ev.priority ≠ (0 : Int))
  induction pairs generalizing w with
  | nil =>
    dsimp [gSimBurst, burstFuel', World.popSpawnAcc]
    simp [pPri]
  | cons p ps ih =>
    rcases p with ⟨gi, k⟩
    dsimp only [gSimBurst, List.foldl_cons, burstFuel']
    set m := (pos t)[k]?.getD 0
    set ordered : List Nat := (withinOrd gi).foldl (fun acc ci =>
      match (obsAll[gi]?.getD [])[ci]? with
      | some oid => acc ++ [oid]
      | none => acc) []
    set Wp := processNEvents w m
    set W₁ := activateGroup Wp ordered
    have h_ih := ih W₁
    have h_tick_Wp : Wp.tick = w.tick := by
      dsimp [Wp]; exact processNEvents_tick w m
    have h_tick_W₁ : W₁.tick = w.tick := by
      dsimp [W₁, Wp]; rw [activateGroup_tick, h_tick_Wp]
    rw [h_tick_W₁] at h_ih
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
        apply filter_empty_of_none'
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
    have h_acc : World.popSpawnAcc W₁ (burstFuel' t pos ps) =
        World.popSpawnAcc Wp (burstFuel' t pos ps) := by
      refine popSpawnAcc_congr' W₁ Wp ?_ ?_ (activateGroup_nodes Wp ordered)
        (burstFuel' t pos ps)
      · dsimp [W₁]
        exact activateGroup_tick Wp ordered
      · dsimp [W₁]
        rw [activateGroup_tick]
        exact activateGroup_due_filter Wp ordered
    change ((gSimBurst t obsAll withinOrd pos W₁ ps).events.filter
        (fun ev => ev.targetTick ≠ w.tick)).filter pPri =
      (w.events.filter (fun ev => ev.targetTick ≠ w.tick)).filter pPri ++
        (World.popSpawnAcc w (m + burstFuel' t pos ps)).filter pPri
    rw [h_ih, h_W₁_filter, h_acc, h_Wp_filter]
    rw [List.append_assoc, ← List.filter_append]
    congr 1
    rw [popSpawnAcc_concat' w m (burstFuel' t pos ps)]
    have h_tail : World.popSpawnAcc Wp (burstFuel' t pos ps) =
        World.popSpawnAcc (World.popSeqWorldFuel w m)
          (burstFuel' t pos ps) := by
      congr 1
      dsimp [Wp]
      exact processNEvents_eq_popSeqWorldFuel w m
    rw [h_tail]

/-! ## Popped burst events are absent from the burst result -/

/-- Filter reduction for a kept head. -/
private theorem filter_cons_true' (p : ScheduledEvent → Bool)
    (a : ScheduledEvent) (l : List ScheduledEvent) (h_pa : p a = true) :
    (a :: l).filter p = a :: l.filter p := by
  simp [List.filter, h_pa]

/-- If `l[idx] = a` and `a` survives `eraseIdx idx`, then `l` carries `a`
    at two positions. -/
private theorem two_split_of_mem_eraseIdx' {α : Type} (l : List α)
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

/-- A popped due event leaves the queue of the popped world. The due
    filter is duplicate-free, so the pop removed its only copy. -/
private theorem not_mem_popWorld_of_due_nodup' (w : World)
    (ev₀ : ScheduledEvent) (w_pop : World)
    (h_pop : w.popNextEvent = some (ev₀, w_pop))
    (h_nodup : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup) :
    ev₀ ∉ w_pop.events := by
  obtain ⟨idx, h_idx, h_erase, h_tick_ev, _, h_get⟩ :=
    World.popNextEvent_eraseIdx w ev₀ w_pop h_pop
  rw [h_erase]
  intro h_mem
  obtain ⟨l₁, l₂, l₃, h_split⟩ :=
    two_split_of_mem_eraseIdx' w.events idx h_idx ev₀ h_get h_mem
  set p := (fun e : ScheduledEvent => e.targetTick == w.tick)
  have h_p : p ev₀ = true := by dsimp [p]; rw [h_tick_ev]; simp
  have h_filter : w.events.filter p =
      l₁.filter p ++ ev₀ :: (l₂.filter p ++ ev₀ :: l₃.filter p) := by
    rw [h_split, List.filter_append, List.filter_append,
      filter_cons_true' p ev₀ l₂ h_p, filter_cons_true' p ev₀ l₃ h_p,
      ← List.cons_append, List.append_assoc]
  exact nodup_cons_append_not_mem (h_filter ▸ h_nodup)
    (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))

/-- An event due at the current tick that is absent from the queue stays
    absent through any fuel-bounded pop run. -/
private theorem due_absent_stays_absent' (w : World) (fuel : Nat)
    (ev : ScheduledEvent) (h_due : ev.targetTick = w.tick)
    (h_absent : ev ∉ w.events) :
    ev ∉ (World.popSeqWorldFuel w fuel).events := by
  induction fuel generalizing w with
  | zero => dsimp [World.popSeqWorldFuel]; exact h_absent
  | succ fuel ih =>
    dsimp only [World.popSeqWorldFuel]
    cases h_pop : w.popNextEvent with
    | none => exact h_absent
    | some p =>
      rcases p with ⟨ev₀, w_pop⟩
      apply ih (w_pop.onScheduledTick ev₀.nodeId)
      · rw [World.onScheduledTick_tick,
          World.popNextEvent_tick w ev₀ w_pop h_pop, h_due]
      · obtain ⟨new, h_app, h_fut⟩ :=
          World.onScheduledTick_appends_future w_pop ev₀.nodeId
        obtain ⟨idx, h_idx, h_erase, _, _, _⟩ :=
          World.popNextEvent_eraseIdx w ev₀ w_pop h_pop
        rw [h_app, List.mem_append]
        intro h_mem
        rcases h_mem with h_mem | h_new
        · rw [h_erase] at h_mem
          exact h_absent (List.eraseIdx_subset' w.events idx h_mem)
        · have h_gt := h_fut ev h_new
          rw [World.popNextEvent_tick w ev₀ w_pop h_pop, h_due] at h_gt
          omega

/-- An event popped within the fuel bound is absent from the fuel-bounded
    pop world: each pop removes the only due copy. -/
private theorem not_mem_popSeqWorldFuel_of_mem_popSeqFuel' (w : World)
    (fuel : Nat)
    (h_nd : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup)
    (ev : ScheduledEvent) (h_ev : ev ∈ World.popSeqFuel w fuel) :
    ev ∉ (World.popSeqWorldFuel w fuel).events := by
  induction fuel generalizing w h_nd with
  | zero =>
    dsimp [World.popSeqFuel] at h_ev
    cases h_ev
  | succ fuel ih =>
    dsimp only [World.popSeqFuel, World.popSeqWorldFuel] at h_ev ⊢
    cases h_pop : w.popNextEvent with
    | none =>
      simp only [h_pop] at h_ev
      cases h_ev
    | some p =>
      rcases p with ⟨ev₀, w_pop⟩
      simp only [h_pop] at h_ev ⊢
      set w' := w_pop.onScheduledTick ev₀.nodeId
      rw [List.mem_cons] at h_ev
      rcases h_ev with h_ev₀ | h_ev_tail
      · rw [h_ev₀]
        apply due_absent_stays_absent' w' fuel ev₀
        · dsimp only [w']
          rw [World.onScheduledTick_tick,
            World.popNextEvent_tick w ev₀ w_pop h_pop]
          obtain ⟨_, _, _, h_tick_ev, _, _⟩ :=
            World.popNextEvent_eraseIdx w ev₀ w_pop h_pop
          exact h_tick_ev
        · dsimp only [w']
          have h_nd_pop : ev₀ ∉ w_pop.events :=
            not_mem_popWorld_of_due_nodup' w ev₀ w_pop h_pop h_nd
          obtain ⟨new₀, h_app₀, h_fut₀⟩ :=
            World.onScheduledTick_appends_future w_pop ev₀.nodeId
          rw [h_app₀, List.mem_append]
          intro h_mem
          rcases h_mem with h_mem | h_new
          · exact h_nd_pop h_mem
          · have h_gt := h_fut₀ ev₀ h_new
            rw [World.popNextEvent_tick w ev₀ w_pop h_pop] at h_gt
            obtain ⟨_, _, _, h_tick_ev, _, _⟩ :=
              World.popNextEvent_eraseIdx w ev₀ w_pop h_pop
            rw [h_tick_ev] at h_gt
            omega
      · have h_nd_w' : (w'.events.filter
            (fun e => e.targetTick == w'.tick)).Nodup := by
          dsimp only [w']
          obtain ⟨j, hj, h_eq⟩ := due_tail_eq_eraseIdx' w ev₀ w_pop h_pop
          rw [World.onScheduledTick_tick,
            World.popNextEvent_tick w ev₀ w_pop h_pop, h_eq]
          exact nodup_eraseIdx _ j h_nd
        exact ih w' h_nd_w' h_ev_tail

/-- The pop sequence is unchanged by appending non-due events: pops
    depend only on the due sublist. -/
private theorem popSeqFuel_congr' (w₁ w₂ : World)
    (h_tick : w₁.tick = w₂.tick)
    (h_filter : w₁.events.filter (fun e => e.targetTick == w₁.tick) =
        w₂.events.filter (fun e => e.targetTick == w₂.tick))
    (h_nodes : w₁.nodes = w₂.nodes) (fuel : Nat) :
    World.popSeqFuel w₁ fuel = World.popSeqFuel w₂ fuel := by
  induction fuel generalizing w₁ w₂ h_tick h_filter h_nodes with
  | zero => dsimp [World.popSeqFuel]
  | succ fuel ih =>
    dsimp only [World.popSeqFuel]
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
          apply filter_empty_of_none'
          intro e h_e
          have h_gt := h_fut₁ e h_e
          exact nat_beq_false_of_ne' e.targetTick w_pop₁.tick (by omega)
        have h_nil₂ :
            new₂.filter (fun e => e.targetTick == w_pop₂.tick) = [] := by
          apply filter_empty_of_none'
          intro e h_e
          have h_gt := h_fut₂ e h_e
          exact nat_beq_false_of_ne' e.targetTick w_pop₂.tick (by omega)
        rw [h_nil₁, h_nil₂, List.append_nil, List.append_nil]
        exact popNextEvent_filter_eq w₁ w₂ h_tick h_filter ev₀ w_pop₁
          w_pop₂ h_pop₁ h_pop₂
      have h_nodes_v : v₁.nodes = v₂.nodes :=
        onScheduledTick_nodes_of_nodes_eq' w_pop₁ w_pop₂ ev₀.nodeId
          h_nodes_pop
      rw [ih v₁ v₂ (by
          dsimp only [v₁, v₂]
          rw [World.onScheduledTick_tick, World.onScheduledTick_tick,
            h_tick_pop]) h_filter_v h_nodes_v]

/-- `activateGroup` appends non-due events, so it does not change the
    pop sequence. -/
private theorem popSeqFuel_activateGroup' (w : World)
    (observers : List Nat) (fuel : Nat) :
    World.popSeqFuel (activateGroup w observers) fuel =
      World.popSeqFuel w fuel :=
  popSeqFuel_congr' (activateGroup w observers) w
    (activateGroup_tick w observers)
    (by rw [activateGroup_tick]; exact activateGroup_due_filter w observers)
    (activateGroup_nodes w observers) fuel

/-- An event popped by the burst pop sequence is absent from the burst
    result. -/
private theorem mem_popSeqFuel_not_mem_gSimBurst' (t : Nat)
    (obsAll : List (List Nat)) (withinOrd pos : Nat → List Nat)
    (w : World) (pairs : List (Nat × Nat))
    (h_nd : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup) :
    ∀ ev ∈ World.popSeqFuel w (burstFuel' t pos pairs),
      ev ∉ (gSimBurst t obsAll withinOrd pos w pairs).events := by
  induction pairs generalizing w h_nd with
  | nil =>
    intro ev h_ev
    dsimp only [burstFuel', World.popSeqFuel] at h_ev
    cases h_ev
  | cons p ps ih =>
    rcases p with ⟨gi, k⟩
    dsimp only [burstFuel']
    intro ev h_ev
    set m := (pos t)[k]?.getD 0
    set ordered : List Nat := (withinOrd gi).foldl (fun acc ci =>
      match (obsAll[gi]?.getD [])[ci]? with
      | some oid => acc ++ [oid]
      | none => acc) []
    set Wp := processNEvents w m
    set W₁ := activateGroup Wp ordered
    have h_tick_W₁ : W₁.tick = w.tick := by
      dsimp [W₁, Wp]; rw [activateGroup_tick, processNEvents_tick]
    rw [World.popSeqFuel_concat w m (burstFuel' t pos ps),
      List.mem_append] at h_ev
    rcases h_ev with h_ev | h_ev
    · -- ev was popped in the first segment
      have h_ev_due : ev.targetTick = w.tick :=
        World.mem_popSeqFuel_due w m ev h_ev
      have h_ev_np : ev ∉ Wp.events := by
        dsimp [Wp]
        rw [processNEvents_eq_popSeqWorldFuel]
        exact not_mem_popSeqWorldFuel_of_mem_popSeqFuel' w m h_nd ev h_ev
      intro h_ev_B
      have h_ev_W₁ : ev ∈ W₁.events :=
        mem_gSimBurst_due_back t obsAll withinOrd pos W₁ ps ev h_ev_B (by
          rw [h_ev_due, h_tick_W₁])
      dsimp [W₁] at h_ev_W₁
      rw [activateGroup_events_map, List.mem_append] at h_ev_W₁
      rcases h_ev_W₁ with h_ev_p | h_obs
      · exact h_ev_np h_ev_p
      · rcases List.mem_map.mp h_obs with ⟨nid, _, h_ev_eq⟩
        have h_tgt : ev.targetTick = Wp.tick + 2 := by rw [← h_ev_eq]
        have h_tick_Wp : Wp.tick = w.tick := by
          dsimp [Wp]; exact processNEvents_tick w m
        rw [h_tgt, h_tick_Wp] at h_ev_due
        omega
    · -- ev was popped in a later segment
      have h_ev_Wp : ev ∈ World.popSeqFuel Wp (burstFuel' t pos ps) := by
        rwa [← processNEvents_eq_popSeqWorldFuel] at h_ev
      have h_ev_W₁ : ev ∈ World.popSeqFuel W₁ (burstFuel' t pos ps) := by
        rwa [popSeqFuel_activateGroup']
      have h_nd_W₁ : (W₁.events.filter
          (fun e => e.targetTick == W₁.tick)).Nodup := by
        dsimp [W₁]
        rw [activateGroup_tick, activateGroup_due_filter]
        dsimp [Wp]
        exact processNEvents_due_nodup w m h_nd
      exact ih W₁ h_nd_W₁ ev h_ev_W₁

/-! ## Old events precede new events in the burst result -/

/-- A survivor of the original world sits before any event that was not
    in the original world, after a full burst. -/
private theorem gSimBurst_survivor_before_nonmember'
    (t : Nat) (obsAll : List (List Nat))
    (withinOrd pos : Nat → List Nat)
    (w : World) (pairs : List (Nat × Nat))
    (e sA : ScheduledEvent)
    (h_e_mem : e ∈ w.events)
    (h_e_nd : e.targetTick ≠ w.tick)
    (h_e_pri : e.priority ≠ (0 : Int))
    (h_sA_absent : sA ∉ w.events)
    (h_sA_mem : sA ∈
        (gSimBurst t obsAll withinOrd pos w pairs).events)
    (h_sA_nd : sA.targetTick ≠ w.tick)
    (h_sA_pri : sA.priority ≠ (0 : Int)) :
    evBefore (gSimBurst t obsAll withinOrd pos w pairs).events
      e sA := by
  revert w e sA h_e_mem h_e_nd h_e_pri h_sA_absent h_sA_mem
    h_sA_nd h_sA_pri
  induction pairs with
  | nil =>
    intro w e sA h_e_mem h_e_nd h_e_pri h_sA_absent h_sA_mem
      h_sA_nd h_sA_pri
    dsimp [gSimBurst] at h_sA_mem
    exact absurd h_sA_mem h_sA_absent
  | cons p ps ih =>
    intro w e sA h_e_mem h_e_nd h_e_pri h_sA_absent h_sA_mem
      h_sA_nd h_sA_pri
    rcases p with ⟨gi, k⟩
    dsimp only [gSimBurst, List.foldl_cons]
    set m := (pos t)[k]?.getD 0
    set obs : List Nat := obsAll[gi]?.getD []
    set ordered := (withinOrd gi).foldl (fun acc ci =>
      match obs[ci]? with
      | some oid => acc ++ [oid]
      | none => acc) []
    set wProc := processNEvents w m
    set w₁ := activateGroup wProc ordered
    set pTick : ScheduledEvent → Bool :=
      fun ev => decide (ev.targetTick ≠ w.tick)
    have h_tick_wProc : wProc.tick = w.tick :=
      processNEvents_tick w m
    have h_tick_w₁ : w₁.tick = w.tick := by
      dsimp [w₁]
      rw [activateGroup_tick, h_tick_wProc]
    -- e survives the step
    have h_e_filt : e ∈ w.events.filter pTick := by
      rw [List.mem_filter]
      exact ⟨h_e_mem, by rw [decide_eq_true_eq]; exact h_e_nd⟩
    have h_split : wProc.events.filter pTick =
        w.events.filter pTick ++ World.popSpawnAcc w m := by
      have h_f := (World.popSeqWorldFuel_filter_split w m).1
      rw [← processNEvents_eq_popSeqWorldFuel] at h_f
      exact h_f
    have h_e_wProc_f : e ∈ wProc.events.filter pTick := by
      rw [h_split]
      exact List.mem_append_left _ h_e_filt
    have h_e_wProc : e ∈ wProc.events :=
      List.mem_of_mem_filter h_e_wProc_f
    have h_e_w₁ : e ∈ w₁.events := by
      have h_w₁_ev : w₁.events = wProc.events ++
          ordered.map (fun nid =>
            (⟨wProc.tick + 2, 0, nid⟩ : ScheduledEvent)) := by
        dsimp [w₁]
        exact activateGroup_events_map wProc ordered
      rw [h_w₁_ev]
      exact List.mem_append_left _ h_e_wProc
    by_cases h_sA_w₁ : sA ∈ w₁.events
    · -- sA appeared in the first segment
      have h_w₁_ev : w₁.events = wProc.events ++
          ordered.map (fun nid =>
            (⟨wProc.tick + 2, 0, nid⟩ : ScheduledEvent)) := by
        dsimp [w₁]
        exact activateGroup_events_map wProc ordered
      have h_sA_proc : sA ∈ wProc.events := by
        rw [h_w₁_ev] at h_sA_w₁
        rw [List.mem_append] at h_sA_w₁
        rcases h_sA_w₁ with h_sA_p | h_sA_obs
        · exact h_sA_p
        · rcases List.mem_map.mp h_sA_obs with ⟨nid, _, h_eq⟩
          have h_pri₀ :
              (⟨wProc.tick + 2, 0, nid⟩ : ScheduledEvent).priority =
                (0 : Int) := by rfl
          rw [← h_eq] at h_sA_pri
          exact absurd h_pri₀ h_sA_pri
      have h_sA_filt_proc : sA ∈ wProc.events.filter pTick := by
        rw [List.mem_filter]
        exact ⟨h_sA_proc, by
          rw [decide_eq_true_eq]
          dsimp [wProc] at *
          rw [processNEvents_tick] at *
          exact h_sA_nd⟩
      rw [h_split] at h_sA_filt_proc
      have h_sA_sp : sA ∈ World.popSpawnAcc w m := by
        rw [List.mem_append] at h_sA_filt_proc
        rcases h_sA_filt_proc with h_sA_surv | h_sA_sp
        · exact absurd
              (List.mem_filter.mp h_sA_surv).1 h_sA_absent
        · exact h_sA_sp
      -- e is a survivor, sA is a spawn: e before sA
      have h_eb_proc_f : evBefore
          (wProc.events.filter pTick) e sA := by
        rw [h_split]
        exact evBefore.of_mem_append h_e_filt h_sA_sp
      have h_eb_proc : evBefore wProc.events e sA :=
        evBefore.of_filter pTick h_eb_proc_f
      have h_eb_w₁ : evBefore w₁.events e sA := by
        rw [h_w₁_ev]
        exact evBefore.append_right h_eb_proc
      exact evBefore_gSimBurst_of_notDue t obsAll withinOrd pos
        w₁ ps e sA
        (by rw [h_tick_w₁]; exact h_e_nd)
        (by rw [h_tick_w₁]; exact h_sA_nd) h_eb_w₁
    · -- sA is not in w₁. Apply the IH.
      exact ih w₁ e sA h_e_w₁
        (by rw [h_tick_w₁]; exact h_e_nd) h_e_pri
        h_sA_w₁ h_sA_mem
        (by rw [h_tick_w₁]; exact h_sA_nd) h_sA_pri

/-! ## Pop classification from the due-restricted stage invariant

The drain pops of the burst result `W_B` are due events, hence they were
already queued before the burst (`mem_gSimBurst_due_back`), where the
stage invariant classifies them. The next three helpers package the
single-spawn, unique-spawn and distinct-spawn facts that the converse
machinery of ConverseSpawn needs, under this due-restricted invariant. -/

/-- Every popped event spawns at most one event. -/
private theorem pops_single_spawn' (groups : List GroupSpec)
    (actTick : Nat → Nat) (w : World) (n : Nat)
    (h_stage_due : ∀ ev ∈ w.events, ev.targetTick = w.tick →
      ∃ gi ci j, gi < groups.length ∧ ci < (groupAt groups gi).length ∧
        j ≤ (chainAt groups gi ci).middleDelays.length + 1 ∧
        ev = stageEvent actTick groups gi ci j ∧
        (if j = 0 then actTick gi else
          stageTarget actTick groups gi ci (j - 1)) < w.tick + 1 ∧
        w.tick ≤ stageTarget actTick groups gi ci j) :
    ∀ ev ∈ World.popSeqFuel w n, ∀ (v : World),
      v.tick = w.tick → NodeLayoutOk groups v →
      ∃ s, (v.onScheduledTick ev.nodeId).events = v.events ++ [s] ∨
        (v.onScheduledTick ev.nodeId).events = v.events := by
  intro ev h_ev v h_v h_lay
  have h_ev_w : ev ∈ w.events :=
    World.mem_popSeqFuel_mem_events w n ev h_ev
  have h_ev_due : ev.targetTick = w.tick :=
    World.mem_popSeqFuel_due w n ev h_ev
  obtain ⟨gi₀, ci₀, k₀, h_gi₀, h_ci₀, _, h_ev_eq₀, _, _⟩ :=
    h_stage_due ev h_ev_w h_ev_due
  by_cases h_last :
      k₀ = (chainAt groups gi₀ ci₀).middleDelays.length + 1
  · refine ⟨ev, Or.inr ?_⟩
    rw [h_ev_eq₀, h_last]
    exact lastStage_spawn_nil groups actTick v gi₀ ci₀ h_gi₀ h_ci₀ h_lay
  · refine ⟨stageEvent actTick groups gi₀ ci₀ (k₀ + 1), Or.inl ?_⟩
    have h_mid : k₀ ≤ (chainAt groups gi₀ ci₀).middleDelays.length := by
      omega
    have h_tick : v.tick = stageTarget actTick groups gi₀ ci₀ k₀ := by
      rw [h_v, ← h_ev_due]
      have := congr_arg ScheduledEvent.targetTick h_ev_eq₀
      dsimp [stageEvent] at this
      exact this
    rw [h_ev_eq₀]
    exact stage_spawn groups actTick v gi₀ ci₀ k₀ h_gi₀ h_ci₀ h_mid
      h_tick h_lay

/-- Only the reference stage event spawns its reference successor. -/
private theorem pops_unique_spawn' (groups : List GroupSpec)
    (actTick : Nat → Nat) (w : World) (n : Nat)
    (A sA : ScheduledEvent) (gA cA jA : Nat)
    (h_gA : gA < groups.length) (h_cA : cA < (groupAt groups gA).length)
    (h_jA : jA ≤ (chainAt groups gA cA).middleDelays.length)
    (h_A : A = stageEvent actTick groups gA cA jA)
    (h_sA : sA = stageEvent actTick groups gA cA (jA + 1))
    (h_stage_due : ∀ ev ∈ w.events, ev.targetTick = w.tick →
      ∃ gi ci j, gi < groups.length ∧ ci < (groupAt groups gi).length ∧
        j ≤ (chainAt groups gi ci).middleDelays.length + 1 ∧
        ev = stageEvent actTick groups gi ci j ∧
        (if j = 0 then actTick gi else
          stageTarget actTick groups gi ci (j - 1)) < w.tick + 1 ∧
        w.tick ≤ stageTarget actTick groups gi ci j) :
    ∀ ev ∈ World.popSeqFuel w n, ∀ (v : World),
      v.tick = w.tick → NodeLayoutOk groups v → ∀ s,
      (v.onScheduledTick ev.nodeId).events = v.events ++ [s] →
      s = sA → ev = A := by
  intro ev h_ev v h_v h_lay s h_sp h_s
  have h_ev_w : ev ∈ w.events :=
    World.mem_popSeqFuel_mem_events w n ev h_ev
  have h_ev_due : ev.targetTick = w.tick :=
    World.mem_popSeqFuel_due w n ev h_ev
  obtain ⟨gi₀, ci₀, k₀, h_gi₀, h_ci₀, _, h_ev_eq₀, _, _⟩ :=
    h_stage_due ev h_ev_w h_ev_due
  by_cases h_last :
      k₀ = (chainAt groups gi₀ ci₀).middleDelays.length + 1
  · have h_nil : (v.onScheduledTick ev.nodeId).events = v.events := by
      rw [h_ev_eq₀, h_last]
      exact lastStage_spawn_nil groups actTick v gi₀ ci₀ h_gi₀ h_ci₀ h_lay
    rw [h_nil] at h_sp
    have h_len := congrArg List.length h_sp
    simp at h_len
  · have h_mid : k₀ ≤ (chainAt groups gi₀ ci₀).middleDelays.length := by
      omega
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
    have h_inj := append_left_cancel'' v.events
      [stageEvent actTick groups gi₀ ci₀ (k₀ + 1)] [s] h_sp
    injection h_inj with h_one
    rw [h_s, h_sA] at h_one
    obtain ⟨h_g_eq, h_c_eq, h_k_eq⟩ :=
      stageEvent_injective actTick groups gi₀ ci₀ (k₀ + 1) gA cA (jA + 1)
        h_gi₀ h_ci₀ h_gA h_cA (by omega) (by omega) h_one
    rw [h_ev_eq₀, h_g_eq, h_c_eq, h_A]
    congr 1
    omega

/-- Distinct pops spawn distinct events. -/
private theorem pops_distinct_spawn' (groups : List GroupSpec)
    (actTick : Nat → Nat) (w : World) (n : Nat)
    (h_stage_due : ∀ ev ∈ w.events, ev.targetTick = w.tick →
      ∃ gi ci j, gi < groups.length ∧ ci < (groupAt groups gi).length ∧
        j ≤ (chainAt groups gi ci).middleDelays.length + 1 ∧
        ev = stageEvent actTick groups gi ci j ∧
        (if j = 0 then actTick gi else
          stageTarget actTick groups gi ci (j - 1)) < w.tick + 1 ∧
        w.tick ≤ stageTarget actTick groups gi ci j) :
    ∀ ev₁ ∈ World.popSeqFuel w n,
      ∀ ev₂ ∈ World.popSeqFuel w n, ev₁ ≠ ev₂ →
      ∀ (v₁ v₂ : World), v₁.tick = w.tick → v₂.tick = w.tick →
      NodeLayoutOk groups v₁ → NodeLayoutOk groups v₂ →
      ∀ s₁ s₂, (v₁.onScheduledTick ev₁.nodeId).events = v₁.events ++ [s₁] →
      (v₂.onScheduledTick ev₂.nodeId).events = v₂.events ++ [s₂] →
      s₁ ≠ s₂ := by
  intro ev₁ h₁ ev₂ h₂ h_ne v₁ v₂ h_v₁ h_v₂ h_l₁ h_l₂ s₁ s₂ h_sp₁ h_sp₂
      h_s_eq
  obtain ⟨gi₁, ci₁, k₁, h_gi₁, h_ci₁, _, h_ev₁, _, _⟩ :=
    h_stage_due ev₁ (World.mem_popSeqFuel_mem_events w n ev₁ h₁)
      (World.mem_popSeqFuel_due w n ev₁ h₁)
  obtain ⟨gi₂, ci₂, k₂, h_gi₂, h_ci₂, _, h_ev₂, _, _⟩ :=
    h_stage_due ev₂ (World.mem_popSeqFuel_mem_events w n ev₂ h₂)
      (World.mem_popSeqFuel_due w n ev₂ h₂)
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
  have h_inj₁ := append_left_cancel'' v₁.events
    [stageEvent actTick groups gi₁ ci₁ (k₁ + 1)] [s₁] h_sp₁
  have h_inj₂ := append_left_cancel'' v₂.events
    [stageEvent actTick groups gi₂ ci₂ (k₂ + 1)] [s₂] h_sp₂
  injection h_inj₁ with h_s₁
  injection h_inj₂ with h_s₂
  rw [← h_s₁, ← h_s₂] at h_s_eq
  obtain ⟨h_g, h_c, h_k⟩ := stageEvent_injective actTick groups gi₁ ci₁
    (k₁ + 1) gi₂ ci₂ (k₂ + 1) h_gi₁ h_ci₁ h_gi₂ h_ci₂ (by omega)
    (by omega) h_s_eq
  rw [h_ev₁, h_ev₂, h_g, h_c] at h_ne
  exact h_ne (by congr 1; omega)

/-- Classifying a stage-`(j + 1)` interloper from its parent between the
    two stage-`j` reference events in the due filter: the stage-`j`
    invariant identifies the parent's chain, injectivity pins the stage
    index to `j`, and the prefix extends to stage `j + 1`. -/
private theorem middleBlock_succ_of_parent_between'
    (groups : List GroupSpec) (actTick : Nat → Nat) (T : Nat)
    (g₁ c₁ g₂ c₂ j : Nat) (queue : List ScheduledEvent)
    (e : ScheduledEvent) (g c k : Nat)
    (h_g : g < groups.length) (h_c : c < (groupAt groups g).length)
    (h_k_ge : 1 ≤ k)
    (h_k_le : k ≤ (chainAt groups g c).middleDelays.length)
    (h_e_eq : e = stageEvent actTick groups g c (k + 1))
    (hP_tgt : (stageEvent actTick groups g c k).targetTick =
        stageTarget actTick groups g₁ c₁ j)
    (hAC : evBefore queue (stageEvent actTick groups g₁ c₁ j)
        (stageEvent actTick groups g c k))
    (hCD : evBefore queue (stageEvent actTick groups g c k)
        (stageEvent actTick groups g₂ c₂ j))
    (h_mb : MiddleBlockOk groups actTick T queue g₁ c₁ g₂ c₂ j)
    (h_pri : e.priority = (-3 : Int))
    (h_tgt : e.targetTick = stageTarget actTick groups g₁ c₁ (j + 1))
    (h_j₁ : j + 1 ≤ (chainAt groups g₁ c₁).middleDelays.length) :
    MiddleBlock groups actTick T g₁ c₁ (j + 1) e := by
  set P := stageEvent actTick groups g c k
  have hP_pri : P.priority = (-3 : Int) := by
    dsimp [P, stageEvent]
    exact stagePri_middle groups g c k h_k_ge h_k_le
  have h_mb_P : MiddleBlock groups actTick T g₁ c₁ j P :=
    h_mb P hAC hCD hP_pri hP_tgt
  rcases h_mb_P with h_fin | ⟨g', c', h_g', h_c', h_P_eq, h_P_pri', _,
      h_pref⟩
  · exact absurd h_fin
      (fun h_fin' =>
        (IsFinalEvent_priority_ne_middle groups actTick T P h_fin') hP_pri)
  · -- the parent is a stage-j event: pin the indices
    have h_j_le' : j ≤ (chainAt groups g' c').middleDelays.length := by
      have h_p : stagePri groups g' c' j = (-3 : Int) := by
        have := congr_arg ScheduledEvent.priority h_P_eq.symm
        dsimp [stageEvent] at this
        rw [h_P_pri'] at this
        exact this
      dsimp only [stagePri] at h_p
      split_ifs at h_p <;> omega
    obtain ⟨h_g_eq, h_c_eq, h_k_eq⟩ :=
      stageEvent_injective actTick groups g c k g' c' j h_g h_c h_g' h_c'
        (by omega) (by omega) h_P_eq
    rw [← h_g_eq, ← h_c_eq] at h_pref
    rw [h_k_eq] at h_e_eq
    have hP_tgt' : (stageEvent actTick groups g c j).targetTick =
        stageTarget actTick groups g₁ c₁ j := by
      convert hP_tgt using 1
      dsimp [P, stageEvent]
      rw [h_k_eq]
    -- the prefix extends to stage j + 1
    have h_j_gc : j < (chainAt groups g c).middleDelays.length := by
      have h_p : stagePri groups g c (j + 1) = (-3 : Int) := by
        have := congr_arg ScheduledEvent.priority h_e_eq
        dsimp [stageEvent] at this
        rw [h_pri] at this
        exact this.symm
      dsimp only [stagePri] at h_p
      split_ifs at h_p <;> omega
    have h_pref_succ : prefixDelays groups g c (j + 1) =
        prefixDelays groups g₁ c₁ (j + 1) :=
      prefixDelays_ext_of_targets_eq groups actTick g c g₁ c₁ j h_j_gc
        (by omega) h_pref hP_tgt' (by
          have := congr_arg ScheduledEvent.targetTick h_e_eq
          dsimp [stageEvent] at this
          exact this.symm.trans h_tgt)
    exact Or.inr ⟨g, c, h_g, h_c, h_e_eq, h_pri, h_tgt, h_pref_succ⟩

/-! ## The general burst-step theorem -/

/-- One active `gSimBody` tick preserves the middle-block invariant,
    whatever the fates of the two stage-`(j + 1)` reference events:
    each may survive the burst or be spawned by the burst or by the
    drain. Generalizes MiddleBlockOkTicks's `MiddleBlockOk_gSimBody_step_burst`,
    whose two survival premises are not provable in general. -/
theorem MiddleBlockOk_gSimBody_step_burst_general (groups : List GroupSpec)
    (actTick : Nat → Nat) (T : Nat)
    (obsAll : List (List Nat)) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat)
    (w : World) (i : Nat) (g₁ c₁ g₂ c₂ j : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_layout : NodeLayoutOk groups w)
    (h_j_ge : 1 ≤ j)
    (h_j₁ : j + 1 ≤ (chainAt groups g₁ c₁).middleDelays.length)
    (h_j₂ : j + 1 ≤ (chainAt groups g₂ c₂).middleDelays.length)
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
        (w.events.filter (fun e => e.targetTick == w.tick))
        g₁ c₁ g₂ c₂ j)
    (h_stage : StageMemAt groups actTick w w.tick)
    (h_sA_absent : stageEvent actTick groups g₁ c₁ (j + 1) ∉ w.events)
    (h_sD_absent : stageEvent actTick groups g₂ c₂ (j + 1) ∉ w.events)
    (h_active : groupOrd.filter (fun gi =>
        decide (gi < obsAll.length) && (actTick gi == w.tick)) ≠ [])
    (h_nd_burst :
      let w_log := w.logOutput s!"tick {w.tick}"
      let active := groupOrd.filter (fun gi =>
        decide (gi < obsAll.length) && (actTick gi == w.tick))
      (gSimBurst w.tick obsAll withinOrd pos w_log
        active.zipIdx).events.Nodup)
    (h_nd_post :
        (gSimBody actTick obsAll groupOrd withinOrd pos w i).events.Nodup) :
    MiddleBlockOk groups actTick T
      (gSimBody actTick obsAll groupOrd withinOrd pos w i).events
      g₁ c₁ g₂ c₂ (j + 1) := by
  set w_log := w.logOutput s!"tick {w.tick}"
  set active := groupOrd.filter (fun gi =>
    decide (gi < obsAll.length) && (actTick gi == w.tick))
  set W_B := gSimBurst w.tick obsAll withinOrd pos w_log active.zipIdx
  have h_ev_log : w_log.events = w.events := by simp [w_log]
  have h_tick_log : w_log.tick = w.tick := by simp [w_log]
  -- gSimBody reduces to W_B.stepUntilNextTick
  have h_body : gSimBody actTick obsAll groupOrd withinOrd pos w i =
      W_B.stepUntilNextTick := by
    dsimp only [gSimBody]
    simp only [World.logOutput_tick]
    dsimp [W_B, w_log, active]
    split_ifs with h_cond
    · exfalso
      have h_eq : active = [] := by simpa [active] using h_cond
      exact h_active h_eq
    · rfl
  rw [h_body] at h_nd_post
  rw [h_body]
  -- transfer hypotheses to w_log
  have h_layout_log : NodeLayoutOk groups w_log :=
    NodeLayoutOk_logOutput groups w _ h_layout
  have h_stage_log : StageMemAt groups actTick w_log w_log.tick := by
    intro ev h_ev; exact h_stage ev (by rwa [h_ev_log] at h_ev)
  have hA_mem_log : stageEvent actTick groups g₁ c₁ j ∈ w_log.events := by
    rwa [h_ev_log]
  have hD_mem_log : stageEvent actTick groups g₂ c₂ j ∈ w_log.events := by
    rwa [h_ev_log]
  have h_nodup_log :
      (w_log.events.filter (fun e => e.targetTick == w_log.tick)).Nodup := by
    rw [h_ev_log, h_tick_log]; exact h_nodup
  have hAD_log : evBefore
      (w_log.events.filter (fun e => e.targetTick == w_log.tick))
      (stageEvent actTick groups g₁ c₁ j)
      (stageEvent actTick groups g₂ c₂ j) := by
    rw [h_ev_log, h_tick_log]; exact hAD
  have h_mb_log : MiddleBlockOk groups actTick T
      (w_log.events.filter (fun e => e.targetTick == w_log.tick))
      g₁ c₁ g₂ c₂ j := by
    rw [h_ev_log, h_tick_log]; exact h_mb
  have h_sA_absent_log :
      stageEvent actTick groups g₁ c₁ (j + 1) ∉ w_log.events := by
    rwa [h_ev_log]
  have h_sD_absent_log :
      stageEvent actTick groups g₂ c₂ (j + 1) ∉ w_log.events := by
    rwa [h_ev_log]
  -- tick of W_B
  have h_tick_WB : W_B.tick = w.tick := by
    dsimp [W_B]; rw [gSimBurst_tick, h_tick_log]
  -- STEP 1: the burst advances the invariant to stage j + 1
  have h_mb_burst : MiddleBlockOk groups actTick T W_B.events
      g₁ c₁ g₂ c₂ (j + 1) :=
    MiddleBlockOk_step_gSimBurst groups actTick T w.tick obsAll withinOrd pos
      w_log active.zipIdx g₁ c₁ g₂ c₂ j
      h_g₁ h_c₁ h_g₂ h_c₂ h_layout_log h_j_ge h_j₁ h_j₂
      (by rw [h_tick_log]; exact h_due)
      h_tgt₂ hA_mem_log hD_mem_log h_nodup_log hAD_log h_mb_log
      h_stage_log h_sA_absent_log h_sD_absent_log h_nd_burst
  -- reference events at stage j + 1
  set sA₁ := stageEvent actTick groups g₁ c₁ (j + 1)
  set sD₁ := stageEvent actTick groups g₂ c₂ (j + 1)
  -- the stage-(j+1) events miss the tick of W_B
  have h_sA_nd : sA₁.targetTick ≠ W_B.tick := by
    rw [h_tick_WB, h_due]
    dsimp [sA₁, stageEvent]
    exact (stageTarget_lt_succ actTick groups g₁ c₁ j (by omega)).ne'
  have h_sD_nd : sD₁.targetTick ≠ W_B.tick := by
    rw [h_tick_WB, h_due, ← h_tgt₂]
    dsimp [sD₁, stageEvent]
    exact (stageTarget_lt_succ actTick groups g₂ c₂ j (by omega)).ne'
  -- STEP 2: the drain split — post queue = survivors ++ spawns
  set due := W_B.events.filter (fun ev => ev.targetTick == W_B.tick)
  set n := due.length
  set W_D := processNEvents W_B n
  have h_drain : W_D.events.filter
      (fun ev => ev.targetTick == W_B.tick) = [] :=
    drain_due_filter' W_B
  have h_no : ∀ ev ∈ W_D.events, ev.targetTick ≠ W_D.tick := by
    intro ev h_ev h_eq
    have h_mem : ev ∈ W_D.events.filter
        (fun e => e.targetTick == W_B.tick) := by
      rw [List.mem_filter]
      exact ⟨h_ev, by
        rw [processNEvents_tick] at h_eq
        rw [h_eq]
        simp⟩
    rw [h_drain] at h_mem
    cases h_mem
  have h_pop_none : W_D.popNextEvent = none :=
    World.popNextEvent_none_of_no_due W_D h_no
  have h_step_none : W_D.step = none := by
    simp only [World.step, h_pop_none]
  have h_sunt : W_B.stepUntilNextTick.events = W_D.events := by
    rw [← processNEvents_stepUntilNextTick_eq W_B n,
      stepUntilNextTick_of_step_none W_D h_step_none]
  have h_split : W_D.events =
      W_B.events.filter (fun ev => ev.targetTick ≠ W_B.tick) ++
        World.popSpawnAcc W_B n := by
    have h_f := (World.popSeqWorldFuel_filter_split W_B n).1
    rw [← processNEvents_eq_popSeqWorldFuel] at h_f
    have h_keep : W_D.events.filter
        (fun ev => ev.targetTick ≠ W_B.tick) = W_D.events := by
      apply filter_eq_self_of_forall''
      intro ev h_ev
      have h_ne : ev.targetTick ≠ W_B.tick := by
        have h := h_no ev h_ev
        rwa [processNEvents_tick] at h
      rw [decide_eq_true_eq]
      exact h_ne
    rw [← h_keep]
    exact h_f
  set survivors := W_B.events.filter (fun ev => ev.targetTick ≠ W_B.tick)
  set spawns := World.popSpawnAcc W_B n
  -- the interloper
  intro e h_b1 h_b2 h_pri h_tgt
  -- e misses the tick of W_B
  have h_e_nd : e.targetTick ≠ W_B.tick := by
    rw [h_tgt, h_tick_WB, h_due]
    exact (stageTarget_lt_succ actTick groups g₁ c₁ j (by omega)).ne'
  -- keep copies of the betweenness on the post-drain queue
  have h_b1_post : evBefore W_B.stepUntilNextTick.events sA₁ e := h_b1
  have h_b2_post : evBefore W_B.stepUntilNextTick.events e sD₁ := h_b2
  rw [h_sunt, h_split] at h_b1 h_b2
  -- nodup of survivors ++ spawns
  have h_nd_app : (survivors ++ spawns).Nodup := by
    rw [← h_split, ← h_sunt]; exact h_nd_post
  -- fate case split on membership in the burst result
  by_cases h_sA : sA₁ ∈ W_B.events
  · by_cases h_e : e ∈ W_B.events
    · -- sA₁ and e are in the burst result
      by_cases h_sD : sD₁ ∈ W_B.events
      · -- all three survive the burst: transport backwards, apply the
        -- burst invariant
        have h_ne_Ae : sA₁ ≠ e :=
          evBefore.ne_of_nodup h_nd_post h_b1_post
        have h_b1_WB : evBefore W_B.events sA₁ e :=
          evBefore_stepUNT_backward W_B sA₁ e h_nd_burst h_nd_post h_sA h_e
            h_sA_nd h_e_nd h_ne_Ae h_b1_post
        have h_ne_eD : e ≠ sD₁ :=
          evBefore.ne_of_nodup h_nd_post h_b2_post
        have h_b2_WB : evBefore W_B.events e sD₁ :=
          evBefore_stepUNT_backward W_B e sD₁ h_nd_burst h_nd_post h_e h_sD
            h_e_nd h_sD_nd h_ne_eD h_b2_post
        exact h_mb_burst e h_b1_WB h_b2_WB h_pri h_tgt
      · -- sA₁ and e survive the burst, sD₁ does not: e must be a burst
        -- spawn whose parent sits between A_j and D_j in the due filter
        have h_ne_Ae : sA₁ ≠ e :=
          evBefore.ne_of_nodup h_nd_post h_b1_post
        have h_b1_WB : evBefore W_B.events sA₁ e :=
          evBefore_stepUNT_backward W_B sA₁ e h_nd_burst h_nd_post h_sA h_e
            h_sA_nd h_e_nd h_ne_Ae h_b1_post
        have h_e_nd_log : e.targetTick ≠ w_log.tick := by
          rw [h_tick_log, ← h_tick_WB]
          exact h_e_nd
        have h_sA_nd_log : sA₁.targetTick ≠ w_log.tick := by
          rw [h_tick_log, ← h_tick_WB]
          exact h_sA_nd
        -- e was not queued pre-burst: survivors precede non-members
        have h_e_not_log : e ∉ w_log.events := by
          intro h_e_log
          have h_e_before_sA : evBefore W_B.events e sA₁ :=
            gSimBurst_survivor_before_nonmember' w.tick obsAll withinOrd
              pos w_log active.zipIdx e sA₁ h_e_log h_e_nd_log
              (by omega) h_sA_absent_log h_sA h_sA_nd_log
              (by
                dsimp [sA₁, stageEvent]
                rw [stagePri_middle groups g₁ c₁ (j + 1) (by omega) h_j₁]
                omega)
          exact evBefore.asymm h_nd_burst h_b1_WB h_e_before_sA
        -- filtered split of the burst result
        set pPri : ScheduledEvent → Bool :=
          fun ev => decide (ev.priority ≠ (0 : Int))
        set M := burstFuel' w.tick pos active.zipIdx
        have h_split_B : (W_B.events.filter
            (fun ev => ev.targetTick ≠ w_log.tick)).filter pPri =
            (w_log.events.filter
              (fun ev => ev.targetTick ≠ w_log.tick)).filter pPri ++
            (World.popSpawnAcc w_log M).filter pPri :=
          gSimBurst_filter_split' w.tick obsAll withinOrd pos w_log
            active.zipIdx
        have h_e_pri' : pPri e = true := by
          dsimp [pPri]
          rw [h_pri]
          decide
        have h_sA_pri' : pPri sA₁ = true := by
          dsimp [pPri, sA₁, stageEvent]
          rw [stagePri_middle groups g₁ c₁ (j + 1) (by omega) h_j₁]
          rfl
        have h_e_acc : e ∈ World.popSpawnAcc w_log M := by
          have h_e_lhs : e ∈ (W_B.events.filter
              (fun ev => ev.targetTick ≠ w_log.tick)).filter pPri := by
            rw [List.mem_filter]
            refine ⟨?_, h_e_pri'⟩
            rw [List.mem_filter]
            exact ⟨h_e, by rw [decide_eq_true_eq]; exact h_e_nd_log⟩
          rw [h_split_B, List.mem_append] at h_e_lhs
          rcases h_e_lhs with h_old | h_acc
          · exact absurd (List.mem_filter.mp (List.mem_filter.mp h_old).1).1
              h_e_not_log
          · exact (List.mem_filter.mp h_acc).1
        have h_sA_acc : sA₁ ∈ World.popSpawnAcc w_log M := by
          have h_sA_lhs : sA₁ ∈ (W_B.events.filter
              (fun ev => ev.targetTick ≠ w_log.tick)).filter pPri := by
            rw [List.mem_filter]
            refine ⟨?_, h_sA_pri'⟩
            rw [List.mem_filter]
            exact ⟨h_sA, by rw [decide_eq_true_eq]; exact h_sA_nd_log⟩
          rw [h_split_B, List.mem_append] at h_sA_lhs
          rcases h_sA_lhs with h_old | h_acc
          · exact absurd (List.mem_filter.mp (List.mem_filter.mp h_old).1).1
              h_sA_absent_log
          · exact (List.mem_filter.mp h_acc).1
        -- spawn classification from the due-restricted stage invariant
        have h_single_L := pops_single_spawn' groups actTick w_log M
          (fun ev h_ev _ => h_stage_log ev h_ev)
        have h_distinct_L := pops_distinct_spawn' groups actTick w_log M
          (fun ev h_ev _ => h_stage_log ev h_ev)
        have h_uniqueA_L := pops_unique_spawn' groups actTick w_log M
          (stageEvent actTick groups g₁ c₁ j) sA₁ g₁ c₁ j
          h_g₁ h_c₁ (by omega) rfl (by dsimp [sA₁])
          (fun ev h_ev _ => h_stage_log ev h_ev)
        have hA_pop_L : stageEvent actTick groups g₁ c₁ j ∈
            World.popSeqFuel w_log M := by
          obtain ⟨evA, h_evA, vA, sA', h_vA, h_layA, h_spA, h_sA'⟩ :=
            mem_popSpawnAcc_singleton_spawn groups w_log M sA₁ h_layout_log
              h_single_L h_sA_acc
          rwa [← h_uniqueA_L evA h_evA vA h_vA h_layA sA' h_spA h_sA'.symm]
        -- betweenness of sA₁ < e inside the burst accumulator
        have h_b_acc : evBefore (World.popSpawnAcc w_log M) sA₁ e := by
          have h_f1 : evBefore (W_B.events.filter
              (fun ev => ev.targetTick ≠ w_log.tick)) sA₁ e := by
            apply evBefore.filter (fun ev => ev.targetTick ≠ w_log.tick)
            · rw [decide_eq_true_eq]; exact h_sA_nd_log
            · rw [decide_eq_true_eq]; exact h_e_nd_log
            · exact h_b1_WB
          have h_f2 : evBefore ((W_B.events.filter
              (fun ev => ev.targetTick ≠ w_log.tick)).filter pPri) sA₁ e :=
            evBefore.filter pPri h_sA_pri' h_e_pri' h_f1
          rw [h_split_B] at h_f2
          have h_sA_not_old : sA₁ ∉ (w_log.events.filter
              (fun ev => ev.targetTick ≠ w_log.tick)).filter pPri :=
            fun h_mem => h_sA_absent_log
              (List.mem_filter.mp (List.mem_filter.mp h_mem).1).1
          have h_acc_f := evBefore_append_left_absent' h_sA_not_old h_f2
          exact evBefore.of_filter pPri h_acc_f
        have h_e_ne_sA : e ≠ sA₁ :=
          (evBefore.ne_of_nodup h_nd_burst h_b1_WB).symm
        -- trace e back to its burst parent
        obtain ⟨eP, h_eP_pop, h_AP, vP, h_vP_tick, h_vP_lay, h_eP_fire,
            h_eP_fresh⟩ :=
          popSpawnAcc_left_converse groups w_log M
            (stageEvent actTick groups g₁ c₁ j) sA₁ e h_layout_log
            h_nodup_log hA_pop_L
            (by dsimp [stageEvent]; rw [← h_due, ← h_tick_log])
            h_sA_absent_log
            (by
              dsimp [sA₁, stageEvent]
              have := stageTarget_lt_succ actTick groups g₁ c₁ j (by omega)
              rw [← h_due, ← h_tick_log] at this
              exact this)
            (by
              intro v h_v h_lay
              simpa [sA₁, stageEvent] using
                stage_spawn groups actTick v g₁ c₁ j h_g₁ h_c₁ (by omega)
                  (h_v.trans (h_tick_log.trans h_due)) h_lay)
            h_single_L h_uniqueA_L h_distinct_L h_e_not_log h_e_ne_sA
            h_b_acc
        -- decode the parent as a stage event
        have h_eP_log : eP ∈ w_log.events :=
          World.mem_popSeqFuel_mem_events w_log M eP h_eP_pop
        obtain ⟨gi, ci, k, h_gi, h_ci, _, h_eP_eq, _, _⟩ :=
          h_stage_log eP h_eP_log
        have h_eP_due : eP.targetTick = w_log.tick :=
          World.mem_popSeqFuel_due w_log M eP h_eP_pop
        have h_k_mid : k ≤ (chainAt groups gi ci).middleDelays.length := by
          by_contra h_last
          have h_last' :
              k = (chainAt groups gi ci).middleDelays.length + 1 := by omega
          have h_nil : (vP.onScheduledTick eP.nodeId).events =
              vP.events := by
            rw [h_eP_eq, h_last']
            exact lastStage_spawn_nil groups actTick vP gi ci h_gi h_ci
              h_vP_lay
          rw [h_nil] at h_eP_fire
          exact h_eP_fresh h_eP_fire
        have h_tick_P : vP.tick = stageTarget actTick groups gi ci k := by
          rw [h_vP_tick, ← h_eP_due]
          have := congr_arg ScheduledEvent.targetTick h_eP_eq
          dsimp [stageEvent] at this
          exact this
        have h_fire_P : (vP.onScheduledTick eP.nodeId).events =
            vP.events ++ [stageEvent actTick groups gi ci (k + 1)] := by
          rw [h_eP_eq]
          exact stage_spawn groups actTick vP gi ci k h_gi h_ci h_k_mid
            h_tick_P h_vP_lay
        have h_e_eq : e = stageEvent actTick groups gi ci (k + 1) := by
          rw [h_fire_P] at h_eP_fire
          rcases List.mem_append.mp h_eP_fire with h_mem | h_mem
          · exact absurd h_mem h_eP_fresh
          · simpa using h_mem
        -- the parent was popped by the burst, hence it left the burst
        have h_eP_not_WB : eP ∉ W_B.events :=
          mem_popSeqFuel_not_mem_gSimBurst' w.tick obsAll withinOrd pos
            w_log active.zipIdx h_nodup_log eP h_eP_pop
        -- D_j survives the burst: otherwise sD₁ would be queued
        have hD_WB : stageEvent actTick groups g₂ c₂ j ∈ W_B.events := by
          by_contra hD_gone
          have h_sD_B : sD₁ ∈ W_B.events :=
            gSimBurst_spawn_mem groups w.tick obsAll withinOrd pos w_log
              active.zipIdx (stageEvent actTick groups g₂ c₂ j) sD₁
              h_layout_log hD_mem_log
              (by dsimp [stageEvent]; rw [h_tgt₂, ← h_due, ← h_tick_log])
              hD_gone
              (by
                intro h
                apply h_sD_nd
                rw [h, h_tick_log]
                exact h_tick_WB.symm)
              (by
                intro v h_v h_lay
                simpa [sD₁, stageEvent] using
                  stage_spawn groups actTick v g₂ c₂ j h_g₂ h_c₂ (by omega)
                    (h_v.trans (h_tick_log.trans (h_due.trans h_tgt₂.symm)))
                    h_lay)
          exact h_sD h_sD_B
        -- the parent cannot be stage 0: a priority-0 pop is blocked while
        -- the priority-(-3) event D_j survives
        have h_k_ne0 : k ≠ 0 := by
          intro h_k0
          have h_pri0 : eP.priority = (0 : Int) := by
            have := congr_arg ScheduledEvent.priority h_eP_eq
            dsimp [stageEvent] at this
            rw [this, h_k0]
            dsimp [stagePri]
          have h_contra := gSimBurst_not_pop_larger_pri w.tick obsAll
            withinOrd pos w_log active.zipIdx
            (stageEvent actTick groups g₂ c₂ j) eP
            (by dsimp [stageEvent]; rw [h_tgt₂, ← h_due, ← h_tick_log])
            h_eP_due
            (by
              dsimp [stageEvent]
              rw [stagePri_middle groups g₂ c₂ j h_j_ge (by omega), h_pri0]
              omega)
            h_eP_log hD_WB
          exact h_eP_not_WB h_contra
        have h_k_ge : 1 ≤ k := by omega
        have h_pri_P : eP.priority = (-3 : Int) := by
          have := congr_arg ScheduledEvent.priority h_eP_eq
          dsimp [stageEvent] at this
          rw [this]
          exact stagePri_middle groups gi ci k h_k_ge h_k_mid
        have hA_pri_log : (stageEvent actTick groups g₁ c₁ j).priority =
            (-3 : Int) := by
          dsimp [stageEvent]
          exact stagePri_middle groups g₁ c₁ j h_j_ge (by omega)
        have hD_pri_log : (stageEvent actTick groups g₂ c₂ j).priority =
            (-3 : Int) := by
          dsimp [stageEvent]
          exact stagePri_middle groups g₂ c₂ j h_j_ge (by omega)
        -- pop order at equal priority = due-filter order
        have h_log_AP : evBefore
            (w_log.events.filter (fun ev => ev.targetTick == w_log.tick))
            (stageEvent actTick groups g₁ c₁ j) eP :=
          due_evBefore_of_popSeq_evBefore w_log M _ _ hA_pop_L h_eP_pop
            (by dsimp [stageEvent]; rw [← h_due, ← h_tick_log]) h_eP_due
            (by rw [hA_pri_log, h_pri_P]) h_nodup_log h_AP
        have h_log_PD : evBefore
            (w_log.events.filter (fun ev => ev.targetTick == w_log.tick))
            eP (stageEvent actTick groups g₂ c₂ j) := by
          have hP_log : eP ∈ w_log.events.filter
              (fun ev => ev.targetTick == w_log.tick) := by
            rw [List.mem_filter]
            exact ⟨h_eP_log, by rw [h_eP_due]; simp⟩
          have hD_log : stageEvent actTick groups g₂ c₂ j ∈
              w_log.events.filter
                (fun ev => ev.targetTick == w_log.tick) := by
            rw [List.mem_filter]
            refine ⟨hD_mem_log, ?_⟩
            dsimp [stageEvent]
            rw [h_tgt₂, ← h_due, ← h_tick_log]
            simp
          have h_PD_ne : eP ≠ stageEvent actTick groups g₂ c₂ j := by
            intro h_eq
            exact h_eP_not_WB (h_eq.symm ▸ hD_WB)
          obtain h_fwd | h_rev := evBefore.total_of_nodup h_nodup_log hP_log
            hD_log h_PD_ne
          · exact h_fwd
          · exfalso
            have h_P_WB : eP ∈ W_B.events :=
              gSimBurst_not_pop_later_samePri w.tick obsAll withinOrd pos
                w_log active.zipIdx (stageEvent actTick groups g₂ c₂ j) eP
                (by dsimp [stageEvent]; rw [h_tgt₂, ← h_due, ← h_tick_log])
                h_eP_due
                (by rw [hD_pri_log, h_pri_P])
                h_nodup_log h_rev hD_mem_log hD_WB
            exact h_eP_not_WB h_P_WB
        -- the parent targets the stage-j tick
        have hP_tgt : (stageEvent actTick groups gi ci k).targetTick =
            stageTarget actTick groups g₁ c₁ j := by
          have := congr_arg ScheduledEvent.targetTick h_eP_eq
          dsimp [stageEvent] at this ⊢
          rw [← this, h_eP_due, h_tick_log, h_due]
        -- apply the tail classification lemma
        rw [h_eP_eq] at h_log_AP h_log_PD
        exact middleBlock_succ_of_parent_between' groups actTick T
          g₁ c₁ g₂ c₂ j
          (w_log.events.filter (fun ev => ev.targetTick == w_log.tick))
          e gi ci k h_gi h_ci h_k_ge h_k_mid h_e_eq hP_tgt h_log_AP
          h_log_PD h_mb_log h_pri h_tgt h_j₁
    · -- sA₁ survives the burst, e does not
      by_cases h_sD : sD₁ ∈ W_B.events
      · -- sD₁ is a survivor and e a spawn: sD₁ precedes e, but h_b2
        -- says e precedes sD₁
        have h_absurd : False := by
          have h_sD_surv : sD₁ ∈ survivors := by
            dsimp [survivors]
            rw [List.mem_filter]
            exact ⟨h_sD, by simp [h_sD_nd]⟩
          have h_e_sp : e ∈ spawns := by
            have h_e_mem : e ∈ survivors ++ spawns :=
              evBefore.mem_left h_b2
            rw [List.mem_append] at h_e_mem
            rcases h_e_mem with h_e_s | h_e_sp
            · exact absurd (List.mem_filter.mp h_e_s).1 h_e
            · exact h_e_sp
          exact evBefore.asymm h_nd_app h_b2
            (evBefore.of_mem_append h_sD_surv h_e_sp)
        exact h_absurd.elim
      · -- sA₁ survives the burst; e and sD₁ are drain spawns. Restrict
        -- the right betweenness to the spawn accumulator.
        have h_surv_e : e ∉ survivors :=
          fun h_mem => h_e (List.mem_filter.mp h_mem).1
        have h_b_right : evBefore spawns e sD₁ := by
          rcases evBefore_append_split_right' h_b2 with h_e_s | h_b
          · exact absurd h_e_s h_surv_e
          · exact h_b
        -- the drain pops of W_B decode via the pre-burst invariant
        have h_layout_WB : NodeLayoutOk groups W_B :=
          NodeLayoutOk_gSimBurst groups w.tick obsAll withinOrd pos w_log
            active.zipIdx h_layout_log
        have h_stage_due_B : ∀ ev ∈ W_B.events,
            ev.targetTick = W_B.tick →
            ∃ gi ci j₀, gi < groups.length ∧
              ci < (groupAt groups gi).length ∧
              j₀ ≤ (chainAt groups gi ci).middleDelays.length + 1 ∧
              ev = stageEvent actTick groups gi ci j₀ ∧
              (if j₀ = 0 then actTick gi else
                stageTarget actTick groups gi ci (j₀ - 1)) < W_B.tick + 1 ∧
              W_B.tick ≤ stageTarget actTick groups gi ci j₀ := by
          intro ev h_ev h_due
          obtain ⟨gi, ci, j₀, hgi, hci, hj₀, heq, hprev, htgt⟩ :=
            h_stage_log ev
              (mem_gSimBurst_due_back w.tick obsAll withinOrd pos w_log
                active.zipIdx ev h_ev (by
                rwa [h_tick_WB, ← h_tick_log] at h_due))
          refine ⟨gi, ci, j₀, hgi, hci, hj₀, heq, ?_, ?_⟩
          · rw [h_tick_WB, ← h_tick_log]; exact hprev
          · rw [h_tick_WB, ← h_tick_log]; exact htgt
        have h_single_B :=
          pops_single_spawn' groups actTick W_B n h_stage_due_B
        have h_uniqueD_B :=
          pops_unique_spawn' groups actTick W_B n
            (stageEvent actTick groups g₂ c₂ j) sD₁ g₂ c₂ j
            h_g₂ h_c₂ (by omega) rfl (by dsimp [sD₁])
            h_stage_due_B
        have h_distinct_B :=
          pops_distinct_spawn' groups actTick W_B n h_stage_due_B
        -- D_j is the drain popper of sD₁
        have hD_pop : stageEvent actTick groups g₂ c₂ j ∈
            World.popSeqFuel W_B n := by
          have h_sD_acc : sD₁ ∈ spawns := evBefore.mem_right h_b_right
          obtain ⟨evD, h_evD, vD, sD', h_vD, h_layD, h_spD, h_sD'⟩ :=
            mem_popSpawnAcc_singleton_spawn groups W_B n sD₁ h_layout_WB
              h_single_B h_sD_acc
          have h_evD_eq : evD = stageEvent actTick groups g₂ c₂ j :=
            h_uniqueD_B evD h_evD vD h_vD h_layD sD' h_spD h_sD'.symm
          rwa [← h_evD_eq]
        have hD_due : (stageEvent actTick groups g₂ c₂ j).targetTick =
            W_B.tick := by
          dsimp [stageEvent]; rw [h_tgt₂, ← h_due, h_tick_WB]
        have hD_pri : (stageEvent actTick groups g₂ c₂ j).priority =
            (-3 : Int) := by
          dsimp [stageEvent]
          exact stagePri_middle groups g₂ c₂ j h_j_ge (by omega)
        have h_nd_due_B : (W_B.events.filter
            (fun ev => ev.targetTick == W_B.tick)).Nodup :=
          List.Nodup.filter (fun ev => ev.targetTick == W_B.tick) h_nd_burst
        have h_acc_nd : spawns.Nodup :=
          popSpawnAcc_nodup groups W_B n h_layout_WB h_nd_due_B h_single_B
            h_distinct_B
        have h_e_ne_sD : e ≠ sD₁ := by
          intro h_eq
          rw [h_eq] at h_b_right
          obtain ⟨l₁, l₂, l₃, h_two⟩ := evBefore_self_two_split' h_b_right
          exact nodup_cons_append_not_mem (h_two ▸ h_acc_nd)
            (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
        have h_spawnD_B : ∀ (v : World), v.tick = W_B.tick →
            NodeLayoutOk groups v →
            (v.onScheduledTick
                (stageEvent actTick groups g₂ c₂ j).nodeId).events =
              v.events ++ [sD₁] := by
          intro v h_v h_lay
          simpa [sD₁, stageEvent] using
            stage_spawn groups actTick v g₂ c₂ j h_g₂ h_c₂ (by omega)
              (h_v.trans (h_tick_WB.trans (h_due.trans h_tgt₂.symm))) h_lay
        have h_sD_gt : sD₁.targetTick > W_B.tick := by
          dsimp [sD₁, stageEvent]
          have := stageTarget_lt_succ actTick groups g₂ c₂ j (by omega)
          rw [h_tgt₂, ← h_due, ← h_tick_WB] at this
          exact this
        -- trace e back to its drain parent
        obtain ⟨eR, h_eR_pop, h_eRD, vR, h_vR_tick, h_vR_lay, h_eR_fire,
            h_eR_fresh⟩ :=
          popSpawnAcc_right_converse groups W_B n
            (stageEvent actTick groups g₂ c₂ j) sD₁ e h_layout_WB
            h_nd_due_B hD_pop hD_due h_sD h_sD_gt h_spawnD_B h_single_B
            h_uniqueD_B h_e h_e_ne_sD h_b_right
        -- decode the parent as a stage event
        have h_eR_WB : eR ∈ W_B.events :=
          World.mem_popSeqFuel_mem_events W_B n eR h_eR_pop
        have h_eR_due : eR.targetTick = W_B.tick :=
          World.mem_popSeqFuel_due W_B n eR h_eR_pop
        obtain ⟨gi, ci, k, h_gi, h_ci, _, h_eR_eq, _, _⟩ :=
          h_stage_due_B eR h_eR_WB h_eR_due
        have h_k_mid : k ≤ (chainAt groups gi ci).middleDelays.length := by
          by_contra h_last
          have h_last' :
              k = (chainAt groups gi ci).middleDelays.length + 1 := by omega
          have h_nil : (vR.onScheduledTick eR.nodeId).events =
              vR.events := by
            rw [h_eR_eq, h_last']
            exact lastStage_spawn_nil groups actTick vR gi ci h_gi h_ci
              h_vR_lay
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
          exact stage_spawn groups actTick vR gi ci k h_gi h_ci h_k_mid
            h_tick_R h_vR_lay
        have h_e_eq : e = stageEvent actTick groups gi ci (k + 1) := by
          rw [h_fire_R] at h_eR_fire
          rcases List.mem_append.mp h_eR_fire with h_mem | h_mem
          · exact absurd h_mem h_eR_fresh
          · simpa using h_mem
        -- the parent carries priority -3: it pops before the priority-(-3)
        -- event D_j, and it is a stage event
        have h_k_ge : 1 ≤ k := by
          have h_le : stagePri groups gi ci k ≤ (-3 : Int) := by
            have h_pri_le : eR.priority ≤ (-3 : Int) := by
              have := popSeqFuel_priority_mono W_B n eR
                (stageEvent actTick groups g₂ c₂ j) h_eRD
              rwa [hD_pri] at this
            have h_congr : stagePri groups gi ci k = eR.priority := by
              have := congr_arg ScheduledEvent.priority h_eR_eq.symm
              dsimp [stageEvent] at this
              exact this
            rwa [h_congr]
          dsimp only [stagePri] at h_le
          split_ifs at h_le
          all_goals omega
        have h_pri_eR : eR.priority = (-3 : Int) := by
          have := congr_arg ScheduledEvent.priority h_eR_eq.symm
          dsimp [stageEvent] at this
          rw [← this]
          exact stagePri_middle groups gi ci k h_k_ge h_k_mid
        -- the parent pops before D_j in the due filter of W_B
        have h_due_eRD : evBefore
            (W_B.events.filter (fun ev => ev.targetTick == W_B.tick))
            eR (stageEvent actTick groups g₂ c₂ j) :=
          due_evBefore_of_popSeq_evBefore W_B n _ _ h_eR_pop hD_pop h_eR_due
            hD_due (by rw [h_pri_eR, hD_pri]) h_nd_due_B h_eRD
        -- lift the due-filter order to the pre-burst due filter
        have h_lift : ∀ {X Y : ScheduledEvent},
            evBefore (W_B.events.filter
                (fun ev => ev.targetTick == W_B.tick)) X Y →
            X ∈ w_log.events.filter
                (fun ev => ev.targetTick == w_log.tick) →
            Y ∈ w_log.events.filter
                (fun ev => ev.targetTick == w_log.tick) →
            evBefore (w_log.events.filter
                (fun ev => ev.targetTick == w_log.tick)) X Y := by
          intro X Y h_b hX hY
          by_cases h_fwd : evBefore
              (w_log.events.filter (fun ev => ev.targetTick == w_log.tick))
              X Y
          · exact h_fwd
          · have h_ne : X ≠ Y := evBefore.ne_of_nodup h_nd_due_B h_b
            obtain hXY | hYX := evBefore.total_of_nodup h_nodup_log hX hY
              h_ne
            · exact absurd hXY h_fwd
            · have hX_WB : X ∈ W_B.events :=
                (List.mem_filter.mp (evBefore.mem_left h_b)).1
              have hY_WB : Y ∈ W_B.events :=
                (List.mem_filter.mp (evBefore.mem_right h_b)).1
              have hX_due : X.targetTick = w_log.tick := by
                simpa [Nat.beq_eq] using (List.mem_filter.mp hX).2
              have hY_due : Y.targetTick = w_log.tick := by
                simpa [Nat.beq_eq] using (List.mem_filter.mp hY).2
              have hYX_B : evBefore (W_B.events.filter
                  (fun ev => ev.targetTick == W_B.tick)) Y X :=
                evBefore_due_gSimBurst_of_mem w.tick obsAll withinOrd pos
                  w_log active.zipIdx Y X (by rw [h_tick_log]; exact hY_due)
                  (by rw [h_tick_log]; exact hX_due) h_nodup_log hYX
                  hY_WB hX_WB
              exact (evBefore.asymm h_nd_due_B h_b hYX_B).elim
        have h_eR_log : eR ∈ w_log.events.filter
            (fun ev => ev.targetTick == w_log.tick) := by
          rw [List.mem_filter]
          refine ⟨mem_gSimBurst_due_back w.tick obsAll withinOrd pos w_log
            active.zipIdx eR h_eR_WB (by
            rwa [h_tick_WB, ← h_tick_log] at h_eR_due), by
            rw [h_eR_due, h_tick_WB, h_tick_log]; simp⟩
        have h_log_eRD : evBefore
            (w_log.events.filter (fun ev => ev.targetTick == w_log.tick))
            eR (stageEvent actTick groups g₂ c₂ j) :=
          h_lift h_due_eRD h_eR_log (by
            rw [List.mem_filter]
            refine ⟨hD_mem_log, by
              dsimp [stageEvent]; rw [h_tgt₂, ← h_due, h_tick_log]; simp⟩)
        -- A_j precedes the parent in the pre-burst due filter
        have h_log_AeR : evBefore
            (w_log.events.filter (fun ev => ev.targetTick == w_log.tick))
            (stageEvent actTick groups g₁ c₁ j) eR := by
          have hA_log : stageEvent actTick groups g₁ c₁ j ∈
              w_log.events.filter
                (fun ev => ev.targetTick == w_log.tick) := by
            rw [List.mem_filter]
            refine ⟨hA_mem_log, by
              dsimp [stageEvent]; rw [← h_due, h_tick_log]; simp⟩
          have h_AR_ne : stageEvent actTick groups g₁ c₁ j ≠ eR := by
            intro h_eq
            obtain ⟨h_g_eq, h_c_eq, h_k_eq⟩ :=
              stageEvent_injective actTick groups gi ci k g₁ c₁ j h_gi h_ci
                h_g₁ h_c₁ (by omega) (by omega)
                (h_eR_eq.symm.trans h_eq.symm)
            rw [h_g_eq, h_c_eq, h_k_eq] at h_e_eq
            have h_sA_e : e ∈ W_B.events := h_e_eq.symm ▸ h_sA
            exact h_e h_sA_e
          obtain h_fwd | h_rev := evBefore.total_of_nodup h_nodup_log hA_log
            h_eR_log h_AR_ne
          · exact h_fwd
          · -- parent before A_j: since the parent stays queued through the
            -- burst, so does A_j; then the drain spawns sA₁ a second time
            exfalso
            have h_eR_log_mem : eR ∈ w_log.events :=
              mem_gSimBurst_due_back w.tick obsAll withinOrd pos w_log
                active.zipIdx eR h_eR_WB
                (h_eR_due.trans (h_tick_WB.trans h_tick_log.symm))
            have hA_WB : stageEvent actTick groups g₁ c₁ j ∈ W_B.events :=
              gSimBurst_not_pop_later_samePri w.tick obsAll withinOrd pos
                w_log active.zipIdx eR (stageEvent actTick groups g₁ c₁ j)
                (h_eR_due.trans (h_tick_WB.trans h_tick_log.symm))
                (by dsimp [stageEvent]; rw [← h_due, h_tick_log])
                (by
                  rw [h_pri_eR]
                  dsimp [stageEvent]
                  rw [stagePri_middle groups g₁ c₁ j h_j_ge (by omega)])
                h_nodup_log h_rev h_eR_log_mem h_eR_WB
            have hA_due_B : (stageEvent actTick groups g₁ c₁ j).targetTick =
                W_B.tick := by
              dsimp [stageEvent]; rw [← h_due, h_tick_WB]
            have h_sA_sp : sA₁ ∈ spawns :=
              drain_spawn_mem' groups W_B
                (stageEvent actTick groups g₁ c₁ j) sA₁ hA_WB hA_due_B
                (by
                  intro v h_v h_lay
                  simpa [sA₁, stageEvent] using
                    stage_spawn groups actTick v g₁ c₁ j h_g₁ h_c₁
                      (by omega) (h_v.trans (h_tick_WB.trans h_due)) h_lay)
                h_layout_WB
            have h_sA_surv : sA₁ ∈ survivors := by
              dsimp [survivors]
              rw [List.mem_filter]
              exact ⟨h_sA, by simp [h_sA_nd]⟩
            have h_nd_fail : (survivors ++ spawns).Nodup → False := by
              intro h_nd
              obtain ⟨p, q, h_pq⟩ := mem_split_append survivors sA₁
                h_sA_surv
              have h_split' : survivors ++ spawns =
                  p ++ sA₁ :: (q ++ spawns) := by
                rw [h_pq, List.append_assoc, List.cons_append]
              exact nodup_cons_append_not_mem (h_split' ▸ h_nd)
                (List.mem_append.mpr (Or.inr h_sA_sp))
            exact h_nd_fail h_nd_app
        -- the stage-j invariant classifies the parent
        have hP_tgt : (stageEvent actTick groups gi ci k).targetTick =
            stageTarget actTick groups g₁ c₁ j := by
          have h_ttick := congr_arg ScheduledEvent.targetTick h_eR_eq.symm
          dsimp [stageEvent] at h_ttick ⊢
          rw [h_ttick, h_eR_due, h_tick_WB, h_due]
        rw [h_eR_eq] at h_log_AeR h_log_eRD
        exact middleBlock_succ_of_parent_between' groups actTick T
          g₁ c₁ g₂ c₂ j
          (w_log.events.filter (fun ev => ev.targetTick == w_log.tick))
          e gi ci k h_gi h_ci h_k_ge h_k_mid h_e_eq hP_tgt h_log_AeR
          h_log_eRD h_mb_log h_pri h_tgt h_j₁
  · by_cases h_e : e ∈ W_B.events
    · -- e is a survivor and sA₁ a spawn: e precedes sA₁, but h_b1
      -- says sA₁ precedes e
      have h_absurd : False := by
        have h_e_surv : e ∈ survivors := by
          dsimp [survivors]
          rw [List.mem_filter]
          exact ⟨h_e, by simp [h_e_nd]⟩
        have h_sA_sp : sA₁ ∈ spawns := by
          have h_sA_mem : sA₁ ∈ survivors ++ spawns :=
            evBefore.mem_left h_b1
          rw [List.mem_append] at h_sA_mem
          rcases h_sA_mem with h_sA_s | h_sA_sp
          · exact absurd (List.mem_filter.mp h_sA_s).1 h_sA
          · exact h_sA_sp
        exact evBefore.asymm h_nd_app h_b1
          (evBefore.of_mem_append h_e_surv h_sA_sp)
      exact h_absurd.elim
    · -- neither sA₁ nor e survives the burst
      by_cases h_sD : sD₁ ∈ W_B.events
      · -- sD₁ is a survivor and e a spawn: contradiction with h_b2
        have h_absurd : False := by
          have h_sD_surv : sD₁ ∈ survivors := by
            dsimp [survivors]
            rw [List.mem_filter]
            exact ⟨h_sD, by simp [h_sD_nd]⟩
          have h_e_sp : e ∈ spawns := by
            have h_e_mem : e ∈ survivors ++ spawns :=
              evBefore.mem_left h_b2
            rw [List.mem_append] at h_e_mem
            rcases h_e_mem with h_e_s | h_e_sp
            · exact absurd (List.mem_filter.mp h_e_s).1 h_e
            · exact h_e_sp
          exact evBefore.asymm h_nd_app h_b2
            (evBefore.of_mem_append h_sD_surv h_e_sp)
        exact h_absurd.elim
      · -- none of the three survives the burst: all are drain spawns.
        -- Restrict the betweenness to the spawn accumulator.
        have h_surv_sA : sA₁ ∉ survivors :=
          fun h_mem => h_sA (List.mem_filter.mp h_mem).1
        have h_b_left : evBefore spawns sA₁ e :=
          evBefore_append_left_absent' h_surv_sA h_b1
        have h_surv_e : e ∉ survivors :=
          fun h_mem => h_e (List.mem_filter.mp h_mem).1
        have h_b_right : evBefore spawns e sD₁ := by
          rcases evBefore_append_split_right' h_b2 with h_e_s | h_b
          · exact absurd h_e_s h_surv_e
          · exact h_b
        -- the drain pops of W_B decode via the pre-burst invariant
        have h_layout_WB : NodeLayoutOk groups W_B :=
          NodeLayoutOk_gSimBurst groups w.tick obsAll withinOrd pos w_log
            active.zipIdx h_layout_log
        have h_stage_due_B : ∀ ev ∈ W_B.events,
            ev.targetTick = W_B.tick →
            ∃ gi ci j₀, gi < groups.length ∧
              ci < (groupAt groups gi).length ∧
              j₀ ≤ (chainAt groups gi ci).middleDelays.length + 1 ∧
              ev = stageEvent actTick groups gi ci j₀ ∧
              (if j₀ = 0 then actTick gi else
                stageTarget actTick groups gi ci (j₀ - 1)) < W_B.tick + 1 ∧
              W_B.tick ≤ stageTarget actTick groups gi ci j₀ := by
          intro ev h_ev h_due
          obtain ⟨gi, ci, j₀, hgi, hci, hj₀, heq, hprev, htgt⟩ :=
            h_stage_log ev
              (mem_gSimBurst_due_back w.tick obsAll withinOrd pos w_log
                active.zipIdx ev h_ev (by
                rwa [h_tick_WB, ← h_tick_log] at h_due))
          refine ⟨gi, ci, j₀, hgi, hci, hj₀, heq, ?_, ?_⟩
          · rw [h_tick_WB, ← h_tick_log]; exact hprev
          · rw [h_tick_WB, ← h_tick_log]; exact htgt
        have h_single_B :=
          pops_single_spawn' groups actTick W_B n h_stage_due_B
        have h_uniqueA_B :=
          pops_unique_spawn' groups actTick W_B n
            (stageEvent actTick groups g₁ c₁ j) sA₁ g₁ c₁ j
            h_g₁ h_c₁ (by omega) rfl (by dsimp [sA₁])
            h_stage_due_B
        have h_uniqueD_B :=
          pops_unique_spawn' groups actTick W_B n
            (stageEvent actTick groups g₂ c₂ j) sD₁ g₂ c₂ j
            h_g₂ h_c₂ (by omega) rfl (by dsimp [sD₁])
            h_stage_due_B
        have h_distinct_B :=
          pops_distinct_spawn' groups actTick W_B n h_stage_due_B
        -- the reference pops sit in the drain pop sequence
        have hA_pop : stageEvent actTick groups g₁ c₁ j ∈
            World.popSeqFuel W_B n := by
          have h_sA_acc : sA₁ ∈ spawns := evBefore.mem_left h_b_left
          obtain ⟨evA, h_evA, vA, sA', h_vA, h_layA, h_spA, h_sA'⟩ :=
            mem_popSpawnAcc_singleton_spawn groups W_B n sA₁ h_layout_WB
              h_single_B h_sA_acc
          have h_evA_eq : evA = stageEvent actTick groups g₁ c₁ j :=
            h_uniqueA_B evA h_evA vA h_vA h_layA sA' h_spA h_sA'.symm
          rwa [← h_evA_eq]
        have hD_pop : stageEvent actTick groups g₂ c₂ j ∈
            World.popSeqFuel W_B n := by
          have h_sD_acc : sD₁ ∈ spawns := evBefore.mem_right h_b_right
          obtain ⟨evD, h_evD, vD, sD', h_vD, h_layD, h_spD, h_sD'⟩ :=
            mem_popSpawnAcc_singleton_spawn groups W_B n sD₁ h_layout_WB
              h_single_B h_sD_acc
          have h_evD_eq : evD = stageEvent actTick groups g₂ c₂ j :=
            h_uniqueD_B evD h_evD vD h_vD h_layD sD' h_spD h_sD'.symm
          rwa [← h_evD_eq]
        have hA_due : (stageEvent actTick groups g₁ c₁ j).targetTick =
            W_B.tick := by
          dsimp [stageEvent]; rw [← h_due, h_tick_WB]
        have hD_due : (stageEvent actTick groups g₂ c₂ j).targetTick =
            W_B.tick := by
          dsimp [stageEvent]; rw [h_tgt₂, ← h_due, h_tick_WB]
        have hA_pri : (stageEvent actTick groups g₁ c₁ j).priority =
            (-3 : Int) := by
          dsimp [stageEvent]
          exact stagePri_middle groups g₁ c₁ j h_j_ge (by omega)
        have hD_pri : (stageEvent actTick groups g₂ c₂ j).priority =
            (-3 : Int) := by
          dsimp [stageEvent]
          exact stagePri_middle groups g₂ c₂ j h_j_ge (by omega)
        -- the accumulator is duplicate-free; e differs from sA₁ and sD₁
        have h_nd_due_B : (W_B.events.filter
            (fun ev => ev.targetTick == W_B.tick)).Nodup :=
          List.Nodup.filter (fun ev => ev.targetTick == W_B.tick) h_nd_burst
        have h_acc_nd : spawns.Nodup :=
          popSpawnAcc_nodup groups W_B n h_layout_WB h_nd_due_B h_single_B
            h_distinct_B
        have h_e_ne_sA : e ≠ sA₁ := by
          intro h_eq
          rw [h_eq] at h_b_left
          obtain ⟨l₁, l₂, l₃, h_two⟩ := evBefore_self_two_split' h_b_left
          exact nodup_cons_append_not_mem (h_two ▸ h_acc_nd)
            (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
        have h_e_ne_sD : e ≠ sD₁ := by
          intro h_eq
          rw [h_eq] at h_b_right
          obtain ⟨l₁, l₂, l₃, h_two⟩ := evBefore_self_two_split' h_b_right
          exact nodup_cons_append_not_mem (h_two ▸ h_acc_nd)
            (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
        -- the spawn facts of the two reference events
        have h_spawnA_B : ∀ (v : World), v.tick = W_B.tick →
            NodeLayoutOk groups v →
            (v.onScheduledTick
                (stageEvent actTick groups g₁ c₁ j).nodeId).events =
              v.events ++ [sA₁] := by
          intro v h_v h_lay
          simpa [sA₁, stageEvent] using
            stage_spawn groups actTick v g₁ c₁ j h_g₁ h_c₁ (by omega)
              (h_v.trans (h_tick_WB.trans h_due)) h_lay
        have h_spawnD_B : ∀ (v : World), v.tick = W_B.tick →
            NodeLayoutOk groups v →
            (v.onScheduledTick
                (stageEvent actTick groups g₂ c₂ j).nodeId).events =
              v.events ++ [sD₁] := by
          intro v h_v h_lay
          simpa [sD₁, stageEvent] using
            stage_spawn groups actTick v g₂ c₂ j h_g₂ h_c₂ (by omega)
              (h_v.trans (h_tick_WB.trans (h_due.trans h_tgt₂.symm))) h_lay
        have h_sA_gt : sA₁.targetTick > W_B.tick := by
          dsimp [sA₁, stageEvent]
          have := stageTarget_lt_succ actTick groups g₁ c₁ j (by omega)
          rw [← h_due, ← h_tick_WB] at this
          exact this
        have h_sD_gt : sD₁.targetTick > W_B.tick := by
          dsimp [sD₁, stageEvent]
          have := stageTarget_lt_succ actTick groups g₂ c₂ j (by omega)
          rw [h_tgt₂, ← h_due, ← h_tick_WB] at this
          exact this
        -- trace e back to its parent pops on both sides
        obtain ⟨eL, h_eL_pop, h_AeL, vL, h_vL_tick, h_vL_lay, h_eL_fire,
            h_eL_fresh⟩ :=
          popSpawnAcc_left_converse groups W_B n
            (stageEvent actTick groups g₁ c₁ j) sA₁ e h_layout_WB
            h_nd_due_B hA_pop hA_due h_sA h_sA_gt h_spawnA_B h_single_B
            h_uniqueA_B h_distinct_B h_e h_e_ne_sA h_b_left
        obtain ⟨eR, h_eR_pop, h_eRD, vR, h_vR_tick, h_vR_lay, h_eR_fire,
            h_eR_fresh⟩ :=
          popSpawnAcc_right_converse groups W_B n
            (stageEvent actTick groups g₂ c₂ j) sD₁ e h_layout_WB
            h_nd_due_B hD_pop hD_due h_sD h_sD_gt h_spawnD_B h_single_B
            h_uniqueD_B h_e h_e_ne_sD h_b_right
        -- decode the right parent as a stage event
        have h_eR_WB : eR ∈ W_B.events :=
          World.mem_popSeqFuel_mem_events W_B n eR h_eR_pop
        have h_eR_due : eR.targetTick = W_B.tick :=
          World.mem_popSeqFuel_due W_B n eR h_eR_pop
        obtain ⟨gi, ci, k, h_gi, h_ci, _, h_eR_eq, _, _⟩ :=
          h_stage_due_B eR h_eR_WB h_eR_due
        have h_k_mid : k ≤ (chainAt groups gi ci).middleDelays.length := by
          by_contra h_last
          have h_last' :
              k = (chainAt groups gi ci).middleDelays.length + 1 := by omega
          have h_nil : (vR.onScheduledTick eR.nodeId).events =
              vR.events := by
            rw [h_eR_eq, h_last']
            exact lastStage_spawn_nil groups actTick vR gi ci h_gi h_ci
              h_vR_lay
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
          exact stage_spawn groups actTick vR gi ci k h_gi h_ci h_k_mid
            h_tick_R h_vR_lay
        have h_e_eq : e = stageEvent actTick groups gi ci (k + 1) := by
          rw [h_fire_R] at h_eR_fire
          rcases List.mem_append.mp h_eR_fire with h_mem | h_mem
          · exact absurd h_mem h_eR_fresh
          · simpa using h_mem
        -- decode the left parent and identify it with the right one
        have h_eL_WB : eL ∈ W_B.events :=
          World.mem_popSeqFuel_mem_events W_B n eL h_eL_pop
        have h_eL_due : eL.targetTick = W_B.tick :=
          World.mem_popSeqFuel_due W_B n eL h_eL_pop
        obtain ⟨gi', ci', k', h_gi', h_ci', _, h_eL_eq, _, _⟩ :=
          h_stage_due_B eL h_eL_WB h_eL_due
        have h_parent_eq : eL = eR := by
          by_cases h_k'_last :
              k' = (chainAt groups gi' ci').middleDelays.length + 1
          · have h_nil : (vL.onScheduledTick eL.nodeId).events =
                vL.events := by
              rw [h_eL_eq, h_k'_last]
              exact lastStage_spawn_nil groups actTick vL gi' ci' h_gi'
                h_ci' h_vL_lay
            rw [h_nil] at h_eL_fire
            exact absurd h_eL_fire h_eL_fresh
          · have h_k'_mid : k' ≤
                (chainAt groups gi' ci').middleDelays.length := by omega
            have h_tick_L : vL.tick =
                stageTarget actTick groups gi' ci' k' := by
              rw [h_vL_tick, ← h_eL_due]
              have := congr_arg ScheduledEvent.targetTick h_eL_eq
              dsimp [stageEvent] at this
              exact this
            have h_fire_L : (vL.onScheduledTick eL.nodeId).events =
                vL.events ++ [stageEvent actTick groups gi' ci' (k' + 1)] :=
              by
              rw [h_eL_eq]
              exact stage_spawn groups actTick vL gi' ci' k' h_gi' h_ci'
                h_k'_mid h_tick_L h_vL_lay
            have h_e_eq_L : e = stageEvent actTick groups gi' ci' (k' + 1) :=
              by
              rw [h_fire_L] at h_eL_fire
              rcases List.mem_append.mp h_eL_fire with h_mem | h_mem
              · exact absurd h_mem h_eL_fresh
              · simpa using h_mem
            obtain ⟨h_g_eq, h_c_eq, h_k_eq⟩ :=
              stageEvent_injective actTick groups gi' ci' (k' + 1) gi ci
                (k + 1) h_gi' h_ci' h_gi h_ci (by omega) (by omega)
                (h_e_eq_L.symm.trans h_e_eq)
            rw [h_eL_eq, h_eR_eq, h_g_eq, h_c_eq]
            congr 1
            omega
        have h_AeR : evBefore (World.popSeqFuel W_B n)
            (stageEvent actTick groups g₁ c₁ j) eR := by
          rwa [← h_parent_eq]
        -- the parent sits between two priority-(-3) pops
        have h_pri_eR : eR.priority = (-3 : Int) := by
          have h_le₁ : (stageEvent actTick groups g₁ c₁ j).priority ≤
              eR.priority :=
            popSeqFuel_priority_mono W_B n _ _ h_AeR
          have h_le₂ : eR.priority ≤
              (stageEvent actTick groups g₂ c₂ j).priority :=
            popSeqFuel_priority_mono W_B n _ _ h_eRD
          rw [hA_pri] at h_le₁
          rw [hD_pri] at h_le₂
          omega
        -- priority -3 occurs only at middle stages
        have h_k_ge : 1 ≤ k := by
          have h_p : stagePri groups gi ci k = (-3 : Int) := by
            have := congr_arg ScheduledEvent.priority h_eR_eq.symm
            dsimp [stageEvent] at this
            rw [h_pri_eR] at this
            exact this
          dsimp only [stagePri] at h_p
          split_ifs at h_p
          all_goals omega
        -- the parent sits between the references in the due filter of W_B
        have h_due_AeR : evBefore
            (W_B.events.filter (fun ev => ev.targetTick == W_B.tick))
            (stageEvent actTick groups g₁ c₁ j) eR :=
          due_evBefore_of_popSeq_evBefore W_B n _ _ hA_pop h_eR_pop hA_due
            h_eR_due (by rw [hA_pri, h_pri_eR]) h_nd_due_B h_AeR
        have h_due_eRD : evBefore
            (W_B.events.filter (fun ev => ev.targetTick == W_B.tick))
            eR (stageEvent actTick groups g₂ c₂ j) :=
          due_evBefore_of_popSeq_evBefore W_B n _ _ h_eR_pop hD_pop h_eR_due
            hD_due (by rw [h_pri_eR, hD_pri]) h_nd_due_B h_eRD
        -- lift the due-filter order to the pre-burst due filter
        have h_lift : ∀ {X Y : ScheduledEvent},
            evBefore (W_B.events.filter
                (fun ev => ev.targetTick == W_B.tick)) X Y →
            X ∈ w_log.events.filter
                (fun ev => ev.targetTick == w_log.tick) →
            Y ∈ w_log.events.filter
                (fun ev => ev.targetTick == w_log.tick) →
            evBefore (w_log.events.filter
                (fun ev => ev.targetTick == w_log.tick)) X Y := by
          intro X Y h_b hX hY
          by_cases h_fwd : evBefore
              (w_log.events.filter (fun ev => ev.targetTick == w_log.tick))
              X Y
          · exact h_fwd
          · have h_ne : X ≠ Y := evBefore.ne_of_nodup h_nd_due_B h_b
            obtain hXY | hYX := evBefore.total_of_nodup h_nodup_log hX hY
              h_ne
            · exact absurd hXY h_fwd
            · have hX_WB : X ∈ W_B.events :=
                (List.mem_filter.mp (evBefore.mem_left h_b)).1
              have hY_WB : Y ∈ W_B.events :=
                (List.mem_filter.mp (evBefore.mem_right h_b)).1
              have hX_due : X.targetTick = w_log.tick := by
                simpa [Nat.beq_eq] using (List.mem_filter.mp hX).2
              have hY_due : Y.targetTick = w_log.tick := by
                simpa [Nat.beq_eq] using (List.mem_filter.mp hY).2
              have hYX_B : evBefore (W_B.events.filter
                  (fun ev => ev.targetTick == W_B.tick)) Y X :=
                evBefore_due_gSimBurst_of_mem w.tick obsAll withinOrd pos
                  w_log active.zipIdx Y X (by rw [h_tick_log]; exact hY_due)
                  (by rw [h_tick_log]; exact hX_due) h_nodup_log hYX
                  hY_WB hX_WB
              exact (evBefore.asymm h_nd_due_B h_b hYX_B).elim
        have h_eR_log : eR ∈ w_log.events.filter
            (fun ev => ev.targetTick == w_log.tick) := by
          rw [List.mem_filter]
          refine ⟨mem_gSimBurst_due_back w.tick obsAll withinOrd pos w_log
            active.zipIdx eR h_eR_WB (by
            rwa [h_tick_WB, ← h_tick_log] at h_eR_due), by
            rw [h_eR_due, h_tick_WB, h_tick_log]; simp⟩
        have h_log_AeR : evBefore
            (w_log.events.filter (fun ev => ev.targetTick == w_log.tick))
            (stageEvent actTick groups g₁ c₁ j) eR :=
          h_lift h_due_AeR (by
            rw [List.mem_filter]
            refine ⟨hA_mem_log, by
              dsimp [stageEvent]; rw [← h_due, h_tick_log]; simp⟩) h_eR_log
        have h_log_eRD : evBefore
            (w_log.events.filter (fun ev => ev.targetTick == w_log.tick))
            eR (stageEvent actTick groups g₂ c₂ j) :=
          h_lift h_due_eRD h_eR_log (by
            rw [List.mem_filter]
            refine ⟨hD_mem_log, by
              dsimp [stageEvent]; rw [h_tgt₂, ← h_due, h_tick_log]; simp⟩)
        -- the stage-j invariant classifies the parent
        have hP_tgt : (stageEvent actTick groups gi ci k).targetTick =
            stageTarget actTick groups g₁ c₁ j := by
          have h_ttick := congr_arg ScheduledEvent.targetTick h_eR_eq.symm
          dsimp [stageEvent] at h_ttick ⊢
          rw [h_ttick, h_eR_due, h_tick_WB, h_due]
        rw [h_eR_eq] at h_log_AeR h_log_eRD
        exact middleBlock_succ_of_parent_between' groups actTick T
          g₁ c₁ g₂ c₂ j
          (w_log.events.filter (fun ev => ev.targetTick == w_log.tick))
          e gi ci k h_gi h_ci h_k_ge h_k_mid h_e_eq hP_tgt h_log_AeR
          h_log_eRD h_mb_log h_pri h_tgt h_j₁
