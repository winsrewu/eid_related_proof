import BasicProofs.GroupClustering.NoEarlyChainEntries
import BasicProofs.GroupClustering.StageEventCompleteness
import BasicProofs.GroupClustering.ActivationListOrder

set_option linter.unusedVariables false

open BasicRedstoneSim List

/-! # Group clustering — the tick-`T` finals bundle

The log block of the output tick `T` is the entries of the final-stage
events, in queue order. The bundle packages everything the LogShape
bridge `groupBeforeSpec_iff_evBefore_discharged` consumes:

* the log shape in foldl form, and no chain entries before `T`;
* `finals`, the tick-`T` due filter of the tick-start queue;
* `finalEventOf`, `chainOf`, `finalIdx`, `entryOf`, with the
  consistency facts and the split premise for every valid chain.

At tick `T` every due event is a final-stage event (StageEventCompleteness), carries
priority -1, and firing it logs exactly one chain entry (LogShape
`finalEvent_fire_isOutputEntry`) and spawns nothing. A group that
activates at tick `T` is empty, so its within-order is empty and its
burst step is a bare `processNEvents`, which does not change the drain
(`processNEvents_stepUntilNextTick_eq`). The drain entries are
therefore the entries of the whole due filter, in pop order, which is
queue order because all due events share one priority.
-/

/-! ## Delay arithmetic -/

/-- A chain delay is at least 3: observer tick plus the last delay. -/
private theorem chainDelay_ge_three (c : ChainSpec) : chainDelay c ≥ 3 := by
  dsimp [chainDelay]
  have h_last : (c.lastDelay : Nat) ≥ 1 := by
    exact Nat.succ_le_of_lt c.lastDelay.2
  omega

/-- The delay of a nonempty group is at least 3. -/
private theorem groupDelay_ge_three_of_ne (g : GroupSpec) (h_ne : g ≠ []) :
    groupDelay g ≥ 3 := by
  cases g with
  | nil => contradiction
  | cons c cs =>
    dsimp [groupDelay]
    exact chainDelay_ge_three c

/-- A group that activates at tick `T` is empty: a nonempty group
    activates strictly before `T`. -/
private theorem active_at_T_empty (groups : List GroupSpec)
    (actTick : Nat → Nat) (T gi : Nat)
    (h_act : ∀ gi, gi < groups.length → groupAt groups gi ≠ [] →
        actTick gi + groupDelay (groupAt groups gi) = T)
    (h_gi : gi < groups.length) (h_actT : actTick gi = T) :
    groupAt groups gi = [] := by
  by_cases h_ne : groupAt groups gi = []
  · exact h_ne
  · have h := h_act gi h_gi h_ne
    rw [h_actT] at h
    have h_ge := groupDelay_ge_three_of_ne (groupAt groups gi) h_ne
    omega

/-! ## The burst phase of tick `T` does not change the drain -/

/-- If every burst pair has an empty ordered observer list, each burst
    step is a bare `processNEvents`, so the burst does not change the
    drain. -/
private theorem gSimBurst_stepUNT_of_no_observers (t : Nat)
    (obsAll : List (List Nat)) (withinOrd : Nat → List Nat)
    (pos : Nat → List Nat) (W : World) (ps : List (Nat × Nat))
    (h_empty : ∀ gi k, (gi, k) ∈ ps →
        ((withinOrd gi).foldl (fun acc ci =>
            match (obsAll[gi]?.getD [])[ci]? with
            | some oid => acc ++ [oid]
            | none => acc) []) = []) :
    (gSimBurst t obsAll withinOrd pos W ps).stepUntilNextTick =
      W.stepUntilNextTick := by
  revert h_empty
  induction ps generalizing W with
  | nil =>
    intro h_empty
    dsimp [gSimBurst]
  | cons p ps ih =>
    intro h_empty
    rcases p with ⟨gi, k⟩
    have h_ord := h_empty gi k (List.mem_cons.mpr (Or.inl rfl))
    have h_reduce : gSimBurst t obsAll withinOrd pos W ((gi, k) :: ps) =
        gSimBurst t obsAll withinOrd pos
          (processNEvents W ((pos t)[k]?.getD 0)) ps := by
      dsimp [gSimBurst]
      congr 1
      dsimp [activateGroup]
      erw [h_ord]
      dsimp
    rw [h_reduce]
    have h_ih := ih (processNEvents W ((pos t)[k]?.getD 0))
      (fun gi' k' h_mem => h_empty gi' k' (List.mem_cons.mpr (Or.inr h_mem)))
    rw [h_ih]
    exact processNEvents_stepUntilNextTick_eq W ((pos t)[k]?.getD 0)

/-- The burst phase of tick `T` consists of empty-group steps only.
    An empty group has an empty within-order, so its step is a bare
    `processNEvents`, and the burst result has the same drain as the
    burst start. -/
private theorem burst_T_stepUNT_eq (groups : List GroupSpec)
    (actTick : Nat → Nat) (T : Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat)
    (h_act : ∀ gi, gi < groups.length → groupAt groups gi ≠ [] →
        actTick gi + groupDelay (groupAt groups gi) = T)
    (h_within : ∀ gi, gi < groups.length →
        List.Perm (withinOrd gi) (List.range (groupAt groups gi).length))
    (W₁ : World) (h_tick : W₁.tick = T) :
    (gSimBurst T (buildGroups groups).2 withinOrd pos W₁
        ((groupOrd.filter (fun gi =>
            decide (gi < (buildGroups groups).2.length) &&
            (actTick gi == T))).zipIdx)).stepUntilNextTick =
      W₁.stepUntilNextTick := by
  set active := groupOrd.filter (fun gi =>
    decide (gi < (buildGroups groups).2.length) && (actTick gi == T))
  -- every pair of active.zipIdx belongs to an empty group, whose
  -- within-order is empty
  have h_pair_empty : ∀ gi k, (gi, k) ∈ active.zipIdx →
      ((withinOrd gi).foldl (fun acc ci =>
          match (((buildGroups groups).2)[gi]?.getD [])[ci]? with
          | some oid => acc ++ [oid]
          | none => acc) []) = [] := by
    intro gi k h_pair
    have h_zip := List.mem_zipIdx h_pair
    obtain ⟨_, h_k_lt, h_gi_eq⟩ := h_zip
    have h_gi_mem : gi ∈ active := by
      have h_gi_at : gi = active[k] := by simpa using h_gi_eq
      rw [h_gi_at]
      exact List.getElem_mem (by simpa using h_k_lt)
    dsimp [active] at h_gi_mem
    rw [List.mem_filter] at h_gi_mem
    obtain ⟨_, h_cond⟩ := h_gi_mem
    rw [Bool.and_eq_true] at h_cond
    obtain ⟨h_dec, h_beq⟩ := h_cond
    have h_gi_lt : gi < groups.length := by
      have h_dec' : decide (gi < (buildGroups groups).2.length) = true :=
        h_dec
      rw [buildGroups_snd_length] at h_dec'
      simpa using h_dec'
    have h_actT : actTick gi = T := by simpa [Nat.beq_eq] using h_beq
    have h_empty := active_at_T_empty groups actTick T gi h_act h_gi_lt
      h_actT
    have h_perm := h_within gi h_gi_lt
    rw [h_empty] at h_perm
    have h_len := List.Perm.length_eq h_perm
    dsimp at h_len
    have h_wo_nil : withinOrd gi = [] :=
      List.eq_nil_of_length_eq_zero (by simpa using h_len)
    rw [h_wo_nil]
    rfl
  exact gSimBurst_stepUNT_of_no_observers T (buildGroups groups).2 withinOrd
    pos W₁ active.zipIdx h_pair_empty

/-! ## Pop order of a uniform-priority due filter -/

/-- Under uniform priority among the due events, the popped event is the
    head of the due filter: PopOrder places the popped event at the head of
    the due-sublist prefix that is strictly above it, and uniformity makes
    that prefix empty. -/
private theorem popNextEvent_head_of_uniform (w : World)
    (ev₀ : ScheduledEvent) (w_pop : World)
    (h_pop : w.popNextEvent = some (ev₀, w_pop))
    (h_uni : ∀ e₁ ∈ w.events, ∀ e₂ ∈ w.events,
        (e₁.targetTick == w.tick) = true → (e₂.targetTick == w.tick) = true →
        e₁.priority = e₂.priority) :
    ∃ tail, w.events.filter (fun e => (e.targetTick == w.tick)) =
      ev₀ :: tail := by
  obtain ⟨_, _, l₁, l₂, h_split, h_l₁⟩ :=
    popNextEvent_first_min_priority w ev₀ w_pop h_pop
  set due := w.events.filter (fun e => (e.targetTick == w.tick))
  have h_l₁_nil : l₁ = [] := by
    cases l₁ with
    | nil => rfl
    | cons e l₁' =>
      exfalso
      have h_e_mem : e ∈ e :: l₁' := List.mem_cons.mpr (Or.inl rfl)
      have h_e_due : e ∈ due := by
        rw [h_split]
        exact List.mem_append.mpr (Or.inl h_e_mem)
      have h_e_ev : e ∈ w.events := (List.mem_filter.mp h_e_due).1
      have h_e_tick : (e.targetTick == w.tick) = true :=
        (List.mem_filter.mp h_e_due).2
      have h_ev₀_due : ev₀ ∈ due := by
        rw [h_split]
        exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
      have h_ev₀_ev : ev₀ ∈ w.events := (List.mem_filter.mp h_ev₀_due).1
      have h_ev₀_tick : (ev₀.targetTick == w.tick) = true :=
        (List.mem_filter.mp h_ev₀_due).2
      have h_pri_eq := h_uni e h_e_ev ev₀ h_ev₀_ev h_e_tick h_ev₀_tick
      have h_lt := h_l₁ e h_e_mem
      omega
  rw [h_l₁_nil, List.nil_append] at h_split
  exact ⟨l₂, h_split⟩

/-- One pop removes the popped event from the due filter, and the removed
    position holds exactly the popped event. -/
private theorem due_tail_eq_eraseIdx' (w : World) (ev₀ : ScheduledEvent)
    (w_pop : World) (h_pop : w.popNextEvent = some (ev₀, w_pop)) :
    ∃ (j : Nat)
      (hj : j < (w.events.filter (fun e => (e.targetTick == w.tick))).length),
      (w_pop.onScheduledTick ev₀.nodeId).events.filter
          (fun e => (e.targetTick == w.tick)) =
        (w.events.filter (fun e => (e.targetTick == w.tick))).eraseIdx j ∧
      (w.events.filter (fun e => (e.targetTick == w.tick)))[j]'hj = ev₀ := by
  obtain ⟨idx, h_idx, h_erase, h_tick_ev, _, h_get⟩ :=
    World.popNextEvent_eraseIdx w ev₀ w_pop h_pop
  set due := w.events.filter (fun e => (e.targetTick == w.tick))
  have h_due_ev₀ : (fun e => (e.targetTick == w.tick))
      (w.events[idx]'h_idx) = true := by
    simp [h_get, h_tick_ev]
  obtain ⟨j, hj, h_filter_erase, h_get_j⟩ :=
    filter_eraseIdx_getElem (fun e => (e.targetTick == w.tick)) w.events idx
      h_idx h_due_ev₀
  have h_get_j' : due[j]'hj = ev₀ := by
    dsimp [due]
    rw [h_get_j, h_get]
  refine ⟨j, hj, ?_, h_get_j'⟩
  obtain ⟨new, h_app_new, h_fut_new⟩ :=
    World.onScheduledTick_appends_future w_pop ev₀.nodeId
  have h_tick_pop : w_pop.tick = w.tick :=
    World.popNextEvent_tick w ev₀ w_pop h_pop
  rw [h_app_new, List.filter_append]
  have h_new_nil : new.filter (fun e => (e.targetTick == w.tick)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro e h_e h_due_e
    have h_gt := h_fut_new e h_e
    rw [h_tick_pop] at h_gt
    have h_eq : e.targetTick = w.tick := by simpa [Nat.beq_eq] using h_due_e
    omega
  rw [h_new_nil, List.append_nil, h_erase, h_filter_erase]

/-- With one uniform priority among the due events, and a duplicate-free
    due filter, the full pop sequence is the due filter in queue order. -/
private theorem popSeqFuel_eq_due_filter (w : World)
    (h_uni : ∀ e₁ ∈ w.events, ∀ e₂ ∈ w.events,
        (e₁.targetTick == w.tick) = true → (e₂.targetTick == w.tick) = true →
        e₁.priority = e₂.priority)
    (h_nodup : (w.events.filter (fun e => (e.targetTick == w.tick))).Nodup) :
    World.popSeqFuel w (World.countEventAtThisTick w w.tick) =
      w.events.filter (fun e => (e.targetTick == w.tick)) := by
  have h_gen : ∀ (n : Nat) (w : World),
      (w.events.filter (fun e => (e.targetTick == w.tick))).length = n →
      (∀ e₁ ∈ w.events, ∀ e₂ ∈ w.events,
          (e₁.targetTick == w.tick) = true →
          (e₂.targetTick == w.tick) = true → e₁.priority = e₂.priority) →
      (w.events.filter (fun e => (e.targetTick == w.tick))).Nodup →
      World.popSeqFuel w n =
        w.events.filter (fun e => (e.targetTick == w.tick)) := by
    intro n
    induction n with
    | zero =>
      intro w h_len h_uni h_nodup
      dsimp only [World.popSeqFuel]
      exact (List.eq_nil_of_length_eq_zero h_len).symm
    | succ n ih =>
      intro w h_len h_uni h_nodup
      set due := w.events.filter (fun e => (e.targetTick == w.tick))
      -- due is nonempty, so a pop happens
      have h_not_none : w.popNextEvent ≠ none := by
        intro h_none
        have h_no_due : ∀ e ∈ w.events, e.targetTick ≠ w.tick :=
          popNextEvent_none_no_events w h_none
        have h_due_nil : due = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro e h_e h_due_e
          exact h_no_due e h_e (by simpa [Nat.beq_eq] using h_due_e)
        have h_len0 : due.length = 0 := by
          rw [h_due_nil]
          rfl
        omega
      obtain ⟨⟨ev₀, w_pop⟩, h_pop⟩ := Option.ne_none_iff_exists'.mp h_not_none
      -- ev₀ is the head of due
      obtain ⟨tail, h_head⟩ : ∃ tail, due = ev₀ :: tail :=
        popNextEvent_head_of_uniform w ev₀ w_pop h_pop h_uni
      set w' := w_pop.onScheduledTick ev₀.nodeId
      -- the due filter of w' is tail
      have h_tail : w'.events.filter
          (fun e => (e.targetTick == w'.tick)) = tail := by
        obtain ⟨j, hj, h_eq, h_get_j⟩ := due_tail_eq_eraseIdx' w ev₀ w_pop
          h_pop
        have h_tick_w' : w'.tick = w.tick := by
          dsimp [w']
          rw [World.onScheduledTick_tick,
            World.popNextEvent_tick w ev₀ w_pop h_pop]
        have h_j0 : j = 0 := by
          cases j with
          | zero => rfl
          | succ j' =>
            exfalso
            have h_nd' : (ev₀ :: tail).Nodup := by rwa [← h_head]
            have h_ev_not_tail : ev₀ ∉ tail := (List.nodup_cons.mp h_nd').1
            have hjp : j' < tail.length := by
              have hj' : j' + 1 < (ev₀ :: tail).length := by rwa [← h_head]
              dsimp at hj'
              omega
            have h_in_tail : ev₀ ∈ tail := by
              have h_elem : due[j' + 1]'hj ∈ tail := by
                simp only [h_head]
                exact List.getElem_mem hjp
              rwa [h_get_j] at h_elem
            exact h_ev_not_tail h_in_tail
        have h_eq' : w'.events.filter
            (fun e => (e.targetTick == w'.tick)) = due.eraseIdx j := by
          rw [h_tick_w']
          exact h_eq
        rw [h_eq', h_j0, h_head]
        dsimp [List.eraseIdx]
      -- count drops to n
      have h_count_w' : World.countEventAtThisTick w' w'.tick = n := by
        dsimp [World.countEventAtThisTick]
        rw [h_tail]
        have h_tail_len : tail.length = n := by
          have := congr_arg List.length h_head
          simp at this
          omega
        exact h_tail_len
      -- uniformity carries to w'
      have h_uni_w' : ∀ e₁ ∈ w'.events, ∀ e₂ ∈ w'.events,
          (e₁.targetTick == w'.tick) = true →
          (e₂.targetTick == w'.tick) = true → e₁.priority = e₂.priority := by
        intro e₁ h_e₁ e₂ h_e₂ h_d₁ h_d₂
        have h_e₁_tail : e₁ ∈ tail := by
          rw [← h_tail]
          exact List.mem_filter.mpr ⟨h_e₁, h_d₁⟩
        have h_e₂_tail : e₂ ∈ tail := by
          rw [← h_tail]
          exact List.mem_filter.mpr ⟨h_e₂, h_d₂⟩
        have h_e₁_due : e₁ ∈ due := by
          rw [h_head]
          exact List.mem_cons.mpr (Or.inr h_e₁_tail)
        have h_e₂_due : e₂ ∈ due := by
          rw [h_head]
          exact List.mem_cons.mpr (Or.inr h_e₂_tail)
        have h_e₁_ev : e₁ ∈ w.events := (List.mem_filter.mp h_e₁_due).1
        have h_e₂_ev : e₂ ∈ w.events := (List.mem_filter.mp h_e₂_due).1
        have h_e₁_d : (e₁.targetTick == w.tick) = true :=
          (List.mem_filter.mp h_e₁_due).2
        have h_e₂_d : (e₂.targetTick == w.tick) = true :=
          (List.mem_filter.mp h_e₂_due).2
        exact h_uni e₁ h_e₁_ev e₂ h_e₂_ev h_e₁_d h_e₂_d
      -- nodup carries to w'
      have h_nodup_w' : (w'.events.filter
          (fun e => (e.targetTick == w'.tick))).Nodup := by
        rw [h_tail]
        have h_tail_erase : tail = due.eraseIdx 0 := by
          rw [h_head]
          dsimp [List.eraseIdx]
        rw [h_tail_erase]
        exact nodup_eraseIdx due 0 h_nodup
      -- assemble
      have h_ih := ih w' h_count_w' h_uni_w' h_nodup_w'
      dsimp only [World.popSeqFuel]
      rw [h_pop]
      change ev₀ :: World.popSeqFuel w' n = due
      rw [h_ih, h_tail, h_head]
  dsimp [World.countEventAtThisTick]
  exact h_gen (w.events.filter (fun e => (e.targetTick == w.tick))).length w
    rfl h_uni h_nodup

/-! ## Small log-block helpers -/

/-- A member of a filter splits the filter. -/
private theorem filter_mem_split {α : Type} (p : α → Bool) (l : List α)
    (a : α) (h_mem : a ∈ l.filter p) (h_pa : p a = true) :
    ∃ pre post, l.filter p = pre ++ a :: post := by
  revert a h_mem h_pa
  induction l with
  | nil =>
    intro a h_mem
    cases h_mem
  | cons b l ih =>
    intro a h_mem h_pa
    by_cases h_pb : p b = true
    · have h_filter : (b :: l).filter p = b :: l.filter p := by
        simp [List.filter, h_pb]
      rw [h_filter] at h_mem ⊢
      rw [List.mem_cons] at h_mem
      rcases h_mem with rfl | h_mem
      · exact ⟨[], l.filter p, by simp⟩
      · obtain ⟨pre, post, h_split⟩ := ih a h_mem h_pa
        refine ⟨b :: pre, post, ?_⟩
        rw [h_split]
        rfl
    · have h_pbf : p b = false := by
        revert h_pb
        cases p b <;> intro h
        · rfl
        · exfalso
          exact h rfl
      have h_filter : (b :: l).filter p = l.filter p := by
        simp [List.filter, h_pbf]
      rw [h_filter] at h_mem ⊢
      exact ih a h_mem h_pa

/-- The last block of the foldl block shape. -/
private theorem foldl_blocks_last (blocks : Nat → List String) (T : Nat) :
    (List.range (T + 1)).foldl
        (fun acc t => acc ++ (s!"tick {t}" :: blocks t)) [] =
      (List.range T).foldl
        (fun acc t => acc ++ (s!"tick {t}" :: blocks t)) [] ++
      (s!"tick {T}" :: blocks T) := by
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Pointwise equal blocks give equal foldl block shapes. -/
private theorem foldl_blocks_congr' (c₁ c₂ : Nat → List String) (n : Nat)
    (h_eq : ∀ t < n, c₁ t = c₂ t) :
    (List.range n).foldl (fun acc t => acc ++ (s!"tick {t}" :: c₁ t)) [] =
      (List.range n).foldl (fun acc t => acc ++ (s!"tick {t}" :: c₂ t)) [] := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    have h_eq' : ∀ t < n', c₁ t = c₂ t := fun t ht => h_eq t (by omega)
    rw [foldl_blocks_last c₁ n', foldl_blocks_last c₂ n']
    rw [ih h_eq', h_eq n' (by omega)]

/-- `SigLevelsOk` survives `logOutput`. -/
private theorem SigLevelsOk_logOutput (w : World) (msg : String)
    (hS : SigLevelsOk w) : SigLevelsOk (w.logOutput msg) := by
  intro nid nd h_gn
  dsimp [World.logOutput] at h_gn
  exact hS nid nd h_gn

/-- Running the fold through tick `T + 1` reaches the drain of the
    tick-`T` log-output world: the burst at `T` consists only of empty
    groups, so it does not change the drain. -/
private theorem gSimFoldl_succ_T_eq (T : Nat) (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat)
    (h_act : ∀ gi, gi < groups.length → groupAt groups gi ≠ [] →
        actTick gi + groupDelay (groupAt groups gi) = T)
    (h_within : ∀ gi, gi < groups.length →
        List.Perm (withinOrd gi) (List.range (groupAt groups gi).length)) :
    gSimFoldl actTick (buildGroups groups).2 groupOrd withinOrd pos
        (buildGroups groups).1 (T + 1) =
      ((gSimFoldl actTick (buildGroups groups).2 groupOrd withinOrd pos
          (buildGroups groups).1 T).logOutput s!"tick {T}").stepUntilNextTick := by
  set obsAll := (buildGroups groups).2
  set w₀ := (buildGroups groups).1
  set W_T : World := gSimFoldl actTick obsAll groupOrd withinOrd pos w₀ T
  have h_tick : W_T.tick = T := by
    dsimp [W_T, w₀]
    rw [gSimFoldl_tick, buildGroups_tick]
    omega
  have h_reduce : gSimFoldl actTick obsAll groupOrd withinOrd pos w₀ (T + 1) =
      gSimBody actTick obsAll groupOrd withinOrd pos W_T T := by
    dsimp only [gSimFoldl]
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    dsimp only [W_T, gSimFoldl]
  rw [h_reduce]
  dsimp [gSimBody]
  simp only [h_tick]
  split_ifs with h_active
  · rfl
  · exact burst_T_stepUNT_eq groups actTick T groupOrd withinOrd pos h_act
      h_within (W_T.logOutput s!"tick {T}") (by
        dsimp [World.logOutput]
        exact h_tick)

/-! ## The finals bundle -/

/-- A filter preserves duplicate-freedom. -/
private theorem nodup_filter' {α : Type} (p : α → Bool) (l : List α) :
    l.Nodup → (l.filter p).Nodup := by
  intro h
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at h
    dsimp only [List.filter]
    split
    · rw [List.nodup_cons]
      refine ⟨?_, ih h.2⟩
      intro h_mem
      exact h.1 (List.mem_filter.mp h_mem).1
    · exact ih h.2

/-- Reflexivity of the Boolean equality on `Nat`. -/
private theorem nat_beq_self (n : Nat) : (n == n) = true := by
  simp

/-- THE FINALS BUNDLE. At the common output tick `T`:

* the log has the foldl block shape, with no chain entries before `T`;
* `finals` is the tick-`T` due filter of the tick-start queue, and is
  duplicate-free;
* `finalEventOf gi ci` is the final-stage event of chain `(gi, ci)`;
* `blocks T = finals.map entryOf`: the block of tick `T` is exactly the
  drain entries, one per final event, in pop (queue) order;
* `chainOf` recovers the chain of a final event and is consistent with
  `finalEventOf`; `finalIdx` is the queue position, witnessed by a
  split of `finals`.

This packages every premise of LogShape's
`groupBeforeSpec_iff_evBefore_discharged`. -/
theorem groupSimulate_final_bundle (T : Nat) (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat)
    (h_valid : ∀ gi (c : ChainSpec), gi < groups.length →
        c ∈ groupAt groups gi →
        (∀ d ∈ c.middleDelays, ValidDelay d) ∧ ValidDelay c.lastDelay)
    (h_uniform : ∀ gi (c₁ c₂ : ChainSpec), gi < groups.length →
        c₁ ∈ groupAt groups gi → c₂ ∈ groupAt groups gi →
        chainDelay c₁ = chainDelay c₂)
    (h_act : ∀ gi, gi < groups.length → groupAt groups gi ≠ [] →
        actTick gi + groupDelay (groupAt groups gi) = T)
    (h_ord : List.Perm groupOrd (List.range groups.length))
    (h_within : ∀ gi, gi < groups.length →
        List.Perm (withinOrd gi) (List.range (groupAt groups gi).length)) :
    ∃ (blocks : Nat → List String) (finals : List ScheduledEvent)
      (finalEventOf : Nat → Nat → ScheduledEvent)
      (chainOf : ScheduledEvent → Nat × Nat)
      (finalIdx : Nat → Nat → Nat) (entryOf : ScheduledEvent → String),
      groupSimulate T groups actTick groupOrd withinOrd pos =
        (List.range (T + 1)).foldl
          (fun acc t => acc ++ (s!"tick {t}" :: blocks t)) [] ∧
      (∀ t < T, blocks t = []) ∧
      finals =
        (gSimWorld groups actTick groupOrd withinOrd pos T).events.filter
          (fun ev => ev.targetTick == T) ∧
      finals.Nodup ∧
      (∀ gi ci, stageEvent actTick groups gi ci
          ((chainAt groups gi ci).middleDelays.length + 1) =
        finalEventOf gi ci) ∧
      blocks T = finals.map entryOf ∧
      (∀ ev ∈ finals,
          isOutputEntry (entryOf ev) (chainOf ev).1 (chainOf ev).2 = true) ∧
      (∀ ev ∈ finals, ev = finalEventOf (chainOf ev).1 (chainOf ev).2) ∧
      (∀ gi ci, gi < groups.length → ci < (groupAt groups gi).length →
          finalEventOf gi ci ∈ finals →
          chainOf (finalEventOf gi ci) = (gi, ci)) ∧
      ∀ gi ci, gi < groups.length → ci < (groupAt groups gi).length →
        ∃ pre post, finals = pre ++ finalEventOf gi ci :: post ∧
          pre.length = finalIdx gi ci := by
  classical
  set finalEventOf : Nat → Nat → ScheduledEvent := fun gi ci =>
    stageEvent actTick groups gi ci
      ((chainAt groups gi ci).middleDelays.length + 1)
  set W_T : World := gSimFoldl actTick (buildGroups groups).2 groupOrd
    withinOrd pos (buildGroups groups).1 T
  set w : World := W_T.logOutput s!"tick {T}"
  set finals : List ScheduledEvent :=
    (gSimWorld groups actTick groupOrd withinOrd pos T).events.filter
      (fun ev => ev.targetTick == T)
  have h_Wtick : W_T.tick = T := by
    dsimp [W_T]
    rw [gSimFoldl_tick, buildGroups_tick]
    omega
  have h_wtick : w.tick = T := by
    dsimp [w, World.logOutput]
    exact h_Wtick
  have h_w_events : w.events =
      (gSimWorld groups actTick groupOrd withinOrd pos T).events := by
    dsimp [w, W_T, World.logOutput, gSimWorld]
  -- nodup of the orders, and of the due filter
  have h_gord_nd : groupOrd.Nodup :=
    Nodup.of_perm h_ord List.nodup_range
  have h_within_nd : ∀ gi, gi < groups.length → (withinOrd gi).Nodup :=
    fun gi h_gi => Nodup.of_perm (h_within gi h_gi) List.nodup_range
  have h_nd : finals.Nodup := by
    dsimp [finals]
    exact nodup_filter' (fun ev => ev.targetTick == T) _
      (gSimWorld_events_Nodup groups actTick groupOrd withinOrd pos T
        h_gord_nd h_within_nd)
  -- every due event at `T` is a final-stage event with priority -1
  have h_uni : ∀ e₁ ∈ w.events, ∀ e₂ ∈ w.events,
      (e₁.targetTick == w.tick) = true → (e₂.targetTick == w.tick) = true →
      e₁.priority = e₂.priority := by
    intro e₁ h_e₁ e₂ h_e₂ h_d₁ h_d₂
    suffices ∀ e ∈ w.events, (e.targetTick == w.tick) = true →
        e.priority = (-1 : Int) from by
      rw [this e₁ h_e₁ h_d₁, this e₂ h_e₂ h_d₂]
    intro e h_e h_due
    have h_tgt : e.targetTick = T := by
      rw [h_wtick] at h_due
      simpa [Nat.beq_eq] using h_due
    obtain ⟨gi, ci, _, _, h_eq⟩ := due_events_at_T_are_final groups actTick
      groupOrd withinOrd pos T h_uniform h_act e
      (by rwa [← h_w_events]) h_tgt
    rw [h_eq]
    dsimp [stageEvent]
    exact stagePri_last groups gi ci
  -- the pop sequence of `w` is the due filter, i.e. `finals`
  have h_filter_eq : w.events.filter (fun e => (e.targetTick == w.tick)) =
      finals := by
    rw [h_w_events]
    dsimp [finals]
    congr 1
    ext ev
    simp [h_wtick]
  have h_pop_seq : World.popSeqFuel w (World.countEventAtThisTick w w.tick) =
      finals := by
    rw [← h_filter_eq]
    exact popSeqFuel_eq_due_filter w h_uni (by rwa [h_filter_eq])
  -- chainOf: the chain a final event belongs to
  let chainOfPred (ev : ScheduledEvent) (p : Nat × Nat) : Prop :=
    p.1 < groups.length ∧ p.2 < (groupAt groups p.1).length ∧
    ev = finalEventOf p.1 p.2
  set chainOf : ScheduledEvent → Nat × Nat := fun ev =>
    if h : ∃ p, chainOfPred ev p then Classical.choose h else (0, 0)
  have h_chainOf_spec : ∀ ev, (∃ p, chainOfPred ev p) →
      chainOfPred ev (chainOf ev) := by
    intro ev h_ex
    dsimp [chainOf]
    rw [dif_pos h_ex]
    exact Classical.choose_spec h_ex
  have h_exists_pred : ∀ ev ∈ finals, ∃ p, chainOfPred ev p := by
    intro ev h_ev
    dsimp [finals] at h_ev
    obtain ⟨h_ev_W, h_due⟩ := List.mem_filter.mp h_ev
    have h_tgt : ev.targetTick = T := by simpa [Nat.beq_eq] using h_due
    obtain ⟨gi, ci, h_gi, h_ci, h_eq⟩ := due_events_at_T_are_final groups
      actTick groupOrd withinOrd pos T h_uniform h_act ev h_ev_W h_tgt
    exact ⟨⟨gi, ci⟩, h_gi, h_ci, h_eq⟩
  -- layout and signal facts about the drain start world
  have h_layout_W : NodeLayoutOk groups W_T :=
    NodeLayoutOk_gSimFoldl groups actTick (buildGroups groups).2 groupOrd
      withinOrd pos (buildGroups groups).1 T
      (NodeLayoutOk_buildGroups groups)
  have h_layout_w : NodeLayoutOk groups w :=
    NodeLayoutOk_logOutput groups W_T s!"tick {T}" h_layout_W
  obtain ⟨chainAt', h_prefix', h_chain', _, hS_W⟩ :=
    gSimFoldl_log_shape_prefix actTick (buildGroups groups).2 groupOrd
      withinOrd pos (buildGroups groups).1 T
      (buildGroups_OutputNamesOk groups) (buildGroups_SigLevelsOk groups)
  have hS_w : SigLevelsOk w :=
    SigLevelsOk_logOutput W_T s!"tick {T}" hS_W
  have h_WT_log : W_T.outputLog = logBlocks [] 0 chainAt' T := by
    have h := h_prefix' T (by omega : T ≤ T)
    rw [buildGroups_outputLog, buildGroups_tick] at h
    exact h
  -- firing a final event logs its chain's output entry
  have h_fire : ∀ ev ∈ finals, ∀ v, v.tick = w.tick →
      NodeLayoutOk groups v → SigLevelsOk v →
      ∃ s, (v.onScheduledTick ev.nodeId).outputLog = v.outputLog ++ [s] ∧
        isOutputEntry s (chainOf ev).1 (chainOf ev).2 = true := by
    intro ev h_ev v _ h_lay h_sig
    obtain ⟨h_gi, h_ci, h_eq⟩ := h_chainOf_spec ev (h_exists_pred ev h_ev)
    set gi := (chainOf ev).1
    set ci := (chainOf ev).2
    obtain ⟨s, h_log, h_entry⟩ :=
      finalEvent_fire_isOutputEntry groups actTick gi ci h_gi h_ci v h_lay
        h_sig
    refine ⟨s, ?_, h_entry⟩
    dsimp [finalEventOf] at h_eq
    rw [h_eq]
    exact h_log
  -- the drain appends one entry per final pop
  obtain ⟨entries, entryOf, h_drain_log, h_entries, h_entry_match⟩ :=
    chainEntries_are_finalPops groups w h_layout_w hS_w finals h_nd chainOf
      h_pop_seq h_fire
  -- the log block shape, and no entries before `T`
  obtain ⟨blocks, h_shape_lb, h_chain_blocks⟩ :=
    groupSimulate_log_shape T groups actTick groupOrd withinOrd pos
  have h_shape : groupSimulate T groups actTick groupOrd withinOrd pos =
      (List.range (T + 1)).foldl
        (fun acc t => acc ++ (s!"tick {t}" :: blocks t)) [] := by
    rw [h_shape_lb, logBlocks_zero_eq_foldl]
  have h_no_early : ∀ t < T, blocks t = [] :=
    groupSimulate_no_early_chain_entries T groups actTick groupOrd
      withinOrd pos h_valid h_uniform h_act blocks h_shape
  -- the same log, computed through the drain
  have h_log_eq : groupSimulate T groups actTick groupOrd withinOrd pos =
      logBlocks [] 0 chainAt' T ++ (s!"tick {T}" :: entries) := by
    dsimp [groupSimulate]
    rw [gSimFoldl_succ_T_eq T groups actTick groupOrd withinOrd pos h_act
      h_within]
    rw [h_drain_log]
    dsimp [w, World.logOutput]
    rw [h_WT_log, List.append_assoc]
    rfl
  -- comparing the two decompositions pins block `T`: the decomposition
  -- built from the drain entries and the log-shape decomposition of the
  -- same log agree; the latter holds chain entries only
  let blocks'' : Nat → List String := fun t =>
    if t = T then entries else chainAt' t
  have h_bT : blocks'' T = entries := by
    dsimp [blocks'']
    split_ifs with h_eq
    · rfl
    · exfalso
      exact h_eq rfl
  have h_bs_foldl : (List.range (T + 1)).foldl
      (fun acc t => acc ++ (s!"tick {t}" :: blocks'' t)) [] =
    (List.range T).foldl
      (fun acc t => acc ++ (s!"tick {t}" :: chainAt' t)) [] ++
    (s!"tick {T}" :: entries) := by
    rw [foldl_blocks_last blocks'' T, h_bT]
    congr 1
    exact foldl_blocks_congr' blocks'' chainAt' T (fun t h_t => by
      dsimp [blocks'']
      split_ifs with h_eq
      · exfalso
        omega
      · rfl)
  have h_bs_log : logBlocks [] 0 blocks'' (T + 1) =
      logBlocks [] 0 chainAt' T ++ (s!"tick {T}" :: entries) := by
    rw [logBlocks_zero_eq_foldl blocks'' (T + 1), h_bs_foldl,
      ← logBlocks_zero_eq_foldl chainAt' T]
  have h_log_eq' : logBlocks [] 0 blocks'' (T + 1) =
      logBlocks [] 0 blocks (T + 1) := by
    rw [h_bs_log, ← h_log_eq, h_shape_lb]
  have h_blocks_eq : ∀ t < T + 1, blocks'' t = blocks t :=
    logBlocks_chainAt_eq_of_log_eq (T + 1) blocks'' blocks
      (fun t h_t => h_chain_blocks t (by omega)) h_log_eq'
  have h_block : blocks T = finals.map entryOf := by
    have h := h_blocks_eq T (by omega)
    dsimp [blocks''] at h
    split_ifs at h with h_eq
    · rw [← h, h_entries]
    · exfalso
      exact h_eq rfl
  -- every final event sits in `finals`, so `finals` splits around it
  have h_mem_finals : ∀ gi ci, gi < groups.length →
      ci < (groupAt groups gi).length → finalEventOf gi ci ∈ finals := by
    intro gi ci h_gi h_ci
    have h_arr := stageEvent_mem_gSimWorld groups actTick groupOrd withinOrd
      pos h_valid h_ord h_within gi ci h_gi h_ci
      ((chainAt groups gi ci).middleDelays.length + 1) (by omega)
    rw [stageTarget_final_eq_T groups actTick T gi ci h_gi h_ci h_uniform
      h_act] at h_arr
    dsimp [finals, finalEventOf]
    refine List.mem_filter.mpr ⟨h_arr, ?_⟩
    dsimp [stageEvent]
    rw [stageTarget_final_eq_T groups actTick T gi ci h_gi h_ci h_uniform
      h_act]
    exact nat_beq_self T
  have h_split_exists : ∀ gi ci, gi < groups.length →
      ci < (groupAt groups gi).length →
      ∃ pre post, finals = pre ++ finalEventOf gi ci :: post := by
    intro gi ci h_gi h_ci
    dsimp [finals]
    exact filter_mem_split (fun ev => ev.targetTick == T)
      ((gSimWorld groups actTick groupOrd withinOrd pos T).events)
      (finalEventOf gi ci) (h_mem_finals gi ci h_gi h_ci) (by
        dsimp [finalEventOf, stageEvent]
        rw [stageTarget_final_eq_T groups actTick T gi ci h_gi h_ci
          h_uniform h_act]
        exact nat_beq_self T)
  let finalIdx : Nat → Nat → Nat := fun gi ci =>
    if h : gi < groups.length ∧ ci < (groupAt groups gi).length then
      (Classical.choose (h_split_exists gi ci h.1 h.2)).length
    else 0
  have h_pos : ∀ gi ci, gi < groups.length →
      ci < (groupAt groups gi).length →
      ∃ pre post, finals = pre ++ finalEventOf gi ci :: post ∧
        pre.length = finalIdx gi ci := by
    intro gi ci h_gi h_ci
    set pre := Classical.choose (h_split_exists gi ci h_gi h_ci)
    obtain ⟨post, h_split⟩ := Classical.choose_spec
      (h_split_exists gi ci h_gi h_ci)
    refine ⟨pre, post, h_split, ?_⟩
    dsimp [finalIdx, pre]
    rw [dif_pos ⟨h_gi, h_ci⟩]
  -- chainOf is consistent with finalEventOf
  have h_chainOf_eq : ∀ ev ∈ finals,
      ev = finalEventOf (chainOf ev).1 (chainOf ev).2 :=
    fun ev h_ev => (h_chainOf_spec ev (h_exists_pred ev h_ev)).2.2
  have h_eq_chainOf : ∀ gi ci, gi < groups.length →
      ci < (groupAt groups gi).length → finalEventOf gi ci ∈ finals →
      chainOf (finalEventOf gi ci) = (gi, ci) := by
    intro gi ci h_gi h_ci _
    have h_ex : ∃ p, chainOfPred (finalEventOf gi ci) p :=
      ⟨⟨gi, ci⟩, h_gi, h_ci, rfl⟩
    obtain ⟨h_p_gi, h_p_ci, h_p_eq⟩ :=
      h_chainOf_spec (finalEventOf gi ci) h_ex
    dsimp [finalEventOf] at h_p_eq
    have h_inj := stageEvent_injective actTick groups gi ci
      ((chainAt groups gi ci).middleDelays.length + 1)
      (chainOf (finalEventOf gi ci)).1 (chainOf (finalEventOf gi ci)).2
      ((chainAt groups (chainOf (finalEventOf gi ci)).1
          (chainOf (finalEventOf gi ci)).2).middleDelays.length + 1)
      h_gi h_ci h_p_gi h_p_ci (by omega) (by omega) h_p_eq
    exact Prod.ext h_inj.1.symm h_inj.2.1.symm
  refine ⟨blocks, finals, finalEventOf, chainOf, finalIdx, entryOf,
    h_shape, h_no_early, ?_, h_nd, ?_, h_block, h_entry_match, h_chainOf_eq,
    h_eq_chainOf, h_pos⟩
  · rfl
  · intro gi ci
    rfl
