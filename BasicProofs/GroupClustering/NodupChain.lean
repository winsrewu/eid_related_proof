import BasicProofs.GroupClustering.ConverseSpawn
import BasicProofs.GroupClustering.StageEventNodup
import BasicProofs.GroupClustering.OrderPreservationPremises
import BasicProofs.GroupClustering.QSideOrder

set_option linter.unusedVariables false

open BasicRedstoneSim List

/-! # Group clustering — the Nodup chain

This file proves that the event queue of `gSimWorld` is duplicate-free
at every tick start. The due-filter of `popQueueWorld` is then also
duplicate-free. This discharges the `h_nodup` premise of
`sameSpec_orderPreservation` (QSideOrder).

## Method

The proof runs by induction over the ticks of `gSimFoldl`. At each
tick start, QueueMembership gives the stage-window characterization of the
queue. Within one tick (burst phase, then drain), a stronger
characterization is carried:

* `StageCharOk t S ev` — the event is a stage event of a valid chain,
  and one of three cases holds: the stage window at `t` holds, or the
  event is a stage-0 event of a group in `S` activated at `t`, or the
  event is the spawn of a stage popped at `t`.
* `NoSpawnDue w` — for every due stage event in the queue, its
  successor event is not in the queue.
* `TickQueueOk w S` — the queue is Nodup, every event satisfies
  `StageCharOk`, and `NoSpawnDue` holds.

The drain step splits the result queue into survivors and spawns via
`World.popSeqWorldFuel_filter_split` and `drain_due_filter`, then uses
`popSpawnAcc_nodup` (ConverseSpawn) for the spawn part.
-/

/-! ## List helpers -/

/-- Filtering a duplicate-free list keeps it duplicate-free. -/
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

/-- A filter keeps a list unchanged when the predicate holds at every
    element. -/
private theorem filter_eq_self_of_forall'' {α : Type} (p : α → Bool)
    (l : List α) (h : ∀ x ∈ l, p x = true) : l.filter p = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have h_x := h x (List.mem_cons.mpr (Or.inl rfl))
    simp [h_x, ih (fun y hy => h y (List.mem_cons.mpr (Or.inr hy)))]

/-- Appending two singletons to the same list gives equal results only
    when the elements are equal. -/
private theorem append_singleton_cancel {α : Type} (l : List α) (a b : α)
    (h : l ++ [a] = l ++ [b]) : a = b := by
  induction l generalizing a b with
  | nil => simpa using h
  | cons x l ih =>
    apply ih
    injection h

/-- In a duplicate-free list, the element at index `i` is not in the
    list with index `i` erased. -/
private theorem nodup_getElem_not_mem_eraseIdx {α : Type} :
    ∀ (l : List α), l.Nodup → ∀ (i : Nat) (h_i : i < l.length) (a : α),
      l[i]'h_i = a → a ∉ l.eraseIdx i := by
  intro l
  induction l with
  | nil => intro h_nd i h_i; cases h_i
  | cons x l ih =>
    intro h_nd i h_i a h_get h_mem
    rw [List.nodup_cons] at h_nd
    cases i with
    | zero =>
      dsimp [List.eraseIdx] at h_mem
      have h_x : x = a := by
        dsimp at h_get
        exact h_get
      exact h_nd.1 (h_x ▸ h_mem)
    | succ i' =>
      have h_i' : i' < l.length := by simpa using h_i
      dsimp [List.eraseIdx] at h_mem
      dsimp only [List.getElem_cons_succ] at h_get
      rw [List.mem_cons] at h_mem
      rcases h_mem with h_eq | h_mem
      · have hxl : x = l[i'] := h_eq.symm.trans h_get.symm
        exact h_nd.1 (hxl.symm ▸ List.getElem_mem h_i')
      · exact ih h_nd.2 i' h_i' a h_get h_mem

/-- In a duplicate-free append, no element of the right part is in the
    left part. -/
private theorem nodup_append_left_disjoint {α : Type} {l₁ l₂ : List α}
    (h : (l₁ ++ l₂).Nodup) : ∀ x ∈ l₂, x ∉ l₁ := by
  induction l₁ generalizing l₂ with
  | nil => intro x _ h_mem; cases h_mem
  | cons a l ih =>
    rw [List.cons_append, List.nodup_cons] at h
    intro x h_x h_mem
    rw [List.mem_cons] at h_mem
    rcases h_mem with rfl | h_mem
    · exact h.1 (List.mem_append.mpr (Or.inr h_x))
    · exact ih h.2 x h_x h_mem

/-- The right part of a duplicate-free append is duplicate-free. -/
private theorem nodup_append_right' {α : Type} {l₁ l₂ : List α}
    (h : (l₁ ++ l₂).Nodup) : l₂.Nodup := by
  induction l₁ with
  | nil => simpa using h
  | cons a l ih =>
    rw [List.cons_append, List.nodup_cons] at h
    exact ih h.2

/-- The first components of `zipIdx` are the original list. -/
private theorem map_fst_zipIdx {α : Type} (l : List α) :
    (l.zipIdx.map Prod.fst : List α) = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.zipIdx]

/-- A map that builds events with distinct node ids keeps a
    duplicate-free list duplicate-free. -/
private theorem nodup_event_map (t : Nat) (l : List Nat) (h : l.Nodup) :
    (l.map (fun nid =>
      ({ targetTick := t, priority := (0 : Int), nodeId := nid } :
        ScheduledEvent))).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at h
    simp only [List.map_cons]
    rw [List.nodup_cons]
    refine ⟨?_, ih h.2⟩
    intro h_mem
    rcases List.mem_map.mp h_mem with ⟨nid, h_nid, h_eq⟩
    have h_node := congr_arg ScheduledEvent.nodeId h_eq
    dsimp at h_node
    exact h.1 (h_node ▸ h_nid)

/-! ## Within-tick queue characterization -/

/-- An event passes the within-tick characterization at tick `t` with
    activated-group list `S`. The event is a stage event of a valid
    chain. One of three cases holds: the stage window at `t` holds, or
    the event is a stage-0 event of a group in `S` activated at `t`,
    or the event is the spawn of a stage event popped at `t`. -/
def StageCharOk (groups : List GroupSpec) (actTick : Nat → Nat)
    (t : Nat) (S : List Nat) (ev : ScheduledEvent) : Prop :=
  ∃ gi ci j, gi < groups.length ∧ ci < (groupAt groups gi).length ∧
    j ≤ (chainAt groups gi ci).middleDelays.length + 1 ∧
    ev = stageEvent actTick groups gi ci j ∧
    (stageWindow actTick groups gi ci j t ∨
     (j = 0 ∧ actTick gi = t ∧ gi ∈ S) ∨
     (1 ≤ j ∧ stageTarget actTick groups gi ci (j - 1) = t))

/-- For every due stage event in the queue, its successor event is not
    in the queue. -/
def NoSpawnDue (groups : List GroupSpec) (actTick : Nat → Nat)
    (w : World) : Prop :=
  ∀ gi ci j, gi < groups.length → ci < (groupAt groups gi).length →
    j ≤ (chainAt groups gi ci).middleDelays.length →
    stageTarget actTick groups gi ci j = w.tick →
    stageEvent actTick groups gi ci j ∈ w.events →
    stageEvent actTick groups gi ci (j + 1) ∉ w.events

/-- The within-tick queue invariant: duplicate-free, all events pass
    the characterization, and no spawn of a due event is present. -/
def TickQueueOk (groups : List GroupSpec) (actTick : Nat → Nat)
    (w : World) (S : List Nat) : Prop :=
  w.events.Nodup ∧
  (∀ ev ∈ w.events, StageCharOk groups actTick w.tick S ev) ∧
  NoSpawnDue groups actTick w

/-- Growing the activated-group list preserves the characterization. -/
private theorem stageCharOk_mono (groups : List GroupSpec)
    (actTick : Nat → Nat) (t : Nat) (S S' : List Nat)
    (ev : ScheduledEvent)
    (h_sub : ∀ gi ∈ S, gi ∈ S') :
    StageCharOk groups actTick t S ev →
    StageCharOk groups actTick t S' ev := by
  rintro ⟨gi, ci, j, h_gi, h_ci, h_j, h_ev, h_disj⟩
  refine ⟨gi, ci, j, h_gi, h_ci, h_j, h_ev, ?_⟩
  rcases h_disj with h_win | h_fresh | h_spawn
  · exact Or.inl h_win
  · exact Or.inr (Or.inl ⟨h_fresh.1, h_fresh.2.1,
      h_sub gi h_fresh.2.2⟩)
  · exact Or.inr (Or.inr h_spawn)

/-! ## A due event in a characterized queue carries the stage window -/

/-- An event of a characterized queue whose target is the current tick
    satisfies the stage window, and its stage targets the tick. -/
private theorem char_due_is_window (groups : List GroupSpec)
    (actTick : Nat → Nat) (t : Nat) (S : List Nat)
    (ev : ScheduledEvent) (gi ci j : Nat)
    (h_gi : gi < groups.length) (h_ci : ci < (groupAt groups gi).length)
    (h_j : j ≤ (chainAt groups gi ci).middleDelays.length + 1)
    (h_ev : ev = stageEvent actTick groups gi ci j)
    (h_disj : stageWindow actTick groups gi ci j t ∨
      (j = 0 ∧ actTick gi = t ∧ gi ∈ S) ∨
      (1 ≤ j ∧ stageTarget actTick groups gi ci (j - 1) = t))
    (h_due : ev.targetTick = t) :
    stageWindow actTick groups gi ci j t ∧
    stageTarget actTick groups gi ci j = t := by
  have h_tgt : stageTarget actTick groups gi ci j = t := by
    rw [h_ev] at h_due
    dsimp [stageEvent] at h_due
    exact h_due
  refine ⟨?_, h_tgt⟩
  rcases h_disj with h_win | h_fresh | h_spawn
  · exact h_win
  · rcases h_fresh with ⟨h_j0, h_act, _⟩
    subst h_j0
    dsimp [stageTarget] at h_tgt
    rw [stageCumDelay_zero, h_act] at h_tgt
    omega
  · rcases h_spawn with ⟨h_jge, h_prev⟩
    have h_lt := stageTarget_lt_succ actTick groups gi ci (j - 1)
      (by omega)
    have h_conv : (j - 1) + 1 = j := by omega
    rw [h_conv] at h_lt
    omega

/-! ## Observer-list helpers -/

/-- Observer id at index `ci` of group `gi`. -/
private def obsAtIdx' (obsAll : List (List Nat)) (gi ci : Nat) :
    Option Nat :=
  (obsAll[gi]?.getD [])[ci]?

/-- Every element of the observer fold comes from an index of the
    firing-order list. -/
private theorem mem_foldl_observers' (obsAll : List (List Nat))
    (wi : List Nat) (gi oid : Nat) :
    ∀ (acc : List Nat),
      (∀ oid' ∈ acc, ∃ ci, some oid' = obsAtIdx' obsAll gi ci) →
      oid ∈ wi.foldl (fun acc' ci' =>
        match obsAtIdx' obsAll gi ci' with
        | some o => acc' ++ [o]
        | none => acc') acc →
      ∃ ci, some oid = obsAtIdx' obsAll gi ci := by
  revert oid
  induction wi with
  | nil =>
    intro oid acc h_acc h_mem
    exact h_acc oid (by simpa using h_mem)
  | cons hd tl ih =>
    intro oid acc h_acc h_mem
    simp only [List.foldl_cons] at h_mem
    split at h_mem
    · rename_i o h_split
      apply ih oid (acc ++ [o])
      · intro oid' h_oid'
        rw [List.mem_append] at h_oid'
        rcases h_oid' with h_oid' | h_oid'
        · exact h_acc oid' h_oid'
        · have h_eq : oid' = o := by simpa using h_oid'
          subst h_eq
          exact ⟨hd, h_split.symm⟩
      · exact h_mem
    · exact ih oid acc h_acc h_mem

/-- Two observer indices that give the same observer id are equal. -/
private theorem obsAtIdx_inj (groups : List GroupSpec)
    (gi ci₁ ci₂ o₁ o₂ : Nat)
    (h₁ : obsAtIdx' (buildGroups groups).2 gi ci₁ = some o₁)
    (h₂ : obsAtIdx' (buildGroups groups).2 gi ci₂ = some o₂)
    (h_eq : o₁ = o₂) : ci₁ = ci₂ := by
  have h_gi : gi < groups.length := by
    by_contra h_ge
    have h_none : (buildGroups groups).2[gi]? = none :=
      List.getElem?_eq_none (by
        rw [buildGroups_snd_length]
        omega)
    dsimp [obsAtIdx'] at h₁
    rw [h_none] at h₁
    cases h₁
  have h_len₁ : ci₁ < (groupAt groups gi).length := by
    have h_raw : ci₁ < ((buildGroups groups).2[gi]?.getD []).length := by
      by_contra h_ge
      have h_none : ((buildGroups groups).2[gi]?.getD [])[ci₁]? = none :=
        List.getElem?_eq_none (by omega)
      dsimp [obsAtIdx'] at h₁
      rw [h_none] at h₁
      cases h₁
    rwa [← buildGroups_obs_length]
  have h_len₂ : ci₂ < (groupAt groups gi).length := by
    have h_raw : ci₂ < ((buildGroups groups).2[gi]?.getD []).length := by
      by_contra h_ge
      have h_none : ((buildGroups groups).2[gi]?.getD [])[ci₂]? = none :=
        List.getElem?_eq_none (by omega)
      dsimp [obsAtIdx'] at h₂
      rw [h_none] at h₂
      cases h₂
    rwa [← buildGroups_obs_length]
  dsimp [obsAtIdx'] at h₁ h₂
  have h_o₁ := buildGroups_snd_getElem_getElem? groups gi ci₁ h_gi h_len₁
  have h_o₂ := buildGroups_snd_getElem_getElem? groups gi ci₂ h_gi h_len₂
  rw [h₁] at h_o₁
  rw [h₂] at h_o₂
  injection h_o₁ with h₁'
  injection h_o₂ with h₂'
  subst h_eq
  have h_base : chainBaseId groups gi ci₁ = chainBaseId groups gi ci₂ := by
    omega
  -- the chain base id is strictly monotone in the chain index
  by_contra h_ne
  have h_ord : ci₁ < ci₂ ∨ ci₂ < ci₁ := by omega
  rcases h_ord with h_lt | h_lt
  · have h_le := chainBaseId_interval_le groups gi ci₁ gi ci₂ h_gi h_len₁
      h_gi h_len₂ (Or.inr ⟨rfl, h_lt⟩)
    have h_cnt : chainNodeCount (chainAt groups gi ci₁) =
        (chainAt groups gi ci₁).middleDelays.length + 4 := rfl
    omega
  · have h_le := chainBaseId_interval_le groups gi ci₂ gi ci₁ h_gi h_len₂
      h_gi h_len₁ (Or.inr ⟨rfl, h_lt⟩)
    have h_cnt : chainNodeCount (chainAt groups gi ci₂) =
        (chainAt groups gi ci₂).middleDelays.length + 4 := rfl
    omega

/-- Every element of the ordered-observer fold is the observer id of a
    valid chain of the group. -/
private theorem ordered_observers_char (groups : List GroupSpec)
    (withinOrd : Nat → List Nat) (gi oid : Nat)
    (h_oid : oid ∈ (withinOrd gi).foldl (fun acc ci =>
      match obsAtIdx' (buildGroups groups).2 gi ci with
      | some o => acc ++ [o]
      | none => acc) []) :
    ∃ ci, ci < (groupAt groups gi).length ∧
      oid = chainBaseId groups gi ci + 1 := by
  obtain ⟨ci, h_ci⟩ := mem_foldl_observers' (buildGroups groups).2
    (withinOrd gi) gi oid [] (by simp) h_oid
  have h_gi : gi < groups.length := by
    by_contra h_ge
    have h_none : (buildGroups groups).2[gi]? = none :=
      List.getElem?_eq_none (by
        rw [buildGroups_snd_length]
        omega)
    dsimp [obsAtIdx'] at h_ci
    rw [h_none] at h_ci
    cases h_ci
  have h_len : ci < (groupAt groups gi).length := by
    have h_raw : ci < ((buildGroups groups).2[gi]?.getD []).length := by
      by_contra h_ge
      have h_none : ((buildGroups groups).2[gi]?.getD [])[ci]? = none :=
        List.getElem?_eq_none (by omega)
      dsimp [obsAtIdx'] at h_ci
      rw [h_none] at h_ci
      cases h_ci
    rwa [← buildGroups_obs_length]
  dsimp [obsAtIdx'] at h_ci
  have h_official := buildGroups_snd_getElem_getElem? groups gi ci h_gi h_len
  rw [← h_ci] at h_official
  injection h_official with h_oid_eq
  exact ⟨ci, h_len, h_oid_eq⟩

/-- The ordered-observer fold is duplicate-free when the firing order
    is duplicate-free. -/
private theorem ordered_observers_nodup (groups : List GroupSpec)
    (withinOrd : Nat → List Nat) (gi : Nat)
    (h_nd : (withinOrd gi).Nodup) :
    ((withinOrd gi).foldl (fun acc ci =>
      match obsAtIdx' (buildGroups groups).2 gi ci with
      | some o => acc ++ [o]
      | none => acc) []).Nodup := by
  have h_gen : ∀ (l : List Nat) (acc : List Nat),
      l.Nodup → acc.Nodup →
      (∀ oid ∈ acc, ∃ ci, some oid = obsAtIdx' (buildGroups groups).2 gi ci ∧
        ci ∉ l) →
      (l.foldl (fun acc' ci' =>
        match obsAtIdx' (buildGroups groups).2 gi ci' with
        | some o => acc' ++ [o]
        | none => acc') acc).Nodup := by
    intro l
    induction l with
    | nil =>
      intro acc _ h_acc_nd _
      simpa
    | cons hd tl ih =>
      intro acc h_l_nd h_acc_nd h_fresh
      simp only [List.foldl_cons]
      have h_nd_tl : tl.Nodup := by
        rw [List.nodup_cons] at h_l_nd; exact h_l_nd.2
      have h_hd_not : hd ∉ tl := by
        rw [List.nodup_cons] at h_l_nd; exact h_l_nd.1
      cases h_hd_case : obsAtIdx' (buildGroups groups).2 gi hd with
      | none =>
        simp
        have h_fresh_tl : ∀ oid ∈ acc, ∃ ci,
            some oid = obsAtIdx' (buildGroups groups).2 gi ci ∧ ci ∉ tl := by
          intro oid h_oid
          obtain ⟨ci, h_ci, h_not⟩ := h_fresh oid h_oid
          exact ⟨ci, h_ci, fun h' => h_not (List.mem_cons.mpr (Or.inr h'))⟩
        exact ih acc h_nd_tl h_acc_nd h_fresh_tl
      | some o =>
        simp
        apply ih (acc ++ [o])
        · exact h_nd_tl
        · apply nodup_append_of_disjoint h_acc_nd
          · rw [List.nodup_cons]; simp
          · intro x hx
            have h_x : x = o := by simpa using hx
            rw [h_x]
            intro h_o
            obtain ⟨ci, h_ci, h_not⟩ := h_fresh o h_o
            have h_inj := obsAtIdx_inj groups gi ci hd o o
              (by simpa using h_ci.symm) h_hd_case rfl
            have h_ci_mem : ci ∈ hd :: tl := by
              rw [h_inj]
              exact List.mem_cons.mpr (Or.inl rfl)
            exact h_not h_ci_mem
        · intro oid h_oid
          rw [List.mem_append] at h_oid
          rcases h_oid with h_oid | h_oid
          · obtain ⟨ci, h_ci, h_not⟩ := h_fresh oid h_oid
            exact ⟨ci, h_ci, fun h' => h_not (List.mem_cons.mpr (Or.inr h'))⟩
          · have h_eq : oid = o := by simpa using h_oid
            subst h_eq
            exact ⟨hd, h_hd_case.symm, h_hd_not⟩
  exact h_gen (withinOrd gi) [] h_nd List.nodup_nil (by simp)

/-! ## Popped-event classification -/

/-- An event popped within `fuel` steps from a characterized queue is
    a due stage event carrying the stage window. -/
private theorem popSeqFuel_spawn_shape (groups : List GroupSpec)
    (actTick : Nat → Nat) (w : World) (fuel : Nat) (S : List Nat)
    (h_char : ∀ ev ∈ w.events, StageCharOk groups actTick w.tick S ev)
    (ev : ScheduledEvent) (h_ev : ev ∈ World.popSeqFuel w fuel) :
    ∃ gi ci j, gi < groups.length ∧ ci < (groupAt groups gi).length ∧
      stageWindow actTick groups gi ci j w.tick ∧
      stageTarget actTick groups gi ci j = w.tick ∧
      ev = stageEvent actTick groups gi ci j ∧
      j ≤ (chainAt groups gi ci).middleDelays.length + 1 := by
  obtain ⟨gi, ci, j, h_gi, h_ci, h_j, h_ev_eq, h_disj⟩ :=
    h_char ev (World.mem_popSeqFuel_mem_events w fuel ev h_ev)
  have h_due : ev.targetTick = w.tick :=
    World.mem_popSeqFuel_due w fuel ev h_ev
  obtain ⟨h_win, h_tgt⟩ := char_due_is_window groups actTick w.tick S ev
    gi ci j h_gi h_ci h_j h_ev_eq h_disj h_due
  exact ⟨gi, ci, j, h_gi, h_ci, h_win, h_tgt, h_ev_eq, h_j⟩

/-- A singleton spawn of a popped event is the successor stage event
    of that event. The popped event is due and not at the last
    stage. -/
private theorem popSeqFuel_singleton_spawn_eq (groups : List GroupSpec)
    (actTick : Nat → Nat) (w : World) (fuel : Nat) (S : List Nat)
    (h_layout : NodeLayoutOk groups w)
    (h_char : ∀ ev ∈ w.events, StageCharOk groups actTick w.tick S ev)
    (ev : ScheduledEvent) (h_ev : ev ∈ World.popSeqFuel w fuel)
    (v : World) (s : ScheduledEvent)
    (h_v_tick : v.tick = w.tick) (h_v_layout : NodeLayoutOk groups v)
    (h_sp : (v.onScheduledTick ev.nodeId).events = v.events ++ [s]) :
    ∃ gi ci j, gi < groups.length ∧ ci < (groupAt groups gi).length ∧
      j ≤ (chainAt groups gi ci).middleDelays.length ∧
      stageTarget actTick groups gi ci j = w.tick ∧
      ev = stageEvent actTick groups gi ci j ∧
      s = stageEvent actTick groups gi ci (j + 1) := by
  obtain ⟨gi, ci, j, h_gi, h_ci, _, h_tgt, h_ev_eq, h_j⟩ :=
    popSeqFuel_spawn_shape groups actTick w fuel S h_char ev h_ev
  by_cases h_jm : j ≤ (chainAt groups gi ci).middleDelays.length
  · refine ⟨gi, ci, j, h_gi, h_ci, h_jm, h_tgt, h_ev_eq, ?_⟩
    have h_tick_v : v.tick = stageTarget actTick groups gi ci j := by
      rw [h_v_tick]; exact h_tgt.symm
    have h_sp' := stage_spawn groups actTick v gi ci j h_gi h_ci h_jm
      h_tick_v h_v_layout
    have h_node : ev.nodeId = chainBaseId groups gi ci + 1 + j := by
      rw [h_ev_eq]
      dsimp [stageEvent]
    rw [← h_node] at h_sp'
    rw [h_sp] at h_sp'
    exact append_singleton_cancel v.events s
      (stageEvent actTick groups gi ci (j + 1)) h_sp'
  · have h_jm1 : j = (chainAt groups gi ci).middleDelays.length + 1 := by
      omega
    have h_nil := lastStage_spawn_nil groups actTick v gi ci h_gi h_ci
      h_v_layout
    have h_node : ev.nodeId = (stageEvent actTick groups gi ci
        ((chainAt groups gi ci).middleDelays.length + 1)).nodeId := by
      rw [h_ev_eq, h_jm1]
    have h_contra : v.events ++ [s] = v.events := by
      rw [← h_sp]
      rw [h_node]
      exact h_nil
    have h_len := congrArg List.length h_contra
    simp only [List.length_append, List.length_singleton] at h_len
    omega

/-! ## `processNEvents` preserves the within-tick invariant -/

/-- One pop-and-fire step inside a tick keeps the queue invariant. The
    popped event is a due stage event. Its successor spawn (if any) is
    fresh for the queue. -/
private theorem step_tickQueueOk (groups : List GroupSpec)
    (actTick : Nat → Nat) (w w' : World) (S : List Nat)
    (h_step : w.step = some w')
    (h_layout : NodeLayoutOk groups w)
    (h_ok : TickQueueOk groups actTick w S) :
    TickQueueOk groups actTick w' S := by
  rcases h_ok with ⟨h_nd, h_char, h_nospawn⟩
  dsimp [World.step] at h_step
  cases h_pop : w.popNextEvent with
  | none =>
    simp only [h_pop] at h_step
    cases h_step
  | some p =>
    rcases p with ⟨ev₀, w_pop⟩
    simp only [h_pop] at h_step
    injection h_step with h_w'_eq
    obtain ⟨idx, h_idx, h_erase, h_tick₀, h_mem₀, h_get⟩ :=
      World.popNextEvent_eraseIdx w ev₀ w_pop h_pop
    have h_tick_pop : w_pop.tick = w.tick :=
      World.popNextEvent_tick w ev₀ w_pop h_pop
    have h_layout_pop : NodeLayoutOk groups w_pop :=
      NodeLayoutOk_of_nodes_eq groups w w_pop
        (World.popNextEvent_nodes w ev₀ w_pop h_pop) h_layout
    -- classify the popped event
    obtain ⟨gi, ci, j, h_gi, h_ci, h_win, h_due, h_ev₀, h_j⟩ :=
      popSeqFuel_spawn_shape groups actTick w 1 S h_char ev₀ (by
        rw [World.popSeqFuel, h_pop]
        exact List.mem_cons.mpr (Or.inl rfl))
    have h_nd_pop : w_pop.events.Nodup := by
      rw [h_erase]
      exact nodup_eraseIdx w.events idx h_nd
    have h_char_pop : ∀ ev ∈ w_pop.events,
        StageCharOk groups actTick w_pop.tick S ev := by
      intro ev h_ev
      rw [h_tick_pop]
      exact h_char ev (List.mem_of_mem_eraseIdx (h_erase ▸ h_ev))
    have h_nospawn_pop : NoSpawnDue groups actTick w_pop := by
      intro gi' ci' j' h_g' h_c' h_jm' h_tgt' h_mem' h_sp'
      rw [h_tick_pop] at h_tgt'
      have h_mem_w : stageEvent actTick groups gi' ci' j' ∈ w.events :=
        List.mem_of_mem_eraseIdx (h_erase ▸ h_mem')
      have h_sp_w : stageEvent actTick groups gi' ci' (j' + 1) ∈
          w.events :=
        List.mem_of_mem_eraseIdx (h_erase ▸ h_sp')
      exact h_nospawn gi' ci' j' h_g' h_c' h_jm' h_tgt' h_mem_w h_sp_w
    by_cases h_jm : j ≤ (chainAt groups gi ci).middleDelays.length
    · -- the pop appends the successor stage event
      set sp := stageEvent actTick groups gi ci (j + 1)
      have h_events_w' : w'.events = w_pop.events ++ [sp] := by
        rw [← h_w'_eq]
        have h_tick_sp : w_pop.tick =
            stageTarget actTick groups gi ci j := by
          rw [h_tick_pop]; exact h_due.symm
        have h_sp := stage_spawn groups actTick w_pop gi ci j h_gi
          h_ci h_jm h_tick_sp h_layout_pop
        have h_node : ev₀.nodeId = chainBaseId groups gi ci + 1 + j := by
          rw [h_ev₀]
          dsimp [stageEvent]
        rw [h_node, h_sp]
      have h_sp_fresh : sp ∉ w_pop.events := by
        intro h_mem
        have h_mem_w : sp ∈ w.events :=
          List.mem_of_mem_eraseIdx (h_erase ▸ h_mem)
        -- sp is the successor of the due event ev₀ = stageEvent gi ci j,
        -- which lies in w.events; NoSpawnDue rules sp out.
        have h_parent_mem : stageEvent actTick groups gi ci j ∈ w.events :=
          h_ev₀ ▸ h_mem₀
        have h_contra := h_nospawn gi ci j h_gi h_ci h_jm h_due h_parent_mem
        exact h_contra h_mem_w
      refine ⟨?_, ?_, ?_⟩
      · -- Nodup
        rw [h_events_w']
        exact nodup_append_of_disjoint h_nd_pop (by simp)
          (fun x hx => by
            have h_x : x = sp := by simpa using hx
            subst h_x
            exact h_sp_fresh)
      · -- characterization
        have h_tick_w' : w'.tick = w.tick := by
          rw [← h_w'_eq, World.onScheduledTick_tick, h_tick_pop]
        rw [h_tick_w', ← h_tick_pop]
        intro ev h_ev
        rw [h_events_w', List.mem_append] at h_ev
        rcases h_ev with h_ev | h_ev
        · exact h_char_pop ev h_ev
        · have h_eq : ev = sp := by simpa using h_ev
          subst h_eq
          refine ⟨gi, ci, j + 1, h_gi, h_ci, by omega, rfl,
            Or.inr (Or.inr ⟨by omega, ?_⟩)⟩
          rw [Nat.add_sub_cancel]
          exact h_due.trans h_tick_pop.symm
      · -- NoSpawnDue after the append
        have h_tick_w' : w'.tick = w.tick := by
          rw [← h_w'_eq, World.onScheduledTick_tick, h_tick_pop]
        dsimp [NoSpawnDue]
        rw [h_tick_w']
        intro gi' ci' j' h_g' h_c' h_jm' h_tgt' h_mem' h_sp_mem
        rw [← h_tick_pop] at h_tgt'
        rw [h_events_w', List.mem_append] at h_mem'
        rcases h_mem' with h_mem' | h_mem'
        · rw [h_events_w', List.mem_append] at h_sp_mem
          rcases h_sp_mem with h_sp_pop | h_sp_eq'
          · exact h_nospawn_pop gi' ci' j' h_g' h_c' h_jm' h_tgt'
              h_mem' h_sp_pop
          · -- the successor equals the new spawn sp: the parent is ev₀
            have h_sp_eq : stageEvent actTick groups gi' ci' (j' + 1) =
                stageEvent actTick groups gi ci (j + 1) := by
              simpa [sp] using h_sp_eq'
            have h_inj := stageEvent_injective actTick groups gi' ci'
              (j' + 1) gi ci (j + 1) h_g' h_c' h_gi h_ci
              (by omega) (by omega) h_sp_eq
            obtain ⟨h_g_eq, h_c_eq, h_j_eq⟩ := h_inj
            have h_j_eq' : j' = j := by omega
            rw [h_g_eq, h_c_eq, h_j_eq'] at h_mem'
            rw [← h_ev₀] at h_mem'
            have h_ev₀_not : ev₀ ∉ w_pop.events := by
              rw [h_erase]
              exact nodup_getElem_not_mem_eraseIdx w.events h_nd idx
                h_idx ev₀ h_get
            exact h_ev₀_not h_mem'
        · -- the due event is the new spawn sp: target arithmetic fails
          have h_mem_eq : stageEvent actTick groups gi' ci' j' =
              stageEvent actTick groups gi ci (j + 1) := by
            simpa [sp] using h_mem'
          have h_inj := stageEvent_injective actTick groups gi' ci' j'
            gi ci (j + 1) h_g' h_c' h_gi h_ci (by omega) (by omega)
            h_mem_eq
          obtain ⟨h_g_eq, h_c_eq, h_j_eq⟩ := h_inj
          rw [h_g_eq, h_c_eq, h_j_eq] at h_tgt'
          have h_lt := stageTarget_lt_succ actTick groups gi ci j h_jm
          omega
    · -- stage m + 1: the pop appends nothing
      have h_jm1 : j = (chainAt groups gi ci).middleDelays.length + 1 :=
        by omega
      have h_events_w' : w'.events = w_pop.events := by
        rw [← h_w'_eq]
        have h_node : ev₀.nodeId = (stageEvent actTick groups gi ci
            ((chainAt groups gi ci).middleDelays.length + 1)).nodeId := by
          rw [h_ev₀, h_jm1]
        rw [h_node, lastStage_spawn_nil groups actTick w_pop gi ci h_gi
          h_ci h_layout_pop]
      have h_tick_w' : w'.tick = w.tick := by
        rw [← h_w'_eq, World.onScheduledTick_tick, h_tick_pop]
      refine ⟨?_, ?_, ?_⟩
      · rw [h_events_w']; exact h_nd_pop
      · intro ev h_ev
        have h_ev_pop : ev ∈ w_pop.events := by
          rwa [h_events_w'] at h_ev
        rw [h_tick_w', ← h_tick_pop]
        exact h_char_pop ev h_ev_pop
      · dsimp [NoSpawnDue]
        rw [h_tick_w']
        intro gi' ci' j' h_g' h_c' h_jm' h_tgt' h_mem' h_sp_mem
        rw [← h_tick_pop] at h_tgt'
        rw [h_events_w'] at h_mem' h_sp_mem
        exact h_nospawn_pop gi' ci' j' h_g' h_c' h_jm' h_tgt' h_mem'
          h_sp_mem

/-- `processNEvents` preserves the queue invariant at every fuel
    level. -/
theorem processNEvents_tickQueueOk (groups : List GroupSpec)
    (actTick : Nat → Nat) (w : World) (n : Nat) (S : List Nat)
    (h_layout : NodeLayoutOk groups w)
    (h_ok : TickQueueOk groups actTick w S) :
    TickQueueOk groups actTick (processNEvents w n) S ∧
    NodeLayoutOk groups (processNEvents w n) := by
  induction n generalizing w h_layout h_ok with
  | zero => simpa [processNEvents] using ⟨h_ok, h_layout⟩
  | succ n' ih =>
    simp only [processNEvents]
    cases h_step : w.step with
    | none => exact ⟨h_ok, h_layout⟩
    | some w' =>
      have h_ok_w' : TickQueueOk groups actTick w' S :=
        step_tickQueueOk groups actTick w w' S h_step h_layout h_ok
      have h_layout_w' : NodeLayoutOk groups w' :=
        NodeLayoutOk_step groups w w' h_step h_layout
      exact ih w' h_layout_w' h_ok_w'

/-! ## `activateGroup` preserves the within-tick invariant -/

/-- Activating one group appends its stage-0 events. The appended
    events are fresh for the queue. The group joins the activated
    list `S`. -/
theorem activateGroup_tickQueueOk (groups : List GroupSpec)
    (actTick : Nat → Nat) (w : World) (S : List Nat) (gi : Nat)
    (ordered : List Nat)
    (h_layout : NodeLayoutOk groups w)
    (h_ok : TickQueueOk groups actTick w S)
    (h_gi : gi < groups.length)
    (h_act : actTick gi = w.tick)
    (h_gi_not : gi ∉ S)
    (h_obs : ∀ oid ∈ ordered, ∃ ci, ci < (groupAt groups gi).length ∧
        oid = chainBaseId groups gi ci + 1)
    (h_ord_nd : ordered.Nodup) :
    TickQueueOk groups actTick (activateGroup w ordered) (S ++ [gi]) ∧
    NodeLayoutOk groups (activateGroup w ordered) := by
  rcases h_ok with ⟨h_nd, h_char, h_nospawn⟩
  set mkEv : Nat → ScheduledEvent := fun nid =>
    { targetTick := w.tick + 2, priority := (0 : Int), nodeId := nid }
  set obsEvs := ordered.map mkEv
  have h_events : (activateGroup w ordered).events =
      w.events ++ obsEvs := by
    dsimp [obsEvs, mkEv]
    rw [activateGroup_events_map]
  have h_tick_act : (activateGroup w ordered).tick = w.tick :=
    activateGroup_tick w ordered
  -- the appended stage-0 events are fresh for the old queue
  have h_fresh : ∀ e ∈ obsEvs, e ∉ w.events := by
    intro e h_e h_mem
    rcases List.mem_map.mp h_e with ⟨nid, h_nid, h_e_eq⟩
    obtain ⟨ci, h_ci, h_nid_eq⟩ := h_obs nid h_nid
    have h_stage : mkEv nid = stageEvent actTick groups gi ci 0 := by
      dsimp [mkEv, stageEvent, stageTarget, stagePri]
      simp [h_act, stageCumDelay_zero, h_nid_eq]
    have h_mem' : stageEvent actTick groups gi ci 0 ∈ w.events := by
      rwa [← h_stage, h_e_eq]
    obtain ⟨gi', ci', j', h_g', h_c', h_j', h_ev_eq', h_disj⟩ :=
      h_char (stageEvent actTick groups gi ci 0) h_mem'
    have h_inj := stageEvent_injective actTick groups gi' ci' j' gi ci 0
      h_g' h_c' h_gi h_ci h_j' (by omega) h_ev_eq'.symm
    rcases h_inj with ⟨h_g_eq, h_c_eq, h_j_eq⟩
    subst h_g_eq; subst h_c_eq; subst h_j_eq
    rcases h_disj with h_win | h_fresh' | h_spawn
    · dsimp [stageWindow] at h_win
      omega
    · rcases h_fresh' with ⟨_, _, h_gi_mem⟩
      exact h_gi_not h_gi_mem
    · rcases h_spawn with ⟨h_jge, _⟩
      omega
  -- Nodup of the append
  have h_nd_app : (w.events ++ obsEvs).Nodup :=
    nodup_append_of_disjoint h_nd
      (by
        dsimp [obsEvs, mkEv]
        exact nodup_event_map (w.tick + 2) ordered h_ord_nd) h_fresh
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rwa [h_events]
  · -- characterization of the appended events
    rw [h_tick_act]
    intro e h_e
    rw [h_events, List.mem_append] at h_e
    rcases h_e with h_e | h_e
    · exact stageCharOk_mono groups actTick w.tick S (S ++ [gi]) e
        (fun gi' h_gi' => List.mem_append.mpr (Or.inl h_gi'))
        (h_char e h_e)
    · rcases List.mem_map.mp h_e with ⟨nid, h_nid, h_e_eq⟩
      obtain ⟨ci, h_ci, h_nid_eq⟩ := h_obs nid h_nid
      refine ⟨gi, ci, 0, h_gi, h_ci, by omega, ?_,
        Or.inr (Or.inl ⟨rfl, ?_, ?_⟩)⟩
      · rw [← h_e_eq]
        dsimp [mkEv, stageEvent, stageTarget, stagePri]
        simp [h_act, stageCumDelay_zero, h_nid_eq]
      · exact h_act
      · exact List.mem_append.mpr (Or.inr (by simp))
  · -- NoSpawnDue after the append
    dsimp [NoSpawnDue]
    rw [h_tick_act]
    intro gi' ci' j' h_g' h_c' h_jm' h_tgt' h_mem' h_sp_mem
    rw [h_events, List.mem_append] at h_mem' h_sp_mem
    rcases h_mem' with h_mem' | h_mem'
    · rcases h_sp_mem with h_sp_mem | h_sp_mem
      · exact h_nospawn gi' ci' j' h_g' h_c' h_jm' h_tgt' h_mem' h_sp_mem
      · -- the spawn is one of the appended stage-0 events
        rcases List.mem_map.mp h_sp_mem with ⟨nid, h_nid, h_eq⟩
        obtain ⟨ci₀, h_ci₀, h_nid_eq⟩ := h_obs nid h_nid
        have h_stage₀ : mkEv nid = stageEvent actTick groups gi ci₀ 0 := by
          dsimp [mkEv, stageEvent, stageTarget, stagePri]
          simp [h_act, stageCumDelay_zero, h_nid_eq]
        have h_inj := stageEvent_injective actTick groups gi' ci' (j' + 1)
          gi ci₀ 0 h_g' h_c' h_gi h_ci₀ (by omega) (by omega)
          (h_eq.symm.trans h_stage₀)
        rcases h_inj with ⟨_, _, h_j_eq⟩
        omega
    · -- the parent is one of the appended stage-0 events
      rcases List.mem_map.mp h_mem' with ⟨nid, h_nid, h_eq⟩
      obtain ⟨ci₀, h_ci₀, h_nid_eq⟩ := h_obs nid h_nid
      have h_stage₀ : mkEv nid = stageEvent actTick groups gi ci₀ 0 := by
        dsimp [mkEv, stageEvent, stageTarget, stagePri]
        simp [h_act, stageCumDelay_zero, h_nid_eq]
      have h_inj := stageEvent_injective actTick groups gi' ci' j'
        gi ci₀ 0 h_g' h_c' h_gi h_ci₀ (by omega) (by omega)
        (h_eq.symm.trans h_stage₀)
      rcases h_inj with ⟨h_g_eq, h_c_eq, h_j_eq⟩
      subst h_g_eq; subst h_c_eq; subst h_j_eq
      dsimp [stageTarget] at h_tgt'
      rw [stageCumDelay_zero, h_act] at h_tgt'
      omega
  · exact NodeLayoutOk_activateGroup groups w ordered h_layout

/-! ## The burst phase preserves the within-tick invariant -/

/-- The burst phase preserves the queue invariant. The activated
    groups accumulate in `S`. The list `S ++ pairs.map Prod.fst` must
    be duplicate-free, so no group activates twice in one tick. -/
theorem gSimBurst_tickQueueOk (groups : List GroupSpec)
    (actTick : Nat → Nat) (t : Nat) (withinOrd pos : Nat → List Nat)
    (w : World) (pairs : List (Nat × Nat)) (S : List Nat)
    (h_tick : w.tick = t)
    (h_layout : NodeLayoutOk groups w)
    (h_ok : TickQueueOk groups actTick w S)
    (h_nd_gis : (S ++ pairs.map Prod.fst).Nodup)
    (h_active : ∀ gi k, (gi, k) ∈ pairs →
      gi < groups.length ∧ actTick gi = t)
    (h_within_nd : ∀ gi, gi < groups.length → (withinOrd gi).Nodup) :
    TickQueueOk groups actTick
      (gSimBurst t (buildGroups groups).2 withinOrd pos w pairs)
      (S ++ pairs.map Prod.fst) ∧
    NodeLayoutOk groups
      (gSimBurst t (buildGroups groups).2 withinOrd pos w pairs) := by
  induction pairs generalizing w S h_tick h_layout h_ok with
  | nil =>
    simp only [gSimBurst, List.map_nil, List.append_nil]
    exact ⟨h_ok, h_layout⟩
  | cons p ps ih =>
    simp only [gSimBurst, List.foldl_cons]
    rcases p with ⟨gi, k⟩
    simp only
    set m := (pos t)[k]?.getD 0
    set ordered : List Nat := (withinOrd gi).foldl (fun acc ci =>
      match obsAtIdx' (buildGroups groups).2 gi ci with
      | some o => acc ++ [o]
      | none => acc) []
    set Wproc := processNEvents w m
    set Wact := activateGroup Wproc ordered
    have ⟨h_gi, h_act_gi⟩ := h_active gi k (by simp)
    have h_map_fst : List.map Prod.fst ((gi, k) :: ps) =
        gi :: ps.map Prod.fst := rfl
    have h_gi_not_S : gi ∉ S :=
      nodup_append_left_disjoint (h_map_fst ▸ h_nd_gis) gi (by simp)
    have h_nd_rest : (gi :: ps.map Prod.fst).Nodup :=
      nodup_append_right' (h_map_fst ▸ h_nd_gis)
    obtain ⟨h_ok_proc, h_layout_proc⟩ :=
      processNEvents_tickQueueOk groups actTick w m S h_layout h_ok
    have h_tick_proc : Wproc.tick = t := by
      dsimp [Wproc]
      rw [processNEvents_tick, h_tick]
    have h_obs_char : ∀ oid ∈ ordered, ∃ ci,
        ci < (groupAt groups gi).length ∧
        oid = chainBaseId groups gi ci + 1 :=
      fun oid h_oid => ordered_observers_char groups withinOrd gi oid h_oid
    have h_ord_nd : ordered.Nodup :=
      ordered_observers_nodup groups withinOrd gi (h_within_nd gi h_gi)
    obtain ⟨h_ok_act, h_layout_act⟩ := activateGroup_tickQueueOk groups
      actTick Wproc S gi ordered h_layout_proc h_ok_proc h_gi
      (by rw [h_tick_proc]; exact h_act_gi) h_gi_not_S h_obs_char h_ord_nd
    have h_tick_Wact : Wact.tick = t := by
      dsimp [Wact, Wproc]
      rw [activateGroup_tick, processNEvents_tick, h_tick]
    have h_nd_rest : ((S ++ [gi]) ++ ps.map Prod.fst).Nodup := by
      convert h_nd_gis using 1
      simp [List.append_assoc]
    have h_active_ps : ∀ gi' k', (gi', k') ∈ ps →
        gi' < groups.length ∧ actTick gi' = t :=
      fun gi' k' h_mem => h_active gi' k' (by simp [h_mem])
    obtain ⟨h_ih_ok, h_ih_layout⟩ := ih Wact (S ++ [gi]) h_tick_Wact
      h_layout_act h_ok_act h_nd_rest h_active_ps
    have h_S_eq : S ++ List.map Prod.fst ((gi, k) :: ps) =
        (S ++ [gi]) ++ ps.map Prod.fst := by
      simp [List.map_cons, List.append_assoc]
    refine ⟨?_, ?_⟩
    · rw [h_S_eq]
      exact h_ih_ok
    · exact h_ih_layout

/-! ## The drain step keeps the queue duplicate-free -/

/-- The drain step keeps the queue duplicate-free. The result queue is
    the survivors plus the chronological spawn accumulator. The
    survivors inherit Nodup from the input. The spawn accumulator is
    duplicate-free by `popSpawnAcc_nodup`. The two parts are disjoint
    by `NoSpawnDue`. -/
theorem stepUntilNextTick_events_nodup_of_ok (groups : List GroupSpec)
    (actTick : Nat → Nat) (w : World) (S : List Nat)
    (h_layout : NodeLayoutOk groups w)
    (h_ok : TickQueueOk groups actTick w S) :
    w.stepUntilNextTick.events.Nodup := by
  rcases h_ok with ⟨h_nd, h_char, h_nospawn⟩
  set due := w.events.filter (fun e => e.targetTick == w.tick)
  set n := due.length
  set W := processNEvents w n
  have h_drain : W.events.filter (fun ev => ev.targetTick == w.tick) =
      [] :=
    drain_due_filter w
  have h_no : ∀ ev ∈ W.events, ev.targetTick ≠ W.tick := by
    intro ev h_ev h_eq
    have h_mem : ev ∈ W.events.filter
        (fun e => e.targetTick == w.tick) := by
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
      apply filter_eq_self_of_forall''
      intro ev h_ev
      rw [decide_eq_true_eq]
      have h := h_no ev h_ev
      rwa [processNEvents_tick] at h
    rw [← h_keep]
    exact h_f
  -- every pop spawns at most one event, shaped by stage_spawn
  have h_single : ∀ ev ∈ World.popSeqFuel w n, ∀ (v : World),
      v.tick = w.tick → NodeLayoutOk groups v →
      ∃ s, (v.onScheduledTick ev.nodeId).events = v.events ++ [s] ∨
        (v.onScheduledTick ev.nodeId).events = v.events := by
    intro ev h_ev v h_v_tick h_v_layout
    obtain ⟨gi, ci, j, h_gi, h_ci, _, h_tgt, h_ev_eq, h_j⟩ :=
      popSeqFuel_spawn_shape groups actTick w n S h_char ev h_ev
    by_cases h_jm : j ≤ (chainAt groups gi ci).middleDelays.length
    · refine ⟨stageEvent actTick groups gi ci (j + 1), Or.inl ?_⟩
      have h_tick_v : v.tick = stageTarget actTick groups gi ci j := by
        rw [h_v_tick]; exact h_tgt.symm
      have h_node : ev.nodeId = chainBaseId groups gi ci + 1 + j := by
        rw [h_ev_eq]
        dsimp [stageEvent]
      rw [h_node, stage_spawn groups actTick v gi ci j h_gi h_ci h_jm
        h_tick_v h_v_layout]
    · have h_jm1 : j = (chainAt groups gi ci).middleDelays.length + 1 :=
        by omega
      refine ⟨stageEvent actTick groups gi ci 0, Or.inr ?_⟩
      have h_node : ev.nodeId = (stageEvent actTick groups gi ci
          ((chainAt groups gi ci).middleDelays.length + 1)).nodeId := by
        rw [h_ev_eq, h_jm1]
      rw [h_node, lastStage_spawn_nil groups actTick v gi ci h_gi h_ci
        h_v_layout]
  rw [h_post_events, h_split]
  apply nodup_append_of_disjoint
  · exact nodup_filter' (fun ev => ev.targetTick ≠ w.tick) w.events h_nd
  · -- the spawn accumulator is duplicate-free
    apply popSpawnAcc_nodup groups w n h_layout ?_ h_single ?_
    · exact nodup_filter' (fun ev => ev.targetTick == w.tick) w.events h_nd
    · -- distinct pops spawn distinct events
      intro ev₁ h_ev₁ ev₂ h_ev₂ h_ne v₁ v₂ h_v₁ h_v₂ h_l₁ h_l₂ s₁ s₂
        h_sp₁ h_sp₂
      obtain ⟨g₁, c₁, j₁, hg₁, hc₁, hj₁, _, hev₁, hs₁⟩ :=
        popSeqFuel_singleton_spawn_eq groups actTick w n S h_layout
          h_char ev₁ h_ev₁ v₁ s₁ h_v₁ h_l₁ h_sp₁
      obtain ⟨g₂, c₂, j₂, hg₂, hc₂, hj₂, _, hev₂, hs₂⟩ :=
        popSeqFuel_singleton_spawn_eq groups actTick w n S h_layout
          h_char ev₂ h_ev₂ v₂ s₂ h_v₂ h_l₂ h_sp₂
      rw [hs₁, hs₂]
      exact stageEvent_succ_inj_of_distinct actTick groups g₁ c₁ j₁ g₂
        c₂ j₂ hg₁ hc₁ hg₂ hc₂ hj₁ hj₂ (by
          intro h_eq
          exact h_ne (by rw [hev₁, hev₂, h_eq]))
  · -- no spawn is a survivor
    intro s h_s h_surv
    have h_surv_w : s ∈ w.events := (List.mem_filter.mp h_surv).1
    obtain ⟨ev, h_ev, v, s', h_v_tick, h_v_layout, h_sp_eq, h_s_eq⟩ :=
      mem_popSpawnAcc_singleton_spawn groups w n s h_layout h_single h_s
    obtain ⟨gi, ci, j, h_gi, h_ci, h_jm, h_tgt, h_ev_eq, h_s'_eq⟩ :=
      popSeqFuel_singleton_spawn_eq groups actTick w n S h_layout h_char
        ev h_ev v s' h_v_tick h_v_layout h_sp_eq
    have h_s_shape : s = stageEvent actTick groups gi ci (j + 1) := by
      rw [h_s_eq, h_s'_eq]
    rw [h_s_shape] at h_surv_w
    have h_parent_mem : stageEvent actTick groups gi ci j ∈ w.events :=
      h_ev_eq ▸ World.mem_popSeqFuel_mem_events w n ev h_ev
    exact h_nospawn gi ci j h_gi h_ci h_jm h_tgt h_parent_mem h_surv_w

/-! ## One simulation tick keeps the queue duplicate-free -/

/-- One `gSimBody` tick keeps the queue duplicate-free. The input queue
    has the stage-window characterization of a tick start. -/
theorem gSimBody_events_nodup (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (w : World) (i t : Nat)
    (h_tick : w.tick = t)
    (h_layout : NodeLayoutOk groups w)
    (h_nd : w.events.Nodup)
    (h_win : ∀ ev ∈ w.events, ∃ gi ci j,
      gi < groups.length ∧ ci < (groupAt groups gi).length ∧
      j ≤ (chainAt groups gi ci).middleDelays.length + 1 ∧
      ev = stageEvent actTick groups gi ci j ∧
      stageWindow actTick groups gi ci j t)
    (h_gord_nd : groupOrd.Nodup)
    (h_within_nd : ∀ gi, gi < groups.length → (withinOrd gi).Nodup) :
    (gSimBody actTick (buildGroups groups).2 groupOrd withinOrd pos w
      i).events.Nodup := by
  set w_log := w.logOutput s!"tick {w.tick}"
  set active := groupOrd.filter (fun gi =>
    decide (gi < (buildGroups groups).2.length) &&
    (actTick gi == w.tick))
  set W_B := gSimBurst w.tick (buildGroups groups).2 withinOrd pos w_log
    (active.zipIdx)
  -- the body is always burst-then-drain (an empty burst is the identity)
  have h_body : gSimBody actTick (buildGroups groups).2 groupOrd
      withinOrd pos w i = W_B.stepUntilNextTick := by
    dsimp only [gSimBody]
    simp only [World.logOutput_tick]
    change (if active == [] then w_log.stepUntilNextTick else
        (gSimBurst w.tick (buildGroups groups).2 withinOrd pos w_log
          (active.zipIdx)).stepUntilNextTick) =
      W_B.stepUntilNextTick
    dsimp [W_B]
    split_ifs with h_cond
    · have h_empty : active = [] := by simpa using h_cond
      simp [gSimBurst, h_empty]
    · rfl
  rw [h_body]
  have h_ev_log : w_log.events = w.events := by
    dsimp [w_log]
  have h_tick_log : w_log.tick = w.tick := by
    dsimp [w_log]
  have h_ok_log : TickQueueOk groups actTick w_log [] := by
    dsimp [TickQueueOk, NoSpawnDue]
    rw [h_ev_log, h_tick_log]
    refine ⟨h_nd, ?_, ?_⟩
    · intro ev h_ev
      obtain ⟨gi, ci, j, h_gi, h_ci, h_j, h_ev_eq, h_win'⟩ :=
        h_win ev h_ev
      exact ⟨gi, ci, j, h_gi, h_ci, h_j, h_ev_eq,
        Or.inl (h_tick ▸ h_win')⟩
    · intro gi ci j h_gi h_ci h_jm h_tgt h_mem h_sp
      obtain ⟨gi', ci', j', h_g', h_c', h_j', h_eq', h_win'⟩ :=
        h_win (stageEvent actTick groups gi ci (j + 1)) h_sp
      have h_inj := stageEvent_injective actTick groups gi' ci' j' gi ci
        (j + 1) h_g' h_c' h_gi h_ci h_j' (by omega) h_eq'.symm
      obtain ⟨h_g_eq, h_c_eq, h_j_eq⟩ := h_inj
      rw [h_g_eq, h_c_eq, h_j_eq] at h_win'
      dsimp [stageWindow] at h_win'
      omega
  have h_layout_log : NodeLayoutOk groups w_log :=
    NodeLayoutOk_logOutput groups w _ h_layout
  have h_active_char : ∀ gi k, (gi, k) ∈ active.zipIdx →
      gi < groups.length ∧ actTick gi = w.tick := by
    intro gi k h_mem
    have h_zip := List.mem_zipIdx h_mem
    obtain ⟨_, h_k_lt, h_gi_eq⟩ := h_zip
    have h_k_lt' : k < active.length := by simpa using h_k_lt
    have h_gi_mem : gi ∈ active := by
      have h_gi_eq' : gi = active[k] := by simpa using h_gi_eq
      rw [h_gi_eq']
      exact List.getElem_mem h_k_lt'
    dsimp [active] at h_gi_mem
    rw [List.mem_filter] at h_gi_mem
    obtain ⟨_, h_cond⟩ := h_gi_mem
    rw [Bool.and_eq_true] at h_cond
    obtain ⟨h_dec, h_beq⟩ := h_cond
    have h_gi_lt : gi < (buildGroups groups).2.length :=
      of_decide_eq_true h_dec
    have h_act_eq : actTick gi = w.tick := by
      simpa [Nat.beq_eq] using h_beq
    exact ⟨by rwa [buildGroups_snd_length] at h_gi_lt, h_act_eq⟩
  have h_nd_gis : ([] ++ active.zipIdx.map Prod.fst).Nodup := by
    rw [List.nil_append, map_fst_zipIdx]
    exact nodup_filter'
      (fun gi => decide (gi < (buildGroups groups).2.length) &&
        (actTick gi == w.tick)) groupOrd h_gord_nd
  obtain ⟨h_ok_B, h_layout_B⟩ := gSimBurst_tickQueueOk groups actTick
    w.tick withinOrd pos w_log active.zipIdx [] h_tick_log h_layout_log
    h_ok_log h_nd_gis h_active_char h_within_nd
  have h_ok_B' : TickQueueOk groups actTick W_B
      (active.zipIdx.map Prod.fst) := by
    convert h_ok_B using 1
    simp
  exact stepUntilNextTick_events_nodup_of_ok groups actTick W_B
    (active.zipIdx.map Prod.fst) h_layout_B h_ok_B'

/-! ## The main result -/

/-- The event queue of `gSimWorld` is duplicate-free at every tick
    start. The group order and every firing order must be
    duplicate-free. Otherwise two equal events are appended. -/
theorem gSimWorld_events_Nodup (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (t : Nat)
    (h_gord_nd : groupOrd.Nodup)
    (h_within_nd : ∀ gi, gi < groups.length → (withinOrd gi).Nodup) :
    (gSimWorld groups actTick groupOrd withinOrd pos t).events.Nodup := by
  dsimp [gSimWorld]
  induction t with
  | zero =>
    dsimp [gSimFoldl]
    rw [buildGroups_no_events]
    exact List.nodup_nil
  | succ t ih =>
    simp only [gSimFoldl, List.range_succ, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    set W : World := List.foldl
      (gSimBody actTick (buildGroups groups).2 groupOrd withinOrd pos)
      (buildGroups groups).1 (List.range t)
    have h_W : W = gSimWorld groups actTick groupOrd withinOrd pos t := by
      dsimp [W, gSimWorld, gSimFoldl]
    have h_tick : W.tick = t := by
      rw [h_W]
      exact gSimWorld_tick groups actTick groupOrd withinOrd pos t
    have h_nd : W.events.Nodup := by rwa [h_W]
    have h_layout : NodeLayoutOk groups W := by
      rw [h_W]
      dsimp [gSimWorld]
      exact NodeLayoutOk_gSimFoldl groups actTick (buildGroups groups).2
        groupOrd withinOrd pos (buildGroups groups).1 t
        (NodeLayoutOk_buildGroups groups)
    have h_win : ∀ ev ∈ W.events, ∃ gi ci j,
        gi < groups.length ∧ ci < (groupAt groups gi).length ∧
        j ≤ (chainAt groups gi ci).middleDelays.length + 1 ∧
        ev = stageEvent actTick groups gi ci j ∧
        stageWindow actTick groups gi ci j t := by
      intro ev h_ev
      rw [h_W] at h_ev
      exact gSimWorld_events_stageWindow groups actTick groupOrd
        withinOrd pos t ev h_ev
    exact gSimBody_events_nodup groups actTick groupOrd withinOrd pos W t
      t h_tick h_layout h_nd h_win h_gord_nd h_within_nd

/-! ## Consequences for the due-filter -/

/-- The due-filter of the tick-start queue is duplicate-free. -/
theorem gSimWorld_due_nodup (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (t : Nat)
    (h_gord_nd : groupOrd.Nodup)
    (h_within_nd : ∀ gi, gi < groups.length → (withinOrd gi).Nodup) :
    ((gSimWorld groups actTick groupOrd withinOrd pos t).events.filter
      (fun e => e.targetTick == t)).Nodup :=
  nodup_filter' (fun e => e.targetTick == t) _
    (gSimWorld_events_Nodup groups actTick groupOrd withinOrd pos t
      h_gord_nd h_within_nd)

/-- The due-filter of `popQueueWorld` is duplicate-free. -/
theorem popQueueWorld_due_nodup (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (g₁ c₁ j : Nat)
    (h_gord_nd : groupOrd.Nodup)
    (h_within_nd : ∀ gi, gi < groups.length → (withinOrd gi).Nodup) :
    ((popQueueWorld groups actTick groupOrd withinOrd pos g₁ c₁
        j).events.filter
      (fun e => e.targetTick ==
        stageTarget actTick groups g₁ c₁ j)).Nodup := by
  dsimp [popQueueWorld]
  exact gSimWorld_due_nodup groups actTick groupOrd withinOrd pos
    (stageTarget actTick groups g₁ c₁ j) h_gord_nd h_within_nd

/-- The `h_nodup` premise of `sameSpec_orderPreservation` holds. -/
theorem sameSpec_h_nodup_discharge (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (g₁ c₁ : Nat)
    (h_gord_nd : groupOrd.Nodup)
    (h_within_nd : ∀ gi, gi < groups.length → (withinOrd gi).Nodup) :
    ∀ k, k ≤ (chainAt groups g₁ c₁).middleDelays.length →
      ((popQueueWorld groups actTick groupOrd withinOrd pos g₁ c₁
          k).events.filter
        (fun e => e.targetTick ==
          stageTarget actTick groups g₁ c₁ k)).Nodup :=
  fun k _ => popQueueWorld_due_nodup groups actTick groupOrd withinOrd
    pos g₁ c₁ k h_gord_nd h_within_nd
