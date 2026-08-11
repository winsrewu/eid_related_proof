import BasicProofs.GroupClustering.LockstepComposition


open BasicRedstoneSim List

/-! # Group clustering — prefix classes and the middle-block invariant

Same-spec chains move in lockstep. This file defines the prefix class of
a stage and proves two facts about it.

Chains group into prefix classes by the first delays of the chain. At
stage `j`, the class of chain `c` contains every stage-`j` event with the
same target tick, priority -3, and first `j` delays. The last repeater
acts as a final stage that fits every class.

The first fact holds at the activation tick of a group. The observer
events carry priority 0, so no middle-stage event sits between two of
them. The middle-block invariant holds there in a vacuous way.

The second fact moves class members from stage `j` to stage `j + 1`. A
class member pops at the stage-`j` tick and spawns its stage-`j + 1`
event. The spawn keeps its position between the two reference events.
Equal targets at stage `j + 1` force the next delay to match, so the
prefix grows by one equal entry.

This file does not close the full induction over ticks. Two parts remain
for a later file: the converse spawn-origin fact (every event between the
two spawned events is the spawn of an event between the two parents), and
the final transition at stage `m + 1`.
-/

/-! ## Definitions -/

/-- The first `j` middle delays of chain `(gi, ci)`. This list identifies
    the prefix class of the chain at stage `j`. -/
def prefixDelays (groups : List GroupSpec) (gi ci j : Nat) : List PNat :=
  (chainAt groups gi ci).middleDelays.take j

/-- `e` is the last-repeater event of some chain and targets tick `T`.
    The last repeater acts as a stage that fits every prefix class. -/
def IsFinalEvent (groups : List GroupSpec) (actTick : Nat → Nat) (T : Nat)
    (e : ScheduledEvent) : Prop :=
  ∃ gi ci, gi < groups.length ∧ ci < (groupAt groups gi).length ∧
    e = stageEvent actTick groups gi ci ((chainAt groups gi ci).middleDelays.length + 1) ∧
    stageTarget actTick groups gi ci ((chainAt groups gi ci).middleDelays.length + 1) = T

/-- Membership of the prefix class of chain `(gi, ci)` at stage `j`. The
    event is a final event, or it is the stage-`j` event of some chain.
    That chain has the same first `j` middle delays and the same target
    tick as chain `(gi, ci)`. The event carries priority -3. -/
def MiddleBlock (groups : List GroupSpec) (actTick : Nat → Nat) (T : Nat)
    (gi ci j : Nat) (e : ScheduledEvent) : Prop :=
  IsFinalEvent groups actTick T e ∨
  (∃ g c, g < groups.length ∧ c < (groupAt groups g).length ∧
    e = stageEvent actTick groups g c j ∧
    e.priority = (-3 : Int) ∧
    e.targetTick = stageTarget actTick groups gi ci j ∧
    prefixDelays groups g c j = prefixDelays groups gi ci j)

/-- The middle-block invariant for one ordered pair of chains at stage
    `j`. Take any event that sits between the two stage-`j` events in the
    queue. If it carries priority -3 and targets the stage-`j` tick of the
    first chain, it belongs to the prefix class of the first chain. -/
def MiddleBlockOk (groups : List GroupSpec) (actTick : Nat → Nat) (T : Nat)
    (queue : List ScheduledEvent) (g₁ c₁ g₂ c₂ j : Nat) : Prop :=
  ∀ e, evBefore queue (stageEvent actTick groups g₁ c₁ j) e →
    evBefore queue e (stageEvent actTick groups g₂ c₂ j) →
    e.priority = (-3 : Int) →
    e.targetTick = stageTarget actTick groups g₁ c₁ j →
    MiddleBlock groups actTick T g₁ c₁ j e

/-! ## Stage priorities and final events -/

/-- Middle stages carry priority -3. -/
theorem stagePri_middle (groups : List GroupSpec) (gi ci j : Nat)
    (h_ge : 1 ≤ j) (h_le : j ≤ (chainAt groups gi ci).middleDelays.length) :
    stagePri groups gi ci j = (-3 : Int) := by
  dsimp [stagePri]
  split_ifs <;> omega

/-- The last stage carries priority -1. -/
theorem stagePri_last (groups : List GroupSpec) (gi ci : Nat) :
    stagePri groups gi ci ((chainAt groups gi ci).middleDelays.length + 1) =
    (-1 : Int) := by
  dsimp [stagePri]
  split_ifs <;> omega

/-- A final event carries priority -1. -/
theorem IsFinalEvent_priority (groups : List GroupSpec) (actTick : Nat → Nat)
    (T : Nat) (e : ScheduledEvent) (h : IsFinalEvent groups actTick T e) :
    e.priority = (-1 : Int) := by
  rcases h with ⟨gi, ci, _, _, h_e, _⟩
  rw [h_e]
  dsimp [stageEvent]
  exact stagePri_last groups gi ci

/-- A final event targets the common output tick `T`. -/
theorem IsFinalEvent_target (groups : List GroupSpec) (actTick : Nat → Nat)
    (T : Nat) (e : ScheduledEvent) (h : IsFinalEvent groups actTick T e) :
    e.targetTick = T := by
  rcases h with ⟨gi, ci, _, _, h_e, h_T⟩
  rw [h_e]
  dsimp [stageEvent]
  exact h_T

/-- A final event never carries the middle priority -3. -/
theorem IsFinalEvent_priority_ne_middle (groups : List GroupSpec)
    (actTick : Nat → Nat) (T : Nat) (e : ScheduledEvent)
    (h : IsFinalEvent groups actTick T e) : e.priority ≠ (-3 : Int) := by
  rw [IsFinalEvent_priority groups actTick T e h]
  omega

/-- Every stage up to the last middle stage targets a tick before the
    final target of the chain. -/
theorem stageTarget_lt_final (actTick : Nat → Nat) (groups : List GroupSpec)
    (gi ci j : Nat) (h_j : j ≤ (chainAt groups gi ci).middleDelays.length) :
    stageTarget actTick groups gi ci j <
    stageTarget actTick groups gi ci
      ((chainAt groups gi ci).middleDelays.length + 1) := by
  set m := (chainAt groups gi ci).middleDelays.length
  have h_lt : stageCumDelay (chainAt groups gi ci) j <
      stageCumDelay (chainAt groups gi ci) (j + 1) :=
    stageCumDelay_lt_succ (chainAt groups gi ci) j (by omega)
  have h_le : stageCumDelay (chainAt groups gi ci) (j + 1) ≤
      stageCumDelay (chainAt groups gi ci) (m + 1) :=
    stageCumDelay_mono (chainAt groups gi ci) (j + 1) (m + 1) (by omega)
  dsimp [stageTarget]
  omega

/-! ## Prefix arithmetic -/

private theorem take_succ_of_lt' {α : Type} (l : List α) (i : Nat)
    (h_i : i < l.length) : l.take (i + 1) = l.take i ++ [l[i]'h_i] := by
  revert i h_i
  induction l with
  | nil => intro i h_i; cases h_i
  | cons x xs ih =>
    intro i h_i
    cases i with
    | zero => simp [List.take]
    | succ i' =>
      simp only [List.length_cons] at h_i
      dsimp only [List.take]
      congr 1
      exact ih i' (by simpa using h_i)

/-- Taking one more stage appends the next middle delay. -/
theorem prefixDelays_succ (groups : List GroupSpec) (gi ci j : Nat)
    (h_j : j < (chainAt groups gi ci).middleDelays.length) :
    prefixDelays groups gi ci (j + 1) =
    prefixDelays groups gi ci j ++
      [(chainAt groups gi ci).middleDelays[j]'h_j] := by
  dsimp [prefixDelays]
  exact take_succ_of_lt' (chainAt groups gi ci).middleDelays j h_j

/-- Equal prefixes at stage `j` give equal cumulative delays at stage
    `j`. -/
theorem stageCumDelay_eq_of_prefixDelays_eq (groups : List GroupSpec)
    (g c g₁ c₁ j : Nat)
    (h_j : j ≤ (chainAt groups g c).middleDelays.length)
    (h_j₁ : j ≤ (chainAt groups g₁ c₁).middleDelays.length)
    (h_pref : prefixDelays groups g c j = prefixDelays groups g₁ c₁ j) :
    stageCumDelay (chainAt groups g c) j =
    stageCumDelay (chainAt groups g₁ c₁) j := by
  rw [stageCumDelay_of_le_middle (chainAt groups g c) j h_j,
    stageCumDelay_of_le_middle (chainAt groups g₁ c₁) j h_j₁]
  dsimp [prefixDelays] at h_pref
  rw [h_pref]

/-- Equal prefixes at stage `j` plus equal targets at stages `j` and
    `j + 1` give equal prefixes at stage `j + 1`. The equal targets at
    stage `j + 1` force the next delay to match. -/
theorem prefixDelays_ext_of_targets_eq (groups : List GroupSpec)
    (actTick : Nat → Nat) (g c g₁ c₁ j : Nat)
    (h_j : j < (chainAt groups g c).middleDelays.length)
    (h_j₁ : j < (chainAt groups g₁ c₁).middleDelays.length)
    (h_pref : prefixDelays groups g c j = prefixDelays groups g₁ c₁ j)
    (h_tgt : stageTarget actTick groups g c j =
        stageTarget actTick groups g₁ c₁ j)
    (h_tgt_succ : stageTarget actTick groups g c (j + 1) =
        stageTarget actTick groups g₁ c₁ (j + 1)) :
    prefixDelays groups g c (j + 1) = prefixDelays groups g₁ c₁ (j + 1) := by
  have h_cum : stageCumDelay (chainAt groups g c) j =
      stageCumDelay (chainAt groups g₁ c₁) j :=
    stageCumDelay_eq_of_prefixDelays_eq groups g c g₁ c₁ j
      (by omega) (by omega) h_pref
  have h_act : actTick g = actTick g₁ := by
    dsimp [stageTarget] at h_tgt
    omega
  have h_d : ((chainAt groups g c).middleDelays[j]'h_j : Nat) =
      ((chainAt groups g₁ c₁).middleDelays[j]'h_j₁ : Nat) := by
    have h₁ := stageCumDelay_succ_middle (chainAt groups g c) j h_j
    have h₂ := stageCumDelay_succ_middle (chainAt groups g₁ c₁) j h_j₁
    dsimp [stageTarget] at h_tgt_succ
    omega
  dsimp [prefixDelays] at h_pref ⊢
  rw [take_succ_of_lt' (chainAt groups g c).middleDelays j h_j,
    take_succ_of_lt' (chainAt groups g₁ c₁).middleDelays j h_j₁, h_pref,
    Subtype.ext h_d]

/-! ## Lemma 1: the base at activation -/

/-- In a split `l ++ r = p ++ x :: q` with a short prefix `p`, the element
    `x` lies in the left part `l`. -/
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
  | cons a l' ih =>
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

/-- An event that comes after an anchor of the appended part lies in the
    appended part, when the anchor is absent from the left part. -/
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

/-- After `activateGroup`, every event after the stage-0 event of a
    group-`gi` chain is the stage-0 event of a group-`gi` chain. The
    observer batch is atomic, so nothing else sits inside it. -/
theorem activateGroup_stage_zero_after (groups : List GroupSpec)
    (actTick : Nat → Nat) (w : World) (observers : List Nat) (gi c₁ : Nat)
    (h_tick : w.tick = actTick gi)
    (h_obs : ∀ oid ∈ observers, ∃ ci, ci < (groupAt groups gi).length ∧
        oid = chainBaseId groups gi ci + 1)
    (h_absent : stageEvent actTick groups gi c₁ 0 ∉ w.events)
    (e : ScheduledEvent)
    (h_after : evBefore (activateGroup w observers).events
        (stageEvent actTick groups gi c₁ 0) e) :
    ∃ ci, ci < (groupAt groups gi).length ∧
      e = stageEvent actTick groups gi ci 0 := by
  rw [activateGroup_events_map] at h_after
  have h_e := evBefore_append_right_mem h_absent h_after
  rcases List.mem_map.mp h_e with ⟨oid, h_oid, h_e_eq⟩
  obtain ⟨ci, h_ci, h_id⟩ := h_obs oid h_oid
  refine ⟨ci, h_ci, ?_⟩
  rw [← h_e_eq]
  dsimp [stageEvent, stageTarget, stagePri, stageCumDelay]
  simp [h_tick, h_id]

/-- The middle-block invariant holds at stage 0 right after the activation
    of a group. The appended observer events carry priority 0, so no event
    between two of them carries priority -3. The invariant holds in a
    vacuous way. -/
theorem MiddleBlockOk_activateGroup (groups : List GroupSpec)
    (actTick : Nat → Nat) (T : Nat) (w : World) (observers : List Nat)
    (gi c₁ c₂ : Nat)
    (h_absent : stageEvent actTick groups gi c₁ 0 ∉ w.events) :
    MiddleBlockOk groups actTick T (activateGroup w observers).events
      gi c₁ gi c₂ 0 := by
  intro e h_b₁ _ h_pri _
  rw [activateGroup_events_map] at h_b₁
  have h_e := evBefore_append_right_mem h_absent h_b₁
  rcases List.mem_map.mp h_e with ⟨oid, _, h_e_eq⟩
  rw [← h_e_eq] at h_pri
  dsimp at h_pri
  omega

/-! ## Lemma 2: the stage step -/

/-- Spawn facts for one chain against the reference chain at the pop tick:
    equal priority, a future spawn target, and the SameSpecLockstep spawn
    equation. -/
private theorem stage_step_spawn_facts (groups : List GroupSpec)
    (actTick : Nat → Nat) (w : World) (g₁ c₁ gx cx j : Nat)
    (h_gx : gx < groups.length) (h_cx : cx < (groupAt groups gx).length)
    (h_jx : j ≤ (chainAt groups gx cx).middleDelays.length)
    (h_j₁ : j ≤ (chainAt groups g₁ c₁).middleDelays.length)
    (h_due : w.tick = stageTarget actTick groups g₁ c₁ j)
    (h_tgt : stageTarget actTick groups gx cx j =
        stageTarget actTick groups g₁ c₁ j) :
    (stageEvent actTick groups gx cx j).priority =
      (stageEvent actTick groups g₁ c₁ j).priority ∧
    (stageEvent actTick groups gx cx (j + 1)).targetTick ≠ w.tick ∧
    ∀ (v : World), v.tick = w.tick → NodeLayoutOk groups v →
      (v.onScheduledTick (stageEvent actTick groups gx cx j).nodeId).events =
      v.events ++ [stageEvent actTick groups gx cx (j + 1)] := by
  refine ⟨?_, ?_, ?_⟩
  · dsimp [stageEvent, stagePri]
    split_ifs <;> omega
  · dsimp [stageEvent]
    intro h_eq
    have h_lt := stageTarget_lt_succ actTick groups gx cx j h_jx
    rw [h_eq, h_due, ← h_tgt] at h_lt
    exact Nat.lt_irrefl _ h_lt
  · intro v h_v h_lay
    have h_tick : v.tick = stageTarget actTick groups gx cx j := by
      rw [h_v, h_due, ← h_tgt]
    simpa [stageEvent] using
      stage_spawn groups actTick v gx cx j h_gx h_cx h_jx h_tick h_lay

/-- At the pop tick of stage `j`, a class member between the two reference
    events spawns its stage-`j + 1` event between the two spawned reference
    events. This variant covers a full tick via `stepUntilNextTick`. -/
theorem prefixClass_step_stepUntilNextTick (groups : List GroupSpec)
    (actTick : Nat → Nat) (w : World) (g₁ c₁ g₂ c₂ g c j : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_g : g < groups.length) (h_c : c < (groupAt groups g).length)
    (h_layout : NodeLayoutOk groups w)
    (h_j₁ : j ≤ (chainAt groups g₁ c₁).middleDelays.length)
    (h_j₂ : j ≤ (chainAt groups g₂ c₂).middleDelays.length)
    (h_j : j ≤ (chainAt groups g c).middleDelays.length)
    (h_due : w.tick = stageTarget actTick groups g₁ c₁ j)
    (h_tgt₂ : stageTarget actTick groups g₂ c₂ j =
        stageTarget actTick groups g₁ c₁ j)
    (h_tgt : stageTarget actTick groups g c j =
        stageTarget actTick groups g₁ c₁ j)
    (hA_mem : stageEvent actTick groups g₁ c₁ j ∈ w.events)
    (hC_mem : stageEvent actTick groups g c j ∈ w.events)
    (hD_mem : stageEvent actTick groups g₂ c₂ j ∈ w.events)
    (h_nodup : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup)
    (hAC : evBefore (w.events.filter (fun e => e.targetTick == w.tick))
        (stageEvent actTick groups g₁ c₁ j) (stageEvent actTick groups g c j))
    (hCD : evBefore (w.events.filter (fun e => e.targetTick == w.tick))
        (stageEvent actTick groups g c j) (stageEvent actTick groups g₂ c₂ j)) :
    evBefore w.stepUntilNextTick.events (stageEvent actTick groups g₁ c₁ (j + 1))
      (stageEvent actTick groups g c (j + 1)) ∧
    evBefore w.stepUntilNextTick.events (stageEvent actTick groups g c (j + 1))
      (stageEvent actTick groups g₂ c₂ (j + 1)) := by
  set A := stageEvent actTick groups g₁ c₁ j
  set C := stageEvent actTick groups g c j
  set D := stageEvent actTick groups g₂ c₂ j
  set sA := stageEvent actTick groups g₁ c₁ (j + 1)
  set sC := stageEvent actTick groups g c (j + 1)
  set sD := stageEvent actTick groups g₂ c₂ (j + 1)
  obtain ⟨h_priCA, h_nd_sC, h_spawnC⟩ :=
    stage_step_spawn_facts groups actTick w g₁ c₁ g c j h_g h_c h_j h_j₁
      h_due h_tgt
  obtain ⟨h_priDA, h_nd_sD, h_spawnD⟩ :=
    stage_step_spawn_facts groups actTick w g₁ c₁ g₂ c₂ j h_g₂ h_c₂ h_j₂
      h_j₁ h_due h_tgt₂
  have hA_due : A.targetTick = w.tick := by
    dsimp [A, stageEvent]
    exact h_due.symm
  have hC_due : C.targetTick = w.tick := by
    dsimp [C, stageEvent]
    rw [h_tgt, h_due]
  have hD_due : D.targetTick = w.tick := by
    dsimp [D, stageEvent]
    rw [h_tgt₂, h_due]
  have h_nd_sA : sA.targetTick ≠ w.tick := by
    dsimp [sA, stageEvent]
    intro h_eq
    have h_lt := stageTarget_lt_succ actTick groups g₁ c₁ j h_j₁
    rw [h_eq, h_due] at h_lt
    exact Nat.lt_irrefl _ h_lt
  have h_spawnA : ∀ (v : World), v.tick = w.tick → NodeLayoutOk groups v →
      (v.onScheduledTick A.nodeId).events = v.events ++ [sA] := by
    intro v h_v h_lay
    simpa [A, sA, stageEvent] using
      stage_spawn groups actTick v g₁ c₁ j h_g₁ h_c₁ h_j₁
        (h_v.trans h_due) h_lay
  obtain ⟨p₁, q₁, h_eq₁, hC_q₁⟩ :=
    World.samePriLockstep_layout groups w A C sA sC h_layout hA_mem hC_mem
      hA_due hC_due h_priCA.symm h_nodup hAC h_nd_sA h_nd_sC h_spawnA
      h_spawnC
  obtain ⟨p₂, q₂, h_eq₂, hD_q₂⟩ :=
    World.samePriLockstep_layout groups w C D sC sD h_layout hC_mem hD_mem
      hC_due hD_due (h_priCA.trans h_priDA.symm) h_nodup hCD h_nd_sC h_nd_sD
      h_spawnC h_spawnD
  refine ⟨⟨p₁, q₁, h_eq₁, hC_q₁⟩, ⟨p₂, q₂, h_eq₂, hD_q₂⟩⟩

/-- At the pop tick of stage `j`, a class member between the two reference
    events spawns its stage-`j + 1` event between the two spawned reference
    events. This variant covers a fuel-bounded pop phase. -/
theorem prefixClass_step_processNEvents (groups : List GroupSpec)
    (actTick : Nat → Nat) (w : World) (n : Nat)
    (g₁ c₁ g₂ c₂ g c j : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_g : g < groups.length) (h_c : c < (groupAt groups g).length)
    (h_layout : NodeLayoutOk groups w)
    (h_j₁ : j ≤ (chainAt groups g₁ c₁).middleDelays.length)
    (h_j₂ : j ≤ (chainAt groups g₂ c₂).middleDelays.length)
    (h_j : j ≤ (chainAt groups g c).middleDelays.length)
    (h_due : w.tick = stageTarget actTick groups g₁ c₁ j)
    (h_tgt₂ : stageTarget actTick groups g₂ c₂ j =
        stageTarget actTick groups g₁ c₁ j)
    (h_tgt : stageTarget actTick groups g c j =
        stageTarget actTick groups g₁ c₁ j)
    (hA_mem : stageEvent actTick groups g₁ c₁ j ∈ w.events)
    (hC_mem : stageEvent actTick groups g c j ∈ w.events)
    (hD_mem : stageEvent actTick groups g₂ c₂ j ∈ w.events)
    (h_nodup : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup)
    (hAC : evBefore (w.events.filter (fun e => e.targetTick == w.tick))
        (stageEvent actTick groups g₁ c₁ j) (stageEvent actTick groups g c j))
    (hCD : evBefore (w.events.filter (fun e => e.targetTick == w.tick))
        (stageEvent actTick groups g c j) (stageEvent actTick groups g₂ c₂ j))
    (hA_gone : stageEvent actTick groups g₁ c₁ j ∉
        (processNEvents w n).events)
    (hC_gone : stageEvent actTick groups g c j ∉
        (processNEvents w n).events)
    (hD_gone : stageEvent actTick groups g₂ c₂ j ∉
        (processNEvents w n).events) :
    evBefore (processNEvents w n).events
      (stageEvent actTick groups g₁ c₁ (j + 1))
      (stageEvent actTick groups g c (j + 1)) ∧
    evBefore (processNEvents w n).events
      (stageEvent actTick groups g c (j + 1))
      (stageEvent actTick groups g₂ c₂ (j + 1)) := by
  set A := stageEvent actTick groups g₁ c₁ j
  set C := stageEvent actTick groups g c j
  set D := stageEvent actTick groups g₂ c₂ j
  set sA := stageEvent actTick groups g₁ c₁ (j + 1)
  set sC := stageEvent actTick groups g c (j + 1)
  set sD := stageEvent actTick groups g₂ c₂ (j + 1)
  obtain ⟨h_priCA, h_nd_sC, h_spawnC⟩ :=
    stage_step_spawn_facts groups actTick w g₁ c₁ g c j h_g h_c h_j h_j₁
      h_due h_tgt
  obtain ⟨h_priDA, h_nd_sD, h_spawnD⟩ :=
    stage_step_spawn_facts groups actTick w g₁ c₁ g₂ c₂ j h_g₂ h_c₂ h_j₂
      h_j₁ h_due h_tgt₂
  have hA_due : A.targetTick = w.tick := by
    dsimp [A, stageEvent]
    exact h_due.symm
  have hC_due : C.targetTick = w.tick := by
    dsimp [C, stageEvent]
    rw [h_tgt, h_due]
  have hD_due : D.targetTick = w.tick := by
    dsimp [D, stageEvent]
    rw [h_tgt₂, h_due]
  have h_nd_sA : sA.targetTick ≠ w.tick := by
    dsimp [sA, stageEvent]
    intro h_eq
    have h_lt := stageTarget_lt_succ actTick groups g₁ c₁ j h_j₁
    rw [h_eq, h_due] at h_lt
    exact Nat.lt_irrefl _ h_lt
  have h_spawnA : ∀ (v : World), v.tick = w.tick → NodeLayoutOk groups v →
      (v.onScheduledTick A.nodeId).events = v.events ++ [sA] := by
    intro v h_v h_lay
    simpa [A, sA, stageEvent] using
      stage_spawn groups actTick v g₁ c₁ j h_g₁ h_c₁ h_j₁
        (h_v.trans h_due) h_lay
  have h₁ : evBefore (processNEvents w n).events sA sC :=
    processNEvents_spawn_evBefore groups w n A C sA sC h_layout hA_mem
      hC_mem hA_due hC_due h_priCA.symm h_nodup hAC hA_gone hC_gone
      h_nd_sA h_nd_sC h_spawnA h_spawnC
  have h₂ : evBefore (processNEvents w n).events sC sD :=
    processNEvents_spawn_evBefore groups w n C D sC sD h_layout hC_mem
      hD_mem hC_due hD_due (h_priCA.trans h_priDA.symm) h_nodup hCD
      hC_gone hD_gone h_nd_sC h_nd_sD h_spawnC h_spawnD
  exact ⟨h₁, h₂⟩

/-- At the pop tick of stage `j`, a class member between the two reference
    events spawns its stage-`j + 1` event between the two spawned reference
    events. This variant covers a full burst phase. -/
theorem prefixClass_step_gSimBurst (groups : List GroupSpec) (t : Nat)
    (obsAll : List (List Nat)) (withinOrd pos : Nat → List Nat) (w : World)
    (pairs : List (Nat × Nat)) (g₁ c₁ g₂ c₂ g c j : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_g : g < groups.length) (h_c : c < (groupAt groups g).length)
    (h_layout : NodeLayoutOk groups w)
    (h_j₁ : j ≤ (chainAt groups g₁ c₁).middleDelays.length)
    (h_j₂ : j ≤ (chainAt groups g₂ c₂).middleDelays.length)
    (h_j : j ≤ (chainAt groups g c).middleDelays.length)
    (h_due : w.tick = stageTarget actTick groups g₁ c₁ j)
    (h_tgt₂ : stageTarget actTick groups g₂ c₂ j =
        stageTarget actTick groups g₁ c₁ j)
    (h_tgt : stageTarget actTick groups g c j =
        stageTarget actTick groups g₁ c₁ j)
    (hA_mem : stageEvent actTick groups g₁ c₁ j ∈ w.events)
    (hC_mem : stageEvent actTick groups g c j ∈ w.events)
    (hD_mem : stageEvent actTick groups g₂ c₂ j ∈ w.events)
    (h_nodup : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup)
    (hAC : evBefore (w.events.filter (fun e => e.targetTick == w.tick))
        (stageEvent actTick groups g₁ c₁ j) (stageEvent actTick groups g c j))
    (hCD : evBefore (w.events.filter (fun e => e.targetTick == w.tick))
        (stageEvent actTick groups g c j) (stageEvent actTick groups g₂ c₂ j))
    (hA_gone : stageEvent actTick groups g₁ c₁ j ∉
        (gSimBurst t obsAll withinOrd pos w pairs).events)
    (hC_gone : stageEvent actTick groups g c j ∉
        (gSimBurst t obsAll withinOrd pos w pairs).events)
    (hD_gone : stageEvent actTick groups g₂ c₂ j ∉
        (gSimBurst t obsAll withinOrd pos w pairs).events) :
    evBefore (gSimBurst t obsAll withinOrd pos w pairs).events
      (stageEvent actTick groups g₁ c₁ (j + 1))
      (stageEvent actTick groups g c (j + 1)) ∧
    evBefore (gSimBurst t obsAll withinOrd pos w pairs).events
      (stageEvent actTick groups g c (j + 1))
      (stageEvent actTick groups g₂ c₂ (j + 1)) := by
  set A := stageEvent actTick groups g₁ c₁ j
  set C := stageEvent actTick groups g c j
  set D := stageEvent actTick groups g₂ c₂ j
  set sA := stageEvent actTick groups g₁ c₁ (j + 1)
  set sC := stageEvent actTick groups g c (j + 1)
  set sD := stageEvent actTick groups g₂ c₂ (j + 1)
  obtain ⟨h_priCA, h_nd_sC, h_spawnC⟩ :=
    stage_step_spawn_facts groups actTick w g₁ c₁ g c j h_g h_c h_j h_j₁
      h_due h_tgt
  obtain ⟨h_priDA, h_nd_sD, h_spawnD⟩ :=
    stage_step_spawn_facts groups actTick w g₁ c₁ g₂ c₂ j h_g₂ h_c₂ h_j₂
      h_j₁ h_due h_tgt₂
  have hA_due : A.targetTick = w.tick := by
    dsimp [A, stageEvent]
    exact h_due.symm
  have hC_due : C.targetTick = w.tick := by
    dsimp [C, stageEvent]
    rw [h_tgt, h_due]
  have hD_due : D.targetTick = w.tick := by
    dsimp [D, stageEvent]
    rw [h_tgt₂, h_due]
  have h_nd_sA : sA.targetTick ≠ w.tick := by
    dsimp [sA, stageEvent]
    intro h_eq
    have h_lt := stageTarget_lt_succ actTick groups g₁ c₁ j h_j₁
    rw [h_eq, h_due] at h_lt
    exact Nat.lt_irrefl _ h_lt
  have h_spawnA : ∀ (v : World), v.tick = w.tick → NodeLayoutOk groups v →
      (v.onScheduledTick A.nodeId).events = v.events ++ [sA] := by
    intro v h_v h_lay
    simpa [A, sA, stageEvent] using
      stage_spawn groups actTick v g₁ c₁ j h_g₁ h_c₁ h_j₁
        (h_v.trans h_due) h_lay
  have h₁ : evBefore (gSimBurst t obsAll withinOrd pos w pairs).events sA sC :=
    gSimBurst_spawn_evBefore groups t obsAll withinOrd pos w pairs A C sA sC
      h_layout hA_mem hC_mem hA_due hC_due h_priCA.symm h_nodup hAC
      hA_gone hC_gone h_nd_sA h_nd_sC h_spawnA h_spawnC
  have h₂ : evBefore (gSimBurst t obsAll withinOrd pos w pairs).events sC sD :=
    gSimBurst_spawn_evBefore groups t obsAll withinOrd pos w pairs C D sC sD
      h_layout hC_mem hD_mem hC_due hD_due (h_priCA.trans h_priDA.symm)
      h_nodup hCD hC_gone hD_gone h_nd_sC h_nd_sD h_spawnC h_spawnD
  exact ⟨h₁, h₂⟩

/-- A middle-disjunct witness at stage `j` lifts to one at stage `j + 1`.
    The final disjunct is impossible here. A final event carries priority
    -1, and stage `j` of the chain is not the last stage. -/
theorem MiddleBlock_step_middle (groups : List GroupSpec)
    (actTick : Nat → Nat) (T : Nat) (g₁ c₁ g c j : Nat)
    (h_g : g < groups.length) (h_c : c < (groupAt groups g).length)
    (h_j : j < (chainAt groups g c).middleDelays.length)
    (h_j₁ : j < (chainAt groups g₁ c₁).middleDelays.length)
    (h_mb : MiddleBlock groups actTick T g₁ c₁ j
        (stageEvent actTick groups g c j))
    (h_tgt_succ : stageTarget actTick groups g c (j + 1) =
        stageTarget actTick groups g₁ c₁ (j + 1)) :
    MiddleBlock groups actTick T g₁ c₁ (j + 1)
      (stageEvent actTick groups g c (j + 1)) := by
  rcases h_mb with h_fin | h_mid
  · have h_pri := IsFinalEvent_priority groups actTick T
      (stageEvent actTick groups g c j) h_fin
    dsimp [stageEvent, stagePri] at h_pri
    split_ifs at h_pri <;> omega
  · rcases h_mid with ⟨g', c', h_g', h_c', h_ev_eq, h_pri_e, h_tgt_j, h_pref⟩
    have h_pri_c' : (stageEvent actTick groups g' c' j).priority =
        (-3 : Int) := by
      rw [← h_ev_eq]
      exact h_pri_e
    have h_j_ge : 1 ≤ j := by
      dsimp [stageEvent, stagePri] at h_pri_c'
      split_ifs at h_pri_c' <;> omega
    have h_j_le : j ≤ (chainAt groups g' c').middleDelays.length := by
      dsimp [stageEvent, stagePri] at h_pri_c'
      split_ifs at h_pri_c' <;> omega
    obtain ⟨h_g_eq, h_c_eq, _⟩ :=
      stageEvent_injective actTick groups g c j g' c' j h_g h_c h_g' h_c'
        (by omega) (by omega) h_ev_eq
    rw [← h_g_eq, ← h_c_eq] at h_pref
    refine Or.inr ⟨g, c, h_g, h_c, rfl, ?_, ?_, ?_⟩
    · dsimp [stageEvent]
      exact stagePri_middle groups g c (j + 1) (by omega) (by omega)
    · dsimp [stageEvent]
      exact h_tgt_succ
    · exact prefixDelays_ext_of_targets_eq groups actTick g c g₁ c₁ j h_j
        h_j₁ h_pref h_tgt_j h_tgt_succ
