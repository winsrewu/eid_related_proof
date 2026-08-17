import Proofs.Model.DrainOrder
import Mathlib.Data.List.Lemmas

open BasicRedstoneSim
open World
open List

/-! # Burst interleaving invariance — sublist form

Activations appended during a burst keep their relative queue order no
matter how many events `processNEvents` pops between them: pops erase only
due events (target tick = current tick) while activations target `tick + 2`,
and appends never reorder existing entries. We express "keeps relative
order" as `List.Sublist` (`<+`).

Chain of lemmas:
- erasing a value absent from `l₁` preserves `l₁ <+ ·`;
- `processNEvents` pops due events one by one, so a carry list of
  not-due events survives as a sublist (`processNEvents_sublist_carry`);
- same for the full drain (`stepUntilNextTick_sublist_carry`);
- therefore the observer activations of a burst — and, after the drain,
  of the whole `simBody` tick — appear in activation order
  (`simBurst_obsActs_sublist`, `simBody_obsActs_sublist`). -/

/-! ## Activation events -/

/-- The event `activateChain` appends when the current tick is `t`. -/
def obsActEvt (t : Nat) (oid : Nat) : ScheduledEvent :=
  { targetTick := t + 2, priority := 0, nodeId := oid }

/-- The activation events a burst appends, in pair order. -/
def obsActEvts (t : Nat) (observers : List Nat)
    (pairs : List (Nat × Nat)) : List ScheduledEvent :=
  pairs.filterMap (fun p => (observers[p.1]?).map (obsActEvt t))

/-- Every activation event of a burst targets `t + 2`. -/
theorem obsActEvts_targetTick (t : Nat) (observers : List Nat)
    (pairs : List (Nat × Nat)) (e : ScheduledEvent)
    (h : e ∈ obsActEvts t observers pairs) : e.targetTick = t + 2 := by
  induction pairs with
  | nil => dsimp [obsActEvts] at h; cases h
  | cons p ps ih =>
    dsimp [obsActEvts, List.filterMap] at h
    cases hp : observers[p.1]? with
    | none =>
      rw [hp] at h
      exact ih h
    | some oid =>
      rw [hp] at h
      dsimp at h
      rcases List.mem_cons.mp h with rfl | h
      · rfl
      · exact ih h

/-- Every activation event of a burst has priority 0. -/
theorem obsActEvts_priority (t : Nat) (observers : List Nat)
    (pairs : List (Nat × Nat)) (e : ScheduledEvent)
    (h : e ∈ obsActEvts t observers pairs) : e.priority = 0 := by
  induction pairs with
  | nil => dsimp [obsActEvts] at h; cases h
  | cons p ps ih =>
    dsimp [obsActEvts, List.filterMap] at h
    cases hp : observers[p.1]? with
    | none =>
      rw [hp] at h
      exact ih h
    | some oid =>
      rw [hp] at h
      dsimp at h
      rcases List.mem_cons.mp h with rfl | h
      · rfl
      · exact ih h

/-! ## Sublist survival under erasure -/

/-- Erasing a value that does not occur in the sublist preserves it. -/
private theorem eraseEv_sublist_of_notMem (x : ScheduledEvent)
    {l₁ l₂ : List ScheduledEvent} (hs : l₁ <+ l₂) (hx : x ∉ l₁) :
    l₁ <+ eraseEv x l₂ := by
  induction hs with
  | slnil => exact Sublist.slnil
  | cons a hs' ih =>
    dsimp [eraseEv]
    split
    · exact hs'
    · exact Sublist.cons a (ih hx)
  | cons_cons a hs' ih =>
    dsimp [eraseEv]
    split
    · rename_i heq
      exfalso
      exact hx (by rw [← heq]; exact List.mem_cons.mpr (Or.inl rfl))
    · apply Sublist.cons_cons a
      exact ih (fun h => hx (List.mem_cons.mpr (Or.inr h)))

/-- Erasing by index at a value absent from the sublist preserves it. -/
theorem sublist_eraseIdx_of_notMem_nth
    {l₁ l₂ : List ScheduledEvent} (hs : l₁ <+ l₂) (i : Nat)
    (hi : i < l₂.length) (hnth : l₂[i]'hi ∉ l₁) :
    l₁ <+ l₂.eraseIdx i := by
  induction hs generalizing i with
  | slnil => dsimp [List.length] at hi; omega
  | cons a hs' ih =>
    cases i with
    | zero =>
      dsimp [List.eraseIdx]
      exact hs'
    | succ i' =>
      dsimp [List.eraseIdx]
      apply Sublist.cons a
      exact ih i' (by dsimp [List.length] at hi; omega)
        (by simpa using hnth)
  | cons_cons a hs' ih =>
    cases i with
    | zero =>
      dsimp at hnth
      exact absurd (List.mem_cons.mpr (Or.inl rfl)) hnth
    | succ i' =>
      dsimp [List.eraseIdx]
      apply Sublist.cons_cons a
      exact ih i' (by dsimp [List.length] at hi; omega)
        (fun hm => hnth (List.mem_cons.mpr (Or.inr hm)))

/-- Erasing a list of values none of which occur in the sublist. -/
theorem eraseEvents_sublist_of_notMem (es : List ScheduledEvent)
    {l₁ l₂ : List ScheduledEvent} (hs : l₁ <+ l₂)
    (hx : ∀ e ∈ es, e ∉ l₁) : l₁ <+ eraseEvents l₂ es := by
  induction es generalizing l₂ with
  | nil =>
    dsimp [eraseEvents]
    exact hs
  | cons e es' ih =>
    dsimp [eraseEvents, List.foldl]
    apply ih
    · exact eraseEv_sublist_of_notMem e hs
        (hx e (List.mem_cons.mpr (Or.inl rfl)))
    · intro e' he'
      exact hx e' (List.mem_cons.mpr (Or.inr he'))

/-! ## One pop preserves a not-due sublist -/

/-- Popping one due event and firing it preserves any sublist of events
    that are not due at the starting tick. -/
private theorem step_sublist_carry (w : World) (w' : World)
    (hstep : w.step = some w') (carry : List ScheduledEvent)
    (hc : carry <+ w.events)
    (hcarry : ∀ e ∈ carry, e.targetTick ≠ w.tick) :
    carry <+ w'.events := by
  dsimp [World.step] at hstep
  cases hpop : w.popNextEvent with
  | none => simp [hpop] at hstep
  | some pr =>
    rcases pr with ⟨e, wp⟩
    have hw' : w' = wp.onScheduledTick e.nodeId := by
      apply Eq.symm
      simpa [World.step, hpop] using hstep
    rw [hw']
    obtain ⟨news, hnews, _⟩ := onScheduledTick_events_append wp e.nodeId
    rw [hnews]
    apply sublist_append_of_sublist_left
    obtain ⟨idx, hidx, herase, htickE, hget⟩ :=
      popNextEvent_eraseIdx w e wp hpop
    rw [herase]
    exact sublist_eraseIdx_of_notMem_nth hc idx hidx
      (by rw [hget]; intro heq; exact hcarry e heq htickE)

/-! ## Carry survival through `processNEvents` and the drain -/

/-- A sublist of events that are not due at the current tick survives
    `processNEvents`. -/
theorem processNEvents_sublist_carry (w : World) (n : Nat)
    (carry : List ScheduledEvent) (hc : carry <+ w.events)
    (hcarry : ∀ e ∈ carry, e.targetTick ≠ w.tick) :
    carry <+ (processNEvents w n).events := by
  induction n generalizing w with
  | zero =>
    dsimp [processNEvents]
    exact hc
  | succ n ih =>
    dsimp [processNEvents]
    cases hstep : w.step with
    | none => exact hc
    | some w' =>
      have htickW' : w'.tick = w.tick := by
        dsimp [World.step] at hstep
        cases hpop : w.popNextEvent with
        | none => simp [hpop] at hstep
        | some pr =>
          rcases pr with ⟨e, wp⟩
          have hw' : w' = wp.onScheduledTick e.nodeId := by
            apply Eq.symm
            simpa [World.step, hpop] using hstep
          rw [hw', World.onScheduledTick_tick,
            World.popNextEvent_tick w e wp hpop]
      apply ih
      · exact step_sublist_carry w w' hstep carry hc hcarry
      · intro e he
        rw [htickW']
        exact hcarry e he

/-- A sublist of events that are not due at the current tick survives the
    whole drain `stepUntilNextTick`. -/
theorem stepUntilNextTick_sublist_carry (w : World)
    (carry : List ScheduledEvent) (hc : carry <+ w.events)
    (hcarry : ∀ e ∈ carry, e.targetTick ≠ w.tick) :
    carry <+ w.stepUntilNextTick.events := by
  induction w using World.stepUntilNextTick.induct with
  | case1 x hstep =>
    have hnone : x.popNextEvent = none := by
      dsimp [World.step] at hstep
      cases hp : x.popNextEvent <;> simp_all
    rw [stepUntilNextTick_of_step_none x hstep]
    exact hc
  | case2 x w' hstep ih =>
    dsimp [World.step] at hstep
    cases hpop : x.popNextEvent with
    | none => simp [hpop] at hstep
    | some pr =>
      rcases pr with ⟨e0, wp⟩
      have hw' : w' = wp.onScheduledTick e0.nodeId := by
        apply Eq.symm
        simpa [World.step, hpop] using hstep
      subst hw'
      have hstepUNT : x.stepUntilNextTick =
          (wp.onScheduledTick e0.nodeId).stepUntilNextTick := by
        rw [World.stepUntilNextTick]
        dsimp [World.step]
        rw [hpop]
      rw [hstepUNT]
      apply ih
      · exact step_sublist_carry x (wp.onScheduledTick e0.nodeId) hstep
          carry hc hcarry
      · intro e he
        rw [World.onScheduledTick_tick,
          World.popNextEvent_tick x e0 wp hpop]
        exact hcarry e he

/-- A head element can be folded into the left append. -/
private theorem cons_to_append_cons {α : Type} (a : α)
    (l₁ l₂ : List α) : l₁ ++ a :: l₂ = (l₁ ++ [a]) ++ l₂ := by
  rw [List.append_assoc]
  rfl

/-! ## Activations keep their relative order -/

/-- A carry sublist survives a burst; the burst's activation events are
    appended after the carry, in pair order. -/
theorem simBurst_sublist_carry (t : Nat) (observers : List Nat)
    (pos : Nat → Nat → Nat) (w : World) (pairs : List (Nat × Nat))
    (carry : List ScheduledEvent) (hc : carry <+ w.events)
    (hcarry : ∀ e ∈ carry, e.targetTick ≠ w.tick)
    (htick : w.tick = t) :
    carry ++ obsActEvts t observers pairs <+
      (simBurst t observers pos w pairs).events := by
  induction pairs generalizing w carry with
  | nil => simpa [simBurst, obsActEvts] using hc
  | cons p ps ih =>
    rcases p with ⟨i, k⟩
    dsimp [simBurst, obsActEvts, List.foldl, List.filterMap]
    cases hobs : observers[i]? with
    | none =>
      dsimp
      apply ih
      · exact processNEvents_sublist_carry w (pos t k) carry hc hcarry
      · intro e he
        rw [processNEvents_tick]
        exact hcarry e he
      · rw [processNEvents_tick]
        exact htick
    | some oid =>
      dsimp
      rw [cons_to_append_cons]
      apply ih
      · have hevt : [obsActEvt t oid] =
            [{ targetTick := (processNEvents w (pos t k)).tick + 2,
               priority := 0, nodeId := oid }] := by
          congr 1
          dsimp [obsActEvt]
          conv_lhs =>
            rw [← htick, ← processNEvents_tick w (pos t k)]
        rw [hevt]
        dsimp [activateChain]
        exact Sublist.append_right
          (processNEvents_sublist_carry w (pos t k) carry hc hcarry)
          [{ targetTick := (processNEvents w (pos t k)).tick + 2,
             priority := 0, nodeId := oid }]
      · intro e he
        dsimp [activateChain]
        rw [processNEvents_tick]
        rcases List.mem_append.mp he with he | he
        · exact hcarry e he
        · rcases List.mem_singleton.mp he with rfl
          dsimp [obsActEvt]
          rw [htick]
          omega
      · rw [activateChain_tick, processNEvents_tick]
        exact htick

/-- The burst's activation events appear in its event queue in pair
    order. -/
theorem simBurst_obsActs_sublist (observers : List Nat)
    (pos : Nat → Nat → Nat) (w : World) (pairs : List (Nat × Nat)) :
    obsActEvts w.tick observers pairs <+
      (simBurst w.tick observers pos w pairs).events := by
  simpa using simBurst_sublist_carry w.tick observers pos w pairs []
    (nil_sublist w.events) (by simp) rfl

/-- One `simBody` tick: the activations fired at this tick appear in the
    post-drain queue in `actOrd` order (restricted to this tick). -/
theorem simBody_obsActs_sublist (actTick : Nat → Nat)
    (observers actOrd : List Nat) (pos : Nat → Nat → Nat) (w : World)
    (n : Nat) :
    obsActEvts w.tick observers
        ((actOrd.filter (fun i =>
          decide (i < observers.length) && (actTick i == w.tick))).zipIdx)
      <+ (simBody actTick observers actOrd pos w n).events := by
  dsimp [simBody]
  apply stepUntilNextTick_sublist_carry
  · exact simBurst_obsActs_sublist observers pos
      (w.logOutput s!"tick {w.tick}")
      ((actOrd.filter (fun i =>
        decide (i < observers.length) && (actTick i == w.tick))).zipIdx)
  · intro e he
    have := obsActEvts_targetTick w.tick observers
      ((actOrd.filter (fun i =>
        decide (i < observers.length) && (actTick i == w.tick))).zipIdx) e he
    rw [simBurst_tick, World.logOutput_tick]
    omega
