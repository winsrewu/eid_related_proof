import Proofs.Model.Basic
import Proofs.Model.SimLemmas
import Proofs.Model.Cascade
import Proofs.Model.CascadeDrain
import Proofs.Model.CascadeRealization
import Mathlib.Data.List.Defs
import Mathlib.Data.List.Basic
import Mathlib.Tactic

open BasicRedstoneSim
open World

/-! # Drain order

`popSeq w` is the sequence of events that `w.stepUntilNextTick` fires, in
pop order. Pop discipline: lowest priority first, and within one priority
the queue position order. The central fact is `popSeq_congr_due`: the pop
sequence depends only on the current tick and the *due* events (the filter
of events targeting the tick), so appending or reordering future events
never changes it. This is what makes the activation interleaving of
`simBurst` irrelevant to firing order. -/

/-! ## Small reflection helpers -/

private theorem int_beq_false_of_ne (a b : Int) (h : a ≠ b) :
    (a == b) = false := by
  cases hb : a == b
  · rfl
  · exfalso
    exact h (LawfulBEq.eq_of_beq hb)

private theorem bool_and_eq_true_iff (a b : Bool) :
    (a && b) = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp

private theorem decide_eq_false_of_not (p : Prop) [Decidable p]
    (h : ¬p) : decide p = false := by
  by_cases hp : decide p = true
  · exfalso
    exact h (of_decide_eq_true hp)
  · cases dp : decide p
    · rfl
    · exfalso
      exact hp dp

private theorem filter_length_le {α : Type} (p : α → Bool) (l : List α) :
    (l.filter p).length ≤ l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    dsimp [List.filter]
    split
    · change (xs.filter p).length + 1 ≤ xs.length + 1
      omega
    · omega

/-! ## Erasing events by value (DecidableEq-based) -/

/-- Erase the first occurrence of `x`, using decidable equality. (The
    core `List.erase` is `BEq`-based and `ScheduledEvent` has no
    `LawfulBEq` instance, so the drain algebra uses this instead.) -/
def eraseEv (x : ScheduledEvent) : List ScheduledEvent → List ScheduledEvent
  | [] => []
  | y :: ys => if y = x then ys else y :: eraseEv x ys

theorem eraseEv_self (x : ScheduledEvent) (xs : List ScheduledEvent) :
    eraseEv x (x :: xs) = xs := by
  dsimp [eraseEv]
  split
  · rfl
  · rename_i hne
    exfalso
    exact hne rfl

/-- Erasing an absent element does nothing. -/
theorem eraseEv_of_notMem (x : ScheduledEvent) (l : List ScheduledEvent)
    (h : x ∉ l) : eraseEv x l = l := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    have hne : y ≠ x :=
      fun hy => h (by rw [hy]; exact List.mem_cons.mpr (Or.inl rfl))
    have hn' : x ∉ ys := fun hm => h (List.mem_cons.mpr (Or.inr hm))
    dsimp [eraseEv]
    split
    · rename_i hyx
      exfalso
      exact hne hyx
    · rw [ih hn']

private theorem eraseEv_append_of_notMem (a b : List ScheduledEvent)
    (x : ScheduledEvent) (hx : x ∉ b) :
    eraseEv x (a ++ b) = eraseEv x a ++ b := by
  induction a generalizing b with
  | nil =>
    dsimp [eraseEv]
    exact eraseEv_of_notMem x b hx
  | cons y ys ih =>
    by_cases hy : y = x
    · subst hy
      dsimp [eraseEv]
      split
      · rfl
      · rename_i hne
        exfalso
        exact hne rfl
    · dsimp [eraseEv]
      split
      · rename_i hyx
        exfalso
        exact hy hyx
      · rw [ih b hx, List.cons_append]

/-- Erase the first occurrence of each element of `es` from `l`, in
    order. -/
def eraseEvents (l : List ScheduledEvent) (es : List ScheduledEvent) :
    List ScheduledEvent :=
  es.foldl (fun acc e => eraseEv e acc) l

theorem eraseEvents_cons (l : List ScheduledEvent) (e : ScheduledEvent)
    (es : List ScheduledEvent) :
    eraseEvents l (e :: es) = eraseEvents (eraseEv e l) es := by
  dsimp [eraseEvents]

theorem eraseEvents_append (l es₁ es₂ : List ScheduledEvent) :
    eraseEvents l (es₁ ++ es₂) = eraseEvents (eraseEvents l es₁) es₂ := by
  induction es₁ generalizing l with
  | nil => rfl
  | cons e es ih =>
    show eraseEvents (eraseEv e l) (es ++ es₂) =
      eraseEvents (eraseEvents (eraseEv e l) es) es₂
    exact ih (eraseEv e l)

/-- Erasing elements that do not occur does nothing. -/
theorem eraseEvents_of_notMem (l es : List ScheduledEvent)
    (h : ∀ e ∈ es, e ∉ l) : eraseEvents l es = l := by
  induction es generalizing l with
  | nil => rfl
  | cons e es ih =>
    dsimp [eraseEvents, List.foldl]
    rw [eraseEv_of_notMem e l (h e (List.mem_cons.mpr (Or.inl rfl)))]
    apply ih
    intro e' he'
    exact h e' (List.mem_cons.mpr (Or.inr he'))

/-- Erasing from an appended right part that contains none of the erased
    values leaves the right part intact. -/
theorem eraseEvents_append_right (a b es : List ScheduledEvent)
    (h : ∀ e ∈ es, e ∉ b) :
    eraseEvents (a ++ b) es = eraseEvents a es ++ b := by
  induction es generalizing a with
  | nil => rfl
  | cons e es ih =>
    show eraseEvents (eraseEv e (a ++ b)) es =
      eraseEvents (eraseEv e a) es ++ b
    rw [eraseEv_append_of_notMem a b e (h e (List.mem_cons.mpr (Or.inl rfl)))]
    exact ih (eraseEv e a) (fun e' he' => h e' (List.mem_cons.mpr (Or.inr he')))

/-! ## Fuel-based pop iteration -/

/-- `popNextEvent = none` means the current-tick count is zero. -/
theorem popNextEvent_none_count_zero (w : World)
    (h : w.popNextEvent = none) : countEventAtThisTick w w.tick = 0 := by
  have hs : w.step = none := by dsimp [World.step]; rw [h]
  exact step_none_countEventAtThisTick w hs

/-- One pop–fire step of the drain, iterated with explicit fuel. -/
def popSeqFuel (w : World) : Nat → List ScheduledEvent
  | 0 => []
  | n + 1 =>
    match w.popNextEvent with
    | none => []
    | some (e, w') => e :: popSeqFuel (w'.onScheduledTick e.nodeId) n

/-- One unit of fuel beyond the due count changes nothing. -/
theorem popSeqFuel_stable (w : World) (k : Nat)
    (hk : countEventAtThisTick w w.tick ≤ k) :
    popSeqFuel w (k + 1) = popSeqFuel w k := by
  induction k generalizing w with
  | zero =>
    have hnone : w.popNextEvent = none :=
      popNextEvent_none_of_count_zero w (by omega)
    simp [popSeqFuel, hnone]
  | succ k ih =>
    dsimp [popSeqFuel]
    cases hpop : w.popNextEvent with
    | none => simp
    | some pr =>
      rcases pr with ⟨e, wp⟩
      dsimp
      apply congrArg (List.cons e)
      apply ih
      have h1 : countEventAtThisTick (wp.onScheduledTick e.nodeId)
          (wp.onScheduledTick e.nodeId).tick =
          countEventAtThisTick wp wp.tick := by
        rw [World.onScheduledTick_tick]
        exact onScheduledTick_countEventAtThisTick wp e.nodeId
      have h2 : wp.tick = w.tick := World.popNextEvent_tick w e wp hpop
      have h3 : countEventAtThisTick wp w.tick =
          countEventAtThisTick w w.tick - 1 :=
        (popNextEvent_remove_one_current_tick_event_if_some w e wp hpop).2
      rw [h1, h2, h3]
      omega

/-- More fuel than the due count does not change the result. -/
theorem popSeqFuel_extend (w : World) (n m : Nat)
    (h : countEventAtThisTick w w.tick ≤ n) :
    popSeqFuel w (n + m) = popSeqFuel w n := by
  induction m generalizing w n with
  | zero => rfl
  | succ m ih =>
    have harg : n + (m + 1) = (n + m) + 1 := by omega
    rw [harg, popSeqFuel_stable w (n + m) (by omega), ih w n h]

/-- The events fired by `stepUntilNextTick`, in pop order. The queue
    length is always enough fuel to drain the tick. -/
def popSeq (w : World) : List ScheduledEvent :=
  popSeqFuel w w.events.length

theorem popSeq_of_popNextEvent_none (w : World)
    (h : w.popNextEvent = none) : popSeq w = [] := by
  dsimp [popSeq]
  cases hl : w.events.length with
  | zero => rfl
  | succ n =>
    dsimp [popSeqFuel]
    rw [h]

private theorem length_eraseIdx_lt {α : Type} (l : List α) (i : Nat)
    (hi : i < l.length) : (l.eraseIdx i).length = l.length - 1 := by
  induction l generalizing i with
  | nil => dsimp [List.length] at hi; omega
  | cons x xs ih =>
    cases i with
    | zero => dsimp [List.eraseIdx, List.length]
    | succ i' =>
      have hi' : i' < xs.length := by dsimp [List.length] at hi; omega
      dsimp [List.eraseIdx, List.length]
      rw [ih i' hi']
      omega

theorem popSeq_of_popNextEvent_some (w : World) (e : ScheduledEvent)
    (w' : World) (h : w.popNextEvent = some (e, w')) :
    popSeq w = e :: popSeq (w'.onScheduledTick e.nodeId) := by
  dsimp [popSeq]
  obtain ⟨idx, hidx, herase, _, _⟩ := popNextEvent_eraseIdx w e w' h
  have hlen : w.events.length = w'.events.length + 1 := by
    rw [herase, length_eraseIdx_lt w.events idx hidx]
    omega
  rw [hlen]
  dsimp [popSeqFuel]
  rw [h]
  dsimp [popSeq]
  obtain ⟨news, hnews, _⟩ := onScheduledTick_events_append w' e.nodeId
  have hflen : (w'.onScheduledTick e.nodeId).events.length =
      w'.events.length + news.length := by
    rw [hnews, List.length_append]
  rw [hflen]
  have hext : popSeqFuel (w'.onScheduledTick e.nodeId)
      (w'.events.length + news.length) =
      popSeqFuel (w'.onScheduledTick e.nodeId) w'.events.length := by
    apply popSeqFuel_extend
    rw [World.onScheduledTick_tick, onScheduledTick_countEventAtThisTick]
    dsimp [countEventAtThisTick]
    exact filter_length_le _ _
  rw [hext]

/-- Every event in a fuel-limited pop sequence targets the starting tick
    and was queued in the starting world. -/
theorem popSeqFuel_mem_due (w : World) (n : Nat) (e : ScheduledEvent)
    (h : e ∈ popSeqFuel w n) : e.targetTick = w.tick ∧ e ∈ w.events := by
  induction n generalizing w with
  | zero => dsimp [popSeqFuel] at h; cases h
  | succ n ih =>
    cases hpop : w.popNextEvent with
    | none =>
      have hseq : popSeqFuel w (n + 1) = [] := by
        dsimp [popSeqFuel]
        rw [hpop]
      rw [hseq] at h
      cases h
    | some pr =>
      rcases pr with ⟨e0, wp⟩
      have hseq : popSeqFuel w (n + 1) =
          e0 :: popSeqFuel (wp.onScheduledTick e0.nodeId) n := by
        dsimp [popSeqFuel]
        rw [hpop]
      rw [hseq] at h
      rcases List.mem_cons.mp h with heq | h
      · obtain ⟨idx, hidx, _, htickE, hget⟩ :=
          popNextEvent_eraseIdx w e0 wp hpop
        refine ⟨by rw [heq]; exact htickE, ?_⟩
        rw [heq, ← hget]
        exact List.getElem_mem hidx
      · obtain ⟨htick, hmem⟩ := ih (wp.onScheduledTick e0.nodeId) h
        constructor
        · rw [htick, World.onScheduledTick_tick,
            World.popNextEvent_tick w e0 wp hpop]
        · obtain ⟨news, hnews, hfut⟩ :=
            onScheduledTick_events_append wp e0.nodeId
          rw [hnews] at hmem
          rcases List.mem_append.mp hmem with hmem | hmem
          · obtain ⟨idx, hidx, herase, _, _⟩ :=
              popNextEvent_eraseIdx w e0 wp hpop
            rw [herase] at hmem
            exact List.mem_of_mem_eraseIdx hmem
          · exfalso
            have hgt := hfut e hmem
            rw [World.popNextEvent_tick w e0 wp hpop] at hgt
            rw [World.onScheduledTick_tick,
              World.popNextEvent_tick w e0 wp hpop] at htick
            omega

/-- Every popped event targets the current tick and was queued. -/
theorem popSeq_mem_due (w : World) (e : ScheduledEvent)
    (h : e ∈ popSeq w) : e.targetTick = w.tick ∧ e ∈ w.events := by
  dsimp [popSeq] at h
  exact popSeqFuel_mem_due w w.events.length e h

/-- A fuel-limited pop sequence that reaches exhaustion has exactly the
    due events, counting multiplicities. -/
theorem popSeqFuel_length (w : World) (n : Nat)
    (hn : countEventAtThisTick w w.tick ≤ n) :
    (popSeqFuel w n).length = countEventAtThisTick w w.tick := by
  induction n generalizing w with
  | zero =>
    have hz : countEventAtThisTick w w.tick = 0 := by omega
    dsimp [popSeqFuel]
    exact hz.symm
  | succ n ih =>
    dsimp [popSeqFuel]
    cases hpop : w.popNextEvent with
    | none =>
      simp
      exact (popNextEvent_none_count_zero w hpop).symm
    | some pr =>
      rcases pr with ⟨e, wp⟩
      dsimp
      have h1 : countEventAtThisTick (wp.onScheduledTick e.nodeId)
          (wp.onScheduledTick e.nodeId).tick =
          countEventAtThisTick wp wp.tick := by
        rw [World.onScheduledTick_tick]
        exact onScheduledTick_countEventAtThisTick wp e.nodeId
      have h2 : wp.tick = w.tick := World.popNextEvent_tick w e wp hpop
      have h3 : countEventAtThisTick wp w.tick =
          countEventAtThisTick w w.tick - 1 :=
        (popNextEvent_remove_one_current_tick_event_if_some w e wp hpop).2
      have hle : countEventAtThisTick (wp.onScheduledTick e.nodeId)
          (wp.onScheduledTick e.nodeId).tick ≤ n := by
        rw [h1, h2, h3]
        omega
      rw [ih (wp.onScheduledTick e.nodeId) hle, h1, h2, h3]
      have hpos : 0 < countEventAtThisTick w w.tick := by
        obtain ⟨idx, hidx, _, htickE, hget⟩ :=
          popNextEvent_eraseIdx w e wp hpop
        have hmem : e ∈ w.events.filter (fun ev => ev.targetTick == w.tick) := by
          rw [List.mem_filter]
          refine ⟨by rw [← hget]; exact List.getElem_mem hidx, ?_⟩
          simp [htickE]
        exact List.length_pos_of_mem hmem
      omega

/-- The pop sequence has exactly the current-tick events, counting
    multiplicities. -/
theorem popSeq_length (w : World) :
    (popSeq w).length = countEventAtThisTick w w.tick := by
  dsimp [popSeq]
  apply popSeqFuel_length
  dsimp [countEventAtThisTick]
  exact filter_length_le _ _

theorem popSeq_nil_iff (w : World) :
    popSeq w = [] ↔ w.popNextEvent = none := by
  cases h : w.popNextEvent with
  | none => simp [popSeq_of_popNextEvent_none w h]
  | some p =>
    rcases p with ⟨e, w'⟩
    simp [popSeq_of_popNextEvent_some w e w' h]

/-- `find?` returning `a` splits the list into a predicate-free prefix,
    `a`, and a tail. -/
private theorem find?_some_first {α : Type} (p : α → Bool) (l : List α)
    (a : α) (h : l.find? p = some a) :
    ∃ pre post, l = pre ++ a :: post ∧ ∀ b ∈ pre, p b = false := by
  induction l generalizing a with
  | nil => cases h
  | cons x xs ih =>
    dsimp [List.find?] at h
    by_cases hpx : p x = true
    · rw [hpx] at h
      have hx : x = a := by simpa using h
      subst hx
      exact ⟨[], xs, rfl, by simp⟩
    · have hpxf : p x = false := by cases px : p x <;> simp_all
      rw [hpxf] at h
      obtain ⟨pre, post, hsplit, hpre⟩ := ih a h
      refine ⟨x :: pre, post, by rw [hsplit, List.cons_append], ?_⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hpxf
      · exact hpre b hb

/-- An element of `take n` appears before position `n` in the original
    list. -/
private theorem mem_take_getElem {α : Type} (l : List α) (n : Nat)
    (a : α) (h : a ∈ l.take n) :
    ∃ (j : Nat) (hj : j < l.length), j < n ∧ l[j]'hj = a := by
  revert n h
  induction l with
  | nil =>
    intro n h
    cases n with
    | zero => dsimp [List.take] at h; cases h
    | succ n' => dsimp [List.take] at h; cases h
  | cons x xs ih =>
    intro n h
    cases n with
    | zero => rw [List.take_zero] at h; cases h
    | succ n' =>
      rw [List.take_succ_cons] at h
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨0, Nat.zero_lt_succ _, Nat.zero_lt_succ _, by simp⟩
      · obtain ⟨j, hj, hjn, hjE⟩ := ih n' h
        refine ⟨j + 1, Nat.succ_lt_succ hj, Nat.succ_lt_succ hjn, ?_⟩
        simpa using hjE

/-- The popped event sits at its first occurrence in the queue: before
    `idx`, no event is due with the popped event's priority (and no event
    equals it). -/
theorem popNextEvent_first_occ (w : World) (e : ScheduledEvent)
    (w' : World) (h : w.popNextEvent = some (e, w')) :
    ∃ (idx : Nat) (hidx : idx < w.events.length),
      w'.events = w.events.eraseIdx idx ∧
      w.events[idx]'hidx = e ∧
      e.targetTick = w.tick ∧
      (∀ j (hj : j < idx),
        ((w.events[j]'(hj.trans hidx)).targetTick == w.tick &&
          (w.events[j]'(hj.trans hidx)).priority == e.priority) = false) ∧
      ∀ j (hj : j < idx), w.events[j]'(hj.trans hidx) ≠ e := by
  unfold popNextEvent at h
  dsimp (config := { zeta := true }) at h
  split at h <;> try contradiction
  · split at h <;> try contradiction
    · rename_i idx evM hfind
      rw [Option.some_inj, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      have hmem := List.mem_of_find?_eq_some hfind
      rw [List.mem_filter] at hmem
      have htick := LawfulBEq.eq_of_beq hmem.2
      have hidx : idx < w.events.length := by
        obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp hmem.1
        simp [List.zip, List.getElem_zipWith, List.getElem_range] at hj hjeq
        omega
      have hget : w.events[idx]'hidx = evM := by
        obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp hmem.1
        simp [List.zip, List.getElem_zipWith, List.getElem_range] at hj hjeq
        exact hjeq.1.symm ▸ hjeq.2
      set candidates :=
        (List.zip (List.range w.events.length) w.events).filter
          (fun x => x.2.targetTick == w.tick) with hcdef
      set minPri := candidates.foldl (fun acc x => min acc x.2.priority)
        ((candidates.head?.map (fun x => x.2.priority)).getD 0) with hmdef
      obtain ⟨pre, post, hsplit, hpre⟩ := find?_some_first
        (fun x => x.2.priority == minPri) candidates (idx, evM) hfind
      have hpair : candidates.Pairwise (fun a b => a.1 < b.1) := by
        have h0 := zip_mapRange_filter_pairwise_fst w.events 0
          (fun x => x.2.targetTick == w.tick)
        convert h0 using 1
        rw [hcdef, range_map_zero_add]
      -- a due event before idx lies in find?'s predicate-free prefix
      have hinpre_of : ∀ j (hj : j < idx),
          (w.events[j]'(hj.trans hidx)).targetTick = w.tick →
          (j, w.events[j]'(hj.trans hidx)) ∈ pre := by
        intro j hj hdue
        have hcand : (j, w.events[j]'(hj.trans hidx)) ∈ candidates := by
          rw [hcdef]
          refine List.mem_filter.mpr
            ⟨mem_zip_range_self w.events j (hj.trans hidx), ?_⟩
          rw [hdue]
          exact nat_beq_true_self _
        have hmem2 : (j, w.events[j]'(hj.trans hidx)) ∈
            pre ++ (idx, evM) :: post := by
          rw [← hsplit]
          exact hcand
        rcases List.mem_append.mp hmem2 with hin | hin
        · exact hin
        · rcases List.mem_cons.mp hin with heqp | hinpost
          · have := congrArg Prod.fst heqp
            dsimp at this
            omega
          · have hpw : ((idx, evM) :: post).Pairwise
                (fun a b => a.1 < b.1) := by
              rw [hsplit] at hpair
              rw [List.pairwise_append] at hpair
              exact hpair.2.1
            have htail : ∀ b ∈ post, idx < b.1 :=
              (List.pairwise_cons.mp hpw).1
            exact absurd (htail _ hinpost) (by omega)
      have hpred : (evM.priority == minPri) = true :=
        find?_some candidates
          (fun x => x.2.priority == minPri) (idx, evM) hfind
      refine ⟨idx, hidx, rfl, hget, htick, ?_, ?_⟩
      · intro j hj
        cases hbeq : ((w.events[j]'(hj.trans hidx)).targetTick == w.tick &&
            (w.events[j]'(hj.trans hidx)).priority == evM.priority)
        · rfl
        · rw [bool_and_eq_true_iff] at hbeq
          have hdue : (w.events[j]'(hj.trans hidx)).targetTick = w.tick :=
            LawfulBEq.eq_of_beq hbeq.1
          have hprie : (w.events[j]'(hj.trans hidx)).priority =
              evM.priority :=
            LawfulBEq.eq_of_beq hbeq.2
          have hfalse := hpre (j, w.events[j]'(hj.trans hidx))
            (hinpre_of j hj hdue)
          have htrue :
              ((w.events[j]'(hj.trans hidx)).priority == minPri) = true := by
            rw [hprie]
            exact hpred
          rw [htrue] at hfalse
          cases hfalse
      · intro j hj heq
        have hdue : (w.events[j]'(hj.trans hidx)).targetTick = w.tick := by
          rw [heq]
          exact htick
        have hfalse := hpre (j, w.events[j]'(hj.trans hidx))
          (hinpre_of j hj hdue)
        have htrue :
            ((w.events[j]'(hj.trans hidx)).priority == minPri) = true := by
          rw [heq]
          exact hpred
        rw [htrue] at hfalse
        cases hfalse


/-! ## Priority-class projection of the pop sequence -/

private theorem filter_eraseIdx_of_false {α : Type} (q : α → Bool)
    (l : List α) (i : Nat) (hi : i < l.length)
    (hq : q (l[i]'hi) = false) :
    (l.eraseIdx i).filter q = l.filter q := by
  induction l generalizing i with
  | nil => dsimp [List.length] at hi; omega
  | cons x xs ih =>
    cases i with
    | zero =>
      have hq' : q x = false := by simpa using hq
      dsimp [List.eraseIdx, List.filter]
      rw [hq']
    | succ i' =>
      have hi' : i' < xs.length := by dsimp [List.length] at hi; omega
      have hq' : q (xs[i']'hi') = false := by simpa using hq
      by_cases hqx : q x = true
      · dsimp [List.eraseIdx, List.filter]
        rw [hqx, ih i' hi' hq']
      · have hqxf : q x = false := by cases qx : q x <;> simp_all
        dsimp [List.eraseIdx, List.filter]
        rw [hqxf, ih i' hi' hq']

private theorem filter_eraseIdx_first_true {α : Type} (q : α → Bool)
    (l : List α) (i : Nat) (hi : i < l.length)
    (hfirst : ∀ j (hj : j < i), q (l[j]'(hj.trans hi)) = false)
    (hq : q (l[i]'hi) = true) :
    l.filter q = l[i]'hi :: (l.eraseIdx i).filter q := by
  induction l generalizing i with
  | nil => dsimp [List.length] at hi; omega
  | cons x xs ih =>
    cases i with
    | zero =>
      have hq' : q x = true := by simpa using hq
      dsimp [List.eraseIdx, List.filter]
      rw [hq']
    | succ i' =>
      have hi' : i' < xs.length := by dsimp [List.length] at hi; omega
      have hqx : q x = false := by simpa using hfirst 0 (by omega)
      have hfirst' : ∀ j (hj : j < i'), q (xs[j]'(hj.trans hi')) = false := by
        intro j hj
        simpa using hfirst (j + 1) (by omega)
      have hq' : q (xs[i']'hi') = true := by simpa using hq
      dsimp [List.filter]
      rw [hqx, ih i' hi' hfirst' hq']

/-- The priority-`p` subsequence of the pop sequence is exactly the
    priority-`p` events targeting the current tick, in queue order. -/
theorem filter_popSeq_priority (w : World) (p : Int) :
    (popSeq w).filter (fun e => e.priority == p) =
      w.events.filter (fun e => e.targetTick == w.tick && e.priority == p) := by
  induction w using World.stepUntilNextTick.induct with
  | case1 x hstep =>
    have hnone : x.popNextEvent = none := by
      dsimp [World.step] at hstep
      cases hp : x.popNextEvent <;> simp_all
    rw [popSeq_of_popNextEvent_none x hnone]
    dsimp
    symm
    have hcnt := popNextEvent_none_count_zero x hnone
    dsimp [countEventAtThisTick] at hcnt
    have hnil : x.events.filter (fun ev => ev.targetTick == x.tick) = [] := by
      cases hl : x.events.filter (fun ev => ev.targetTick == x.tick)
      · rfl
      · simp [hl] at hcnt
    apply List.filter_eq_nil_iff.mpr
    intro e he hq
    rw [bool_and_eq_true_iff] at hq
    have hdue : e.targetTick = x.tick := LawfulBEq.eq_of_beq hq.1
    have hmem : e ∈ x.events.filter (fun ev => ev.targetTick == x.tick) := by
      rw [List.mem_filter]
      refine ⟨he, ?_⟩
      rw [hdue]
      exact nat_beq_true_self _
    rw [hnil] at hmem
    cases hmem
  | case2 x w' hstep ih =>
    dsimp [World.step] at hstep
    cases hpop : x.popNextEvent with
    | none => simp [hpop] at hstep
    | some pr =>
      rcases pr with ⟨e, wp⟩
      have hw' : w' = wp.onScheduledTick e.nodeId := by
        apply Eq.symm
        simpa [World.step, hpop] using hstep
      subst hw'
      rw [popSeq_of_popNextEvent_some x e wp hpop]
      obtain ⟨idx, hidx, herase, hget, htickE, hfreeq, _⟩ :=
        popNextEvent_first_occ x e wp hpop
      obtain ⟨news, hnews, hfut⟩ := onScheduledTick_events_append wp e.nodeId
      -- bridge the IH world's events back to x.events.eraseIdx idx
      have hbridge :
          (wp.onScheduledTick e.nodeId).events.filter
              (fun ev => ev.targetTick == x.tick && ev.priority == p) =
            (x.events.eraseIdx idx).filter
              (fun ev => ev.targetTick == x.tick && ev.priority == p) := by
        rw [hnews, List.filter_append]
        have hnewsnil : news.filter
            (fun ev => ev.targetTick == x.tick && ev.priority == p) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro ev hev hbeq
          rw [bool_and_eq_true_iff] at hbeq
          have heq : ev.targetTick = x.tick :=
            LawfulBEq.eq_of_beq hbeq.1
          have hgt := hfut ev hev
          rw [World.popNextEvent_tick x e wp hpop] at hgt
          omega
        rw [hnewsnil, List.append_nil, herase]
      have htickW : (wp.onScheduledTick e.nodeId).tick = x.tick := by
        rw [World.onScheduledTick_tick,
          World.popNextEvent_tick x e wp hpop]
      rw [htickW] at ih
      -- split on whether e itself has priority p
      by_cases hpe : e.priority = p
      · have hbeq : (e.priority == p) = true := by simp [hpe]
        dsimp only [List.filter]
        rw [hbeq]
        dsimp
        rw [ih, hbridge]
        rw [filter_eraseIdx_first_true
          (fun ev => ev.targetTick == x.tick && ev.priority == p)
          x.events idx hidx]
        · rw [hget]
        · intro j hj
          have := hfreeq j hj
          rwa [← hpe]
        · rw [hget, htickE]
          simp [hbeq]
      · have hbfalse : (e.priority == p) = false :=
          int_beq_false_of_ne _ _ hpe
        dsimp only [List.filter]
        rw [hbfalse]
        dsimp
        rw [ih, hbridge]
        apply filter_eraseIdx_of_false
          (fun ev => ev.targetTick == x.tick && ev.priority == p)
          x.events idx hidx
        rw [hget, htickE, nat_beq_true_self x.tick]
        change (e.priority == p) = false
        exact hbfalse

/-- The pop sequence is sorted by priority. -/
theorem popSeq_sorted_priority (w : World) :
    (popSeq w).Pairwise (fun a b => a.priority ≤ b.priority) := by
  induction w using World.stepUntilNextTick.induct with
  | case1 x hstep =>
    have hnone : x.popNextEvent = none := by
      dsimp [World.step] at hstep
      cases hp : x.popNextEvent <;> simp_all
    simp [popSeq_of_popNextEvent_none x hnone]
  | case2 x w' hstep ih =>
    dsimp [World.step] at hstep
    cases hpop : x.popNextEvent with
    | none => simp [hpop] at hstep
    | some pr =>
      rcases pr with ⟨e, wp⟩
      have hw' : w' = wp.onScheduledTick e.nodeId := by
        apply Eq.symm
        simpa [World.step, hpop] using hstep
      subst hw'
      rw [popSeq_of_popNextEvent_some x e wp hpop]
      obtain ⟨_, _, _, _, hleM, _⟩ :=
        popNextEvent_is_min_earliest x e wp hpop
      refine List.pairwise_cons.mpr ⟨?_, ih⟩
      intro b hb
      obtain ⟨htick, hmem⟩ :=
        popSeq_mem_due (wp.onScheduledTick e.nodeId) b hb
      have htick' : b.targetTick = x.tick := by
        rw [htick, World.onScheduledTick_tick,
          World.popNextEvent_tick x e wp hpop]
      obtain ⟨news, hnews, hfut⟩ :=
        onScheduledTick_events_append wp e.nodeId
      have hmem' : b ∈ wp.events := by
        rw [hnews] at hmem
        rcases List.mem_append.mp hmem with hmem | hmem
        · exact hmem
        · exfalso
          have := hfut b hmem
          rw [World.popNextEvent_tick x e wp hpop] at this
          omega
      obtain ⟨idx, hidx, herase, _, _⟩ :=
        popNextEvent_eraseIdx x e wp hpop
      rw [herase] at hmem'
      have hmemx : b ∈ x.events := List.mem_of_mem_eraseIdx hmem'
      obtain ⟨j, hj, hjE⟩ := List.mem_iff_getElem.mp hmemx
      rw [← hjE]
      exact hleM j hj (by rw [hjE]; exact htick')

/-! ## The pop sequence depends only on the due events -/

private theorem take_add_drop {α : Type} (l : List α) (i : Nat) :
    l.take i ++ l.drop i = l := by
  induction l generalizing i with
  | nil => cases i <;> rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i' =>
      dsimp [List.take, List.drop]
      rw [ih i']

private theorem drop_cons_getElem {α : Type} (l : List α) (i : Nat)
    (hi : i < l.length) : l.drop i = l[i]'hi :: l.drop (i + 1) := by
  revert hi
  induction l generalizing i with
  | nil => intro hi; dsimp [List.length] at hi; omega
  | cons x xs ih =>
    intro hi
    cases i with
    | zero => dsimp [List.drop]
    | succ i' =>
      have hi' : i' < xs.length := by dsimp [List.length] at hi; omega
      dsimp only [List.drop]
      change xs.drop i' = xs[i']'hi' :: xs.drop (i' + 1)
      exact ih i' hi'

/-- `eraseIdx` as a take/drop splice. -/
private theorem eraseIdx_take_drop {α : Type} (l : List α) (i : Nat)
    (hi : i < l.length) : l.eraseIdx i = l.take i ++ l.drop (i + 1) := by
  induction l generalizing i with
  | nil => dsimp [List.length] at hi; omega
  | cons x xs ih =>
    cases i with
    | zero => dsimp [List.eraseIdx, List.take, List.drop]
    | succ i' =>
      have hi' : i' < xs.length := by dsimp [List.length] at hi; omega
      dsimp [List.eraseIdx, List.take, List.drop]
      rw [ih i' hi']

/-- Splitting a filter at a predicate-satisfying position. -/
private theorem filter_split_at {α : Type} (q : α → Bool) (l : List α)
    (i : Nat) (hi : i < l.length) (hq : q (l[i]'hi) = true) :
    l.filter q =
      (l.take i).filter q ++ l[i]'hi :: (l.drop (i + 1)).filter q := by
  have hsplit : l = l.take i ++ l[i]'hi :: l.drop (i + 1) := by
    have h1 := take_add_drop l i
    rw [drop_cons_getElem l i hi] at h1
    exact h1.symm
  rw (occs := [1]) [hsplit]
  rw [List.filter_append]
  have hsingle : (l[i]'hi :: l.drop (i + 1)).filter q =
      l[i]'hi :: (l.drop (i + 1)).filter q := by
    dsimp [List.filter]
    rw [hq]
  rw [hsingle]

private theorem append_left_cancel {α : Type} (t l₁ l₂ : List α)
    (h : t ++ l₁ = t ++ l₂) : l₁ = l₂ := by
  induction t generalizing l₁ l₂ with
  | nil => simpa using h
  | cons x xs ih =>
    change x :: (xs ++ l₁) = x :: (xs ++ l₂) at h
    rw [List.cons.injEq] at h
    exact ih l₁ l₂ h.2

/-- Two elements that are each the first `q`-element of the same list are
    equal. -/
private theorem first_occ_unique {α : Type} (q : α → Bool) (L : List α)
    (a b : α) (pre₁ pre₂ post₁ post₂ : List α)
    (h₁ : L = pre₁ ++ a :: post₁) (h₂ : L = pre₂ ++ b :: post₂)
    (ha : q a = true) (hb : q b = true)
    (hn₁ : ∀ x ∈ pre₁, q x = false) (hn₂ : ∀ x ∈ pre₂, q x = false) :
    a = b := by
  suffices hcl : ∀ (p₁ p₂ : List α),
      p₁ ++ a :: post₁ = p₂ ++ b :: post₂ →
      (∀ x ∈ p₁, q x = false) → (∀ x ∈ p₂, q x = false) →
      p₁ = p₂ ∧ a = b by
    exact (hcl pre₁ pre₂ (h₁.symm.trans h₂) hn₁ hn₂).2
  intro p₁ p₂
  induction p₁ generalizing p₂ with
  | nil =>
    cases p₂ with
    | nil =>
      intro hs _ _
      dsimp at hs
      rw [List.cons.injEq] at hs
      exact ⟨rfl, hs.1⟩
    | cons y ys =>
      intro hs _ hf₂
      have hqy : q y = false := hf₂ y (List.mem_cons.mpr (Or.inl rfl))
      dsimp at hs
      rw [List.cons.injEq] at hs
      rw [hs.1] at ha
      rw [ha] at hqy
      cases hqy
  | cons x xs ih =>
    cases p₂ with
    | nil =>
      intro hs hf₁ _
      have hqx : q x = false := hf₁ x (List.mem_cons.mpr (Or.inl rfl))
      dsimp at hs
      rw [List.cons.injEq] at hs
      rw [← hs.1] at hb
      rw [hb] at hqx
      cases hqx
    | cons y ys =>
      intro hs hf₁ hf₂
      dsimp at hs
      rw [List.cons.injEq] at hs
      rcases hs with ⟨hxy, htail⟩
      have hf₁t : ∀ z ∈ xs, q z = false :=
        fun z hz => hf₁ z (List.mem_cons.mpr (Or.inr hz))
      have hf₂t : ∀ z ∈ ys, q z = false :=
        fun z hz => hf₂ z (List.mem_cons.mpr (Or.inr hz))
      obtain ⟨hxs, hab⟩ := ih ys htail hf₁t hf₂t
      exact ⟨by rw [hxy, hxs], hab⟩

/-- Erasing at the first occurrence is erasing by value. -/
theorem eraseIdx_eq_eraseEv (l : List ScheduledEvent)
    (i : Nat) (hi : i < l.length) (e : ScheduledEvent)
    (hget : l[i]'hi = e)
    (hfirst : ∀ j (hj : j < i), l[j]'(hj.trans hi) ≠ e) :
    l.eraseIdx i = eraseEv e l := by
  induction l generalizing i with
  | nil => dsimp [List.length] at hi; omega
  | cons x xs ih =>
    cases i with
    | zero =>
      dsimp [List.eraseIdx, eraseEv]
      split
      · rfl
      · rename_i hne
        exfalso
        exact hne hget
    | succ i' =>
      have hi' : i' < xs.length := by dsimp [List.length] at hi; omega
      have hne : x ≠ e := hfirst 0 (by omega)
      have hfirst' : ∀ j (hj : j < i'), xs[j]'(hj.trans hi') ≠ e :=
        fun j hj => hfirst (j + 1) (by omega)
      dsimp [List.eraseIdx, eraseEv]
      split
      · rename_i heq
        exfalso
        exact hne heq
      · rw [ih i' hi' hget hfirst']

private theorem eraseEv_first_occ (pre post : List ScheduledEvent)
    (a : ScheduledEvent) (hn : a ∉ pre) :
    eraseEv a (pre ++ a :: post) = pre ++ post := by
  induction pre with
  | nil =>
    dsimp [eraseEv]
    split
    · rfl
    · contradiction
  | cons x xs ih =>
    have hne : x ≠ a :=
      fun h => hn (by rw [h]; exact List.mem_cons.mpr (Or.inl rfl))
    have hn' : a ∉ xs := fun h => hn (List.mem_cons.mpr (Or.inr h))
    dsimp [eraseEv]
    split
    · rename_i heq
      exfalso
      exact hne heq
    · rw [ih hn']

/-- `popNextEvent` does not change the node list. -/
theorem popNextEvent_nodes (w : World) (e : ScheduledEvent) (w' : World)
    (h : w.popNextEvent = some (e, w')) : w'.nodes = w.nodes := by
  unfold popNextEvent at h
  dsimp (config := { zeta := true }) at h
  split at h <;> try contradiction
  · split at h <;> try contradiction
    · rw [Option.some_inj, Prod.mk.injEq] at h
      obtain ⟨_, hw'⟩ := h
      rw [← hw']

/-- `popNextEvent` does not change the output log. -/
theorem popNextEvent_outputLog (w : World) (e : ScheduledEvent)
    (w' : World) (h : w.popNextEvent = some (e, w')) :
    w'.outputLog = w.outputLog := by
  unfold popNextEvent at h
  dsimp (config := { zeta := true }) at h
  split at h <;> try contradiction
  · split at h <;> try contradiction
    · rw [Option.some_inj, Prod.mk.injEq] at h
      obtain ⟨_, hw'⟩ := h
      rw [← hw']

/-- The pop sequence depends only on the tick and the due events:
    appending or reordering future events never changes it. -/
theorem popSeq_congr_due (w₁ w₂ : World) (htick : w₁.tick = w₂.tick)
    (hdue : w₁.events.filter (fun e => e.targetTick == w₁.tick) =
        w₂.events.filter (fun e => e.targetTick == w₂.tick)) :
    popSeq w₁ = popSeq w₂ := by
  induction w₁ using World.stepUntilNextTick.induct generalizing w₂ with
  | case1 x hstep =>
    have hnone : x.popNextEvent = none := by
      dsimp [World.step] at hstep
      cases hp : x.popNextEvent <;> simp_all
    have hcnt := popNextEvent_none_count_zero x hnone
    dsimp [countEventAtThisTick] at hcnt
    have hnil : x.events.filter (fun e => e.targetTick == x.tick) = [] := by
      cases hl : x.events.filter (fun e => e.targetTick == x.tick)
      · rfl
      · simp [hl] at hcnt
    have hdue2 : w₂.events.filter (fun e => e.targetTick == w₂.tick) = [] := by
      rw [← hdue, hnil]
    have hcnt2 : countEventAtThisTick w₂ w₂.tick = 0 := by
      dsimp [countEventAtThisTick]
      rw [hdue2]
      rfl
    have hnone2 : w₂.popNextEvent = none :=
      popNextEvent_none_of_count_zero w₂ hcnt2
    rw [popSeq_of_popNextEvent_none x hnone,
      popSeq_of_popNextEvent_none w₂ hnone2]
  | case2 x w' hstep ih =>
    dsimp [World.step] at hstep
    cases hpop : x.popNextEvent with
    | none => simp [hpop] at hstep
    | some pr =>
      rcases pr with ⟨e₁, wp₁⟩
      have hw' : w' = wp₁.onScheduledTick e₁.nodeId := by
        apply Eq.symm
        simpa [World.step, hpop] using hstep
      subst hw'
      -- w₂ also pops
      have hcnt2 : 0 < countEventAtThisTick w₂ w₂.tick := by
        dsimp [countEventAtThisTick]
        have hmem : e₁ ∈
            w₂.events.filter (fun e => e.targetTick == w₂.tick) := by
          rw [← hdue, List.mem_filter]
          obtain ⟨idx, hidx, _, htickE, hget⟩ :=
            popNextEvent_eraseIdx x e₁ wp₁ hpop
          refine ⟨by rw [← hget]; exact List.getElem_mem hidx, ?_⟩
          simp [htickE, htick]
        exact List.length_pos_of_mem hmem
      obtain ⟨e₂, wp₂, hpop₂⟩ := popNextEvent_some_of_count_pos w₂ hcnt2
      -- both pops pick the same event
      have heq : e₁ = e₂ := by
        obtain ⟨idx₁, hidx₁, hget₁, htick₁, hle₁, hlt₁⟩ :=
          popNextEvent_is_min_earliest x e₁ wp₁ hpop
        obtain ⟨idx₂, hidx₂, hget₂, htick₂, hle₂, hlt₂⟩ :=
          popNextEvent_is_min_earliest w₂ e₂ wp₂ hpop₂
        set D := x.events.filter (fun e => e.targetTick == x.tick)
          with hDdef
        have he₁D : e₁ ∈ D := by
          rw [hDdef, List.mem_filter]
          refine ⟨by rw [← hget₁]; exact List.getElem_mem hidx₁, ?_⟩
          simp [htick₁]
        have he₂D : e₂ ∈ D := by
          rw [hdue, List.mem_filter]
          refine ⟨by rw [← hget₂]; exact List.getElem_mem hidx₂, ?_⟩
          simp [htick₂]
        have hpri : e₁.priority = e₂.priority := by
          apply le_antisymm
          · obtain ⟨j, hj, hjE⟩ :=
              List.mem_iff_getElem.mp (List.mem_filter.mp he₂D).1
            have hdue : (x.events[j]'hj).targetTick = x.tick := by
              rw [hjE, htick₂, ← htick]
            have := hle₁ j hj hdue
            rwa [hjE] at this
          · have he₁D₂ : e₁ ∈ w₂.events.filter
                (fun e => e.targetTick == w₂.tick) := by
              rwa [hdue] at he₁D
            obtain ⟨j, hj, hjE⟩ :=
              List.mem_iff_getElem.mp (List.mem_filter.mp he₁D₂).1
            have hdue : (w₂.events[j]'hj).targetTick = w₂.tick := by
              rw [hjE, htick₁, htick]
            have := hle₂ j hj hdue
            rwa [hjE] at this
        -- first occurrence in the shared due list
        have hsplit₁ : D = (x.events.take idx₁).filter
            (fun e => e.targetTick == x.tick) ++
            e₁ :: (x.events.drop (idx₁ + 1)).filter
            (fun e => e.targetTick == x.tick) := by
          have := filter_split_at (fun e => e.targetTick == x.tick)
            x.events idx₁ hidx₁
              (by rw [hget₁, htick₁]; exact nat_beq_true_self x.tick)
          rwa [← hDdef, hget₁] at this
        have hsplit₂ : D = (w₂.events.take idx₂).filter
            (fun e => e.targetTick == w₂.tick) ++
            e₂ :: (w₂.events.drop (idx₂ + 1)).filter
            (fun e => e.targetTick == w₂.tick) := by
          have := filter_split_at (fun e => e.targetTick == w₂.tick)
            w₂.events idx₂ hidx₂
              (by rw [hget₂, htick₂]; exact nat_beq_true_self w₂.tick)
          rwa [← hdue, hget₂] at this
        apply first_occ_unique
          (fun e => decide (e.priority = e₁.priority)) D e₁ e₂
        · exact hsplit₁
        · exact hsplit₂
        · rw [decide_eq_true_eq]
        · rw [hpri, decide_eq_true_eq]
        · intro ev hev
          rw [List.mem_filter] at hev
          obtain ⟨j, hj, hjn, hjE⟩ := mem_take_getElem _ _ _ hev.1
          have hdue : (x.events[j]'(hjn.trans hidx₁)).targetTick = x.tick := by
            rw [hjE]
            exact LawfulBEq.eq_of_beq hev.2
          have hlt := hlt₁ j hjn hdue
          exact decide_eq_false_of_not (ev.priority = e₁.priority) (by
            intro heq
            rw [← hjE] at heq
            rw [heq] at hlt
            omega)
        · intro ev hev
          rw [List.mem_filter] at hev
          obtain ⟨j, hj, hjn, hjE⟩ := mem_take_getElem _ _ _ hev.1
          have hdue : (w₂.events[j]'(hjn.trans hidx₂)).targetTick = w₂.tick := by
            rw [hjE]
            exact LawfulBEq.eq_of_beq hev.2
          have hlt := hlt₂ j hjn hdue
          exact decide_eq_false_of_not (ev.priority = e₁.priority) (by
            intro heq
            rw [← hjE] at heq
            rw [heq, hpri] at hlt
            omega)
      subst heq
      -- the residual due filters agree
      obtain ⟨idxM₁, hidxM₁, heraseM₁, hgetM₁, htickM₁, _, hfirstM₁⟩ :=
        popNextEvent_first_occ x e₁ wp₁ hpop
      obtain ⟨idxM₂, hidxM₂, heraseM₂, hgetM₂, htickM₂, _, hfirstM₂⟩ :=
        popNextEvent_first_occ w₂ e₁ wp₂ hpop₂
      obtain ⟨news₁, hnews₁, hfut₁⟩ :=
        onScheduledTick_events_append wp₁ e₁.nodeId
      obtain ⟨news₂, hnews₂, hfut₂⟩ :=
        onScheduledTick_events_append wp₂ e₁.nodeId
      have hdue' :
          (wp₁.onScheduledTick e₁.nodeId).events.filter
              (fun e => e.targetTick ==
                (wp₁.onScheduledTick e₁.nodeId).tick) =
          (wp₂.onScheduledTick e₁.nodeId).events.filter
              (fun e => e.targetTick ==
                (wp₂.onScheduledTick e₁.nodeId).tick) := by
        rw [World.onScheduledTick_tick,
          World.popNextEvent_tick x e₁ wp₁ hpop,
          World.onScheduledTick_tick,
          World.popNextEvent_tick w₂ e₁ wp₂ hpop₂]
        rw [hnews₁, hnews₂, List.filter_append, List.filter_append]
        have hnil₁ : news₁.filter
            (fun e => e.targetTick == x.tick) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro ev hev hbeq
          have hgt := hfut₁ ev hev
          rw [World.popNextEvent_tick x e₁ wp₁ hpop] at hgt
          have heq := LawfulBEq.eq_of_beq hbeq
          omega
        have hnil₂ : news₂.filter
            (fun e => e.targetTick == w₂.tick) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro ev hev hbeq
          have hgt := hfut₂ ev hev
          rw [World.popNextEvent_tick w₂ e₁ wp₂ hpop₂] at hgt
          have heq := LawfulBEq.eq_of_beq hbeq
          omega
        rw [hnil₁, hnil₂, List.append_nil, List.append_nil,
          heraseM₁, heraseM₂]
        set D := x.events.filter (fun e => e.targetTick == x.tick)
          with hDdef
        have hfil₁ : (x.events.eraseIdx idxM₁).filter
            (fun e => e.targetTick == x.tick) = eraseEv e₁ D := by
          have hsplitD : D = (x.events.take idxM₁).filter
              (fun e => e.targetTick == x.tick) ++
              e₁ :: (x.events.drop (idxM₁ + 1)).filter
              (fun e => e.targetTick == x.tick) := by
            have := filter_split_at (fun e => e.targetTick == x.tick)
              x.events idxM₁ hidxM₁
                (by rw [hgetM₁, htickM₁]; exact nat_beq_true_self x.tick)
            rwa [← hDdef, hgetM₁] at this
          have hnpre : e₁ ∉ (x.events.take idxM₁).filter
              (fun e => e.targetTick == x.tick) := by
            intro hm
            obtain ⟨j, hj, hjn, hjE⟩ := mem_take_getElem _ _ _
              (List.mem_of_mem_filter hm)
            exact hfirstM₁ j hjn hjE
          rw [eraseIdx_take_drop x.events idxM₁ hidxM₁,
            List.filter_append, hsplitD]
          rw [eraseEv_first_occ _ _ e₁ hnpre]
        have hfil₂ : (w₂.events.eraseIdx idxM₂).filter
            (fun e => e.targetTick == w₂.tick) = eraseEv e₁ D := by
          have hsplitD : D = (w₂.events.take idxM₂).filter
              (fun e => e.targetTick == w₂.tick) ++
              e₁ :: (w₂.events.drop (idxM₂ + 1)).filter
              (fun e => e.targetTick == w₂.tick) := by
            have := filter_split_at (fun e => e.targetTick == w₂.tick)
              w₂.events idxM₂ hidxM₂
                (by rw [hgetM₂, htickM₂]; exact nat_beq_true_self w₂.tick)
            rwa [← hdue, hgetM₂] at this
          have hnpre : e₁ ∉ (w₂.events.take idxM₂).filter
              (fun e => e.targetTick == w₂.tick) := by
            intro hm
            obtain ⟨j, hj, hjn, hjE⟩ := mem_take_getElem _ _ _
              (List.mem_of_mem_filter hm)
            exact hfirstM₂ j hjn hjE
          rw [eraseIdx_take_drop w₂.events idxM₂ hidxM₂,
            List.filter_append, hsplitD]
          rw [eraseEv_first_occ _ _ e₁ hnpre]
        rw [hfil₁, hfil₂]
      have htick' : (wp₁.onScheduledTick e₁.nodeId).tick =
          (wp₂.onScheduledTick e₁.nodeId).tick := by
        rw [World.onScheduledTick_tick,
          World.popNextEvent_tick x e₁ wp₁ hpop,
          World.onScheduledTick_tick,
          World.popNextEvent_tick w₂ e₁ wp₂ hpop₂]
        exact htick
      have hih := ih (wp₂.onScheduledTick e₁.nodeId) htick' hdue'
      rw [popSeq_of_popNextEvent_some x e₁ wp₁ hpop,
        popSeq_of_popNextEvent_some w₂ e₁ wp₂ hpop₂, hih]

/-! ## Consequences of due-only dependence -/

/-- Appending an event for a future tick does not change the pop
    sequence. -/
theorem popSeq_scheduleEvent_of_future (w : World) (ev : ScheduledEvent)
    (hf : ev.targetTick > w.tick) :
    popSeq (w.scheduleEvent ev) = popSeq w := by
  apply popSeq_congr_due (w.scheduleEvent ev) w
  · rfl
  · rw [World.scheduleEvent_events, World.scheduleEvent_tick,
      List.filter_append]
    have hnil : [ev].filter
        (fun e => e.targetTick == w.tick) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro e he hbeq
      rcases List.mem_singleton.mp he with rfl
      have heqT := LawfulBEq.eq_of_beq hbeq
      omega
    rw [hnil, List.append_nil]

/-- `activateChain` appends a future event, so it preserves the pop
    sequence. -/
theorem popSeq_activateChain (w : World) (obs : Nat) :
    popSeq (activateChain w obs) = popSeq w := by
  dsimp [activateChain]
  apply popSeq_scheduleEvent_of_future
  dsimp
  omega

/-- `processNEvents` pops a prefix of the pop sequence. -/
theorem popSeq_processNEvents (w : World) (n : Nat) :
    popSeq (processNEvents w n) = (popSeq w).drop n := by
  induction n generalizing w with
  | zero => simp [processNEvents]
  | succ n ih =>
    dsimp [processNEvents]
    cases hstep : w.step with
    | none =>
      have hnone : w.popNextEvent = none := by
        dsimp [World.step] at hstep
        cases hp : w.popNextEvent <;> simp_all
      simp [popSeq_of_popNextEvent_none w hnone]
    | some w' =>
      dsimp [World.step] at hstep
      cases hpop : w.popNextEvent with
      | none => simp [hpop] at hstep
      | some pr =>
        rcases pr with ⟨e, wp⟩
        have hw' : w' = wp.onScheduledTick e.nodeId := by
          apply Eq.symm
          simpa [World.step, hpop] using hstep
        subst hw'
        rw [ih, popSeq_of_popNextEvent_some w e wp hpop]
        rfl

/-! ## The general drain characterization -/

/-- Draining a tick fires exactly the pop sequence, in pop order.
    `spawn e` is the list of events the firing of `e` appends, and
    `logLen e` the number of log entries it adds. The obligations are
    world-generic so that the characterization also holds for every
    intermediate world of the drain. `hfire` carries the node-level
    content for the k-th pop of world `v`: it receives the frame (nodes
    outside the fired prefix read as in `v`) and must deliver the
    event/log effect plus locality. -/
theorem stepUntilNextTick_general_drain (w : World)
    (spawn : ScheduledEvent → List ScheduledEvent)
    (logLen : ScheduledEvent → Nat)
    (hfut : ∀ (v : World) (e : ScheduledEvent), e ∈ v.events →
        e.targetTick = v.tick → ∀ e' ∈ spawn e, e'.targetTick > v.tick)
    (hfire : ∀ (v : World) (k : Nat) (hk : k < (popSeq v).length)
        (u : World),
        u.tick = v.tick →
        u.events = eraseEvents v.events ((popSeq v).take (k + 1)) ++
            spawnFold spawn ((popSeq v).take k) →
        (∀ id, id ∉ ((popSeq v).take k).map (fun e => e.nodeId) →
          u.getNode id = v.getNode id) →
        ∃ msgs : List String,
          (u.onScheduledTick ((popSeq v)[k]'hk).nodeId).events =
            u.events ++ spawn ((popSeq v)[k]'hk) ∧
          (u.onScheduledTick ((popSeq v)[k]'hk).nodeId).outputLog =
            u.outputLog ++ msgs ∧
          msgs.length = logLen ((popSeq v)[k]'hk) ∧
          ∀ id, id ≠ ((popSeq v)[k]'hk).nodeId →
            (u.onScheduledTick ((popSeq v)[k]'hk).nodeId).getNode id =
              u.getNode id) :
    w.stepUntilNextTick.tick = w.tick + 1 ∧
    w.stepUntilNextTick.events =
      eraseEvents w.events (popSeq w) ++ spawnFold spawn (popSeq w) ∧
    ∃ msgs, w.stepUntilNextTick.outputLog = w.outputLog ++ msgs ∧
      msgs.length = ((popSeq w).map logLen).sum := by
  induction w using World.stepUntilNextTick.induct with
  | case1 x hstep =>
    have hnone : x.popNextEvent = none := by
      dsimp [World.step] at hstep
      cases hp : x.popNextEvent <;> simp_all
    have hseq : popSeq x = [] := popSeq_of_popNextEvent_none x hnone
    rw [stepUntilNextTick_of_step_none x hstep]
    refine ⟨rfl, ?_, ?_⟩
    · rw [hseq]
      dsimp [eraseEvents, spawnFold]
      rw [List.append_nil]
    · refine ⟨[], ?_, ?_⟩
      · rw [List.append_nil]
      · rw [hseq]
        simp
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
      set es := popSeq (wp.onScheduledTick e0.nodeId) with hesdef
      have hseq : popSeq x = e0 :: es := by
        rw [popSeq_of_popNextEvent_some x e0 wp hpop, hesdef]
      have hstepUNT : x.stepUntilNextTick =
          (wp.onScheduledTick e0.nodeId).stepUntilNextTick := by
        rw [World.stepUntilNextTick]
        dsimp [World.step]
        rw [hpop]
      obtain ⟨idx, hidx, herase, hget, htickE, _, hfirst⟩ :=
        popNextEvent_first_occ x e0 wp hpop
      -- wp is x with e0 removed
      have hwpEv : wp.events = eraseEvents x.events ((popSeq x).take 1) := by
        rw [hseq]
        change wp.events = eraseEvents x.events [e0]
        rw [herase, eraseIdx_eq_eraseEv x.events idx hidx e0 hget hfirst]
        dsimp [eraseEvents]
      -- firing e0 (k = 0)
      obtain ⟨msgs0, hev0, hlog0, hlen0, hloc0⟩ :=
        hfire x 0 (by rw [hseq]; exact Nat.zero_lt_succ _) wp
          (World.popNextEvent_tick x e0 wp hpop)
          (by rw [hwpEv]; dsimp [spawnFold]; rw [List.append_nil])
          (by intro id _; dsimp [World.getNode]; rw [popNextEvent_nodes x e0 wp hpop])
      -- normalize the (popSeq x)[0] lookups to e0
      have hev0' : (wp.onScheduledTick e0.nodeId).events =
          wp.events ++ spawn e0 := by simpa [hseq] using hev0
      have hlog0' : (wp.onScheduledTick e0.nodeId).outputLog =
          wp.outputLog ++ msgs0 := by simpa [hseq] using hlog0
      have hlen0' : msgs0.length = logLen e0 := by simpa [hseq] using hlen0
      -- apply the IH to the fired world
      obtain ⟨htik', hevs', msgs', hlog', hlen'⟩ := ih
      refine ⟨?_, ?_, ?_⟩
      · rw [hstepUNT, htik', World.onScheduledTick_tick,
          World.popNextEvent_tick x e0 wp hpop]
      · rw [hstepUNT, hevs', hesdef, hev0']
        have havoid : ∀ e ∈ es, e ∉ spawn e0 := by
          intro e he
          have hdue : e.targetTick = x.tick := by
            have := popSeq_mem_due (wp.onScheduledTick e0.nodeId) e
              (by rwa [← hesdef])
            rw [this.1, World.onScheduledTick_tick,
              World.popNextEvent_tick x e0 wp hpop]
          intro hm
          have hgt := hfut x e0
            (by rw [← hget]; exact List.getElem_mem hidx) htickE e hm
          omega
        rw [eraseEvents_append_right wp.events (spawn e0) es havoid]
        have htake : (popSeq x).take 1 = [e0] := by rw [hseq]; rfl
        rw [hwpEv, htake]
        rw [← eraseEvents_append x.events [e0] es]
        dsimp [spawnFold]
        rw [hseq]
        exact List.append_assoc _ _ _
      · refine ⟨msgs0 ++ msgs', ?_, ?_⟩
        · rw [hstepUNT, hlog', hlog0']
          rw [popNextEvent_outputLog x e0 wp hpop]
          rw [← List.append_assoc]
        · rw [List.length_append, hlen0', hlen', hseq]
          simp [List.map]

/-! ## Erasing the whole pop sequence -/

private theorem append_right_cancel {α : Type} (l₁ l₂ t : List α)
    (h : l₁ ++ t = l₂ ++ t) : l₁ = l₂ := by
  have hlen : l₁.length = l₂.length := by
    have := congrArg List.length h
    simp at this
    omega
  exact (List.append_inj h hlen).1

/-- Erasing the whole pop sequence removes exactly the due events. -/
theorem eraseEvents_popSeq_eq_filter (w : World) :
    eraseEvents w.events (popSeq w) =
      w.events.filter (fun e => !(e.targetTick == w.tick)) := by
  induction w using World.stepUntilNextTick.induct with
  | case1 x hstep =>
    have hnone : x.popNextEvent = none := by
      dsimp [World.step] at hstep
      cases hp : x.popNextEvent <;> simp_all
    rw [popSeq_of_popNextEvent_none x hnone]
    dsimp [eraseEvents]
    have hcnt := popNextEvent_none_count_zero x hnone
    dsimp [countEventAtThisTick] at hcnt
    symm
    apply List.filter_eq_self.mpr
    intro e he
    by_cases hb : (e.targetTick == x.tick) = true
    · exfalso
      have hmem : e ∈ x.events.filter (fun ev => ev.targetTick == x.tick) :=
        List.mem_filter.mpr ⟨he, hb⟩
      have hnil : x.events.filter (fun ev => ev.targetTick == x.tick) = [] := by
        cases hl : x.events.filter (fun ev => ev.targetTick == x.tick)
        · rfl
        · simp [hl] at hcnt
      rw [hnil] at hmem
      cases hmem
    · have hbf : (e.targetTick == x.tick) = false := by
        cases hb' : e.targetTick == x.tick <;> simp_all
      simp [hbf]
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
      obtain ⟨idx, hidx, herase, hget, htickE, _, hfirst⟩ :=
        popNextEvent_first_occ x e0 wp hpop
      rw [popSeq_of_popNextEvent_some x e0 wp hpop, eraseEvents_cons]
      have heraseEq : eraseEv e0 x.events = wp.events := by
        rw [herase, eraseIdx_eq_eraseEv x.events idx hidx e0 hget hfirst]
      rw [heraseEq]
      obtain ⟨news, hnews, hfutN⟩ :=
        onScheduledTick_events_append wp e0.nodeId
      have havoid : ∀ e ∈ popSeq (wp.onScheduledTick e0.nodeId),
          e ∉ news := by
        intro e he
        have hdue := (popSeq_mem_due _ e he).1
        intro hm
        have hgt := hfutN e hm
        rw [World.onScheduledTick_tick,
          World.popNextEvent_tick x e0 wp hpop] at hdue
        rw [World.popNextEvent_tick x e0 wp hpop] at hgt
        omega
      have hlhs : eraseEvents wp.events
          (popSeq (wp.onScheduledTick e0.nodeId)) ++ news =
          eraseEvents (wp.events ++ news)
            (popSeq (wp.onScheduledTick e0.nodeId)) := by
        rw [eraseEvents_append_right wp.events news _ havoid]
      have hnewsfil : news.filter (fun e => !(e.targetTick == x.tick)) =
          news := by
        apply List.filter_eq_self.mpr
        intro e he
        have hgt := hfutN e he
        rw [World.popNextEvent_tick x e0 wp hpop] at hgt
        have hbf : (e.targetTick == x.tick) = false := by
          cases hb : e.targetTick == x.tick
          · rfl
          · exfalso
            have := LawfulBEq.eq_of_beq hb
            omega
        simp [hbf]
      have hrhs : (wp.events ++ news).filter
          (fun e => !(e.targetTick == x.tick)) =
          wp.events.filter (fun e => !(e.targetTick == x.tick)) ++ news := by
        rw [List.filter_append, hnewsfil]
      have htickW : (wp.onScheduledTick e0.nodeId).tick = x.tick := by
        rw [World.onScheduledTick_tick, World.popNextEvent_tick x e0 wp hpop]
      have hih := ih
      rw [hnews] at hih
      rw [htickW] at hih
      have heq2 : eraseEvents wp.events
          (popSeq (wp.onScheduledTick e0.nodeId)) =
          wp.events.filter (fun e => !(e.targetTick == x.tick)) := by
        apply append_right_cancel _ _ news
        rw [hlhs, hih, hrhs]
      rw [heq2]
      have hxfil : x.events.filter (fun e => !(e.targetTick == x.tick)) =
          wp.events.filter (fun e => !(e.targetTick == x.tick)) := by
        rw [herase]
        apply Eq.symm
        apply filter_eraseIdx_of_false
          (fun e => !(e.targetTick == x.tick)) x.events idx hidx
        rw [hget, htickE]
        simp
      rw [← hxfil]
