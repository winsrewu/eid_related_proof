import Proofs.Model.Basic
import Proofs.Model.SimLemmas
import Proofs.Model.NodeLayout
import Proofs.Model.WorldInvariants
import Mathlib.Data.List.Defs
import Mathlib.Data.List.Basic
import Mathlib.Tactic


open BasicRedstoneSim
open World

/-! # Candidate-count facts for `popNextEvent`

`popNextEvent` filters the zipped `(index, event)` list down to the events
targeting the current tick. The number of such candidates is exactly
`countEventAtThisTick`. These facts power the drain/FIFO reasoning. -/

/-- Filtering a `range`-indexed zip by a predicate on the second component
    keeps as many elements as filtering the underlying list. -/
theorem zip_map_range_filter_length {α : Type} (l : List α) (p : α → Bool)
    (k : Nat) :
    ((List.zip ((List.range l.length).map (fun i => k + i)) l).filter
        (fun x => p x.2)).length = (l.filter p).length := by
  induction l generalizing k with
  | nil => simp
  | cons hd tl ih =>
    have hfront :
        (List.range (tl.length + 1)).map (fun i => k + i) =
          k :: (List.range tl.length).map (fun i => k + 1 + i) := by
      rw [range_succ_append, List.map_append]
      have hsingle : List.map (fun i => k + i) [tl.length] = [k + tl.length] := by
        simp
      rw [hsingle, range_map_strong]
      simp
    rw [show (hd :: tl).length = tl.length + 1 by rfl, hfront]
    by_cases hphd : p hd = true
    · simp [hphd, List.zip, List.filter]
      exact ih (k + 1)
    · simp [hphd, List.zip, List.filter]
      exact ih (k + 1)

/-- Folding `min` over `rem` keeps the accumulator equal to `f` of some element
    of the enclosing list `L`, provided it starts that way and `rem ⊆ L`. -/
theorem foldl_min_achieved_subset {α : Type} (f : α → Int) (L : List α) :
    ∀ (rem : List α), (∀ x ∈ rem, x ∈ L) → ∀ (acc : Int) (y : α),
      y ∈ L → acc = f y →
        ∃ x ∈ L, f x = rem.foldl (fun a x => min a (f x)) acc := by
  intro rem
  induction rem with
  | nil =>
    intro _ acc y hyL hay
    exact ⟨y, hyL, hay.symm⟩
  | cons rh rtl ih =>
    intro hsub acc y hyL hay
    simp only [List.foldl]
    have hrh : rh ∈ L := hsub rh (List.mem_cons.mpr (Or.inl rfl))
    have hsub' : ∀ x ∈ rtl, x ∈ L :=
      fun x hx => hsub x (List.mem_cons.mpr (Or.inr hx))
    have hmin : min acc (f rh) = f y ∨ min acc (f rh) = f rh := by
      rw [hay]
      by_cases hle : f y ≤ f rh <;> simp [min, hle]
    cases hmin with
    | inl hyf =>
      rw [hyf]
      exact ih hsub' (f y) y hyL rfl
    | inr hrhf =>
      rw [hrhf]
      exact ih hsub' (f rh) rh hrh rfl

/-- The foldl-min of a non-empty list, seeded with the head's value, is the
    `f`-value of some list element. -/
theorem foldl_min_eq_some {α : Type} (f : α → Int) (l : List α) (h : l ≠ []) :
    ∃ x ∈ l, f x = l.foldl (fun acc x => min acc (f x)) (f (l.head h)) := by
  cases l with
  | nil => contradiction
  | cons hd tl =>
    have hsubset : ∀ x ∈ tl, x ∈ (hd :: tl) :=
      fun x hx => List.mem_cons.mpr (Or.inr hx)
    obtain ⟨x, hxl, hfx⟩ :=
      foldl_min_achieved_subset f (hd :: tl) tl hsubset (f hd) hd
        (List.mem_cons.mpr (Or.inl rfl)) rfl
    refine ⟨x, hxl, ?_⟩
    have hhead : (hd :: tl).head h = hd := by dsimp [List.head]
    rw [hhead]
    simp only [List.foldl]
    have hmin : min (f hd) (f hd) = f hd := by simp [min]
    rw [hmin]
    exact hfx

/-- A foldl of `min` never exceeds its seed. -/
theorem foldl_min_le_seed {α : Type} (f : α → Int) (seed : Int) (l : List α) :
    l.foldl (fun acc x => min acc (f x)) seed ≤ seed := by
  induction l generalizing seed with
  | nil => exact le_rfl
  | cons hd tl ih =>
    simp only [List.foldl]
    calc tl.foldl (fun acc x => min acc (f x)) (min seed (f hd)) ≤
          min seed (f hd) := ih (min seed (f hd))
      _ ≤ seed := min_le_left seed (f hd)

/-- A foldl of `min` over `l` is no greater than `f x` for any `x ∈ l`. -/
theorem foldl_min_le {α : Type} (f : α → Int) (seed : Int) (l : List α)
    (x : α) (hx : x ∈ l) :
    l.foldl (fun acc y => min acc (f y)) seed ≤ f x := by
  induction l generalizing seed with
  | nil => cases hx
  | cons hd tl ih =>
    simp only [List.foldl]
    cases List.mem_cons.mp hx with
    | inl heq =>
      rw [heq]
      calc tl.foldl (fun acc y => min acc (f y)) (min seed (f hd)) ≤
            min seed (f hd) := foldl_min_le_seed f (min seed (f hd)) tl
        _ ≤ f hd := min_le_right seed (f hd)
    | inr hxtl => exact ih (min seed (f hd)) hxtl

/-- Every element of a `range`-indexed zip (offset `k`) has first component
    at least `k`. -/
theorem zip_mapRange_fst_ge {α : Type} (l : List α) (k : Nat) :
    ∀ p ∈ List.zip ((List.range l.length).map (k + ·)) l, k ≤ p.1 := by
  induction l generalizing k with
  | nil => intro p hp; cases hp
  | cons hd tl ih =>
    have hcons : (List.range (tl.length + 1)).map (k + ·) =
        k :: (List.range tl.length).map (fun i => k + 1 + i) := by
      rw [range_succ_append, List.map_append]
      have hsingle : List.map (k + ·) [tl.length] = [k + tl.length] := by simp
      rw [hsingle, range_map_strong]
      simp
    intro p hp
    rw [show (hd :: tl).length = tl.length + 1 by rfl, hcons] at hp
    change p ∈ (k, hd) ::
      List.zip ((List.range tl.length).map (fun i => k + 1 + i)) tl at hp
    cases List.mem_cons.mp hp with
    | inl heq => simp [heq]
    | inr htl =>
      have hge := ih (k + 1) p htl
      omega

/-- The original indices (first components) of a `range`-indexed zip, after
    filtering, strictly increase along the list. -/
theorem zip_mapRange_filter_pairwise_fst {α : Type} (l : List α) (k : Nat)
    (q : Nat × α → Bool) :
    ((List.zip ((List.range l.length).map (k + ·)) l).filter q).Pairwise
      (fun a b => a.1 < b.1) := by
  induction l generalizing k with
  | nil => simp
  | cons hd tl ih =>
    have hcons : (List.range (tl.length + 1)).map (k + ·) =
        k :: (List.range tl.length).map (fun i => k + 1 + i) := by
      rw [range_succ_append, List.map_append]
      have hsingle : List.map (k + ·) [tl.length] = [k + tl.length] := by simp
      rw [hsingle, range_map_strong]
      simp
    rw [show (hd :: tl).length = tl.length + 1 by rfl, hcons]
    change (List.filter q ((k, hd) ::
        List.zip ((List.range tl.length).map (fun i => k + 1 + i)) tl)).Pairwise
      (fun a b => a.1 < b.1)
    by_cases hq : q (k, hd) = true
    · have hfilter : List.filter q ((k, hd) ::
          List.zip ((List.range tl.length).map (fun i => k + 1 + i)) tl) =
          (k, hd) :: List.filter q
            (List.zip ((List.range tl.length).map (fun i => k + 1 + i)) tl) := by
        simp [hq, List.filter]
      rw [hfilter]
      refine List.pairwise_cons.mpr ⟨?head, ?tail⟩
      · intro b hb
        have hbrest : b ∈ List.zip ((List.range tl.length).map (fun i => k + 1 + i)) tl :=
          (List.mem_filter.mp hb).1
        have hge := zip_mapRange_fst_ge tl (k + 1) b hbrest
        omega
      · exact ih (k + 1)
    · have hqf : q (k, hd) = false := by cases hq' : q (k, hd) <;> simp_all
      have hfilter : List.filter q ((k, hd) ::
          List.zip ((List.range tl.length).map (fun i => k + 1 + i)) tl) =
          List.filter q
            (List.zip ((List.range tl.length).map (fun i => k + 1 + i)) tl) := by
        simp [hqf, List.filter]
      rw [hfilter]
      exact ih (k + 1)

/-- If `find?` over a list with strictly increasing first components returns
    `(idx, ev)`, then no earlier candidate (first component `< idx`) satisfies
    the predicate. -/
theorem find?_fst_lt_not_pred (cands : List (Nat × ScheduledEvent))
    (hpair : cands.Pairwise (fun a b => a.1 < b.1)) (minPri : Int)
    (idx : Nat) (ev : ScheduledEvent)
    (hfind : cands.find? (fun x => x.2.priority == minPri) = some (idx, ev)) :
    ∀ c ∈ cands, c.1 < idx → c.2.priority ≠ minPri := by
  revert hpair hfind
  induction cands generalizing idx with
  | nil =>
    intro _ hfind
    cases hfind
  | cons c cs ih =>
    intro hpair hfind
    have hpcons := List.pairwise_cons.mp hpair
    dsimp [List.find?] at hfind
    intro c' hc' hclt
    by_cases hp : (c.2.priority == minPri) = true
    · simp [hp] at hfind
      have hceq : c = (idx, ev) := by simpa using hfind
      have hc1 : c.1 = idx := by simpa using congrArg Prod.fst hceq
      cases List.mem_cons.mp hc' with
      | inl heq =>
        rw [heq, hc1] at hclt
        omega
      | inr hct =>
        have hlt : c.1 < c'.1 := hpcons.1 c' hct
        rw [hc1] at hlt
        omega
    · simp [hp] at hfind
      cases List.mem_cons.mp hc' with
      | inl heq =>
        rw [heq]
        intro heq'
        exact hp (by simp [heq'])
      | inr hct =>
        exact ih idx hpcons.2 hfind c' hct hclt

/-- Offsetting `range` by `0` is the identity. -/
theorem range_map_zero_add (n : Nat) :
    (List.range n).map (0 + ·) = List.range n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [range_succ_append n, List.map_append, ih]
    simp

/-- The `j`-th original element of a list appears at original index `k + j` in
    the offset `range`-zip. -/
theorem mem_zip_mapRange_self {α : Type} (l : List α) (k : Nat) (j : Nat)
    (hj : j < l.length) :
    (k + j, l[j]'hj) ∈ List.zip ((List.range l.length).map (k + ·)) l := by
  induction l generalizing k j with
  | nil => exact absurd hj (Nat.not_lt_zero j)
  | cons a as ih =>
    have hcons : (List.range (as.length + 1)).map (k + ·) =
        k :: (List.range as.length).map (fun t => k + 1 + t) := by
      rw [range_succ_append, List.map_append]
      have hsingle : List.map (k + ·) [as.length] = [k + as.length] := by simp
      rw [hsingle, range_map_strong]
      simp
    change (k + j, (a :: as)[j]'hj) ∈ List.zip
      ((List.range (as.length + 1)).map (k + ·)) (a :: as)
    rw [hcons]
    change (k + j, (a :: as)[j]'hj) ∈ (k, a) ::
      List.zip ((List.range as.length).map (fun t => k + 1 + t)) as
    cases j with
    | zero =>
      suffices h : (k + 0, (a :: as)[0]'hj) = (k, a) by
        rw [h]
        exact List.mem_cons.mpr (Or.inl rfl)
      ext <;> simp
    | succ j' =>
      have hj' : j' < as.length := Nat.lt_of_succ_lt_succ hj
      apply List.mem_cons.mpr (Or.inr ?_)
      have hmem := ih (k + 1) j' hj'
      suffices h : (k + (j' + 1), (a :: as)[j' + 1]'hj) =
          ((k + 1) + j', as[j']'hj') by
        rw [h]
        exact hmem
      refine Prod.ext (by omega) ?_
      rfl

/-- Membership in an offset `range`-zip pins the original index and value. -/
theorem mem_zip_mapRange_getElem {α : Type} (l : List α) (k : Nat) (i : Nat)
    (x : α) (hm : (i, x) ∈ List.zip ((List.range l.length).map (k + ·)) l) :
    ∃ (j : Nat) (hj : j < l.length), i = k + j ∧ l[j]'hj = x := by
  induction l generalizing k i with
  | nil => cases hm
  | cons a as ih =>
    have hcons : (List.range (as.length + 1)).map (k + ·) =
        k :: (List.range as.length).map (fun t => k + 1 + t) := by
      rw [range_succ_append, List.map_append]
      have hsingle : List.map (k + ·) [as.length] = [k + as.length] := by simp
      rw [hsingle, range_map_strong]
      simp
    change (i, x) ∈ List.zip ((List.range (as.length + 1)).map (k + ·)) (a :: as) at hm
    rw [hcons] at hm
    change (i, x) ∈ (k, a) ::
      List.zip ((List.range as.length).map (fun t => k + 1 + t)) as at hm
    cases List.mem_cons.mp hm with
    | inl heq =>
      have hi : i = k := by simpa using congrArg Prod.fst heq
      have hx : x = a := by simpa using congrArg Prod.snd heq
      subst hi; subst hx
      exact ⟨0, Nat.zero_lt_succ as.length, by omega, by simp⟩
    | inr htl =>
      obtain ⟨j, hj, hij, hx⟩ := ih (k + 1) i htl
      refine ⟨j + 1, Nat.succ_lt_succ hj, ?_, ?_⟩
      · rw [hij]; omega
      · exact hx

/-- The `j`-th element appears at original index `j` in the `range`-zip. -/
theorem mem_zip_range_self {α : Type} (l : List α) (j : Nat)
    (hj : j < l.length) :
    (j, l[j]'hj) ∈ List.zip (List.range l.length) l := by
  have this := mem_zip_mapRange_self l 0 j hj
  rw [range_map_zero_add] at this
  convert this using 1
  simp

/-- Membership in a `range`-zip pins the value at the original index. -/
theorem mem_zip_range_getElem {α : Type} (l : List α) (i : Nat) (x : α)
    (hm : (i, x) ∈ List.zip (List.range l.length) l) :
    ∃ (h : i < l.length), l[i]'h = x := by
  have hm0 : (i, x) ∈ List.zip ((List.range l.length).map (0 + ·)) l := by
    rw [range_map_zero_add]
    exact hm
  obtain ⟨j, hj, hjidx, hx⟩ := mem_zip_mapRange_getElem l 0 i x hm0
  have hij : i = j := by omega
  subst hij
  exact ⟨hj, hx⟩

/-- `(a == b : Int) = true` implies `a = b`. -/
theorem int_eq_of_beq_true (a b : Int) (h : (a == b) = true) : a = b :=
  LawfulBEq.eq_of_beq h

/-- `popNextEvent` pops the earliest original-index event among those with the
    minimum priority targeting the current tick. -/
theorem popNextEvent_is_min_earliest (w : World) (e : ScheduledEvent)
    (w' : World) (h : w.popNextEvent = some (e, w')) :
    ∃ (idx : Nat) (hidx : idx < w.events.length), w.events[idx]'hidx = e ∧
      e.targetTick = w.tick ∧
      (∀ j (hj : j < w.events.length), (w.events[j]'hj).targetTick = w.tick →
        e.priority ≤ (w.events[j]'hj).priority) ∧
      (∀ j (hj : j < idx), (w.events[j]'(hj.trans hidx)).targetTick = w.tick →
        e.priority < (w.events[j]'(hj.trans hidx)).priority) := by
  unfold popNextEvent at h
  dsimp (config := { zeta := true }) at h
  set candidates := (List.zip (List.range w.events.length) w.events).filter
    (fun x => x.2.targetTick == w.tick) with hcdef
  set minPri := candidates.foldl (fun acc x => min acc x.2.priority)
    ((candidates.head?.map (fun x => x.2.priority)).getD 0) with hmdef
  split at h
  · contradiction
  · split at h
    · contradiction
    · rename_i idx evM hfind
      have hevM : evM = e := by
        simpa using congrArg Prod.fst (Option.some_inj.mp h)
      have hmem : (idx, evM) ∈ candidates := List.mem_of_find?_eq_some hfind
      have hzipmem : (idx, evM) ∈
          List.zip (List.range w.events.length) w.events :=
        (List.mem_filter.mp hmem).1
      have htickM : evM.targetTick = w.tick :=
        Nat.eq_of_beq_eq_true (by simpa using (List.mem_filter.mp hmem).2)
      obtain ⟨hidx, hevMget⟩ := mem_zip_range_getElem w.events idx evM hzipmem
      have hev : w.events[idx]'hidx = e := by rw [hevMget, hevM]
      have htick : e.targetTick = w.tick := by rw [← hevM]; exact htickM
      have hpri : e.priority = minPri := by
        have hfpred := find?_some candidates
          (fun x => x.2.priority == minPri) (idx, evM) hfind
        rw [← hevM]
        exact int_eq_of_beq_true evM.priority minPri hfpred
      refine ⟨idx, hidx, hev, htick, ?_, ?_⟩
      · intro j hj hjtick
        have hcandj : (j, w.events[j]'hj) ∈ candidates := by
          refine List.mem_filter.mpr ⟨mem_zip_range_self w.events j hj, ?_⟩
          rw [hjtick]
          exact nat_beq_true_self w.tick
        have hle := foldl_min_le
          (fun x : Nat × ScheduledEvent => x.2.priority)
          ((candidates.head?.map (fun x => x.2.priority)).getD 0) candidates
          (j, w.events[j]'hj) hcandj
        rw [← hmdef] at hle
        rw [hpri]
        exact hle
      · intro j hj hjtick
        have hjw : j < w.events.length := hj.trans hidx
        have hcandj : (j, w.events[j]'hjw) ∈ candidates := by
          refine List.mem_filter.mpr ⟨mem_zip_range_self w.events j hjw, ?_⟩
          rw [hjtick]
          exact nat_beq_true_self w.tick
        have hpair : candidates.Pairwise (fun a b => a.1 < b.1) := by
          have h0 := zip_mapRange_filter_pairwise_fst w.events 0
            (fun x => x.2.targetTick == w.tick)
          convert h0 using 1
          rw [hcdef, range_map_zero_add]
        have hfindE := hfind
        rw [hevM] at hfindE
        have hne := find?_fst_lt_not_pred candidates hpair minPri idx e
          hfindE (j, w.events[j]'hjw) hcandj hj
        have hle : minPri ≤ (w.events[j]'hjw).priority := by
          have hle' := foldl_min_le
            (fun x : Nat × ScheduledEvent => x.2.priority)
            ((candidates.head?.map (fun x => x.2.priority)).getD 0)
            candidates (j, w.events[j]'hjw) hcandj
          rw [← hmdef] at hle'
          exact hle'
        rw [hpri]
        exact lt_of_le_of_ne hle (Ne.symm hne)

/-- The `candidates` list in `popNextEvent` has length
    `countEventAtThisTick w w.tick`. -/
theorem popNextEvent_candidates_length (w : World) :
    ((List.zip (List.range w.events.length) w.events).filter
        (fun x => x.2.targetTick == w.tick)).length =
      countEventAtThisTick w w.tick := by
  dsimp [countEventAtThisTick]
  simpa using zip_map_range_filter_length w.events
    (fun e => e.targetTick == w.tick) 0

/-- A positive current-tick count means `popNextEvent` returns an event. -/
theorem popNextEvent_some_of_count_pos (w : World)
    (hc : 0 < countEventAtThisTick w w.tick) :
    ∃ ev w', w.popNextEvent = some (ev, w') := by
  rw [← popNextEvent_candidates_length] at hc
  obtain ⟨c, cs, hcons⟩ : ∃ c cs,
      ((List.zip (List.range w.events.length) w.events).filter
        (fun x => x.2.targetTick == w.tick)) = c :: cs := by
    cases h : (List.zip (List.range w.events.length) w.events).filter
        (fun x => x.2.targetTick == w.tick) with
    | nil => simp [h] at hc
    | cons c cs => exact ⟨c, cs, rfl⟩
  unfold popNextEvent
  dsimp (config := { zeta := true })
  rw [hcons]
  -- `c :: cs` is non-empty, so the `isEmpty` guard takes the else branch
  have hisEmpty : (c :: cs).isEmpty = false := by
    cases cs <;> dsimp [List.isEmpty]
  rw [hisEmpty]
  -- the seed `head? .. getD 0` of the min-fold is `c.2.priority`
  have hseed : ((List.head? (c :: cs)).map (fun x => x.2.priority)).getD 0 =
      c.2.priority := by simp
  rw [hseed]
  -- the min-fold is achieved, so `find?` is `some`
  have hmin : ∃ x ∈ (c :: cs : List (Nat × ScheduledEvent)),
      x.2.priority = (c :: cs).foldl (fun acc x => min acc x.2.priority)
        c.2.priority := by
    apply foldl_min_eq_some (fun x : Nat × ScheduledEvent => x.2.priority)
    intro hnil
    cases hnil
  obtain ⟨x, hxmem, hxpri⟩ := hmin
  have hfind : (c :: cs).find? (fun x => x.2.priority ==
      (c :: cs).foldl (fun acc x => min acc x.2.priority) c.2.priority) ≠
      none := by
    intro hnone
    rw [List.find?_eq_none] at hnone
    have hfalse := hnone x hxmem
    simp [hxpri] at hfalse
  cases hfindEq : (c :: cs).find? (fun x => x.2.priority ==
      (c :: cs).foldl (fun acc x => min acc x.2.priority) c.2.priority) with
  | none => contradiction
  | some p =>
    rcases p with ⟨idx, ev⟩
    exact ⟨ev, { w with events := w.events.eraseIdx idx }, by simp⟩

/-- `step = none` means no event targets the current tick. -/
theorem step_none_countEventAtThisTick (w : World) (h : w.step = none) :
    countEventAtThisTick w w.tick = 0 := by
  by_contra hne
  have hpos : 0 < countEventAtThisTick w w.tick := Nat.pos_of_ne_zero hne
  obtain ⟨ev, w', hpop⟩ := popNextEvent_some_of_count_pos w hpos
  have hstep : w.step = some (w'.onScheduledTick ev.nodeId) := by
    dsimp [World.step]
    rw [hpop]
  rw [hstep] at h
  cases h

/-- After `stepUntilNextTick`, no event targets the starting tick. -/
theorem countEventAtThisTick_stepUntilNextTick (w : World) :
    countEventAtThisTick w.stepUntilNextTick w.tick = 0 := by
  induction w using World.stepUntilNextTick.induct with
  | case1 x h =>
    rw [World.stepUntilNextTick, h]
    change countEventAtThisTick x x.tick = 0
    exact step_none_countEventAtThisTick x h
  | case2 x w' h ih =>
    rw [World.stepUntilNextTick, h]
    have htick : w'.tick = x.tick := World.step_tick x w' h
    rw [← htick]
    exact ih
