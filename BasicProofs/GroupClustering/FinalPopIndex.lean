import BasicProofs.GroupClustering.OutputLogEntries
import BasicProofs.GroupClustering.OutputPositionBridge

open BasicRedstoneSim List

/-! # Group clustering — output position and the final-pop index

OutputLogEntries proved the `findIdx?` isSome/none facts. It did not prove what
value `findIdx?` returns. This file proves the value facts and uses
them to connect `outputPos` (a position in the full log, tick entries
included) to the index of a chain entry among the chain entries only.

## Log shape used here

Every group runs so that all last repeaters fire at the common tick
`T`. No output node logs before tick `T`. Each `gSimBody` call writes
`"tick {t}"` before it drains the tick. So the log up to and including
tick `T` has this shape:

    log = [tick 0, tick 1, ..., tick T] ++ [chain entries in pop order]

The tick block has `T + 1` entries. The chain entries follow it. LogBridge
proved every entry is a tick entry or a chain entry. OutputPositionBridge proved a
tick entry never matches `isOutputEntry`. Both facts are used here.

## Main results

* `findIdx?_eq_some_of_first_match`: `findIdx?` returns the length of
  the prefix that precedes the first matching element.

* `outputPos_eq_pre_length`: `outputPos` returns the length of the
  prefix that precedes the first output entry of the chain.

* `outputPos_eq_index_of_chain_entry`: `outputPos` equals
  `(T + 1) + k`, where `k` is the number of chain entries logged before
  the entry of chain `(gi, ci)`. This is deliverable 2.

* `chain_entries_are_final_pops`: the chain-entry index order equals the
  `evBefore` order of the final events. This is deliverable 1.

* `groupBeforeSpec_iff_evBefore_final`: `groupBeforeSpec` is equivalent
  to `evBefore` on the final events of same-spec chains. This is
  deliverable 3.

## What remains

All results here are proved in full; none uses `sorry`. But the
deliverables are stated with the simulation facts as explicit
hypotheses. Discharging those hypotheses from `groupSimulate` is the
open simulation analysis that OutputLogEntries flagged:

* Deliverable 2 assumes the log shape (`h_log`, `h_ticks_len`, `h_ticks`,
  `h_chain_split`, `h_first_c`). Proving them means showing the tick block
  has exactly `T + 1` entries and that no chain entry precedes tick `T`.

* Deliverable 1 assumes each final event sits in the final-pop list at the
  chain-entry index (`h_pos1`, `h_pos2`). Proving them means showing the
  chain entries are appended in pop order, one per final pop, via the
  `logOutput` append chain inside `stepUntilNextTick`.

* Deliverable 3 assumes deliverable 2's output (`h_outPos`) and
  deliverable 1's output (`h_bridge`).

So the list-level bridge is complete; wiring it to the concrete
`groupSimulate` run remains.
-/

/-! ## Value of findIdx? at the first match -/

/-- `findIdx?` returns the length of the prefix that precedes the first
    matching element. No element of the prefix matches. The head of the
    tail matches. -/
theorem findIdx?_eq_some_of_first_match {α : Type} (p : α → Bool)
    (pre : List α) (x : α) (post : List α)
    (h_match : p x = true)
    (h_pre : ∀ y ∈ pre, p y = false) :
    _root_.findIdx? p (pre ++ x :: post) = some pre.length := by
  revert h_pre
  induction pre with
  | nil =>
    intro h_pre
    dsimp [_root_.findIdx?]
    simp [h_match]
  | cons a pre ih =>
    intro h_pre
    have h_pa : p a = false := h_pre a (List.mem_cons.mpr (Or.inl rfl))
    have h_pre' : ∀ y ∈ pre, p y = false :=
      fun y hy => h_pre y (List.mem_cons.mpr (Or.inr hy))
    dsimp [_root_.findIdx?]
    rw [h_pa]
    dsimp
    rw [ih h_pre']
    dsimp [Option.map]

/-- `outputPos` returns the length of the prefix that precedes the first
    output entry of chain `(gi, ci)`. The prefix holds no matching entry.
    The head of the tail matches. -/
theorem outputPos_eq_pre_length (log : List String) (gi ci : Nat)
    (pre : List String) (x : String) (post : List String)
    (h_split : log = pre ++ x :: post)
    (h_match : isOutputEntry x gi ci = true)
    (h_pre : ∀ y ∈ pre, isOutputEntry y gi ci = false) :
    outputPos log gi ci = some pre.length := by
  dsimp [outputPos]
  rw [h_split]
  exact findIdx?_eq_some_of_first_match
    (fun s => isOutputEntry s gi ci) pre x post h_match h_pre

/-! ## Deliverable 2 — outputPos equals (T + 1) plus the chain index -/

/-- A tick entry never matches `isOutputEntry`. This restates the OutputPositionBridge
    fact in a form that consumes an `IsTickEntry` proof. -/
theorem tickEntry_not_isOutputEntry (s : String) (gi ci : Nat)
    (h_tick : IsTickEntry s) : isOutputEntry s gi ci = false := by
  rcases h_tick with ⟨t, rfl⟩
  exact tick_entry_isOutputEntry_false t gi ci

/-- Deliverable 2. The log is the tick block followed by the chain
    entries. The tick block has `T + 1` entries. The entry of chain
    `(gi, ci)` is the next entry after `pre_c` chain entries. Then
    `outputPos log gi ci = some (T + 1 + pre_c.length)`. The value
    `pre_c.length` is the index of the entry among the chain entries. -/
theorem outputPos_eq_index_of_chain_entry
    (log : List String) (T gi ci : Nat)
    (ticks chainEntries : List String)
    (h_log : log = ticks ++ chainEntries)
    (h_ticks_len : ticks.length = T + 1)
    (h_ticks : ∀ s ∈ ticks, IsTickEntry s)
    (pre_c : List String) (x : String) (post_c : List String)
    (h_chain_split : chainEntries = pre_c ++ x :: post_c)
    (h_match : isOutputEntry x gi ci = true)
    (h_first_c : ∀ y ∈ pre_c, isOutputEntry y gi ci = false) :
    outputPos log gi ci = some (T + 1 + pre_c.length) := by
  -- No entry of the tick block matches isOutputEntry.
  have h_pre : ∀ y ∈ ticks ++ pre_c, isOutputEntry y gi ci = false := by
    intro y hy
    rw [List.mem_append] at hy
    rcases hy with hy | hy
    · exact tickEntry_not_isOutputEntry y gi ci (h_ticks y hy)
    · exact h_first_c y hy
  dsimp [outputPos]
  rw [h_log, h_chain_split]
  -- Reassociate: ticks ++ (pre_c ++ x :: post_c) = (ticks ++ pre_c) ++ x :: post_c
  have h_assoc : ticks ++ (pre_c ++ x :: post_c) =
      (ticks ++ pre_c) ++ x :: post_c := by
    rw [← List.append_assoc]
  rw [h_assoc]
  rw [findIdx?_eq_some_of_first_match
    (fun s => isOutputEntry s gi ci) (ticks ++ pre_c) x post_c h_match h_pre]
  simp [List.length_append, h_ticks_len]

/-! ## Deliverable 3 — groupBeforeSpec is evBefore on the final events

`groupBeforeSpec` compares `outputPos` values. By deliverable 2 each
`outputPos` is `(T + 1) + k` where `k` is the chain-entry index. The
constant offset `(T + 1)` does not change the order, so comparing
`outputPos` values is the same as comparing chain-entry indices. The
chain-entry indices follow the pop order of the final events, which is
the `evBefore` order on the final-pop list. Deliverable 1 supplies that
last step as `h_bridge`. -/

/-- Deliverable 3. `groupBeforeSpec log groups ga gb s` is equivalent to:
    for every same-spec chain of `ga` and every same-spec chain of `gb`,
    the `ga` chain's final event is `evBefore` the `gb` chain's final
    event in the final-pop list.

    The two bridge hypotheses capture the simulation facts:
    * `h_outPos`: deliverable 2 for each relevant chain, i.e.
      `outputPos log gi ci = some (T + 1 + finalIdx gi ci)`.
    * `h_bridge`: deliverable 1, i.e. the final-index order equals the
      `evBefore` order of the final events. -/
theorem groupBeforeSpec_iff_evBefore_final
    (log : List String) (groups : List GroupSpec) (ga gb : Nat) (s : ChainSpec)
    (T : Nat)
    (h_ga : ga < groups.length) (h_gb : gb < groups.length)
    (finals : List ScheduledEvent)
    (finalEventOf : Nat → Nat → ScheduledEvent)
    (finalIdx : Nat → Nat → Nat)
    (h_outPos : ∀ gi ci, gi < groups.length → ci < (groupAt groups gi).length →
        outputPos log gi ci = some (T + 1 + finalIdx gi ci))
    (h_bridge : ∀ g1 c1 g2 c2,
        finalIdx g1 c1 < finalIdx g2 c2 ↔
        evBefore finals (finalEventOf g1 c1) (finalEventOf g2 c2)) :
    groupBeforeSpec log groups ga gb s ↔
    ∀ ca cb, ca < (groupAt groups ga).length → cb < (groupAt groups gb).length →
      chainAt groups ga ca = s → chainAt groups gb cb = s →
      evBefore finals (finalEventOf ga ca) (finalEventOf gb cb) := by
  constructor
  · -- Forward: groupBeforeSpec gives outputPos order, hence evBefore.
    intro h_spec ca cb h_ca h_cb h_sa h_sb
    obtain ⟨p, q, h_p, h_q, h_lt⟩ := h_spec ca cb h_ca h_cb h_sa h_sb
    have h_p_eq : p = T + 1 + finalIdx ga ca := by
      have h := h_outPos ga ca h_ga h_ca
      rw [h] at h_p
      exact Option.some_inj.mp h_p.symm
    have h_q_eq : q = T + 1 + finalIdx gb cb := by
      have h := h_outPos gb cb h_gb h_cb
      rw [h] at h_q
      exact Option.some_inj.mp h_q.symm
    rw [h_p_eq, h_q_eq] at h_lt
    -- The constant offset (T + 1) cancels from the order.
    have h_idx : finalIdx ga ca < finalIdx gb cb := by omega
    exact (h_bridge ga ca gb cb).mp h_idx
  · -- Backward: evBefore gives index order, hence outputPos order.
    intro h_ev ca cb h_ca h_cb h_sa h_sb
    have h_idx : finalIdx ga ca < finalIdx gb cb :=
      (h_bridge ga ca gb cb).mpr (h_ev ca cb h_ca h_cb h_sa h_sb)
    refine ⟨T + 1 + finalIdx ga ca, T + 1 + finalIdx gb cb, ?_, ?_, ?_⟩
    · exact h_outPos ga ca h_ga h_ca
    · exact h_outPos gb cb h_gb h_cb
    · omega

/-! ## Deliverable 1 — chain entries follow the final-pop order

The final events pop in the order of the duplicate-free final-pop list.
Each chain's final event sits in that list at the chain-entry index. A
smaller index therefore means an earlier pop, which is exactly the
`evBefore` relation. The proof compares the two append-splits of the
final-pop list. -/

/-- Appending on the left is cancellative. -/
private theorem append_left_cancel {α : Type} (l l₁ l₂ : List α)
    (h : l ++ l₁ = l ++ l₂) : l₁ = l₂ := by
  induction l generalizing l₁ l₂ with
  | nil => simpa using h
  | cons a l ih =>
    change a :: (l ++ l₁) = a :: (l ++ l₂) at h
    injection h with _ h_tail
    exact ih l₁ l₂ h_tail

/-- If `p1 ++ a = p2 ++ b` and `p1` is strictly shorter than `p2`, then
    `p2` extends `p1` by a non-empty remainder `r`, and `a = r ++ b`. -/
private theorem append_decomp {α : Type} (p1 p2 a b : List α)
    (h : p1 ++ a = p2 ++ b) (hlt : p1.length < p2.length) :
    ∃ r, p2 = p1 ++ r ∧ a = r ++ b ∧ 0 < r.length := by
  revert p2 a b h hlt
  induction p1 with
  | nil =>
    intro p2 a b h hlt
    refine ⟨p2, by simp, ?_, ?_⟩
    · simpa using h
    · simpa using hlt
  | cons x p1 ih =>
    intro p2 a b h hlt
    cases p2 with
    | nil => simp at hlt
    | cons x' p2' =>
      injection h with h_head h_tail
      have hlt' : p1.length < p2'.length := by
        simp only [List.length_cons] at hlt
        omega
      obtain ⟨r, h_p2', h_a, h_pos⟩ := ih p2' a b h_tail hlt'
      refine ⟨r, ?_, h_a, h_pos⟩
      show x' :: p2' = (x :: p1) ++ r
      rw [← h_head, h_p2']
      rfl

/-- Equal cons lists have equal heads. -/
private theorem cons_inj_head {α : Type} {x y : α} {q1 q2 : List α}
    (h : x :: q1 = y :: q2) : x = y := by
  cases h
  rfl

/-- Two prefixes of the same length of the same list are equal. -/
private theorem prefix_eq_of_length_eq {α : Type} (p1 p2 a b : List α)
    (h : p1 ++ a = p2 ++ b) (hlen : p1.length = p2.length) : p1 = p2 := by
  revert p2 a b h hlen
  induction p1 with
  | nil =>
    intro p2 a b h hlen
    cases p2 <;> simp at hlen ⊢
  | cons x p1 ih =>
    intro p2 a b h hlen
    cases p2 with
    | nil => simp at hlen
    | cons x' p2' =>
      change x :: (p1 ++ a) = x' :: (p2' ++ b) at h
      injection h with h_head h_tail
      have hlen' : p1.length = p2'.length := by
        simp only [List.length_cons] at hlen
        omega
      have h_tail_eq : p1 = p2' := ih p2' a b h_tail hlen'
      show x :: p1 = x' :: p2'
      rw [h_head, h_tail_eq]

/-- A smaller split position means an earlier element, i.e. `evBefore`. -/
private theorem evBefore_of_lt_split_length (l : List ScheduledEvent)
    (x y : ScheduledEvent) (p1 q1 p2 q2 : List ScheduledEvent)
    (h1 : l = p1 ++ x :: q1) (h2 : l = p2 ++ y :: q2)
    (hlt : p1.length < p2.length) : evBefore l x y := by
  refine ⟨p1, q1, h1, ?_⟩
  have h_eq : p1 ++ (x :: q1) = p2 ++ (y :: q2) := by rw [← h1, ← h2]
  obtain ⟨r, _, h_a, h_pos⟩ := append_decomp p1 p2 (x :: q1) (y :: q2) h_eq hlt
  cases r with
  | nil =>
    have h0 : 0 < 0 := by
      dsimp at h_pos
      exact h_pos
    omega
  | cons rh rt =>
    change x :: q1 = rh :: (rt ++ y :: q2) at h_a
    injection h_a with _ h_q1
    rw [h_q1]
    exact List.mem_append_right rt (List.mem_cons.mpr (Or.inl rfl))

/-- For a duplicate-free list, the `evBefore` order of two elements equals
    the order of their split positions. -/
private theorem evBefore_iff_lt_split (l : List ScheduledEvent)
    (h_nd : l.Nodup) (x y : ScheduledEvent)
    (p1 q1 p2 q2 : List ScheduledEvent)
    (h1 : l = p1 ++ x :: q1) (h2 : l = p2 ++ y :: q2) :
    evBefore l x y ↔ p1.length < p2.length := by
  constructor
  · intro h_ev
    by_contra h_not
    have h_le : p2.length ≤ p1.length := by omega
    by_cases h_eq_len : p1.length = p2.length
    · -- equal positions force x = y, so evBefore l x x, impossible
      have h_p12 : p1 = p2 :=
        prefix_eq_of_length_eq p1 p2 (x :: q1) (y :: q2)
          (by rw [← h1, ← h2]) h_eq_len
      have h_cancel : x :: q1 = y :: q2 :=
        append_left_cancel p1 (x :: q1) (y :: q2) (by
          calc p1 ++ (x :: q1) = l := h1.symm
            _ = p2 ++ (y :: q2) := h2
            _ = p1 ++ (y :: q2) := by rw [h_p12])
      have h_xy : x = y := cons_inj_head h_cancel
      have h_self : evBefore l x x := by
        simpa [h_xy.symm] using h_ev
      exact (evBefore.asymm h_nd h_self) h_self
    · -- p2 strictly shorter gives evBefore l y x, contradicting asymmetry
      have h_lt2 : p2.length < p1.length := by omega
      have h_ev_yx : evBefore l y x :=
        evBefore_of_lt_split_length l y x p2 q2 p1 q1 h2 h1 h_lt2
      exact (evBefore.asymm h_nd h_ev) h_ev_yx
  · exact evBefore_of_lt_split_length l x y p1 q1 p2 q2 h1 h2

/-- Deliverable 1. The chain entries follow the final-pop order. Each
    chain's final event sits in the duplicate-free final-pop list at the
    chain-entry index. A smaller chain-entry index then means the final
    event pops earlier, which is the `evBefore` relation. -/
theorem chain_entries_are_final_pops
    (finals : List ScheduledEvent) (h_nd : finals.Nodup)
    (finalEventOf : Nat → Nat → ScheduledEvent)
    (finalIdx : Nat → Nat → Nat)
    (g1 c1 g2 c2 : Nat)
    (h_pos1 : ∃ pre post, finals = pre ++ finalEventOf g1 c1 :: post ∧
        pre.length = finalIdx g1 c1)
    (h_pos2 : ∃ pre post, finals = pre ++ finalEventOf g2 c2 :: post ∧
        pre.length = finalIdx g2 c2) :
    finalIdx g1 c1 < finalIdx g2 c2 ↔
    evBefore finals (finalEventOf g1 c1) (finalEventOf g2 c2) := by
  obtain ⟨p1, q1, h1, hlen1⟩ := h_pos1
  obtain ⟨p2, q2, h2, hlen2⟩ := h_pos2
  have h_iff : evBefore finals (finalEventOf g1 c1) (finalEventOf g2 c2) ↔
      p1.length < p2.length :=
    evBefore_iff_lt_split finals h_nd (finalEventOf g1 c1) (finalEventOf g2 c2)
      p1 q1 p2 q2 h1 h2
  rw [hlen1, hlen2] at h_iff
  exact h_iff.symm

