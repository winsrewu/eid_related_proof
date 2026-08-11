import BasicProofs.GroupClustering.OutputPositionBridge
import BasicProofs.GroupClustering.LogBridge

open BasicRedstoneSim List

/-! # Group clustering — output position and log entries

OutputLogEntries connects `outputPos` (log-based position) to log structure.

`outputPos log gi ci` calls `findIdx?` to locate the first entry of
chain `(gi, ci)` in the log. The custom `findIdx?` from PrefixChain
Definitions has no structural lemmas yet. This file proves the key ones
and applies them to `outputPos`.

The simulation-level link (log order equals pop order of final events
at tick `T`) requires a detailed analysis of `stepUntilNextTick` and
the `logOutput` append chain. That work remains open.

## Main results

* `findIdx?_isSome_iff_exists`: `findIdx?` returns `some` exactly when
  a matching element exists in the list.

* `findIdx?_none_iff_forall_not`: `findIdx?` returns `none` exactly
  when no element matches the predicate.

* `outputPos_some_iff_output_exists`: `outputPos log gi ci` returns
  `some p` exactly when an output entry for chain `(gi, ci)` is in
  the log.

* `outputPos_none_of_tickEntry`: a log with only tick entries gives
  `outputPos = none` for every chain.

* `outputPos_chain_entry_zero` / `outputPos_chain_entry_fifteen`:
  a log that holds a chain entry for `(gi, ci)` gives
  `outputPos = some _` for that chain.

## What remains toward the capstone

The two simulation-level bridges still need proof:

1. `outputPos_eq_finalPopIndex`: log position of chain `(gi, ci)`
   equals its index among final events popped at tick `T`. The proof
   tracks `logOutput` appends through each `step` call inside
   `stepUntilNextTick`.

2. `groupBeforeSpec_iff_evBefore_final`: `groupBeforeSpec` on the log
   matches `evBefore` on final events in the queue. The proof
   combines the log-pop correspondence with
   `sameSpec_orderPreservation` from QSideOrder.
-/

/-! ## findIdx? structural lemmas -/

/-- `findIdx?` returns `none` when no element in the list satisfies
    the predicate. -/
theorem findIdx?_none_of_not_exists {α : Type} (p : α → Bool) (l : List α)
    (h : ∀ x ∈ l, p x ≠ true) :
    _root_.findIdx? p l = none := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hpx : p x = false := by
      cases hp : p x
      · rfl
      · have hxmem : x ∈ x :: xs := by simp
        have : False := h x hxmem hp
        cases this
    dsimp only [_root_.findIdx?]
    rw [hpx]
    simp
    exact ih (fun y hy => by
      have hxy : y ∈ x :: xs := by simp [hy]
      exact h y hxy)

/-- If some element of the list satisfies the predicate, then
    `findIdx?` returns `some`. -/
theorem findIdx?_isSome_of_exists {α : Type} (p : α → Bool) (l : List α)
    (h : ∃ x ∈ l, p x = true) :
    (_root_.findIdx? p l).isSome := by
  induction l with
  | nil =>
    rcases h with ⟨x, hx, _⟩
    cases hx
  | cons x xs ih =>
    dsimp only [_root_.findIdx?]
    cases hpx : p x with
    | false =>
      dsimp [hpx]
      rcases h with ⟨y, hy, hpy⟩
      have hmem : y = x ∨ y ∈ xs := by simpa using hy
      rcases hmem with rfl | hy_rest
      · rw [hpx] at hpy
        cases hpy
      · cases h_find : _root_.findIdx? p xs with
        | none =>
          have ih_y := ih (Exists.intro y ⟨hy_rest, hpy⟩)
          simp [Option.isSome, h_find] at ih_y
        | some n =>
          simp [Option.isSome, Option.map]
    | true =>
      dsimp [hpx]

/-- `findIdx?` returns `some` if and only if a matching element exists
    in the list. -/
theorem findIdx?_isSome_iff_exists {α : Type} (p : α → Bool) (l : List α) :
    (_root_.findIdx? p l).isSome ↔ ∃ x ∈ l, p x = true := by
  constructor
  · intro h
    by_contra hn
    have hnone : _root_.findIdx? p l = none := by
      refine findIdx?_none_of_not_exists p l ?_
      intro x hx hpx
      exact hn ⟨x, hx, hpx⟩
    rw [hnone] at h
    dsimp [Option.isSome] at h
    cases h
  · exact findIdx?_isSome_of_exists p l

/-- `findIdx?` returns `none` if and only if no element satisfies the
    predicate. -/
theorem findIdx?_none_iff_forall_not {α : Type} (p : α → Bool) (l : List α) :
    _root_.findIdx? p l = none ↔ ∀ x ∈ l, p x ≠ true := by
  constructor
  · intro h x hx hpx
    have := (findIdx?_isSome_iff_exists p l).2 ⟨x, hx, hpx⟩
    rw [h] at this
    dsimp [Option.isSome] at this
    cases this
  · exact findIdx?_none_of_not_exists p l

/-! ## outputPos theorems -/

/-- `outputPos` returns `some` if and only if an output entry for the
    chain is in the log. -/
theorem outputPos_some_iff_output_exists (log : List String) (gi ci : Nat) :
    (outputPos log gi ci).isSome ↔
    ∃ s ∈ log, isOutputEntry s gi ci = true := by
  dsimp [outputPos]
  exact findIdx?_isSome_iff_exists (fun s => isOutputEntry s gi ci) log

/-- `outputPos` returns `none` when no output entry for the chain is
    in the log. -/
theorem outputPos_none_of_no_entry (log : List String) (gi ci : Nat)
    (h : ∀ s ∈ log, isOutputEntry s gi ci ≠ true) :
    outputPos log gi ci = none := by
  dsimp [outputPos]
  exact findIdx?_none_of_not_exists (fun s => isOutputEntry s gi ci) log h

/-- Tick entries never match `isOutputEntry`, so a log that holds only
    tick entries gives `outputPos = none` for every chain. -/
theorem outputPos_none_of_tickEntry (log : List String) (gi ci : Nat)
    (h : ∀ s ∈ log, ∃ (n : Nat), s = s!"tick {n}") :
    outputPos log gi ci = none := by
  refine outputPos_none_of_no_entry log gi ci ?_
  intro s hs hp
  rcases h s hs with ⟨n, rfl⟩
  have htick : isOutputEntry s!"tick {n}" gi ci = false :=
    tick_entry_isOutputEntry_false n gi ci
  rw [htick] at hp
  cases hp

/-- When the chain entry `s!"{chainName gi ci}: 0"` is in the log,
    `outputPos` returns `some` for that chain. -/
theorem outputPos_chain_entry_zero (log : List String) (gi ci : Nat)
    (hmem : s!"{chainName gi ci}: 0" ∈ log) :
    (outputPos log gi ci).isSome := by
  refine (outputPos_some_iff_output_exists log gi ci).2
    ⟨s!"{chainName gi ci}: 0", hmem, ?_⟩
  exact (chain_entry_isOutputEntry_true gi ci).1

/-- When the chain entry `s!"{chainName gi ci}: 15"` is in the log,
    `outputPos` returns `some` for that chain. -/
theorem outputPos_chain_entry_fifteen (log : List String) (gi ci : Nat)
    (hmem : s!"{chainName gi ci}: 15" ∈ log) :
    (outputPos log gi ci).isSome := by
  refine (outputPos_some_iff_output_exists log gi ci).2
    ⟨s!"{chainName gi ci}: 15", hmem, ?_⟩
  exact (chain_entry_isOutputEntry_true gi ci).2
