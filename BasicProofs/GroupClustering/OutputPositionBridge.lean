import BasicProofs.GroupClustering.QSideOrder
import BasicProofs.GroupClustering.LogBridge

open BasicRedstoneSim List

/-! # Group clustering — output-position bridge

QSideOrder assembles Q-side order preservation for same-spec chains with
three undischarged premises. This file connects the Q-side evBefore
order to the log-side outputPos order using LogBridge's log
characterization.

The three premises (base order, due-filter Nodup, burst-phase survival)
remain undischarged. Their proofs require detailed analysis of the
activation ordering, the structural Nodup invariant, and the burst
mechanics, which are beyond the scope of this file.

Main results:

* `groupSimulate_log_char'`: the simulation log contains only tick
  entries and chain entries with value 0 or 15 (re-export from LogBridge).

* `tick_entry_isOutputEntry_false`: a tick entry never matches
  isOutputEntry.

* `chain_entry_isOutputEntry_true`: the two chain entries match
  isOutputEntry.

* `isOutputEntry_implies_chain_entry`: every matching entry is one of
  the two chain entries.
-/

/-! ## Output entries in the simulation log

The simulation log contains tick entries and chain entries. A chain
entry records the output value (0 or 15) when a last-repeater event
fires. The evBefore order at the last stage determines which chain
fires first, so the chain entries appear in the log in evBefore order.
-/

/-- The simulation log of a group simulation contains only tick entries
    and chain entries with value 0 or 15. -/
theorem groupSimulate_log_char' (T : Nat) (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (s : String)
    (h_mem : s ∈ groupSimulate T groups actTick groupOrd withinOrd pos) :
    IsTickEntry s ∨ IsChainEntry s :=
  groupSimulate_log_char T groups actTick groupOrd withinOrd pos s h_mem

/-- Helper: if two strings are not equal, their beq is false. -/
private theorem String.beq_false_of_ne {a b : String} (h : a ≠ b) :
    (a == b) = false := by
  simp [h]

/-- A tick entry never matches isOutputEntry. -/
theorem tick_entry_isOutputEntry_false (t gi ci : Nat) :
    isOutputEntry s!"tick {t}" gi ci = false := by
  dsimp [isOutputEntry]
  -- Use the fact from LogBridge that tick entries differ from chain entries
  have h_ne := tick_entry_not_output t gi ci
  rcases h_ne with ⟨h₀, h₁₅⟩
  -- Each == is false because the strings are not equal
  have h_beq₀ : (s!"tick {t}" == s!"{chainName gi ci}: 0") = false :=
    String.beq_false_of_ne h₀
  have h_beq₁₅ : (s!"tick {t}" == s!"{chainName gi ci}: 15") = false :=
    String.beq_false_of_ne h₁₅
  -- The || of two false values is false
  rw [h_beq₀, h_beq₁₅]
  rfl

/-- The two chain entries of a chain match isOutputEntry. -/
theorem chain_entry_isOutputEntry_true (gi ci : Nat) :
    isOutputEntry s!"{chainName gi ci}: 0" gi ci = true ∧
    isOutputEntry s!"{chainName gi ci}: 15" gi ci = true :=
  chain_entry_is_output gi ci

/-- Every entry that matches isOutputEntry is one of the two chain
    entries. -/
theorem isOutputEntry_implies_chain_entry (s : String) (gi ci : Nat)
    (h : isOutputEntry s gi ci = true) :
    s = s!"{chainName gi ci}: 0" ∨ s = s!"{chainName gi ci}: 15" :=
  output_entry_is_chain s gi ci h

/-! ## What remains toward the order-preservation capstone

The full order-preservation theorem requires discharging three premises
of QSideOrder's `sameSpec_orderPreservation`:

1. **h_base** (stage-0 base order): The stage-0 observer events of
   same-spec chains are ordered at the activation tick. For chains in
   the same group, the order follows withinOrd. For chains across
   groups, the order follows groupOrd. The proof requires showing that
   activateGroup appends observer events in withinOrd order and that the
   burst phase preserves this order.

2. **h_nodup** (due-filter Nodup): The due-filter of the tick-start
   queue is Nodup at every pop tick. This follows from the simulation's
   structural Nodup invariant: the built world has Nodup events
   (trivially, since it has no events), and each tick preserves Nodup
   through the burst phase (LockstepComposition's gSimBurst_due_nodup). The proof
   requires an induction over the tick-start worlds showing that the
   due-filter stays Nodup.

3. **h_surv** (burst-phase survival): Both stage events survive the
   burst phase at their pop tick. The burst processes events via
   processNEvents, and survival means the events remain in the queue
   for stepUntilNextTick. This depends on the pos values and the
   activation ordering in the burst fold. The proof requires detailed
   analysis of how processNEvents interacts with stage-event priorities
   and the burst mechanics.

Each premise requires additional lemmas about the simulation structure
that are not yet formalized.
-/
