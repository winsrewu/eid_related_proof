import BasicProofs.GroupClustering.FinalPopIndex
import BasicProofs.GroupClustering.LogBridge

open BasicRedstoneSim List

/-! # Group clustering — log shape and discharge of FinalPopIndex

FinalPopIndex proved the list-level bridge between the log and the final-pop
order. Its theorems carry the log shape and the final-pop facts as
explicit hypotheses. This file proves the log shape from the
definition of `groupSimulate` and supplies the final-pop analysis of
the tick-`T` drain.

## Results

* `chainEntry_name_inj` — two chain entries with different chain
  indices never collide as strings.

* `isOutputEntry_chain_inj` — a string that matches `isOutputEntry`
  for two chains comes from one chain.

* `groupSimulate_log_shape` — the log of `groupSimulate T` is a
  sequence of `T + 1` blocks. Block `t` starts with the tick entry
  `s!"tick {t}"`; the rest of the block holds chain entries. This is
  deliverable 1.

* `groupSimulate_log_split` — when no block before `T` holds chain
  entries, the log is the tick block followed by the chain entries of
  tick `T`. This discharges the `h_log`, `h_ticks_len` and `h_ticks`
  premises of FinalPopIndex.

* `finalEvent_fire_isOutputEntry` — firing the last-repeater event of
  a chain appends exactly one entry, and that entry matches the
  chain's `isOutputEntry`.

* `chainEntries_are_finalPops` — when the drain of a tick pops exactly
  the events of `finals`, the appended log holds one entry per popped
  event, in pop order. This is deliverable 2.

* `outputPos_eq_finalPopIndex_discharged` — FinalPopIndex's
  `outputPos_eq_index_of_chain_entry` with the log shape and the
  final-pop split supplied. This is deliverable 3.

* `groupBeforeSpec_iff_evBefore_discharged` — `groupBeforeSpec` on the
  `groupSimulate` log is equivalent to `evBefore` on the final events
  of same-spec chains. This is deliverable 4.

## What remains

Two scenario facts stay as hypotheses here:

* No output node logs before tick `T` (the `h_no_early` premise). It
  says every block before `T` is empty. The proof needs the activation
  schedule: every chain fires its last repeater exactly at tick `T`.

* The drain of tick `T` pops exactly the final events, in the list
  `finals` (the `h_pop_seq` premise). The proof needs the queue
  characterization at tick `T`.
-/

/-! ## Chain entries of different chains never collide

A chain entry is `g.repr ++ ":" ++ c.repr ++ ": " ++ v.repr`. Decimal
digit lists carry no colon. The first colon therefore ends the group
index, and the second colon ends the chain index. Equal entries force
equal group and chain indices. The decimal representation is injective:
equal digit lists give equal numbers. -/

/-- A digit character is not the colon character. -/
private theorem Char.ne_colon_of_isDigit (c : Char) (h : c.isDigit) :
    c ≠ ':' := by
  intro h_eq
  rw [h_eq] at h
  exact (by decide : ¬ (':' : Char).isDigit) h

/-- No character of a base-10 digit list is a colon. -/
private theorem no_colon_in_digits (n : Nat) :
    ∀ ch ∈ Nat.toDigits 10 n, ch ≠ ':' := by
  intro ch h_ch
  exact Char.ne_colon_of_isDigit ch
    (Nat.isDigit_of_mem_toDigits (by decide) (by decide) h_ch)

/-- Splitting two lists at their first colon: equal sums with
    colon-free left parts give equal left parts and equal remainders. -/
private theorem append_colon_inj (l₁ l₂ r₁ r₂ : List Char)
    (h₁ : ∀ c ∈ l₁, c ≠ ':') (h₂ : ∀ c ∈ l₂, c ≠ ':')
    (h : l₁ ++ ':' :: r₁ = l₂ ++ ':' :: r₂) :
    l₁ = l₂ ∧ r₁ = r₂ := by
  revert l₂ r₁ r₂ h₁ h₂ h
  induction l₁ with
  | nil =>
    intro l₂ r₁ r₂ h₁ h₂ h
    cases l₂ with
    | nil =>
      simp at h
      exact ⟨rfl, h⟩
    | cons b l₂' =>
      have h_b : b ≠ ':' := h₂ b (List.mem_cons.mpr (Or.inl rfl))
      change ':' :: r₁ = b :: (l₂' ++ ':' :: r₂) at h
      injection h with h_bc
      exact (h_b h_bc.symm).elim
  | cons a l₁' ih =>
    intro l₂ r₁ r₂ h₁ h₂ h
    cases l₂ with
    | nil =>
      have h_a : a ≠ ':' := h₁ a (List.mem_cons.mpr (Or.inl rfl))
      change a :: (l₁' ++ ':' :: r₁) = ':' :: r₂ at h
      injection h with h_ac
      exact (h_a h_ac).elim
    | cons b l₂' =>
      change a :: (l₁' ++ ':' :: r₁) = b :: (l₂' ++ ':' :: r₂) at h
      injection h with h_ab h_rest
      obtain ⟨h_l, h_r⟩ := ih l₂' r₁ r₂
        (fun c hc => h₁ c (List.mem_cons.mpr (Or.inr hc)))
        (fun c hc => h₂ c (List.mem_cons.mpr (Or.inr hc))) h_rest
      exact ⟨by rw [h_ab, h_l], h_r⟩

/-- `digitChar` is injective below 10. -/
private theorem digitChar_inj_of_lt_ten {a b : Nat} (ha : a < 10)
    (hb : b < 10) (h : a.digitChar = b.digitChar) : a = b := by
  have h_a := Nat.toNat_digitChar_of_lt_ten ha
  have h_b := Nat.toNat_digitChar_of_lt_ten hb
  rw [h] at h_a
  omega

/-- Two lists that end in one element: equality gives equal bodies and
    equal last elements. -/
private theorem append_singleton_inj {α : Type} (l₁ l₂ : List α) (a b : α)
    (h : l₁ ++ [a] = l₂ ++ [b]) : l₁ = l₂ ∧ a = b := by
  revert l₂ h
  induction l₁ with
  | nil =>
    intro l₂ h
    cases l₂ with
    | nil =>
      simp at h
      exact ⟨rfl, h⟩
    | cons c l₂' =>
      change [a] = c :: (l₂' ++ [b]) at h
      -- injection derives `[] = l₂' ++ [b]`, impossible by length
      injection h with _ h_tail
      have h_len := congrArg List.length h_tail
      simp at h_len
  | cons x l₁' ih =>
    intro l₂ h
    cases l₂ with
    | nil =>
      change x :: (l₁' ++ [a]) = [b] at h
      -- injection derives `l₁' ++ [a] = []`, impossible by length
      injection h with _ h_tail
      have h_len := congrArg List.length h_tail
      simp at h_len
    | cons y l₂' =>
      change x :: (l₁' ++ [a]) = y :: (l₂' ++ [b]) at h
      injection h with h_xy h_tail
      obtain ⟨h_l, h_ab⟩ := ih l₂' h_tail
      exact ⟨by rw [h_xy, h_l], h_ab⟩

/-- Base-10 digit lists determine the number. -/
private theorem toDigits10_inj (g gi : Nat)
    (h : Nat.toDigits 10 g = Nat.toDigits 10 gi) : g = gi := by
  have hb : 1 < (10 : Nat) := by decide
  induction g using Nat.strongRecOn generalizing gi with
  | ind g ih =>
    -- expand both sides at rigid occurrences
    rw [show Nat.toDigits 10 gi =
        if gi < 10 then [gi.digitChar]
        else Nat.toDigits 10 (gi / 10) ++ [Nat.digitChar (gi % 10)] from
      Nat.toDigits_eq_if hb] at h
    rw [show Nat.toDigits 10 g =
        if g < 10 then [g.digitChar]
        else Nat.toDigits 10 (g / 10) ++ [Nat.digitChar (g % 10)] from
      Nat.toDigits_eq_if hb] at h
    by_cases h_g : g < 10
    · by_cases h_gi : gi < 10
      · -- both below 10
        rw [if_pos h_g, if_pos h_gi] at h
        injection h with h_digit
        exact digitChar_inj_of_lt_ten h_g h_gi h_digit
      · -- g below 10, gi at least 10: length mismatch
        rw [if_pos h_g, if_neg h_gi] at h
        have h_len := congrArg List.length h
        simp only [List.length_cons, List.length_append, List.length_nil,
          Nat.zero_add] at h_len
        have h_pos : 0 < (Nat.toDigits 10 (gi / 10)).length :=
          Nat.length_toDigits_pos
        omega
    · by_cases h_gi : gi < 10
      · -- g at least 10, gi below 10: length mismatch
        rw [if_neg h_g, if_pos h_gi] at h
        have h_len := congrArg List.length h
        simp only [List.length_cons, List.length_append, List.length_nil,
          Nat.zero_add] at h_len
        have h_pos : 0 < (Nat.toDigits 10 (g / 10)).length :=
          Nat.length_toDigits_pos
        omega
      · -- both at least 10: peel the last digit
        rw [if_neg h_g, if_neg h_gi] at h
        obtain ⟨h_pre, h_last⟩ := append_singleton_inj
          (Nat.toDigits 10 (g / 10)) (Nat.toDigits 10 (gi / 10))
          (g % 10).digitChar (gi % 10).digitChar h
        have h_mod : g % 10 = gi % 10 :=
          digitChar_inj_of_lt_ten (Nat.mod_lt g (by decide))
            (Nat.mod_lt gi (by decide)) h_last
        have h_div : g / 10 = gi / 10 :=
          ih (g / 10) (Nat.div_lt_self (by omega) hb) (gi / 10) h_pre
        calc g = 10 * (g / 10) + g % 10 := (Nat.div_add_mod g 10).symm
          _ = 10 * (gi / 10) + gi % 10 := by rw [h_div, h_mod]
          _ = gi := Nat.div_add_mod gi 10

/-- The character list of the literal `":"`. -/
private theorem toList_colon : (":" : String).toList = [':'] := by decide

/-- The character list of the literal `": 0"`. -/
private theorem toList_colon_space_zero :
    (": 0" : String).toList = [':', ' ', '0'] := by decide

/-- The character list of the literal `": 15"`. -/
private theorem toList_colon_space_fifteen :
    (": 15" : String).toList = [':', ' ', '1', '5'] := by decide

/-- The character list of a chain name. -/
private theorem chainName_toList (a b : Nat) :
    (chainName a b).toList =
    Nat.toDigits 10 a ++ [':'] ++ Nat.toDigits 10 b := by
  dsimp [chainName]
  change (a.repr ++ ":" ++ b.repr).toList = _
  rw [String.toList_append, String.toList_append, toList_colon,
    Nat.toList_repr, Nat.toList_repr]

/-- Two lists joined by colons: the group digits and the chain digits
    are determined by the joined list. -/
private theorem chainEntry_name_inj_core (g c gi ci : Nat)
    (t t' : List Char)
    (h : Nat.toDigits 10 g ++ ':' :: (Nat.toDigits 10 c ++ ':' :: t) =
        Nat.toDigits 10 gi ++ ':' :: (Nat.toDigits 10 ci ++ ':' :: t')) :
    g = gi ∧ c = ci := by
  obtain ⟨h_dg, h_rest⟩ := append_colon_inj (Nat.toDigits 10 g)
    (Nat.toDigits 10 gi) (Nat.toDigits 10 c ++ ':' :: t)
    (Nat.toDigits 10 ci ++ ':' :: t')
    (no_colon_in_digits g) (no_colon_in_digits gi) h
  obtain ⟨h_dc, _⟩ := append_colon_inj (Nat.toDigits 10 c)
    (Nat.toDigits 10 ci) t t' (no_colon_in_digits c)
    (no_colon_in_digits ci) h_rest
  exact ⟨toDigits10_inj g gi h_dg, toDigits10_inj c ci h_dc⟩

/-- A list joined as `a ++ [':'] ++ b` followed by a colon list equals
    `a ++ ':' :: (b ++ rest)`. -/
private theorem colon_join_form (a b rest : List Char) :
    (a ++ [':'] ++ b) ++ rest = a ++ ':' :: (b ++ rest) := by
  rw [List.append_assoc, List.append_assoc,
    show ([':'] : List Char) = ':' :: [] from rfl, List.cons_append,
    List.nil_append]

/-- Chain entries of different chains never collide as strings. The two
    suffixes are the character lists of `": 0"` or `": 15"`. -/
theorem chainEntry_name_inj (g c gi ci : Nat) (sfx sfx' : String)
    (h_sfx : sfx.toList = [':', ' ', '0'] ∨
        sfx.toList = [':', ' ', '1', '5'])
    (h_sfx' : sfx'.toList = [':', ' ', '0'] ∨
        sfx'.toList = [':', ' ', '1', '5'])
    (h : chainName g c ++ sfx = chainName gi ci ++ sfx') :
    g = gi ∧ c = ci := by
  have h_list := congrArg String.toList h
  rw [String.toList_append, String.toList_append] at h_list
  rw [chainName_toList, chainName_toList] at h_list
  rcases h_sfx with h_sfx | h_sfx <;>
    rcases h_sfx' with h_sfx' | h_sfx' <;>
    rw [h_sfx, h_sfx'] at h_list
  all_goals
    rw [colon_join_form, colon_join_form] at h_list
    exact chainEntry_name_inj_core g c gi ci _ _ h_list

/-- A string that matches `isOutputEntry` for two chains belongs to one
    chain. -/
theorem isOutputEntry_chain_inj (s : String) (g c gi ci : Nat)
    (h₁ : isOutputEntry s g c = true) (h₂ : isOutputEntry s gi ci = true) :
    g = gi ∧ c = ci := by
  rcases output_entry_is_chain s g c h₁ with h_s | h_s
  · rcases output_entry_is_chain s gi ci h₂ with h_s' | h_s'
    · apply chainEntry_name_inj g c gi ci ": 0" ": 0"
        (Or.inl toList_colon_space_zero) (Or.inl toList_colon_space_zero)
      exact h_s.symm.trans h_s'
    · apply chainEntry_name_inj g c gi ci ": 0" ": 15"
        (Or.inl toList_colon_space_zero) (Or.inr toList_colon_space_fifteen)
      exact h_s.symm.trans h_s'
  · rcases output_entry_is_chain s gi ci h₂ with h_s' | h_s'
    · apply chainEntry_name_inj g c gi ci ": 15" ": 0"
        (Or.inr toList_colon_space_fifteen) (Or.inl toList_colon_space_zero)
      exact h_s.symm.trans h_s'
    · apply chainEntry_name_inj g c gi ci ": 15" ": 15"
        (Or.inr toList_colon_space_fifteen)
        (Or.inr toList_colon_space_fifteen)
      exact h_s.symm.trans h_s'

/-- Equal functions on the members give equal maps. -/
private theorem List.map_congr' {α β : Type} {f g : α → β} (l : List α)
    (h : ∀ a ∈ l, f a = g a) : l.map f = l.map g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, h a (List.mem_cons.mpr (Or.inl rfl)),
      ih (fun a' h_a' => h a' (List.mem_cons.mpr (Or.inr h_a')))]

/-! ## Log growth: every simulation operation appends chain entries

The log grows only through `logOutput`. The tick prelude of `gSimBody`
appends the tick entry; every other append comes from an output node
and is a chain entry under `OutputNamesOk` and `SigLevelsOk`. -/

/-- The output log of `w'` is the output log of `w` plus chain entries
    only. -/
private def LogAppendChain (w w' : World) : Prop :=
  ∃ rest, w'.outputLog = w.outputLog ++ rest ∧ ∀ s ∈ rest, IsChainEntry s

/-- Setting a node's signal level keeps the output-name invariant. -/
private theorem OutputNamesOk_updateNode_keep (w : World) (id : Nat)
    (f : NodeData → NodeData) (h_f : ∀ nd, (f nd).kind = nd.kind)
    (hO : OutputNamesOk w) : OutputNamesOk (w.updateNode id f) := by
  intro nid nd nm h_gn h_k
  obtain ⟨nd₀, h₀, h_kind⟩ := World.updateNode_getNode_kind w id nid f h_f nd h_gn
  exact hO nid nd₀ nm h₀ (by rw [h_kind, h_k])

/-- Setting a node's signal level to 0 or 15 keeps the signal-level
    invariant. -/
private theorem SigLevelsOk_updateNode_keep (w : World) (id : Nat)
    (f : NodeData → NodeData)
    (h_f : ∀ nd, (f nd).sigLevel = 0 ∨ (f nd).sigLevel = 15)
    (hS : SigLevelsOk w) : SigLevelsOk (w.updateNode id f) := by
  intro nid nd h
  by_cases h_eq : nid = id
  · subst nid
    cases h_orig : w.getNode id with
    | none =>
      rw [World.updateNode_getNode_none w id f h_orig] at h
      cases h
    | some nd₀ =>
      rw [World.updateNode_getNode_eq w id f nd₀ h_orig] at h
      injection h with h_nd
      rw [← h_nd]
      exact h_f nd₀
  · rw [World.updateNode_getNode_ne w id nid f (Ne.symm h_eq)] at h
    exact hS nid nd h

/-- `onNeighborUpdate` keeps the output-name invariant. -/
private theorem OutputNamesOk_onNeighborUpdate_keep (w : World) (id : Nat)
    (hO : OutputNamesOk w) : OutputNamesOk (w.onNeighborUpdate id) := by
  intro nid nd nm h_gn h_k
  rw [World.onNeighborUpdate_getNode] at h_gn
  exact hO nid nd nm h_gn h_k

/-- `onNeighborUpdate` keeps the signal-level invariant. -/
private theorem SigLevelsOk_onNeighborUpdate_keep (w : World) (id : Nat)
    (hS : SigLevelsOk w) : SigLevelsOk (w.onNeighborUpdate id) := by
  intro nid nd h_gn
  rw [World.onNeighborUpdate_getNode] at h_gn
  exact hS nid nd h_gn

/-- One neighbor update appends at most one chain entry. -/
private theorem LogAppendChain_onNeighborUpdate (w : World) (id : Nat)
    (hO : OutputNamesOk w) (hS : SigLevelsOk w) :
    LogAppendChain w (w.onNeighborUpdate id) := by
  cases h_gn : w.getNode id with
  | none =>
    refine ⟨[], ?_, ?_⟩
    · dsimp [World.onNeighborUpdate]
      simp only [h_gn, List.append_nil]
    · intro s h_s
      cases h_s
  | some nd =>
    cases h_kind : nd.kind with
    | input =>
      refine ⟨[], ?_, ?_⟩
      · dsimp [World.onNeighborUpdate]
        simp only [h_gn, h_kind, List.append_nil]
      · intro s h_s
        cases h_s
    | observer =>
      refine ⟨[], ?_, ?_⟩
      · dsimp [World.onNeighborUpdate]
        simp only [h_gn, h_kind, World.scheduleEvent_outputLog,
          List.append_nil]
      · intro s h_s
        cases h_s
    | repeater d p =>
      refine ⟨[], ?_, ?_⟩
      · dsimp [World.onNeighborUpdate]
        simp only [h_gn, h_kind, World.scheduleEvent_outputLog,
          List.append_nil]
      · intro s h_s
        cases h_s
    | output nm =>
      obtain ⟨gi, ci, h_nm⟩ := hO id nd nm h_gn h_kind
      refine ⟨[s!"{nm}: {w.getInputSignal id}"], ?_, ?_⟩
      · dsimp [World.onNeighborUpdate]
        simp only [h_gn, h_kind]
        dsimp [World.logOutput]
      · intro s h_s
        rw [List.mem_singleton] at h_s
        subst h_s
        rw [h_nm]
        refine ⟨gi, ci, w.getInputSignal id, ?_, rfl⟩
        exact getInputSignal_zero_or_fifteen w id hS

/-- A foldl of neighbor updates appends chain entries only. -/
private theorem LogAppendChain_foldl_onNeighborUpdate (l : List Nat)
    (w : World) (hO : OutputNamesOk w) (hS : SigLevelsOk w) :
    LogAppendChain w (l.foldl (fun w' outId => w'.onNeighborUpdate outId) w) := by
  induction l generalizing w with
  | nil =>
    refine ⟨[], ?_, ?_⟩
    · simp
    · intro s h_s
      cases h_s
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    obtain ⟨r₁, h_r₁, h_c₁⟩ := LogAppendChain_onNeighborUpdate w hd hO hS
    obtain ⟨r₂, h_r₂, h_c₂⟩ := ih (w.onNeighborUpdate hd)
      (OutputNamesOk_onNeighborUpdate_keep w hd hO)
      (SigLevelsOk_onNeighborUpdate_keep w hd hS)
    refine ⟨r₁ ++ r₂, ?_, ?_⟩
    · rw [h_r₂, h_r₁, ← List.append_assoc]
    · intro s h_s
      rw [List.mem_append] at h_s
      rcases h_s with h_s | h_s
      · exact h_c₁ s h_s
      · exact h_c₂ s h_s

/-- `onScheduledTick` keeps the output-name invariant. -/
private theorem OutputNamesOk_onScheduledTick_keep (w : World) (id : Nat)
    (hO : OutputNamesOk w) : OutputNamesOk (w.onScheduledTick id) := by
  intro nid nd nm h_gn h_k
  obtain ⟨nd₀, h₀, h_kind⟩ := World.onScheduledTick_getNode_kind w id nid nd h_gn
  exact hO nid nd₀ nm h₀ (by rw [h_kind, h_k])

/-- `onScheduledTick` keeps the signal-level invariant. -/
private theorem SigLevelsOk_onScheduledTick_keep (w : World) (id : Nat)
    (hS : SigLevelsOk w) : SigLevelsOk (w.onScheduledTick id) := by
  intro nid nd h
  dsimp [World.onScheduledTick] at h
  split at h
  · exact hS nid nd h
  · rename_i nd_id; split at h
    · rw [World.notifyOutputs_getNode] at h
      exact SigLevelsOk_updateNode_keep w id
        (fun nd' => ({ nd' with
            sigLevel := if w.getInputSignal id > 0 then 15 else 0 } : NodeData))
        (fun nd' => by
          dsimp only
          split_ifs with h_c
          · right; rfl
          · left; rfl) hS nid nd h
    · rw [World.notifyOutputs_getNode] at h
      exact SigLevelsOk_updateNode_keep w id
        (fun nd' => ({ nd' with sigLevel := 15 } : NodeData))
        (fun nd' => Or.inr rfl) hS nid nd h
    · exact hS nid nd h

/-- Firing a node appends chain entries only. -/
private theorem LogAppendChain_onScheduledTick (w : World) (id : Nat)
    (hO : OutputNamesOk w) (hS : SigLevelsOk w) :
    LogAppendChain w (w.onScheduledTick id) := by
  dsimp [World.onScheduledTick]
  split
  · -- no node: no change
    refine ⟨[], ?_, ?_⟩
    · rw [List.append_nil]
    · intro s h_s
      cases h_s
  · rename_i nd; split
    · -- repeater: set the level, notify the outputs
      set f : NodeData → NodeData := fun nd' =>
        { nd' with sigLevel := if w.getInputSignal id > 0 then 15 else 0 }
      dsimp [World.notifyOutputs]
      cases h_gn' : (w.updateNode id f).getNode id with
      | none =>
        refine ⟨[], ?_, ?_⟩
        · change w.outputLog = w.outputLog ++ []
          rw [List.append_nil]
        · intro s h_s
          cases h_s
      | some nd' =>
        obtain ⟨rest, h_rest, h_chain⟩ := LogAppendChain_foldl_onNeighborUpdate
          nd'.outputs (w.updateNode id f)
          (OutputNamesOk_updateNode_keep w id f (fun nd' => rfl) hO)
          (SigLevelsOk_updateNode_keep w id f (fun nd' => by
            show (if w.getInputSignal id > 0 then 15 else 0) = 0 ∨
              (if w.getInputSignal id > 0 then 15 else 0) = 15
            split_ifs with h_c
            · right; rfl
            · left; rfl) hS)
        refine ⟨rest, ?_, h_chain⟩
        rw [h_rest]
        exact rfl
    · -- observer: set the level to 15, notify the outputs
      set f : NodeData → NodeData := fun nd' => { nd' with sigLevel := 15 }
      dsimp [World.notifyOutputs]
      cases h_gn' : (w.updateNode id f).getNode id with
      | none =>
        refine ⟨[], ?_, ?_⟩
        · change w.outputLog = w.outputLog ++ []
          rw [List.append_nil]
        · intro s h_s
          cases h_s
      | some nd' =>
        obtain ⟨rest, h_rest, h_chain⟩ := LogAppendChain_foldl_onNeighborUpdate
          nd'.outputs (w.updateNode id f)
          (OutputNamesOk_updateNode_keep w id f (fun nd' => rfl) hO)
          (SigLevelsOk_updateNode_keep w id f (fun nd' => Or.inr rfl) hS)
        refine ⟨rest, ?_, h_chain⟩
        rw [h_rest]
        exact rfl
    · -- output or input: no change
      refine ⟨[], ?_, ?_⟩
      · rw [List.append_nil]
      · intro s h_s
        cases h_s

/-- One step appends chain entries only and keeps both invariants. -/
private theorem LogAppendChain_step (w w' : World)
    (h_step : w.step = some w') (hO : OutputNamesOk w) (hS : SigLevelsOk w) :
    ∃ rest, w'.outputLog = w.outputLog ++ rest ∧
      (∀ s ∈ rest, IsChainEntry s) ∧ OutputNamesOk w' ∧ SigLevelsOk w' := by
  dsimp [World.step] at h_step
  cases h_pop : w.popNextEvent with
  | none =>
    simp only [h_pop] at h_step
    cases h_step
  | some p =>
    rcases p with ⟨ev, w_pop⟩
    simp only [h_pop] at h_step
    injection h_step with h_w'
    have h_nodes_pop : w_pop.nodes = w.nodes :=
      World.popNextEvent_nodes w ev w_pop h_pop
    have hO_pop : OutputNamesOk w_pop := by
      intro nid nd nm h_gn h_k
      dsimp [World.getNode] at h_gn ⊢
      rw [h_nodes_pop] at h_gn
      exact hO nid nd nm h_gn h_k
    have hS_pop : SigLevelsOk w_pop := by
      intro nid nd h_gn
      dsimp [World.getNode] at h_gn ⊢
      rw [h_nodes_pop] at h_gn
      exact hS nid nd h_gn
    obtain ⟨rest, h_rest, h_chain⟩ :=
      LogAppendChain_onScheduledTick w_pop ev.nodeId hO_pop hS_pop
    refine ⟨rest, ?_, h_chain, ?_, ?_⟩
    · rw [← h_w', h_rest, World.popNextEvent_outputLog w ev w_pop h_pop]
    · rw [← h_w']
      exact OutputNamesOk_onScheduledTick_keep w_pop ev.nodeId hO_pop
    · rw [← h_w']
      exact SigLevelsOk_onScheduledTick_keep w_pop ev.nodeId hS_pop

/-- `processNEvents` appends chain entries only and keeps both
    invariants. -/
private theorem LogAppendChain_processNEvents (w : World) (n : Nat)
    (hO : OutputNamesOk w) (hS : SigLevelsOk w) :
    ∃ rest, (processNEvents w n).outputLog = w.outputLog ++ rest ∧
      (∀ s ∈ rest, IsChainEntry s) ∧
      OutputNamesOk (processNEvents w n) ∧ SigLevelsOk (processNEvents w n) := by
  induction n generalizing w with
  | zero =>
    refine ⟨[], ?_, ?_, hO, hS⟩
    · dsimp [processNEvents]
      rw [List.append_nil]
    · intro s h_s
      cases h_s
  | succ n' ih =>
    dsimp only [processNEvents]
    cases h_step : w.step with
    | none =>
      refine ⟨[], ?_, ?_, hO, hS⟩
      · rw [List.append_nil]
      · intro s h_s
        cases h_s
    | some w'' =>
      obtain ⟨r₁, h_r₁, h_c₁, hO', hS'⟩ :=
        LogAppendChain_step w w'' h_step hO hS
      obtain ⟨r₂, h_r₂, h_c₂, hO'', hS''⟩ := ih w'' hO' hS'
      refine ⟨r₁ ++ r₂, ?_, ?_, hO'', hS''⟩
      · rw [h_r₂, h_r₁, ← List.append_assoc]
      · intro s h_s
        rw [List.mem_append] at h_s
        rcases h_s with h_s | h_s
        · exact h_c₁ s h_s
        · exact h_c₂ s h_s

/-- `activateGroup` does not touch the output log. -/
private theorem activateGroup_outputLog (w : World) (observers : List Nat) :
    (activateGroup w observers).outputLog = w.outputLog := by
  induction observers generalizing w with
  | nil => dsimp [activateGroup]
  | cons oid os ih =>
    dsimp [activateGroup, List.foldl_cons]
    set ev : ScheduledEvent :=
      { targetTick := w.tick + 2, priority := 0, nodeId := oid }
    change (activateGroup (w.scheduleEvent ev) os).outputLog = w.outputLog
    rw [ih, World.scheduleEvent_outputLog]

/-- `gSimBurst` appends chain entries only and keeps both invariants. -/
private theorem LogAppendChain_gSimBurst (t : Nat) (obsAll : List (List Nat))
    (withinOrd pos : Nat → List Nat) (w : World) (pairs : List (Nat × Nat))
    (hO : OutputNamesOk w) (hS : SigLevelsOk w) :
    ∃ rest, (gSimBurst t obsAll withinOrd pos w pairs).outputLog =
        w.outputLog ++ rest ∧
      (∀ s ∈ rest, IsChainEntry s) ∧
      OutputNamesOk (gSimBurst t obsAll withinOrd pos w pairs) ∧
      SigLevelsOk (gSimBurst t obsAll withinOrd pos w pairs) := by
  induction pairs generalizing w with
  | nil =>
    refine ⟨[], ?_, ?_, hO, hS⟩
    · dsimp [gSimBurst]
      rw [List.append_nil]
    · intro s h_s
      cases h_s
  | cons p ps ih =>
    rcases p with ⟨gi, k⟩
    dsimp only [gSimBurst, List.foldl_cons]
    obtain ⟨r₁, h_r₁, h_c₁, hO_p, hS_p⟩ :=
      LogAppendChain_processNEvents w ((pos t)[k]?.getD 0) hO hS
    have hO₁ : OutputNamesOk
        (activateGroup (processNEvents w ((pos t)[k]?.getD 0))
          ((withinOrd gi).foldl (fun acc ci =>
            match ((obsAll[gi]?.getD [])[ci]?) with
            | some oid => acc ++ [oid]
            | none => acc) [])) := by
      intro nid nd nm h_gn h_k
      dsimp [World.getNode] at h_gn
      rw [activateGroup_nodes] at h_gn
      exact hO_p nid nd nm h_gn h_k
    have hS₁ : SigLevelsOk
        (activateGroup (processNEvents w ((pos t)[k]?.getD 0))
          ((withinOrd gi).foldl (fun acc ci =>
            match ((obsAll[gi]?.getD [])[ci]?) with
            | some oid => acc ++ [oid]
            | none => acc) [])) := by
      intro nid nd h_gn
      dsimp [World.getNode] at h_gn
      rw [activateGroup_nodes] at h_gn
      exact hS_p nid nd h_gn
    obtain ⟨r₂, h_r₂, h_c₂, hO', hS'⟩ := ih
      (activateGroup (processNEvents w ((pos t)[k]?.getD 0))
        ((withinOrd gi).foldl (fun acc ci =>
          match ((obsAll[gi]?.getD [])[ci]?) with
          | some oid => acc ++ [oid]
          | none => acc) [])) hO₁ hS₁
    refine ⟨r₁ ++ r₂, ?_, ?_, hO', hS'⟩
    · change (gSimBurst t obsAll withinOrd pos
          (activateGroup (processNEvents w ((pos t)[k]?.getD 0))
            ((withinOrd gi).foldl (fun acc ci =>
              match ((obsAll[gi]?.getD [])[ci]?) with
              | some oid => acc ++ [oid]
              | none => acc) [])) ps).outputLog =
        w.outputLog ++ (r₁ ++ r₂)
      rw [h_r₂, activateGroup_outputLog, h_r₁, ← List.append_assoc]
    · intro s h_s
      rw [List.mem_append] at h_s
      rcases h_s with h_s | h_s
      · exact h_c₁ s h_s
      · exact h_c₂ s h_s

/-- `stepUntilNextTick` appends chain entries only and keeps both
    invariants. -/
private theorem LogAppendChain_stepUntilNextTick (w : World)
    (hO : OutputNamesOk w) (hS : SigLevelsOk w) :
    ∃ rest, w.stepUntilNextTick.outputLog = w.outputLog ++ rest ∧
      (∀ s ∈ rest, IsChainEntry s) ∧
      OutputNamesOk w.stepUntilNextTick ∧ SigLevelsOk w.stepUntilNextTick := by
  revert hO hS
  induction w using World.stepUntilNextTick.induct with
  | case1 x h_step =>
    intro hO hS
    rw [stepUntilNextTick_of_step_none x h_step]
    refine ⟨[], ?_, ?_, ?_, ?_⟩
    · rw [List.append_nil]
    · intro s h_s
      cases h_s
    · intro nid nd nm h_gn h_k
      dsimp [World.getNode] at h_gn
      exact hO nid nd nm h_gn h_k
    · intro nid nd h_gn
      dsimp [World.getNode] at h_gn
      exact hS nid nd h_gn
  | case2 x w' h_step ih =>
    intro hO hS
    have h_sunt : x.stepUntilNextTick = w'.stepUntilNextTick := by
      rw [World.stepUntilNextTick, h_step]
    obtain ⟨r₁, h_r₁, h_c₁, hO', hS'⟩ :=
      LogAppendChain_step x w' h_step hO hS
    obtain ⟨r₂, h_r₂, h_c₂, hO'', hS''⟩ := ih hO' hS'
    refine ⟨r₁ ++ r₂, ?_, ?_, ?_, ?_⟩
    · rw [h_sunt, h_r₂, h_r₁, ← List.append_assoc]
    · intro s h_s
      rw [List.mem_append] at h_s
      rcases h_s with h_s | h_s
      · exact h_c₁ s h_s
      · exact h_c₂ s h_s
    · rw [h_sunt]
      exact hO''
    · rw [h_sunt]
      exact hS''

/-- One `gSimBody` call appends its tick entry, then chain entries
    only. It keeps both invariants. -/
private theorem LogAppendChain_gSimBody (actTick : Nat → Nat)
    (obsAll : List (List Nat)) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (w : World) (i : Nat)
    (hO : OutputNamesOk w) (hS : SigLevelsOk w) :
    ∃ rest, (gSimBody actTick obsAll groupOrd withinOrd pos w i).outputLog =
        w.outputLog ++ (s!"tick {w.tick}" :: rest) ∧
      (∀ s ∈ rest, IsChainEntry s) ∧
      OutputNamesOk (gSimBody actTick obsAll groupOrd withinOrd pos w i) ∧
      SigLevelsOk (gSimBody actTick obsAll groupOrd withinOrd pos w i) := by
  dsimp [gSimBody]
  set W₁ := w.logOutput s!"tick {w.tick}"
  set A := groupOrd.filter (fun gi =>
    decide (gi < obsAll.length) && (actTick gi == w.tick))
  have hO₁ : OutputNamesOk W₁ := by
    intro nid nd nm h_gn h_k
    change (w.logOutput s!"tick {w.tick}").getNode nid = some nd at h_gn
    rw [World.logOutput_getNode] at h_gn
    exact hO nid nd nm h_gn h_k
  have hS₁ : SigLevelsOk W₁ := by
    intro nid nd h_gn
    change (w.logOutput s!"tick {w.tick}").getNode nid = some nd at h_gn
    rw [World.logOutput_getNode] at h_gn
    exact hS nid nd h_gn
  have hW₁_log : W₁.outputLog = w.outputLog ++ [s!"tick {w.tick}"] := by
    dsimp [W₁, World.logOutput]
  split_ifs with h_active
  · obtain ⟨rest, h_rest, h_chain, hO', hS'⟩ :=
      LogAppendChain_stepUntilNextTick W₁ hO₁ hS₁
    refine ⟨rest, ?_, h_chain, hO', hS'⟩
    rw [h_rest, hW₁_log, List.append_assoc]
    rfl
  · set W₂ := gSimBurst w.tick obsAll withinOrd pos W₁ (A.zipIdx)
    obtain ⟨r₁, h_r₁, h_c₁, hO₂, hS₂⟩ :=
      LogAppendChain_gSimBurst w.tick obsAll withinOrd pos W₁ A.zipIdx hO₁ hS₁
    obtain ⟨r₂, h_r₂, h_c₂, hO', hS'⟩ :=
      LogAppendChain_stepUntilNextTick W₂ hO₂ hS₂
    refine ⟨r₁ ++ r₂, ?_, ?_, hO', hS'⟩
    · rw [h_r₂, h_r₁, hW₁_log]
      rw [List.append_assoc, List.append_assoc]
      rfl
    · intro s h_s
      rw [List.mem_append] at h_s
      rcases h_s with h_s | h_s
      · exact h_c₁ s h_s
      · exact h_c₂ s h_s

/-! ## Deliverable 1 — the block shape of the log -/

/-- The foldl of block appends over `range n`. -/
def logBlocks (init : List String) (start : Nat)
    (chainAt : Nat → List String) (n : Nat) : List String :=
  (List.range n).foldl
    (fun acc t => acc ++ (s!"tick {start + t}" :: chainAt t)) init

/-- The blocks of `range n` contain the tick entry of each tick. -/
private theorem mem_logBlocks_tick (start t n : Nat)
    (chainAt : Nat → List String) (h_t : t < n) :
    s!"tick {start + t}" ∈ logBlocks [] start chainAt n := by
  dsimp [logBlocks]
  induction n generalizing start with
  | zero => omega
  | succ n' ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [List.mem_append]
    by_cases h : t < n'
    · left
      exact ih start h
    · right
      have h_eq : t = n' := by omega
      subst h_eq
      exact List.mem_cons.mpr (Or.inl rfl)

/-- Every entry of the blocks of `range n` is a tick entry of a tick
    below `n` or an entry of one of the block tails. -/
private theorem mem_logBlocks_cases (start n : Nat)
    (chainAt : Nat → List String) (s : String)
    (h_mem : s ∈ logBlocks [] start chainAt n) :
    (∃ t < n, s = s!"tick {start + t}") ∨ ∃ t < n, s ∈ chainAt t := by
  dsimp [logBlocks] at h_mem
  induction n generalizing s with
  | zero =>
    dsimp [List.range] at h_mem
    cases h_mem
  | succ n' ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil] at h_mem
    rw [List.mem_append] at h_mem
    rcases h_mem with h_mem | h_mem
    · obtain h_tick | h_chain := ih s h_mem
      · left
        obtain ⟨t, h_t, h_eq⟩ := h_tick
        exact ⟨t, by omega, h_eq⟩
      · right
        obtain ⟨t, h_t, h_mem_t⟩ := h_chain
        exact ⟨t, by omega, h_mem_t⟩
    · rw [List.mem_cons] at h_mem
      rcases h_mem with h_eq | h_mem
      · left
        exact ⟨n', by omega, by simpa using h_eq⟩
      · right
        exact ⟨n', by omega, h_mem⟩

/-- Two block folds are equal when the block tails agree on every
    block of the range. -/
private theorem foldl_blocks_congr (init : List String) (a n : Nat)
    (f g : Nat → List String) (h : ∀ t < n, f t = g t) :
    (List.range n).foldl (fun acc t => acc ++ (s!"tick {a + t}" :: f t))
      init =
    (List.range n).foldl (fun acc t => acc ++ (s!"tick {a + t}" :: g t))
      init := by
  induction n generalizing init with
  | zero => dsimp [List.range]
  | succ n' ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil]
    have h_rhs : (List.range (n' + 1)).foldl
        (fun acc t => acc ++ (s!"tick {a + t}" :: g t)) init =
        (List.range n').foldl
          (fun acc t => acc ++ (s!"tick {a + t}" :: g t)) init ++
        (s!"tick {a + n'}" :: g n') := by
      rw [List.range_succ, List.foldl_append, List.foldl_cons,
        List.foldl_nil]
    rw [ih init (fun t h_t => h t (by omega)), h n' (by omega),
      ← h_rhs, List.range_succ]

/-- The `n`-tick foldl appends one block per tick. Block `t` starts
    with `s!"tick {w.tick + t}"`; its tail holds chain entries. The
    foldl keeps both invariants. -/
theorem gSimFoldl_log_shape (actTick : Nat → Nat) (obsAll : List (List Nat))
    (groupOrd : List Nat) (withinOrd pos : Nat → List Nat) (w : World)
    (n : Nat) (hO : OutputNamesOk w) (hS : SigLevelsOk w) :
    ∃ chainAt : Nat → List String,
      (gSimFoldl actTick obsAll groupOrd withinOrd pos w n).outputLog =
        logBlocks w.outputLog w.tick chainAt n ∧
      (∀ t < n, ∀ s ∈ chainAt t, IsChainEntry s) ∧
      OutputNamesOk (gSimFoldl actTick obsAll groupOrd withinOrd pos w n) ∧
      SigLevelsOk (gSimFoldl actTick obsAll groupOrd withinOrd pos w n) := by
  induction n generalizing w with
  | zero =>
    refine ⟨fun _ => [], ?_, ?_, hO, hS⟩
    · dsimp [gSimFoldl, logBlocks, List.range]
    · intro t h_t
      omega
  | succ n' ih =>
    simp only [gSimFoldl, List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil]
    set W := (List.range n').foldl
      (gSimBody actTick obsAll groupOrd withinOrd pos) w
    obtain ⟨chainAt', h_log', h_chain', hO', hS'⟩ := ih w hO hS
    obtain ⟨rest, h_rest_log, h_rest_chain, hO'', hS''⟩ :=
      LogAppendChain_gSimBody actTick obsAll groupOrd withinOrd pos W n' hO' hS'
    have h_W_tick : W.tick = w.tick + n' := by
      dsimp [W]
      exact gSimFoldl_tick actTick obsAll groupOrd withinOrd pos w n'
    refine ⟨fun t => if t = n' then rest else chainAt' t, ?_, ?_, hO'', hS''⟩
    · rw [h_rest_log]
      change (gSimFoldl actTick obsAll groupOrd withinOrd pos w n').outputLog ++
        (s!"tick {W.tick}" :: rest) =
        logBlocks w.outputLog w.tick
          (fun t => if t = n' then rest else chainAt' t) (n' + 1)
      rw [h_log', h_W_tick]
      dsimp [logBlocks]
      rw [List.range_succ, List.foldl_append, List.foldl_cons,
        List.foldl_nil]
      rw [foldl_blocks_congr w.outputLog w.tick n'
        (fun t => if t = n' then rest else chainAt' t) chainAt' (fun t h_t => by
          have h_ne : t ≠ n' := by omega
          simp [h_ne])]
      simp only [ite_true]
    · intro t h_t
      dsimp only
      split_ifs with h_eq
      · subst h_eq
        exact h_rest_chain
      · exact h_chain' t (by omega)

/-- Deliverable 1. The log of `groupSimulate T` is a sequence of
    `T + 1` blocks. Block `t` starts with the tick entry
    `s!"tick {t}"`; the rest of the block holds chain entries. The
    block tails come from the burst phase and the drain of tick `t`,
    i.e. from the `logOutput` calls of the output nodes. -/
theorem groupSimulate_log_shape (T : Nat) (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) :
    ∃ chainAt : Nat → List String,
      groupSimulate T groups actTick groupOrd withinOrd pos =
        logBlocks [] 0 chainAt (T + 1) ∧
      ∀ t ≤ T, ∀ s ∈ chainAt t, IsChainEntry s := by
  dsimp [groupSimulate]
  set w₀ := (buildGroups groups).1
  set obsAll := (buildGroups groups).2
  obtain ⟨chainAt, h_shape, h_chain, _, _⟩ := gSimFoldl_log_shape actTick
    obsAll groupOrd withinOrd pos w₀ (T + 1)
    (buildGroups_OutputNamesOk groups) (buildGroups_SigLevelsOk groups)
  refine ⟨chainAt, ?_, ?_⟩
  · have h_log₀ : w₀.outputLog = [] := buildGroups_outputLog groups
    have h_tick₀ : w₀.tick = 0 := buildGroups_tick groups
    rw [h_shape, h_log₀, h_tick₀]
  · intro t h_t
    exact h_chain t (by omega)

/-- The tick entry of each tick up to `T` sits in the log. -/
theorem groupSimulate_tick_entry_mem (T : Nat) (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (t : Nat) (h_t : t ≤ T) :
    s!"tick {t}" ∈ groupSimulate T groups actTick groupOrd withinOrd pos := by
  obtain ⟨chainAt, h_shape, _⟩ :=
    groupSimulate_log_shape T groups actTick groupOrd withinOrd pos
  rw [h_shape]
  have h_mem := mem_logBlocks_tick 0 t (T + 1) chainAt (by omega)
  simpa using h_mem

/-- Every entry of the log is a tick entry of a tick up to `T` or a
    chain entry. -/
theorem groupSimulate_entry_cases (T : Nat) (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (s : String)
    (h_mem : s ∈ groupSimulate T groups actTick groupOrd withinOrd pos) :
    (∃ t ≤ T, s = s!"tick {t}") ∨ IsChainEntry s := by
  obtain ⟨chainAt, h_shape, h_chain⟩ :=
    groupSimulate_log_shape T groups actTick groupOrd withinOrd pos
  rw [h_shape] at h_mem
  obtain h_tick | h_chain_mem := mem_logBlocks_cases 0 (T + 1) chainAt s h_mem
  · left
    obtain ⟨t, h_t, h_eq⟩ := h_tick
    refine ⟨t, by omega, ?_⟩
    simpa using h_eq
  · right
    obtain ⟨t, h_t, h_mem_t⟩ := h_chain_mem
    exact h_chain t (by omega) s h_mem_t

/-! ## The log split when nothing logs before tick `T` -/

/-- A foldl of blocks whose tails are all empty but the last is the
    tick block followed by the last tail. -/
private theorem logBlocks_split (T : Nat) (chainAt : Nat → List String)
    (h_no_early : ∀ t < T, chainAt t = []) :
    logBlocks [] 0 chainAt (T + 1) =
      ((List.range (T + 1)).map (fun t => s!"tick {t}")) ++ chainAt T := by
  dsimp [logBlocks]
  induction T with
  | zero =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil]
    dsimp [List.range]
  | succ T ih =>
    have h_early : ∀ t < T, chainAt t = [] := fun t h_t =>
      h_no_early t (by omega)
    have h_T : chainAt T = [] := h_no_early T (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil, ih h_early, h_T]
    simp [List.range_succ, List.map_append, List.append_assoc]

/-- The log split. When every block before `T` has an empty tail, the
    log is the tick block followed by the chain entries of tick `T`.
    This discharges the `h_log`, `h_ticks_len` and `h_ticks` premises
    of FinalPopIndex's `outputPos_eq_index_of_chain_entry`. -/
theorem groupSimulate_log_split (T : Nat) (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (chainAt : Nat → List String)
    (h_shape : groupSimulate T groups actTick groupOrd withinOrd pos =
        logBlocks [] 0 chainAt (T + 1))
    (h_no_early : ∀ t < T, chainAt t = []) :
    let ticks := (List.range (T + 1)).map (fun t => s!"tick {t}")
    groupSimulate T groups actTick groupOrd withinOrd pos =
      ticks ++ chainAt T ∧
    ticks.length = T + 1 ∧
    ∀ s ∈ ticks, IsTickEntry s := by
  intro ticks
  refine ⟨?_, ?_, ?_⟩
  · rw [h_shape, logBlocks_split T chainAt h_no_early]
  · dsimp [ticks]
    rw [List.length_map, List.length_range]
  · intro s h_s
    dsimp [ticks] at h_s
    obtain ⟨t, _, h_t⟩ := List.mem_map.mp h_s
    subst h_t
    exact ⟨t, rfl⟩

/-! ## Deliverable 2 — the drain appends one entry per final pop -/

/-- `SigLevelsOk` carries through one step. -/
private theorem SigLevelsOk_step_keep (w w' : World)
    (h_step : w.step = some w') (hS : SigLevelsOk w) : SigLevelsOk w' := by
  dsimp [World.step] at h_step
  cases h_pop : w.popNextEvent with
  | none =>
    simp only [h_pop] at h_step
    cases h_step
  | some p =>
    rcases p with ⟨ev, w_pop⟩
    simp only [h_pop] at h_step
    injection h_step with h_w'
    rw [← h_w']
    exact SigLevelsOk_onScheduledTick_keep w_pop ev.nodeId
      (by
        intro nid nd h_gn
        dsimp [World.getNode] at h_gn ⊢
        rw [World.popNextEvent_nodes w ev w_pop h_pop] at h_gn
        exact hS nid nd h_gn)

/-- Firing a node keeps the due-event count at the current tick: the
    spawned events target future ticks. -/
private theorem onScheduledTick_count_keep (w : World) (id : Nat) :
    World.countEventAtThisTick (w.onScheduledTick id) w.tick =
    World.countEventAtThisTick w w.tick := by
  obtain ⟨new, h_app, h_fut⟩ := World.onScheduledTick_appends_future w id
  dsimp [World.countEventAtThisTick]
  rw [h_app, List.filter_append]
  have h_nil : new.filter (fun ev => ev.targetTick == w.tick) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro ev h_ev
    have h_ne : ev.targetTick ≠ w.tick := by
      have h_gt := h_fut ev h_ev
      omega
    intro h_be
    apply h_ne
    simpa using h_be
  simp [h_nil]

/-- The drain of one tick appends one log entry per popped event, in
    pop order. The events popped within the tick are the list
    `finals`. Firing a popped event appends the entry `entryOf ev`. -/
theorem chainEntries_are_finalPops (groups : List GroupSpec) (w : World)
    (h_layout : NodeLayoutOk groups w) (hS : SigLevelsOk w)
    (finals : List ScheduledEvent) (h_nd : finals.Nodup)
    (chainOf : ScheduledEvent → Nat × Nat)
    (h_pop_seq : World.popSeqFuel w (World.countEventAtThisTick w w.tick) = finals)
    (h_fire : ∀ ev ∈ finals, ∀ (v : World), v.tick = w.tick →
        NodeLayoutOk groups v → SigLevelsOk v →
        ∃ s, (v.onScheduledTick ev.nodeId).outputLog = v.outputLog ++ [s] ∧
          isOutputEntry s (chainOf ev).1 (chainOf ev).2 = true) :
    ∃ (entries : List String) (entryOf : ScheduledEvent → String),
      w.stepUntilNextTick.outputLog = w.outputLog ++ entries ∧
      entries = finals.map entryOf ∧
      ∀ ev ∈ finals,
        isOutputEntry (entryOf ev) (chainOf ev).1 (chainOf ev).2 = true := by
  revert h_layout hS h_nd h_pop_seq h_fire finals
  induction w using World.stepUntilNextTick.induct with
  | case1 x h_step =>
    intro h_layout hS finals h_nd h_pop_seq h_fire
    have h_pop_none : x.popNextEvent = none := by
      dsimp [World.step] at h_step
      cases h_pop : x.popNextEvent with
      | none => rfl
      | some p =>
        simp only [h_pop] at h_step
        cases h_step
    have h_no_due : ∀ ev ∈ x.events, ev.targetTick ≠ x.tick :=
      popNextEvent_none_no_events x h_pop_none
    have h_finals_nil : finals = [] := by
      rw [← h_pop_seq]
      exact World.popSeqFuel_of_no_due x (World.countEventAtThisTick x x.tick)
        h_no_due
    rw [stepUntilNextTick_of_step_none x h_step]
    refine ⟨[], fun _ => "", ?_, ?_, ?_⟩
    · simp [List.append_nil]
    · simp [h_finals_nil]
    · intro ev h_ev
      rw [h_finals_nil] at h_ev
      cases h_ev
  | case2 x w' h_step ih =>
    intro h_layout hS finals h_nd h_pop_seq h_fire
    have h_sunt : x.stepUntilNextTick = w'.stepUntilNextTick := by
      rw [World.stepUntilNextTick, h_step]
    dsimp [World.step] at h_step
    cases h_pop : x.popNextEvent with
    | none =>
      simp only [h_pop] at h_step
      cases h_step
    | some p =>
      rcases p with ⟨ev₀, w_pop⟩
      simp only [h_pop] at h_step
      injection h_step with h_w'
      have h_step' : x.step = some w' := by
        simp only [World.step, h_pop, h_w']
      have h_tick_w' : w'.tick = x.tick := by
        rw [← h_w', World.onScheduledTick_tick,
          World.popNextEvent_tick x ev₀ w_pop h_pop]
      have h_tick_pop : w_pop.tick = x.tick :=
        World.popNextEvent_tick x ev₀ w_pop h_pop
      have h_nodes_pop : w_pop.nodes = x.nodes :=
        World.popNextEvent_nodes x ev₀ w_pop h_pop
      -- the due count drops by one: the pop removes one due event and
      -- firing spawns future events only
      have h_count : World.countEventAtThisTick x x.tick =
          World.countEventAtThisTick w' w'.tick + 1 := by
        have h_w'_tick : w'.tick = x.tick := by
          rw [← h_w', World.onScheduledTick_tick, h_tick_pop]
        rw [h_w'_tick]
        have h_dec :=
          (World.popNextEvent_remove_one_current_tick_event_if_some
            x ev₀ w_pop h_pop).2
        have h_keep := onScheduledTick_count_keep w_pop ev₀.nodeId
        rw [h_w', h_tick_pop] at h_keep
        have h_pos : World.countEventAtThisTick x x.tick > 0 := by
          obtain ⟨idx, h_idx, _, h_due, _, h_get⟩ :=
            World.popNextEvent_eraseIdx x ev₀ w_pop h_pop
          dsimp [World.countEventAtThisTick]
          have h_mem : ev₀ ∈
              x.events.filter (fun e => e.targetTick == x.tick) := by
            rw [List.mem_filter]
            exact ⟨by rw [← h_get]; exact List.getElem_mem h_idx,
              by simp [h_due]⟩
          exact List.length_pos_of_mem h_mem
        omega
      cases finals with
      | nil =>
        -- the pop sequence is non-empty, contradiction
        rw [h_count] at h_pop_seq
        dsimp only [World.popSeqFuel] at h_pop_seq
        simp only [h_pop] at h_pop_seq
        cases h_pop_seq
      | cons f fs =>
        rw [h_count] at h_pop_seq
        dsimp only [World.popSeqFuel] at h_pop_seq
        simp only [h_pop] at h_pop_seq
        rw [h_w'] at h_pop_seq
        injection h_pop_seq with h_f h_fs
        subst h_f
        -- layout and signal health carry to the popped world and to w'
        have h_get : ∀ nid, w_pop.getNode nid = x.getNode nid := by
          intro nid
          dsimp [World.getNode]
          rw [h_nodes_pop]
        have h_layout_pop : NodeLayoutOk groups w_pop := by
          rcases h_layout with ⟨hOb, hM, hL, hOut⟩
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro gi ci h_gi h_ci
            obtain ⟨nd, h_gn, hk, ho⟩ := hOb gi ci h_gi h_ci
            exact ⟨nd, by rw [h_get]; exact h_gn, hk, ho⟩
          · intro gi ci k h_gi h_ci h_k
            obtain ⟨nd, h_gn, hk, ho⟩ := hM gi ci k h_gi h_ci h_k
            exact ⟨nd, by rw [h_get]; exact h_gn, hk, ho⟩
          · intro gi ci h_gi h_ci
            obtain ⟨nd, h_gn, hk, ho⟩ := hL gi ci h_gi h_ci
            exact ⟨nd, by rw [h_get]; exact h_gn, hk, ho⟩
          · intro gi ci h_gi h_ci
            obtain ⟨nd, h_gn, hk, ho⟩ := hOut gi ci h_gi h_ci
            exact ⟨nd, by rw [h_get]; exact h_gn, hk, ho⟩
        have hS_pop : SigLevelsOk w_pop := by
          intro nid nd h_gn
          dsimp [World.getNode] at h_gn
          rw [h_nodes_pop] at h_gn
          exact hS nid nd h_gn
        obtain ⟨h_layout_w', hS_w'⟩ :
            NodeLayoutOk groups w' ∧ SigLevelsOk w' :=
          ⟨NodeLayoutOk_step groups x w' h_step' h_layout,
            SigLevelsOk_step_keep x w' h_step' hS⟩
        have h_nd_fs : fs.Nodup := (List.nodup_cons.mp h_nd).2
        have h_ev₀_nin : ev₀ ∉ fs := (List.nodup_cons.mp h_nd).1
        obtain ⟨entries', entryOf', h_log', h_map', h_match'⟩ :=
          ih h_layout_w' hS_w' fs h_nd_fs h_fs
            (fun ev h_ev v h_vtick h_lay h_sig =>
              h_fire ev (List.mem_cons.mpr (Or.inr h_ev)) v
                (h_vtick.trans h_tick_w') h_lay h_sig)
        obtain ⟨s₀, h_s₀_log, h_s₀_match⟩ := h_fire ev₀
          (List.mem_cons.mpr (Or.inl rfl)) w_pop h_tick_pop
          h_layout_pop hS_pop
        set entryOf : ScheduledEvent → String :=
          fun e => if e = ev₀ then s₀ else entryOf' e
        have h_entryOf_ev₀ : entryOf ev₀ = s₀ := by
          dsimp [entryOf]
          simp
        have h_map_fs : fs.map entryOf = fs.map entryOf' :=
          List.map_congr' fs (fun e h_e => by
            dsimp [entryOf]
            have h_ne : e ≠ ev₀ := fun h_eq => h_ev₀_nin (h_eq ▸ h_e)
            simp [h_ne])
        refine ⟨s₀ :: entries', entryOf, ?_, ?_, ?_⟩
        · rw [h_sunt, h_log', ← h_w', h_s₀_log,
            World.popNextEvent_outputLog x ev₀ w_pop h_pop]
          rw [List.append_assoc]
          rfl
        · change s₀ :: entries' = entryOf ev₀ :: fs.map entryOf
          rw [h_entryOf_ev₀, h_map_fs, ← h_map']
        · intro ev h_ev
          rw [List.mem_cons] at h_ev
          rcases h_ev with rfl | h_ev
          · rw [h_entryOf_ev₀]
            exact h_s₀_match
          · have h_ne : ev ≠ ev₀ := fun h_eq => h_ev₀_nin (h_eq ▸ h_ev)
            dsimp [entryOf]
            simp [h_ne]
            exact h_match' ev h_ev

/-- The decimal representation of 0. -/
private theorem repr_zero_eq : (0 : Nat).repr = "0" := by decide

/-- The decimal representation of 15. -/
private theorem repr_fifteen_eq : (15 : Nat).repr = "15" := by decide

/-- The interpolated zero entry equals the literal zero entry. -/
private theorem chainEntry_zero_form (nm : String) :
    (s!"{nm}: {(0 : Nat)}" : String) = s!"{nm}: 0" := by
  show nm ++ ": " ++ (0 : Nat).repr = nm ++ ": 0"
  rw [repr_zero_eq, String.append_assoc]
  exact congrArg (fun t => nm ++ t)
    (by decide : (": " : String) ++ "0" = ": 0")

/-- The interpolated fifteen entry equals the literal fifteen entry. -/
private theorem chainEntry_fifteen_form (nm : String) :
    (s!"{nm}: {(15 : Nat)}" : String) = s!"{nm}: 15" := by
  show nm ++ ": " ++ (15 : Nat).repr = nm ++ ": 15"
  rw [repr_fifteen_eq, String.append_assoc]
  exact congrArg (fun t => nm ++ t)
    (by decide : (": " : String) ++ "15" = ": 15")

/-- Firing the final event of chain `(gi, ci)` appends exactly one
    entry, and that entry matches `isOutputEntry` for the chain. -/
theorem finalEvent_fire_isOutputEntry (groups : List GroupSpec)
    (actTick : Nat → Nat) (gi ci : Nat)
    (h_gi : gi < groups.length) (h_ci : ci < (groupAt groups gi).length) :
    let e := stageEvent actTick groups gi ci
      ((chainAt groups gi ci).middleDelays.length + 1)
    ∀ (v : World), NodeLayoutOk groups v → SigLevelsOk v →
      ∃ s, (v.onScheduledTick e.nodeId).outputLog = v.outputLog ++ [s] ∧
        isOutputEntry s gi ci = true := by
  intro e v h_layout h_sig
  set m := (chainAt groups gi ci).middleDelays.length
  set lastRep := chainBaseId groups gi ci + m + 2
  set out := chainBaseId groups gi ci + m + 3
  obtain ⟨nd_rep, h_rep, h_kind_rep, h_outs_rep⟩ :=
    h_layout.2.2.1 gi ci h_gi h_ci
  obtain ⟨nd_out, h_out, h_kind_out, _⟩ :=
    h_layout.2.2.2 gi ci h_gi h_ci
  have h_nodeId : e.nodeId = lastRep := by
    dsimp [e, lastRep, stageEvent]
    omega
  set f : NodeData → NodeData := fun nd' =>
    ({ nd' with
        sigLevel := if v.getInputSignal lastRep > 0 then 15 else 0 } :
      NodeData)
  set lvl : Nat := (v.updateNode lastRep f).getInputSignal out
  have h_ne : lastRep ≠ out := by
    dsimp [lastRep, out]
    omega
  -- firing the last repeater reduces to one `logOutput` call
  have h_red : v.onScheduledTick lastRep =
      (v.updateNode lastRep f).logOutput s!"{chainName gi ci}: {lvl}" := by
    dsimp [World.onScheduledTick, f, lvl]
    rw [h_rep]
    simp only
    rw [h_kind_rep]
    dsimp [World.notifyOutputs]
    rw [World.updateNode_getNode_eq v lastRep f nd_rep h_rep]
    simp only
    rw [h_outs_rep]
    simp only [List.foldl_cons, List.foldl_nil]
    dsimp [World.onNeighborUpdate]
    rw [World.updateNode_getNode_ne v lastRep out f h_ne, h_out]
    simp only
    rw [h_kind_out]
  have h_log : (v.onScheduledTick e.nodeId).outputLog =
      v.outputLog ++ [s!"{chainName gi ci}: {lvl}"] := by
    rw [h_nodeId, h_red]
    dsimp [World.logOutput, World.updateNode]
  have h_sig' : SigLevelsOk (v.updateNode lastRep f) :=
    SigLevelsOk_updateNode_keep v lastRep f (fun nd' => by
      show (if v.getInputSignal lastRep > 0 then 15 else 0) = 0 ∨
        (if v.getInputSignal lastRep > 0 then 15 else 0) = 15
      split_ifs with h_c
      · right; rfl
      · left; rfl) h_sig
  have h_lvl : lvl = 0 ∨ lvl = 15 :=
    getInputSignal_zero_or_fifteen (v.updateNode lastRep f) out h_sig'
  refine ⟨s!"{chainName gi ci}: {lvl}", h_log, ?_⟩
  rcases h_lvl with h_lvl | h_lvl
  · rw [h_lvl, chainEntry_zero_form (chainName gi ci)]
    exact (chain_entry_isOutputEntry_true gi ci).1
  · rw [h_lvl, chainEntry_fifteen_form (chainName gi ci)]
    exact (chain_entry_isOutputEntry_true gi ci).2

/-! ## Deliverables 3 and 4 — discharge of FinalPopIndex's theorems -/

/-- The head element of a duplicate-free split does not sit in the
    prefix. -/
private theorem nodup_not_mem_pre {α : Type} (l pre post : List α) (a : α)
    (h_nd : l.Nodup) (h_split : l = pre ++ a :: post) : a ∉ pre := by
  rw [h_split] at h_nd
  clear h_split l
  revert post h_nd
  induction pre with
  | nil =>
    intro post h_nd h_mem
    cases h_mem
  | cons b pre ih =>
    intro post h_nd h_mem
    rw [List.cons_append] at h_nd
    rw [List.nodup_cons] at h_nd
    rw [List.mem_cons] at h_mem
    rcases h_mem with h_b | h_mem
    · subst h_b
      exact h_nd.1
        (List.mem_append_right pre (List.mem_cons.mpr (Or.inl rfl)))
    · exact ih post h_nd.2 h_mem

/-- Deliverable 3. The log of `groupSimulate T` has the block shape and
    no block before `T` holds chain entries. The chain block of tick
    `T` is the log of the final pops, and the final event of chain
    `(gi, ci)` sits in the final-pop list after `pre`. Then
    `outputPos` returns `T + 1 + pre.length`. -/
theorem outputPos_eq_finalPopIndex_discharged (T : Nat)
    (groups : List GroupSpec) (actTick : Nat → Nat)
    (groupOrd : List Nat) (withinOrd pos : Nat → List Nat) (gi ci : Nat)
    (h_gi : gi < groups.length) (h_ci : ci < (groupAt groups gi).length)
    (chainAt : Nat → List String)
    (h_shape : groupSimulate T groups actTick groupOrd withinOrd pos =
        logBlocks [] 0 chainAt (T + 1))
    (h_no_early : ∀ t < T, chainAt t = [])
    (finals : List ScheduledEvent) (h_nd : finals.Nodup)
    (chainOf : ScheduledEvent → Nat × Nat)
    (finalEventOf : Nat → Nat → ScheduledEvent)
    (entryOf : ScheduledEvent → String)
    (h_block : chainAt T = finals.map entryOf)
    (h_entry_match : ∀ ev ∈ finals,
        isOutputEntry (entryOf ev) (chainOf ev).1 (chainOf ev).2 = true)
    (h_final_of_chainOf : ∀ ev ∈ finals,
        ev = finalEventOf (chainOf ev).1 (chainOf ev).2)
    (h_chainOf_final : ∀ gi' ci', gi' < groups.length →
        ci' < (groupAt groups gi').length → finalEventOf gi' ci' ∈ finals →
        chainOf (finalEventOf gi' ci') = (gi', ci'))
    (pre post : List ScheduledEvent)
    (h_split : finals = pre ++ finalEventOf gi ci :: post) :
    outputPos (groupSimulate T groups actTick groupOrd withinOrd pos) gi ci =
      some (T + 1 + pre.length) := by
  -- FinalPopIndex's log shape premises
  set log := groupSimulate T groups actTick groupOrd withinOrd pos
  set ticks := (List.range (T + 1)).map (fun t => s!"tick {t}")
  obtain ⟨h_log, h_ticks_len, h_ticks⟩ :=
    groupSimulate_log_split T groups actTick groupOrd withinOrd pos chainAt
      h_shape h_no_early
  -- the chain block splits at the chain's final event
  set pre_c := pre.map entryOf
  set x := entryOf (finalEventOf gi ci)
  set post_c := post.map entryOf
  have h_chain_split : chainAt T = pre_c ++ x :: post_c := by
    dsimp [pre_c, x, post_c]
    rw [h_block, h_split, List.map_append, List.map_cons]
  have h_mem_final : finalEventOf gi ci ∈ finals := by
    rw [h_split]
    exact List.mem_append_right pre (List.mem_cons.mpr (Or.inl rfl))
  have h_match : isOutputEntry x gi ci = true := by
    dsimp [x]
    have h_own := h_entry_match (finalEventOf gi ci) h_mem_final
    have h_pair := h_chainOf_final gi ci h_gi h_ci h_mem_final
    rwa [h_pair] at h_own
  have h_first_c : ∀ y ∈ pre_c, isOutputEntry y gi ci = false := by
    intro y h_y
    dsimp [pre_c] at h_y
    obtain ⟨ev, h_ev_pre, h_y_eq⟩ := List.mem_map.mp h_y
    have h_ev_fin : ev ∈ finals := by
      rw [h_split]
      exact List.mem_append_left (finalEventOf gi ci :: post) h_ev_pre
    have h_own := h_entry_match ev h_ev_fin
    cases h_contra : isOutputEntry y gi ci with
    | false => rfl
    | true =>
      exfalso
      rw [← h_y_eq] at h_contra
      obtain ⟨h_g, h_c⟩ := isOutputEntry_chain_inj (entryOf ev)
        (chainOf ev).1 (chainOf ev).2 gi ci h_own h_contra
      have h_ev_final : ev = finalEventOf gi ci := by
        have h_ev_eq := h_final_of_chainOf ev h_ev_fin
        rw [h_ev_eq, h_g, h_c]
      have h_not_mem : finalEventOf gi ci ∉ pre :=
        nodup_not_mem_pre finals pre post (finalEventOf gi ci) h_nd h_split
      exact h_not_mem (h_ev_final ▸ h_ev_pre)
  have h_result := outputPos_eq_index_of_chain_entry log T gi ci ticks
    (chainAt T) h_log h_ticks_len h_ticks pre_c x post_c h_chain_split
    h_match h_first_c
  dsimp [pre_c] at h_result
  rw [List.length_map] at h_result
  exact h_result

/-- Deliverable 4. The log shape and the final-pop structure discharge
    the premises of FinalPopIndex's bridge. `groupBeforeSpec` on the
    `groupSimulate` log is equivalent to `evBefore` on the final
    events of same-spec chains of the two groups. The order bridge
    only needs the final events of the two compared groups, so the
    split premise is bounded to valid chains. -/
theorem groupBeforeSpec_iff_evBefore_discharged (T : Nat)
    (groups : List GroupSpec) (actTick : Nat → Nat)
    (groupOrd : List Nat) (withinOrd pos : Nat → List Nat)
    (ga gb : Nat) (s : ChainSpec)
    (h_ga : ga < groups.length) (h_gb : gb < groups.length)
    (chainAt : Nat → List String)
    (h_shape : groupSimulate T groups actTick groupOrd withinOrd pos =
        logBlocks [] 0 chainAt (T + 1))
    (h_no_early : ∀ t < T, chainAt t = [])
    (finals : List ScheduledEvent) (h_nd : finals.Nodup)
    (chainOf : ScheduledEvent → Nat × Nat)
    (finalEventOf : Nat → Nat → ScheduledEvent)
    (finalIdx : Nat → Nat → Nat)
    (entryOf : ScheduledEvent → String)
    (h_block : chainAt T = finals.map entryOf)
    (h_entry_match : ∀ ev ∈ finals,
        isOutputEntry (entryOf ev) (chainOf ev).1 (chainOf ev).2 = true)
    (h_final_of_chainOf : ∀ ev ∈ finals,
        ev = finalEventOf (chainOf ev).1 (chainOf ev).2)
    (h_chainOf_final : ∀ gi' ci', gi' < groups.length →
        ci' < (groupAt groups gi').length → finalEventOf gi' ci' ∈ finals →
        chainOf (finalEventOf gi' ci') = (gi', ci'))
    (h_pos : ∀ gi' ci', gi' < groups.length →
        ci' < (groupAt groups gi').length →
        ∃ pre post, finals = pre ++ finalEventOf gi' ci' :: post ∧
          pre.length = finalIdx gi' ci') :
    groupBeforeSpec
      (groupSimulate T groups actTick groupOrd withinOrd pos) groups ga gb
      s ↔
    ∀ ca cb, ca < (groupAt groups ga).length →
      cb < (groupAt groups gb).length →
      _root_.chainAt groups ga ca = s → _root_.chainAt groups gb cb = s →
      evBefore finals (finalEventOf ga ca) (finalEventOf gb cb) := by
  set log := groupSimulate T groups actTick groupOrd withinOrd pos
  -- outputPos of each valid chain of the two groups
  have h_outPos : ∀ gi' ci', gi' < groups.length →
      ci' < (groupAt groups gi').length →
      outputPos log gi' ci' = some (T + 1 + finalIdx gi' ci') := by
    intro gi' ci' h_gi' h_ci'
    obtain ⟨pre, post, h_split, h_len⟩ := h_pos gi' ci' h_gi' h_ci'
    have h := outputPos_eq_finalPopIndex_discharged T groups actTick
      groupOrd withinOrd pos gi' ci' h_gi' h_ci' chainAt h_shape h_no_early
      finals h_nd chainOf finalEventOf entryOf h_block h_entry_match
      h_final_of_chainOf h_chainOf_final pre post h_split
    rw [h_len] at h
    exact h
  -- the index order is the evBefore order of the final events
  have h_bridge : ∀ ca cb, ca < (groupAt groups ga).length →
      cb < (groupAt groups gb).length →
      (finalIdx ga ca < finalIdx gb cb ↔
        evBefore finals (finalEventOf ga ca) (finalEventOf gb cb)) := by
    intro ca cb h_ca h_cb
    obtain ⟨pre_a, post_a, h_split_a, h_len_a⟩ := h_pos ga ca h_ga h_ca
    obtain ⟨pre_b, post_b, h_split_b, h_len_b⟩ := h_pos gb cb h_gb h_cb
    exact chain_entries_are_final_pops finals h_nd finalEventOf finalIdx
      ga ca gb cb ⟨pre_a, post_a, h_split_a, h_len_a⟩
      ⟨pre_b, post_b, h_split_b, h_len_b⟩
  constructor
  · intro h_spec ca cb h_ca h_cb h_sa h_sb
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
    have h_idx : finalIdx ga ca < finalIdx gb cb := by omega
    exact (h_bridge ca cb h_ca h_cb).mp h_idx
  · intro h_ev ca cb h_ca h_cb h_sa h_sb
    refine ⟨T + 1 + finalIdx ga ca, T + 1 + finalIdx gb cb, ?_, ?_, ?_⟩
    · exact h_outPos ga ca h_ga h_ca
    · exact h_outPos gb cb h_gb h_cb
    · have h_idx : finalIdx ga ca < finalIdx gb cb :=
        (h_bridge ca cb h_ca h_cb).mpr (h_ev ca cb h_ca h_cb h_sa h_sb)
      omega

/-! ## Prefix log shape, block injectivity and the empty-early-blocks fact

Additions for the capstone (used by NoEarlyChainEntries):

* `gSimFoldl_log_shape_prefix` — the block shape of
  `gSimFoldl_log_shape` strengthened to every prefix of the foldl;
* `logBlocks_chainAt_eq_of_log_eq` — two block decompositions of the
  same log agree on every block when the second decomposition holds
  chain entries only (a tick entry never equals a chain entry, so the
  tick entries delimit the blocks);
* `mem_logBlocks_chain` — an entry of block `t` sits in the block
  fold;
* `logBlocks_zero_eq_foldl` — the `start = 0` block fold written with
  `s!"tick {t}"` instead of `s!"tick {0 + t}"`.
-/

/-- One more block: the fold over `range (n + 1)` appends the block of
    tick `start + n`. -/
private theorem logBlocks_succ_last (start n : Nat) (init : List String)
    (chainAt : Nat → List String) :
    logBlocks init start chainAt (n + 1) =
      logBlocks init start chainAt n ++
        (s!"tick {start + n}" :: chainAt n) := by
  dsimp [logBlocks]
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- With start `0`, the block fold writes the tick entry
    `s!"tick {t}"`. -/
theorem logBlocks_zero_eq_foldl (chainAt : Nat → List String) (n : Nat) :
    logBlocks [] 0 chainAt n =
      (List.range n).foldl
        (fun acc t => acc ++ (s!"tick {t}" :: chainAt t)) [] := by
  dsimp [logBlocks]
  suffices h : ∀ init : List String,
      (List.range n).foldl
        (fun acc t => acc ++ (s!"tick {0 + t}" :: chainAt t)) init =
      (List.range n).foldl
        (fun acc t => acc ++ (s!"tick {t}" :: chainAt t)) init from by
    exact h []
  intro init
  induction n generalizing init with
  | zero => rfl
  | succ n' ih =>
    have h₁ : (List.range (n' + 1)).foldl
        (fun acc t => acc ++ (s!"tick {0 + t}" :: chainAt t)) init =
        (List.range n').foldl
          (fun acc t => acc ++ (s!"tick {0 + t}" :: chainAt t)) init ++
        (s!"tick {0 + n'}" :: chainAt n') := by
      rw [List.range_succ, List.foldl_append, List.foldl_cons,
        List.foldl_nil]
    have h₂ : (List.range (n' + 1)).foldl
        (fun acc t => acc ++ (s!"tick {t}" :: chainAt t)) init =
        (List.range n').foldl
          (fun acc t => acc ++ (s!"tick {t}" :: chainAt t)) init ++
        (s!"tick {n'}" :: chainAt n') := by
      rw [List.range_succ, List.foldl_append, List.foldl_cons,
        List.foldl_nil]
    rw [h₁, h₂, ih]
    simp

/-- An entry of block `t` sits in the block fold over `range n`. -/
theorem mem_logBlocks_chain (start t n : Nat) (s : String)
    (chainAt : Nat → List String) (h_mem : s ∈ chainAt t) (h_t : t < n) :
    s ∈ logBlocks [] start chainAt n := by
  induction n generalizing t with
  | zero => omega
  | succ n' ih =>
    rw [logBlocks_succ_last start n' [] chainAt]
    by_cases h : t < n'
    · apply List.mem_append_left
      exact ih t h_mem h
    · have h_eq : t = n' := by omega
      subst h_eq
      apply List.mem_append_right
      exact List.mem_cons.mpr (Or.inr h_mem)

/-- The `n`-tick foldl appends one block per tick, at every prefix: for
    every `n' ≤ n`, the log of `gSimFoldl ... n'` is the block fold over
    `range n'` with one common `chainAt`. The tails hold chain entries.
    The foldl keeps both invariants. -/
theorem gSimFoldl_log_shape_prefix (actTick : Nat → Nat)
    (obsAll : List (List Nat)) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (w : World) (n : Nat)
    (hO : OutputNamesOk w) (hS : SigLevelsOk w) :
    ∃ chainAt : Nat → List String,
      (∀ n' ≤ n, (gSimFoldl actTick obsAll groupOrd withinOrd pos w n').outputLog =
          logBlocks w.outputLog w.tick chainAt n') ∧
      (∀ t < n, ∀ s ∈ chainAt t, IsChainEntry s) ∧
      OutputNamesOk (gSimFoldl actTick obsAll groupOrd withinOrd pos w n) ∧
      SigLevelsOk (gSimFoldl actTick obsAll groupOrd withinOrd pos w n) := by
  induction n generalizing w with
  | zero =>
    refine ⟨fun _ => [], ?_, ?_, hO, hS⟩
    · intro n' h_le
      have h_n' : n' = 0 := by omega
      subst h_n'
      dsimp [gSimFoldl, logBlocks, List.range]
    · intro t h_t
      omega
  | succ n' ih =>
    simp only [gSimFoldl, List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil]
    set W := (List.range n').foldl
      (gSimBody actTick obsAll groupOrd withinOrd pos) w
    obtain ⟨chainAt', h_prefix', h_chain', hO', hS'⟩ := ih w hO hS
    obtain ⟨rest, h_rest_log, h_rest_chain, hO'', hS''⟩ :=
      LogAppendChain_gSimBody actTick obsAll groupOrd withinOrd pos W n' hO' hS'
    have h_W_tick : W.tick = w.tick + n' := by
      dsimp [W]
      exact gSimFoldl_tick actTick obsAll groupOrd withinOrd pos w n'
    refine ⟨fun t => if t = n' then rest else chainAt' t, ?_, ?_, hO'', hS''⟩
    · intro n'' h_le
      by_cases h_last : n'' = n' + 1
      · subst h_last
        change (gSimFoldl actTick obsAll groupOrd withinOrd pos w (n' + 1)).outputLog =
          logBlocks w.outputLog w.tick
            (fun t => if t = n' then rest else chainAt' t) (n' + 1)
        have h_fold : gSimFoldl actTick obsAll groupOrd withinOrd pos w (n' + 1) =
            gSimBody actTick obsAll groupOrd withinOrd pos W n' := by
          rw [gSimFoldl, List.range_succ, List.foldl_append]
          dsimp [W]
        rw [h_fold, h_rest_log]
        change (gSimFoldl actTick obsAll groupOrd withinOrd pos w n').outputLog ++
          (s!"tick {W.tick}" :: rest) =
          logBlocks w.outputLog w.tick
            (fun t => if t = n' then rest else chainAt' t) (n' + 1)
        rw [h_prefix' n' (by omega), h_W_tick]
        dsimp [logBlocks]
        rw [List.range_succ, List.foldl_append, List.foldl_cons,
          List.foldl_nil]
        rw [foldl_blocks_congr w.outputLog w.tick n' chainAt'
          (fun t => if t = n' then rest else chainAt' t) (fun t h_t => by
            have h_ne : t ≠ n' := by omega
            simp [h_ne])]
        simp only [ite_true]
      · have h_le' : n'' ≤ n' := by omega
        change (gSimFoldl actTick obsAll groupOrd withinOrd pos w n'').outputLog =
          logBlocks w.outputLog w.tick
            (fun t => if t = n' then rest else chainAt' t) n''
        rw [h_prefix' n'' h_le']
        dsimp [logBlocks]
        exact foldl_blocks_congr w.outputLog w.tick n'' chainAt'
          (fun t => if t = n' then rest else chainAt' t) (fun t h_t => by
            have h_ne : t ≠ n' := by omega
            simp [h_ne])
    · intro t h_t
      dsimp only
      split_ifs with h_eq
      · subst h_eq
        exact h_rest_chain
      · exact h_chain' t (by omega)

/-- Equal lists stay equal when the same list is prepended. -/
private theorem append_left_cancel' {α : Type} (l r₁ r₂ : List α)
    (h : l ++ r₁ = l ++ r₂) : r₁ = r₂ := by
  revert r₁ r₂ h
  induction l with
  | nil => intro r₁ r₂ h; simpa using h
  | cons a l ih =>
    intro r₁ r₂ h
    change a :: (l ++ r₁) = a :: (l ++ r₂) at h
    injection h with _ h_tail
    exact ih r₁ r₂ h_tail

/-- Tick strings determine the tick. -/
private theorem tick_string_inj (a b : Nat)
    (h : s!"tick {a}" = s!"tick {b}") : a = b := by
  change ("tick " : String) ++ a.repr = "tick " ++ b.repr at h
  have h_list := congrArg String.toList h
  rw [String.toList_append, String.toList_append] at h_list
  have h_repr : a.repr.toList = b.repr.toList :=
    append_left_cancel' ("tick " : String).toList a.repr.toList b.repr.toList
      h_list
  rw [Nat.toList_repr, Nat.toList_repr] at h_repr
  exact toDigits10_inj a b h_repr

/-- Splitting equal sums when the left part of the first is no longer
    than the left part of the second. -/
private theorem append_split_of_le {α : Type} (l₁ l₂ b₁ b₂ : List α)
    (h : l₁ ++ b₁ = l₂ ++ b₂) (h_le : l₁.length ≤ l₂.length) :
    ∃ x, l₂ = l₁ ++ x ∧ b₁ = x ++ b₂ := by
  revert l₂ b₁ b₂ h h_le
  induction l₁ with
  | nil =>
    intro l₂ b₁ b₂ h _
    exact ⟨l₂, by simp, by simpa using h⟩
  | cons a l₁ ih =>
    intro l₂ b₁ b₂ h h_le
    cases l₂ with
    | nil => simp [List.length] at h_le
    | cons b l₂ =>
      change a :: (l₁ ++ b₁) = b :: (l₂ ++ b₂) at h
      injection h with h_ab h_tail
      have h_le' : l₁.length ≤ l₂.length := by
        simpa [List.length] using h_le
      obtain ⟨x, h_l₂, h_b₁⟩ := ih l₂ b₁ b₂ h_tail h_le'
      refine ⟨x, ?_, h_b₁⟩
      rw [h_ab.symm, h_l₂]
      rfl

/-- Splitting equal sums when the left part of the second is no longer
    than the left part of the first. -/
private theorem append_split_of_ge {α : Type} (l₁ l₂ b₁ b₂ : List α)
    (h : l₁ ++ b₁ = l₂ ++ b₂) (h_le : l₂.length ≤ l₁.length) :
    ∃ x, l₁ = l₂ ++ x ∧ b₂ = x ++ b₁ :=
  append_split_of_le l₂ l₁ b₂ b₁ h.symm h_le

/-- Two block decompositions of the same log agree on every block when
    the second decomposition holds chain entries only. A tick entry
    never equals a chain entry, so the tick entry of each block delimits
    the blocks. -/
theorem logBlocks_chainAt_eq_of_log_eq (n : Nat)
    (c₁ c₂ : Nat → List String)
    (h_chain₂ : ∀ t < n, ∀ s ∈ c₂ t, IsChainEntry s) :
    logBlocks [] 0 c₁ n = logBlocks [] 0 c₂ n → ∀ t < n, c₁ t = c₂ t := by
  revert c₁ c₂ h_chain₂
  induction n with
  | zero =>
    intro c₁ c₂ _ _ t h_t
    omega
  | succ n' ih =>
    intro c₁ c₂ h_chain₂ h t h_t
    have h₁ := logBlocks_succ_last 0 n' [] c₁
    have h₂ := logBlocks_succ_last 0 n' [] c₂
    rw [h₁, h₂] at h
    simp only [Nat.zero_add] at h
    set P₁ := logBlocks [] 0 c₁ n'
    set P₂ := logBlocks [] 0 c₂ n'
    by_cases h_len : P₁.length ≤ P₂.length
    · obtain ⟨x, h_P₂, h_B₁⟩ := append_split_of_le P₁ P₂
        (s!"tick {n'}" :: c₁ n') (s!"tick {n'}" :: c₂ n') h h_len
      have h_x_nil : x = [] := by
        by_contra h_x
        cases x with
        | nil => exact h_x rfl
        | cons y ys =>
          change s!"tick {n'}" :: c₁ n' =
            (y :: ys) ++ (s!"tick {n'}" :: c₂ n') at h_B₁
          rw [List.cons_append] at h_B₁
          injection h_B₁ with h_y _
          have h_mem : y ∈ P₂ := by
            rw [h_P₂]
            exact List.mem_append_right _ (List.mem_cons.mpr (Or.inl rfl))
          obtain h_tick_case | h_chain_case :=
            mem_logBlocks_cases 0 n' c₂ y h_mem
          · obtain ⟨t', h_t', h_eq⟩ := h_tick_case
            have h_inj := tick_string_inj (0 + t') n' (by rw [← h_eq, h_y])
            omega
          · obtain ⟨t', h_t', h_mem_y⟩ := h_chain_case
            obtain ⟨gi, ci, v, h_v, h_eq⟩ := h_chain₂ t' (by omega) y h_mem_y
            rw [h_y.symm] at h_eq
            rcases h_v with rfl | rfl
            · rw [chainEntry_zero_form (chainName gi ci)] at h_eq
              exact (tick_entry_not_output n' gi ci).1 h_eq
            · rw [chainEntry_fifteen_form (chainName gi ci)] at h_eq
              exact (tick_entry_not_output n' gi ci).2 h_eq
      rw [h_x_nil] at h_P₂ h_B₁
      simp only [List.append_nil, List.nil_append] at h_P₂ h_B₁
      by_cases h_tn : t = n'
      · subst h_tn
        exact congrArg List.tail h_B₁
      · exact ih c₁ c₂ (fun t' h_t' => h_chain₂ t' (by omega)) h_P₂.symm t
          (by omega)
    · obtain ⟨x, h_P₁, h_B₂⟩ := append_split_of_ge P₁ P₂
        (s!"tick {n'}" :: c₁ n') (s!"tick {n'}" :: c₂ n') h
        (by omega)
      have h_x_len : x.length > 0 := by
        have := congrArg List.length h_P₁
        simp at this
        omega
      cases x with
      | nil => simp at h_x_len
      | cons y ys =>
        change s!"tick {n'}" :: c₂ n' =
          (y :: ys) ++ (s!"tick {n'}" :: c₁ n') at h_B₂
        rw [List.cons_append] at h_B₂
        have h_tail := congrArg List.tail h_B₂
        change c₂ n' = ys ++ (s!"tick {n'}" :: c₁ n') at h_tail
        have h_tick_mem : s!"tick {n'}" ∈ c₂ n' := by
          rw [h_tail]
          exact List.mem_append_right ys (List.mem_cons.mpr (Or.inl rfl))
        obtain ⟨gi, ci, v, h_v, h_eq⟩ := h_chain₂ n' (by omega)
          (s!"tick {n'}") h_tick_mem
        rcases h_v with rfl | rfl
        · rw [chainEntry_zero_form (chainName gi ci)] at h_eq
          exact False.elim ((tick_entry_not_output n' gi ci).1 h_eq)
        · rw [chainEntry_fifteen_form (chainName gi ci)] at h_eq
          exact False.elim ((tick_entry_not_output n' gi ci).2 h_eq)
