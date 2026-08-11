import BasicProofs.GroupClustering.FinalsBundle
import BasicProofs.GroupClustering.LogShape

set_option linter.unusedVariables false

open BasicRedstoneSim List

/-! # Group clustering — capstone bridge: output order to queue betweenness

This file reduces the clustering capstone's simulation analysis to a
pure betweenness statement on the tick-`T` final events.

## What is proven here

`clustering_outputPos_betweenness` consumes the FinalsBundle finals bundle and
the FinalPopIndex/LogShape log bridge. It shows: if three chains `(gi₁, ci₁)`,
`(gi₂, ci₂)`, `(gi₃, ci₃)` output at positions `p₁ < p₂ < p₃`, then the
final event of the middle chain lies strictly between the final events of
the two outer chains in the tick-`T` due filter `finals` (queue order):

    evBefore finals (finalEventOf gi₁ ci₁) (finalEventOf gi₂ ci₂) ∧
    evBefore finals (finalEventOf gi₂ ci₂) (finalEventOf gi₃ ci₃)

This is the full extent of what the output-order data determines.

## What remains for the capstone (not in the library)

The clustering conclusion `chainAt gi₂ ci₂ = chainAt gi₁ ci₁` requires a
CONVERSE step: a final event between two same-spec reference final events
must itself have that spec. The pieces exist —
`ConverseSpawnFinal_converse` / `converse_spawn_gSimBurst_final_m0`
(ConverseFinalUnconditional) and `chainSpec_eq_of_ConverseSpawnFinal` (ConverseSpawnFinal) — but they take
the betweenness in the POST-BURST queue at the reference chains'
stage-`m` pop tick (`(gSimBurst …).events` with `w.tick = stageTarget … m`),
together with `MiddleBlockOk`, `StageMemAt`, absence and membership
premises. Transporting the tick-`T` due-filter betweenness produced here
back to that spawn-burst betweenness is the still-open betweenness
induction across ticks. This file leaves that step out rather than
postulating it. -/

/-- A chain-index bound forces the group index in range: out-of-range
    groups are empty (`groupAt` is `getD []`). -/
private theorem gi_lt_of_ci_lt_groupAt (groups : List GroupSpec)
    (gi ci : Nat) (h : ci < (groupAt groups gi).length) :
    gi < groups.length := by
  by_contra h_ge
  have h_none : groups[gi]? = none :=
    List.getElem?_eq_none (Nat.le_of_not_lt h_ge)
  dsimp [groupAt] at h
  rw [h_none] at h
  dsimp at h
  omega

/-- The clustering bridge. Three outputs at strictly increasing positions
    put the middle chain's final event strictly between the two outer
    chains' final events in the tick-`T` due filter. The returned
    `finalEventOf` is the final-stage event, `finals` is duplicate-free,
    and every valid chain's final event sits in `finals`. -/
theorem clustering_outputPos_betweenness (groups : List GroupSpec)
    (h_valid : ∀ gi (c : ChainSpec), gi < groups.length →
        c ∈ groupAt groups gi →
        (∀ d ∈ c.middleDelays, ValidDelay d) ∧ ValidDelay c.lastDelay)
    (h_uniform : ∀ gi (c₁ c₂ : ChainSpec), gi < groups.length →
        c₁ ∈ groupAt groups gi → c₂ ∈ groupAt groups gi →
        chainDelay c₁ = chainDelay c₂)
    (T : Nat) (actTick : Nat → Nat)
    (h_act : ∀ gi, gi < groups.length → groupAt groups gi ≠ [] →
        actTick gi + groupDelay (groupAt groups gi) = T)
    (groupOrd : List Nat)
    (h_ord : List.Perm groupOrd (List.range groups.length))
    (withinOrd : Nat → List Nat)
    (h_within : ∀ gi, gi < groups.length →
        List.Perm (withinOrd gi) (List.range (groupAt groups gi).length))
    (pos : Nat → List Nat) :
    let log := groupSimulate T groups actTick groupOrd withinOrd pos
    ∀ gi₁ ci₁ gi₂ ci₂ gi₃ ci₃ p₁ p₂ p₃,
      ci₁ < (groupAt groups gi₁).length →
      ci₂ < (groupAt groups gi₂).length →
      ci₃ < (groupAt groups gi₃).length →
      outputPos log gi₁ ci₁ = some p₁ →
      outputPos log gi₂ ci₂ = some p₂ →
      outputPos log gi₃ ci₃ = some p₃ →
      p₁ < p₂ → p₂ < p₃ →
      ∃ (finals : List ScheduledEvent)
        (finalEventOf : Nat → Nat → ScheduledEvent),
        finals.Nodup ∧
        (∀ gi ci, gi < groups.length → ci < (groupAt groups gi).length →
          finalEventOf gi ci = stageEvent actTick groups gi ci
            ((chainAt groups gi ci).middleDelays.length + 1)) ∧
        (∀ gi ci, gi < groups.length → ci < (groupAt groups gi).length →
          finalEventOf gi ci ∈ finals) ∧
        evBefore finals (finalEventOf gi₁ ci₁) (finalEventOf gi₂ ci₂) ∧
        evBefore finals (finalEventOf gi₂ ci₂) (finalEventOf gi₃ ci₃) := by
  intro log gi₁ ci₁ gi₂ ci₂ gi₃ ci₃ p₁ p₂ p₃
    h_c₁ h_c₂ h_c₃ h_p₁ h_p₂ h_p₃ h₁₂ h₂₃
  -- the bounds force the group indices in range
  have h_g₁ : gi₁ < groups.length := gi_lt_of_ci_lt_groupAt groups gi₁ ci₁ h_c₁
  have h_g₂ : gi₂ < groups.length := gi_lt_of_ci_lt_groupAt groups gi₂ ci₂ h_c₂
  have h_g₃ : gi₃ < groups.length := gi_lt_of_ci_lt_groupAt groups gi₃ ci₃ h_c₃
  -- the finals bundle
  obtain ⟨blocks, finals, finalEventOf, chainOf, finalIdx, entryOf,
    h_shape, h_no_early, h_finals, h_nd, h_feq, h_block, h_match,
    h_chainOf_eq, h_eq_chainOf, h_pos⟩ :=
    groupSimulate_final_bundle T groups actTick groupOrd withinOrd pos
      h_valid h_uniform h_act h_ord h_within
  -- the log shape in the logBlocks form LogShape's bridge consumes
  have h_shape_lb : groupSimulate T groups actTick groupOrd withinOrd pos =
      logBlocks [] 0 blocks (T + 1) := by
    rw [h_shape, logBlocks_zero_eq_foldl]
  -- outputPos of every valid chain is T + 1 + its final-pop index
  have h_outPos : ∀ gi ci, gi < groups.length →
      ci < (groupAt groups gi).length →
      outputPos log gi ci = some (T + 1 + finalIdx gi ci) := by
    intro gi ci h_gi h_ci
    obtain ⟨pre, post, h_split, h_len⟩ := h_pos gi ci h_gi h_ci
    have h := outputPos_eq_finalPopIndex_discharged T groups actTick
      groupOrd withinOrd pos gi ci h_gi h_ci blocks h_shape_lb h_no_early
      finals h_nd chainOf finalEventOf entryOf h_block h_match
      h_chainOf_eq h_eq_chainOf pre post h_split
    rw [h_len] at h
    exact h
  -- pin p_i = T + 1 + finalIdx_i
  have h_p₁_eq : p₁ = T + 1 + finalIdx gi₁ ci₁ := by
    have h := h_outPos gi₁ ci₁ h_g₁ h_c₁
    rw [h] at h_p₁
    exact Option.some_inj.mp h_p₁.symm
  have h_p₂_eq : p₂ = T + 1 + finalIdx gi₂ ci₂ := by
    have h := h_outPos gi₂ ci₂ h_g₂ h_c₂
    rw [h] at h_p₂
    exact Option.some_inj.mp h_p₂.symm
  have h_p₃_eq : p₃ = T + 1 + finalIdx gi₃ ci₃ := by
    have h := h_outPos gi₃ ci₃ h_g₃ h_c₃
    rw [h] at h_p₃
    exact Option.some_inj.mp h_p₃.symm
  -- the final-pop index order
  have h_idx₁₂ : finalIdx gi₁ ci₁ < finalIdx gi₂ ci₂ := by
    rw [h_p₁_eq, h_p₂_eq] at h₁₂
    omega
  have h_idx₂₃ : finalIdx gi₂ ci₂ < finalIdx gi₃ ci₃ := by
    rw [h_p₂_eq, h_p₃_eq] at h₂₃
    omega
  -- index order is evBefore order of the final events
  have h_ev₁₂ : evBefore finals (finalEventOf gi₁ ci₁)
      (finalEventOf gi₂ ci₂) :=
    (chain_entries_are_final_pops finals h_nd finalEventOf finalIdx
      gi₁ ci₁ gi₂ ci₂ (h_pos gi₁ ci₁ h_g₁ h_c₁)
      (h_pos gi₂ ci₂ h_g₂ h_c₂)).mp h_idx₁₂
  have h_ev₂₃ : evBefore finals (finalEventOf gi₂ ci₂)
      (finalEventOf gi₃ ci₃) :=
    (chain_entries_are_final_pops finals h_nd finalEventOf finalIdx
      gi₂ ci₂ gi₃ ci₃ (h_pos gi₂ ci₂ h_g₂ h_c₂)
      (h_pos gi₃ ci₃ h_g₃ h_c₃)).mp h_idx₂₃
  refine ⟨finals, finalEventOf, h_nd, ?_, ?_, h_ev₁₂, h_ev₂₃⟩
  · intro gi ci h_gi h_ci
    exact (h_feq gi ci).symm
  · intro gi ci h_gi h_ci
    obtain ⟨pre, post, h_split, _⟩ := h_pos gi ci h_gi h_ci
    rw [h_split]
    exact List.mem_append_right pre (List.mem_cons.mpr (Or.inl rfl))
