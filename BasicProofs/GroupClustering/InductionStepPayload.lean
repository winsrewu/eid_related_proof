import BasicProofs.GroupClustering.MiddleBlockInvariant
import BasicProofs.GroupClustering.SameSpecLockstep

open BasicRedstoneSim List

/-! # Group clustering — induction-step payload from `MiddleBlockOk`

Two small consequences of applying the stage-`j` middle-block invariant
to the parent of a stage-`(j + 1)` interloper, used by the general
stage-induction step.

* `MiddleBlock_prefix_of_middle_parent`: when the parent sits at stage
  `j` itself, the invariant identifies its chain's first `j` middle
  delays with those of the first reference chain (the payload fed to
  `prefixDelays_ext_of_targets_eq`);
* `MiddleBlock_stage_index_contradiction`: when the parent sits at a
  stage `k ≥ j + 1`, the invariant is impossible — the prefix-class
  alternative would make the parent a stage-`j` event (contradicting
  `stageEvent_injective`), and the final-event alternative carries
  priority `-1`, not `-3`.
-/

/-- The stage index of a priority-`-3` stage event lies in the middle
    range. -/
private theorem stagePri_neg3_middle (groups : List GroupSpec)
    (g c j : Nat) (h_pri : stagePri groups g c j = (-3 : Int)) :
    1 ≤ j ∧ j ≤ (chainAt groups g c).middleDelays.length := by
  dsimp [stagePri] at h_pri
  split_ifs at h_pri <;> omega

/-- Applying the stage-`j` middle-block invariant to a stage-`j` parent
    event identifies the first `j` middle delays of its chain with those
    of the first reference chain. -/
theorem MiddleBlock_prefix_of_middle_parent (groups : List GroupSpec)
    (actTick : Nat → Nat) (T : Nat) (g₁ c₁ j : Nat)
    (P : ScheduledEvent) (g c : Nat)
    (h_g : g < groups.length) (h_c : c < (groupAt groups g).length)
    (h_P_eq : P = stageEvent actTick groups g c j)
    (h_P_pri : P.priority = (-3 : Int))
    (h_mb : MiddleBlock groups actTick T g₁ c₁ j P) :
    prefixDelays groups g c j = prefixDelays groups g₁ c₁ j := by
  have h_j_le : j ≤ (chainAt groups g c).middleDelays.length := by
    have h_pri' : stagePri groups g c j = (-3 : Int) := by
      have := congr_arg ScheduledEvent.priority h_P_eq
      dsimp [stageEvent] at this
      rw [h_P_pri] at this
      exact this.symm
    exact (stagePri_neg3_middle groups g c j h_pri').2
  rcases h_mb with h_final | ⟨g'', c'', h_g'', h_c'', h_P_eq'', _, _, h_pref⟩
  · -- a final event carries priority -1, not -3
    obtain ⟨gi, ci, _, _, h_P_fin, _⟩ := h_final
    have h_pri_final : P.priority = (-1 : Int) := by
      rw [h_P_fin]
      dsimp [stageEvent]
      exact stagePri_last groups gi ci
    rw [h_P_pri] at h_pri_final
    omega
  · -- prefix class: the parent is a stage-j event of (g'', c'') too
    have h_eq : stageEvent actTick groups g c j =
        stageEvent actTick groups g'' c'' j := by
      rw [← h_P_eq, h_P_eq'']
    have h_j_le'' : j ≤ (chainAt groups g'' c'').middleDelays.length := by
      have h_pri'' : stagePri groups g'' c'' j = (-3 : Int) := by
        have := congr_arg ScheduledEvent.priority h_P_eq''
        dsimp [stageEvent] at this
        rw [h_P_pri] at this
        exact this.symm
      exact (stagePri_neg3_middle groups g'' c'' j h_pri'').2
    obtain ⟨rfl, rfl, _⟩ := stageEvent_injective actTick groups g c j
      g'' c'' j h_g h_c h_g'' h_c'' (by omega) (by omega) h_eq
    exact h_pref

/-- Applying the stage-`j` middle-block invariant to a stage-`k` parent
    event with `k ≥ j + 1` is impossible. -/
theorem MiddleBlock_stage_index_contradiction (groups : List GroupSpec)
    (actTick : Nat → Nat) (T : Nat) (g₁ c₁ j : Nat)
    (P : ScheduledEvent) (g c k : Nat)
    (h_g : g < groups.length) (h_c : c < (groupAt groups g).length)
    (h_P_eq : P = stageEvent actTick groups g c k)
    (h_P_pri : P.priority = (-3 : Int))
    (h_k_ge : j + 1 ≤ k)
    (h_k_le : k ≤ (chainAt groups g c).middleDelays.length)
    (h_mb : MiddleBlock groups actTick T g₁ c₁ j P) : False := by
  rcases h_mb with h_final | ⟨g'', c'', h_g'', h_c'', h_P_eq'', _, _, _⟩
  · -- a final event carries priority -1, not -3
    obtain ⟨gi, ci, _, _, h_P_fin, _⟩ := h_final
    have h_pri_final : P.priority = (-1 : Int) := by
      rw [h_P_fin]
      dsimp [stageEvent]
      exact stagePri_last groups gi ci
    rw [h_P_pri] at h_pri_final
    omega
  · -- prefix class: the parent would be a stage-j event
    have h_eq : stageEvent actTick groups g c k =
        stageEvent actTick groups g'' c'' j := by
      rw [← h_P_eq, h_P_eq'']
    have h_j_le'' : j ≤ (chainAt groups g'' c'').middleDelays.length := by
      have h_pri'' : stagePri groups g'' c'' j = (-3 : Int) := by
        have := congr_arg ScheduledEvent.priority h_P_eq''
        dsimp [stageEvent] at this
        rw [h_P_pri] at this
        exact this.symm
      exact (stagePri_neg3_middle groups g'' c'' j h_pri'').2
    obtain ⟨_, _, h_k_eq⟩ := stageEvent_injective actTick groups g c k
      g'' c'' j h_g h_c h_g'' h_c'' (by omega) (by omega) h_eq
    omega
