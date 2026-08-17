import Proofs.Model.CascadeTrace
import Proofs.Model.StageDescent
import Proofs.Model.DrainOrder
import Mathlib.Data.List.Perm.Basic

open BasicRedstoneSim

/-! # Suffix sub-chains — algebra

The last `n` repeaters of a chain form a suffix sub-chain. Two chains that
share their last `n` repeaters form one family. This module defines the
suffix and proves that a shared suffix forces the delay, priority and firing
tick of the repeater `r` steps from the end to agree, for `r < n`.

The tests in `python/suffix_subchain_check.py` pass on 4000 random
configurations. -/

/-- The full repeater sequence of a spec. It holds the middle repeaters in
    order, then the last repeater. -/
def ChainSpec.repeaterSeq (c : ChainSpec) : List (PNat × Int) :=
  c.middleDelays.zip c.middlePriorities ++ [(c.lastDelay, c.lastPriority)]

/-- The last `n` repeaters of a spec. If the spec has fewer than `n`
    repeaters, the result is `none`. -/
def ChainSpec.suffixSpec (c : ChainSpec) (n : Nat) :
    Option (List (PNat × Int)) :=
  let seq := c.repeaterSeq
  if n ≤ seq.length then some (seq.drop (seq.length - n)) else none

/-! ## Suffix algebra -/

/-- The length of a repeater sequence is one more than the middle-repeater
    count. -/
theorem repeaterSeq_length (specs : List ChainSpec) (i : Nat)
    (hpri : (specAt specs i).priLenOk) :
    (specAt specs i).repeaterSeq.length = repLenAt specs i + 1 := by
  dsimp [ChainSpec.repeaterSeq, repLenAt]
  rw [List.length_append, List.length_singleton, List.length_zip]
  have hpri' : (specAt specs i).middlePriorities.length =
      (specAt specs i).middleDelays.length := by
    dsimp [ChainSpec.priLenOk] at hpri
    exact hpri
  rw [hpri', min_self]

/-- A repeater-sequence entry at a valid stage is the stage delay and
    priority. -/
theorem repeaterSeq_getElem (specs : List ChainSpec) (i k : Nat)
    (hpri : (specAt specs i).priLenOk)
    (hk : k ≤ repLenAt specs i) :
    (specAt specs i).repeaterSeq[k]? =
      some (stageDelayAt specs i k, stagePriAt specs i k) := by
  dsimp [ChainSpec.repeaterSeq]
  have hpri' : (specAt specs i).middlePriorities.length =
      (specAt specs i).middleDelays.length := by
    dsimp [ChainSpec.priLenOk] at hpri
    exact hpri
  by_cases hlt : k < (specAt specs i).middleDelays.length
  · have hzip : k < ((specAt specs i).middleDelays.zip
        (specAt specs i).middlePriorities).length := by
      rw [List.length_zip, hpri', min_self]
      exact hlt
    have hp : k < (specAt specs i).middlePriorities.length := by omega
    rw [List.getElem?_append_left (l₁ := (specAt specs i).middleDelays.zip
        (specAt specs i).middlePriorities)
      (l₂ := [((specAt specs i).lastDelay, (specAt specs i).lastPriority)])
      (by simpa using hzip)]
    rw [List.getElem?_eq_getElem hzip]
    simp [List.zip, List.getElem_zipWith]
    have hd := stageDelayAt_of_lt specs i k hlt
    have hpr := stagePriAt_of_lt specs i k hpri hlt
    simp [hd, hpr]
  · have hk_eq : k = (specAt specs i).middleDelays.length := by
      dsimp [repLenAt] at hk
      omega
    subst hk_eq
    have hzip : ((specAt specs i).middleDelays.zip
        (specAt specs i).middlePriorities).length =
        (specAt specs i).middleDelays.length := by
      rw [List.length_zip, hpri', min_self]
    rw [List.getElem?_append_right (l₁ := (specAt specs i).middleDelays.zip
        (specAt specs i).middlePriorities)
      (l₂ := [((specAt specs i).lastDelay, (specAt specs i).lastPriority)])
      (by rw [hzip])]
    simp [hzip]
    have hd : stageDelayAt specs i ((specAt specs i).middleDelays.length) =
        (specAt specs i).lastDelay :=
      stageDelayAt_of_eq specs i (le_refl _)
    have hpr : stagePriAt specs i ((specAt specs i).middleDelays.length) =
        (specAt specs i).lastPriority :=
      stagePriAt_of_eq specs i hpri (le_refl _)
    simp [hd, hpr]

/-- The entry `r` from the end of a suffix is the stage `repLenAt - r`
    delay and priority. -/
theorem suffixSpec_getElem (specs : List ChainSpec) (i n r : Nat)
    (s : List (PNat × Int))
    (hpri : (specAt specs i).priLenOk)
    (hspec : (specAt specs i).suffixSpec n = some s)
    (hr : r < n) :
    s[n - 1 - r]? =
      some (stageDelayAt specs i (repLenAt specs i - r),
        stagePriAt specs i (repLenAt specs i - r)) := by
  have hs : s = (specAt specs i).repeaterSeq.drop
      ((specAt specs i).repeaterSeq.length - n) := by
    dsimp [ChainSpec.suffixSpec] at hspec
    split at hspec <;> simp_all
  have hrep : (specAt specs i).repeaterSeq.length = repLenAt specs i + 1 :=
    repeaterSeq_length specs i hpri
  have hn_le : n ≤ repLenAt specs i + 1 := by
    have hlen : n ≤ (specAt specs i).repeaterSeq.length := by
      dsimp [ChainSpec.suffixSpec] at hspec
      split at hspec <;> simp_all
    rw [hrep] at hlen
    exact hlen
  rw [hs, List.getElem?_drop]
  rw [hrep]
  have hidx : (repLenAt specs i + 1 - n) + (n - 1 - r) = repLenAt specs i - r := by
    omega
  rw [hidx]
  exact repeaterSeq_getElem specs i (repLenAt specs i - r) hpri (by omega)

/-- Two chains with the same `n`-suffix agree on the delay and priority of
    the repeater `r` steps from the end, for `r < n`. -/
theorem suffixStage_eq (specs : List ChainSpec) (i k n r : Nat)
    (s : List (PNat × Int))
    (hpri_i : (specAt specs i).priLenOk) (hpri_k : (specAt specs k).priLenOk)
    (hi_spec : (specAt specs i).suffixSpec n = some s)
    (hk_spec : (specAt specs k).suffixSpec n = some s)
    (hr : r < n) :
    stageDelayAt specs i (repLenAt specs i - r) =
      stageDelayAt specs k (repLenAt specs k - r) ∧
    stagePriAt specs i (repLenAt specs i - r) =
      stagePriAt specs k (repLenAt specs k - r) := by
  have hi_get := suffixSpec_getElem specs i n r s hpri_i hi_spec hr
  have hk_get := suffixSpec_getElem specs k n r s hpri_k hk_spec hr
  have hpair : (stageDelayAt specs i (repLenAt specs i - r),
      stagePriAt specs i (repLenAt specs i - r)) =
      (stageDelayAt specs k (repLenAt specs k - r),
      stagePriAt specs k (repLenAt specs k - r)) := by
    exact Option.some_inj.mp (hi_get.symm.trans hk_get)
  exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

/-- A chain whose `n`-suffix exists has at least `n` repeaters, i.e.
    `n ≤ repLenAt + 1`. -/
theorem suffixSpec_repLen_ge (specs : List ChainSpec) (i n : Nat)
    (s : List (PNat × Int))
    (hpri : (specAt specs i).priLenOk)
    (hspec : (specAt specs i).suffixSpec n = some s) :
    n ≤ repLenAt specs i + 1 := by
  have hlen : n ≤ (specAt specs i).repeaterSeq.length := by
    dsimp [ChainSpec.suffixSpec] at hspec
    split at hspec <;> simp_all
  have hrep : (specAt specs i).repeaterSeq.length = repLenAt specs i + 1 :=
    repeaterSeq_length specs i hpri
  rw [hrep] at hlen
  exact hlen

/-- Dropping the first (most recent) repeater of an `n`-suffix gives the
    `(n - 1)`-suffix. -/
theorem suffixSpec_drop_one (specs : List ChainSpec) (i n : Nat) (s : List (PNat × Int))
    (_hpri : (specAt specs i).priLenOk) (hn : 1 ≤ n)
    (hspec : (specAt specs i).suffixSpec n = some s) :
    (specAt specs i).suffixSpec (n - 1) = some (s.drop 1) := by
  have hs : s = (specAt specs i).repeaterSeq.drop
      ((specAt specs i).repeaterSeq.length - n) := by
    dsimp [ChainSpec.suffixSpec] at hspec
    split at hspec <;> simp_all
  have hn_le : n ≤ (specAt specs i).repeaterSeq.length := by
    dsimp [ChainSpec.suffixSpec] at hspec
    split at hspec <;> simp_all
  dsimp [ChainSpec.suffixSpec]
  rw [if_pos (by omega)]
  congr 1
  rw [hs]
  rw [List.drop_drop]
  congr 1
  omega

/-- Two chains with the same `n`-suffix fire the repeater `r` steps from
    the end at the same tick, for `r < n`. -/
theorem suffixStageTick_eq (T : Nat) (specs : List ChainSpec) (i k n r : Nat)
    (s : List (PNat × Int))
    (hpri_i : (specAt specs i).priLenOk) (hpri_k : (specAt specs k).priLenOk)
    (hfit_i : chainDelay (specAt specs i) ≤ T) (hfit_k : chainDelay (specAt specs k) ≤ T)
    (hi_spec : (specAt specs i).suffixSpec n = some s)
    (hk_spec : (specAt specs k).suffixSpec n = some s)
    (hr : r < n) :
    stageTickOf T specs i (repLenAt specs i - r) =
      stageTickOf T specs k (repLenAt specs k - r) := by
  induction r with
  | zero =>
      rw [Nat.sub_zero, Nat.sub_zero]
      rw [stageTickOf_last T specs i hfit_i, stageTickOf_last T specs k hfit_k]
  | succ r' ih =>
      have hr'_lt : r' < n := by omega
      have hi_ge : n ≤ repLenAt specs i + 1 := suffixSpec_repLen_ge specs i n s hpri_i hi_spec
      have hk_ge : n ≤ repLenAt specs k + 1 := suffixSpec_repLen_ge specs k n s hpri_k hk_spec
      have hr_succ_le_i : r' + 1 ≤ repLenAt specs i := by omega
      have hr_succ_le_k : r' + 1 ≤ repLenAt specs k := by omega
      have hdel := (suffixStage_eq specs i k n r' s hpri_i hpri_k hi_spec hk_spec hr'_lt).1
      have hdelN : (stageDelayAt specs i (repLenAt specs i - r') : Nat) =
          (stageDelayAt specs k (repLenAt specs k - r') : Nat) := by exact_mod_cast hdel
      have hsucc_i := stageTickOf_succ T specs i (repLenAt specs i - (r' + 1)) (by
        dsimp [repLenAt] at hr_succ_le_i ⊢
        omega)
      have hsucc_k := stageTickOf_succ T specs k (repLenAt specs k - (r' + 1)) (by
        dsimp [repLenAt] at hr_succ_le_k ⊢
        omega)
      have harg_i : repLenAt specs i - (r' + 1) + 1 = repLenAt specs i - r' := by omega
      have harg_k : repLenAt specs k - (r' + 1) + 1 = repLenAt specs k - r' := by omega
      rw [harg_i] at hsucc_i
      rw [harg_k] at hsucc_k
      have hih := ih hr'_lt
      omega

/-- If chain `j` has at least `n` repeaters and agrees with chain `i` on the
    delay and priority of every repeater `r < n` steps from the end, then the
    two chains share the same `n`-suffix. -/
theorem suffixSpec_eq_of_stage_eq (specs : List ChainSpec) (i j n : Nat)
    (s : List (PNat × Int))
    (hpri_i : (specAt specs i).priLenOk) (hpri_j : (specAt specs j).priLenOk)
    (hi_spec : (specAt specs i).suffixSpec n = some s)
    (hj_ge : n ≤ repLenAt specs j + 1)
    (hstage : ∀ r < n, stageDelayAt specs j (repLenAt specs j - r) =
        stageDelayAt specs i (repLenAt specs i - r) ∧
      stagePriAt specs j (repLenAt specs j - r) =
        stagePriAt specs i (repLenAt specs i - r)) :
    (specAt specs j).suffixSpec n = some s := by
  have hs : s = (specAt specs i).repeaterSeq.drop
      ((specAt specs i).repeaterSeq.length - n) := by
    dsimp [ChainSpec.suffixSpec] at hi_spec
    split at hi_spec <;> simp_all
  have hrep_i : (specAt specs i).repeaterSeq.length = repLenAt specs i + 1 :=
    repeaterSeq_length specs i hpri_i
  have hrep_j : (specAt specs j).repeaterSeq.length = repLenAt specs j + 1 :=
    repeaterSeq_length specs j hpri_j
  have hj_ge' : n ≤ (specAt specs j).repeaterSeq.length := by
    rw [hrep_j]
    exact hj_ge
  have hi_ge : n ≤ repLenAt specs i + 1 := suffixSpec_repLen_ge specs i n s hpri_i hi_spec
  dsimp [ChainSpec.suffixSpec]
  rw [if_pos hj_ge']
  congr 1
  rw [hrep_j, hs, hrep_i]
  apply List.ext_getElem?
  intro m
  by_cases hm : m < n
  · have hr : n - 1 - m < n := by omega
    have hidx_j : (repLenAt specs j + 1 - n) + m = repLenAt specs j - (n - 1 - m) := by omega
    have hidx_i : (repLenAt specs i + 1 - n) + m = repLenAt specs i - (n - 1 - m) := by omega
    have hj_entry : ((specAt specs j).repeaterSeq.drop (repLenAt specs j + 1 - n))[m]? =
        some (stageDelayAt specs j (repLenAt specs j - (n - 1 - m)),
          stagePriAt specs j (repLenAt specs j - (n - 1 - m))) := by
      rw [List.getElem?_drop, hidx_j]
      exact repeaterSeq_getElem specs j (repLenAt specs j - (n - 1 - m)) hpri_j (by omega)
    have hi_entry : ((specAt specs i).repeaterSeq.drop (repLenAt specs i + 1 - n))[m]? =
        some (stageDelayAt specs i (repLenAt specs i - (n - 1 - m)),
          stagePriAt specs i (repLenAt specs i - (n - 1 - m))) := by
      rw [List.getElem?_drop, hidx_i]
      exact repeaterSeq_getElem specs i (repLenAt specs i - (n - 1 - m)) hpri_i (by omega)
    have hpair : (stageDelayAt specs j (repLenAt specs j - (n - 1 - m)),
        stagePriAt specs j (repLenAt specs j - (n - 1 - m))) =
        (stageDelayAt specs i (repLenAt specs i - (n - 1 - m)),
          stagePriAt specs i (repLenAt specs i - (n - 1 - m))) := by
      obtain ⟨hd, hp⟩ := hstage (n - 1 - m) hr
      exact Prod.ext hd hp
    rw [hj_entry, hi_entry]
    exact congrArg some hpair
  · have hj_len : ((specAt specs j).repeaterSeq.drop (repLenAt specs j + 1 - n)).length = n := by
      rw [List.length_drop, hrep_j]
      omega
    have hi_len : ((specAt specs i).repeaterSeq.drop (repLenAt specs i + 1 - n)).length = n := by
      rw [List.length_drop, hrep_i]
      have hi_ge : n ≤ repLenAt specs i + 1 := suffixSpec_repLen_ge specs i n s hpri_i hi_spec
      omega
    rw [List.getElem?_eq_none (l := ((specAt specs j).repeaterSeq.drop (repLenAt specs j + 1 - n)))
        (by rw [hj_len]; omega),
      List.getElem?_eq_none (l := ((specAt specs i).repeaterSeq.drop (repLenAt specs i + 1 - n)))
        (by rw [hi_len]; omega)]

/-- The sum of the delays of the repeaters at distance `< r` from the end. -/
def suffixDelaySum (specs : List ChainSpec) (i r : Nat) : Nat :=
  match r with
  | 0 => 0
  | r' + 1 => (stageDelayAt specs i (repLenAt specs i - r') : Nat) + suffixDelaySum specs i r'

/-- The firing tick of the repeater `r` steps from the end is the output
    tick minus `suffixDelaySum`. -/
theorem stageTickOf_sub_delays (T : Nat) (specs : List ChainSpec) (i : Nat)
    (hfit : chainDelay (specAt specs i) ≤ T) (r : Nat) (hr : r ≤ repLenAt specs i) :
    stageTickOf T specs i (repLenAt specs i - r) + suffixDelaySum specs i r = T := by
  induction r with
  | zero =>
      dsimp [suffixDelaySum]
      rw [stageTickOf_last T specs i hfit]
  | succ r' ih =>
      have hr' : r' ≤ repLenAt specs i := by omega
      have hih := ih hr'
      have hle : (repLenAt specs i - (r' + 1)) + 1 ≤ (specAt specs i).middleDelays.length := by
        dsimp [repLenAt] at hr ⊢
        omega
      have hsucc := stageTickOf_succ T specs i (repLenAt specs i - (r' + 1)) hle
      have harg : repLenAt specs i - (r' + 1) + 1 = repLenAt specs i - r' := by omega
      rw [harg] at hsucc
      dsimp [suffixDelaySum]
      rw [← Nat.add_assoc, ← hsucc]
      exact hih

