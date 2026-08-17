import Proofs.Model.DescentScaffold

open BasicRedstoneSim
open World
open List

/-! # Chain id monotonicity and injectivity. -/

/-! ## Chain id monotonicity and injectivity -/

private theorem take_succ_in_range {α : Type} (l : List α) (i : Nat)
    (hi : i < l.length) :
    l.take (i + 1) = l.take i ++ [l[i]'hi] := by
  induction l generalizing i with
  | nil => dsimp [List.length] at hi; omega
  | cons a rest ih =>
    cases i with
    | zero => dsimp [List.take]
    | succ i' =>
      dsimp [List.length] at hi
      dsimp [List.take]
      congr 1
      exact ih i' (by omega)

private theorem take_of_length_le {α : Type} (l : List α) (n : Nat)
    (h : l.length ≤ n) : l.take n = l := by
  induction l generalizing n with
  | nil => cases n <;> dsimp [List.take]
  | cons a rest ih =>
    dsimp [List.length] at h
    cases n with
    | zero => omega
    | succ n' =>
      dsimp [List.take]
      congr 1
      exact ih n' (by omega)

/-- Chain node counts are positive. -/
private theorem chainNodeCount_pos (c : ChainSpec) :
    0 < chainNodeCount c := by
  dsimp [chainNodeCount]
  omega

/-- `chainBaseId` over one chain step. -/
theorem chainBaseId_succ (specs : List ChainSpec) (i : Nat)
    (hi : i < specs.length) :
    chainBaseId specs (i + 1) =
      chainBaseId specs i + chainNodeCount (specAt specs i) := by
  dsimp [chainBaseId, specAt]
  rw [List.getElem?_eq_getElem hi]
  dsimp [Option.getD]
  rw [take_succ_in_range specs i hi, List.map_append, List.sum_append]
  simp

/-- Chain base ids increase weakly with the index. -/
theorem chainBaseId_mono (specs : List ChainSpec) (i j : Nat)
    (hij : i ≤ j) : chainBaseId specs i ≤ chainBaseId specs j := by
  revert i hij
  induction j with
  | zero =>
    intro i hij
    have hi0 : i = 0 := by omega
    subst hi0
    exact Nat.le_refl _
  | succ j ih =>
    intro i hij
    by_cases hle : i ≤ j
    · have hbase := ih i hle
      by_cases hj : j < specs.length
      · rw [chainBaseId_succ specs j hj]
        dsimp [chainNodeCount]
        omega
      · have hge : specs.length ≤ j := by omega
        dsimp [chainBaseId] at hbase ⊢
        rw [take_of_length_le specs j hge] at hbase
        rw [take_of_length_le specs (j + 1) (by omega)]
        exact hbase
    · have heq : i = j + 1 := by omega
      subst heq
      exact Nat.le_refl _

/-- Chain base ids strictly increase inside the spec list. -/
theorem chainBaseId_lt_chainBaseId (specs : List ChainSpec)
    (i j : Nat) (hi : i < specs.length) (hj : j < specs.length)
    (hij : i < j) : chainBaseId specs i < chainBaseId specs j := by
  revert i hi hj hij
  induction j with
  | zero => intro i hi hj hij; omega
  | succ j ih =>
    intro i hi hj hij
    by_cases hlt : i < j
    · have hstep : chainBaseId specs j < chainBaseId specs (j + 1) := by
        rw [chainBaseId_succ specs j (by omega)]
        exact Nat.lt_add_of_pos_right (chainNodeCount_pos (specAt specs j))
      exact Nat.lt_trans (ih i hi (by omega) hlt) hstep
    · have heq : i = j := by omega
      rw [heq]
      rw [chainBaseId_succ specs j (by omega)]
      exact Nat.lt_add_of_pos_right (chainNodeCount_pos (specAt specs j))

/-- Observer ids determine the chain. -/
theorem chainObserverId_inj (specs : List ChainSpec) (i j : Nat)
    (hi : i < specs.length) (hj : j < specs.length)
    (h : chainObserverId specs i = chainObserverId specs j) :
    i = j := by
  by_contra hne
  have : i < j ∨ j < i := by omega
  rcases this with hlt | hlt
  · have := chainBaseId_lt_chainBaseId specs i j hi hj hlt
    dsimp [chainObserverId] at h
    omega
  · have := chainBaseId_lt_chainBaseId specs j i hj hi hlt
    dsimp [chainObserverId] at h
    omega

/-- A stage repeater id lies strictly before the next chain's base. -/
theorem chainRepId_lt_nextBase (specs : List ChainSpec)
    (i s : Nat)
    (hs : s ≤ (specAt specs i).middleDelays.length)
    (hpri : (specAt specs i).priLenOk) :
    chainRepId specs i s <
      chainBaseId specs i + chainNodeCount (specAt specs i) := by
  dsimp [chainRepId, chainNodeCount]
  have hzip : ((specAt specs i).middleDelays.zip
      (specAt specs i).middlePriorities).length =
      (specAt specs i).middleDelays.length := by
    dsimp [ChainSpec.priLenOk] at hpri
    rw [List.length_zip, hpri, min_self]
  omega

/-- Stage repeater ids determine the chain and the stage. -/
theorem chainRepId_inj (specs : List ChainSpec) (i j s t : Nat)
    (hi : i < specs.length) (hj : j < specs.length)
    (hs : s ≤ (specAt specs i).middleDelays.length)
    (ht : t ≤ (specAt specs j).middleDelays.length)
    (hpri_i : (specAt specs i).priLenOk)
    (hpri_j : (specAt specs j).priLenOk)
    (h : chainRepId specs i s = chainRepId specs j t) :
    i = j ∧ s = t := by
  have hij : i = j := by
    by_contra hne
    have : i < j ∨ j < i := by omega
    rcases this with hlt | hlt
    · have hle : chainBaseId specs (i + 1) ≤ chainBaseId specs j :=
        chainBaseId_mono specs (i + 1) j (by omega)
      have hsucc := chainBaseId_succ specs i hi
      have hltNext := chainRepId_lt_nextBase specs i s hs hpri_i
      dsimp [chainRepId] at hltNext
      have hchain : chainBaseId specs i +
          chainNodeCount (specAt specs i) ≤ chainBaseId specs j := by
        rw [← hsucc]
        exact hle
      dsimp [chainRepId] at h
      omega
    · have hle : chainBaseId specs (j + 1) ≤ chainBaseId specs i :=
        chainBaseId_mono specs (j + 1) i (by omega)
      have hsucc := chainBaseId_succ specs j hj
      have hltNext := chainRepId_lt_nextBase specs j t ht hpri_j
      dsimp [chainRepId] at hltNext
      have hchain : chainBaseId specs j +
          chainNodeCount (specAt specs j) ≤ chainBaseId specs i := by
        rw [← hsucc]
        exact hle
      dsimp [chainRepId] at h
      omega
  refine ⟨hij, ?_⟩
  subst hij
  dsimp [chainRepId] at h
  omega

