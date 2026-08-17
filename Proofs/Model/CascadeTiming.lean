import Proofs.Model.Basic
import Mathlib.Data.List.Pairwise
import Mathlib.Tactic

open BasicRedstoneSim

/-! # Cascade timing — ported from retired `BasicProofs.PrefixChain.Part01`.

A single chain's firing-tick sequence depends only on its delays (not its
priorities), so this machinery ports verbatim. Activating a chain at tick `t`
fires the observer at `t + 2`, each repeater cumulatively, and the output at
`t + chainDelay c`. -/

/-- `cumSums [d₁, …, dₙ] s = [s, s+d₁, s+d₁+d₂, …, s+Σdᵢ]`. -/
def cumSums : List Nat → Nat → List Nat
  | [], start => [start]
  | d :: rest, start => start :: cumSums rest (start + d)

theorem cumSums_length (ds : List Nat) (s : Nat) :
    (cumSums ds s).length = ds.length + 1 := by
  induction ds generalizing s with
  | nil => simp [cumSums]
  | cons d rest ih => simp [cumSums, ih]

theorem cumSums_ge_start (ds : List Nat) (s : Nat) :
    ∀ x ∈ cumSums ds s, x ≥ s := by
  induction ds generalizing s with
  | nil => simp [cumSums]
  | cons d rest ih =>
    simp only [cumSums]
    intro x hx
    simp only [List.mem_cons] at hx
    cases hx with
    | inl h => rw [h]
    | inr h =>
      have := ih (s + d) x h
      omega

/-- With delays ≥ 2 the cumulative ticks strictly increase. -/
theorem cumSums_pairwise_lt (ds : List Nat) (s : Nat)
    (h : ∀ d ∈ ds, d ≥ 2) : (cumSums ds s).Pairwise (· < ·) := by
  induction ds generalizing s with
  | nil => simp [cumSums]
  | cons d rest ih =>
    simp [cumSums]
    have hd : d ≥ 2 := h d (by simp)
    have hrest : ∀ d ∈ rest, d ≥ 2 := fun d hd' => h d (by simp [hd'])
    constructor
    · intro x hx
      have := cumSums_ge_start rest (s + d) x hx
      omega
    · exact ih (s + d) hrest

/-- `cumSums` ends with the total cumulative sum. -/
theorem cumSums_append (ds : List Nat) (s : Nat) :
    ∃ init, cumSums ds s = init ++ [s + ds.sum] := by
  induction ds generalizing s with
  | nil => exact ⟨[], by simp [cumSums]⟩
  | cons d rest ih =>
    obtain ⟨init, hi⟩ := ih (s + d)
    refine ⟨s :: init, ?_⟩
    simp only [cumSums, hi, List.cons_append, List.sum_cons]
    rw [add_assoc]

/-- Firing-tick sequence of chain `c` activated at tick `t`:
    observer at `t+2`, then each repeater cumulatively, ending at
    `t + chainDelay c`. -/
def chainTickList (c : ChainSpec) (t : Nat) : List Nat :=
  cumSums ((c.middleDelays.map (fun d => (d : Nat))) ++ [(c.lastDelay : Nat)])
    (t + 2)

/-- Every delay in a coerced middle-delay list plus the last delay is ≥ 2. -/
theorem map_coe_append_ge2 (ds : List PNat) (last : PNat)
    (h_mid : ∀ d ∈ ds, ValidDelay d) (h_last : ValidDelay last) :
    ∀ d ∈ (ds.map (fun x => (x : Nat))) ++ [(last : Nat)], d ≥ 2 := by
  intro d hd
  simp at hd
  rcases hd with ⟨a, ha, rfl⟩ | hl
  · exact ValidDelay.ge2 (h_mid a ha)
  · rw [hl]
    exact ValidDelay.ge2 h_last

theorem chainTickList_pairwise_lt (c : ChainSpec) (t : Nat)
    (h_mid : ∀ d ∈ c.middleDelays, ValidDelay d) (h_last : ValidDelay c.lastDelay) :
    (chainTickList c t).Pairwise (· < ·) := by
  apply cumSums_pairwise_lt
  exact map_coe_append_ge2 c.middleDelays c.lastDelay h_mid h_last

/-- The final firing tick is the output tick `t + chainDelay c`. -/
theorem chainTickList_append (c : ChainSpec) (t : Nat) :
    ∃ init, chainTickList c t = init ++ [t + chainDelay c] := by
  obtain ⟨init, hi⟩ := cumSums_append
    ((c.middleDelays.map (fun d => (d : Nat))) ++ [(c.lastDelay : Nat)]) (t + 2)
  refine ⟨init, ?_⟩
  unfold chainTickList
  rw [hi]
  congr 1
  simp [chainDelay, ChainSpec.totalDelay, List.sum_append]
  omega
