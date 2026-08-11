import BasicProofs.GroupClustering.Definitions
import BasicProofs.GroupClustering.OrderPreservationCore
import BasicProofs.GroupClustering.ClusteringCore

/-! # Group clustering and order preservation — theorem statements

The model (chains, groups, direct observer activation, simulation, output
order) is defined in `BasicProofs.GroupClustering.Definitions`. Supporting lemmas
live in the `BasicProofs.GroupClustering.PartNN` chain. This file holds the
two capstone statements.

Claims:
1. **Clustering**: outputs of chains with identical `ChainSpec` are contiguous
   in the output order (nothing of a different spec appears between them).
2. **Order preservation**: for groups A, B and specs a, b present in both,
   if the a-instances order A-before-B then the b-instances also order
   A-before-B (the group-vs-group order is spec-independent).
-/

/-! ## Theorems -/

/-- **Clustering.** Run any group system in which every group activates at
    `T - groupDelay` (all last nodes light up at `T`), with arbitrary group
    order at equal ticks (`groupOrd`), arbitrary within-group firing order
    (`withinOrd`) and arbitrary pos-style insertion (`pos`). Then between any
    two outputs of chains with identical spec, only outputs of that same spec
    appear. -/
theorem group_output_clustering
    (groups : List GroupSpec)
    (h_valid : ∀ gi (c : ChainSpec), gi < groups.length → c ∈ groupAt groups gi →
        (∀ d ∈ c.middleDelays, ValidDelay d) ∧ ValidDelay c.lastDelay)
    (h_uniform : ∀ gi (c₁ c₂ : ChainSpec), gi < groups.length →
        c₁ ∈ groupAt groups gi → c₂ ∈ groupAt groups gi →
        chainDelay c₁ = chainDelay c₂)
    (T : Nat)
    (actTick : Nat → Nat)
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
      chainAt groups gi₁ ci₁ = chainAt groups gi₃ ci₃ →
      chainAt groups gi₂ ci₂ = chainAt groups gi₁ ci₁ := by
  exact group_output_clustering_core groups h_valid h_uniform T actTick
    h_act groupOrd h_ord withinOrd h_within pos

/-- **Order preservation.** Under the same setup: if the instances of spec `sa`
    in group `ga` all output before the instances of spec `sa` in group `gb`
    (with `sa` present in both groups), then the same holds for every other
    spec `sb` — the relative order of two groups does not depend on the spec
    used to observe it. -/
theorem group_order_preservation
    (groups : List GroupSpec)
    (h_valid : ∀ gi (c : ChainSpec), gi < groups.length → c ∈ groupAt groups gi →
        (∀ d ∈ c.middleDelays, ValidDelay d) ∧ ValidDelay c.lastDelay)
    (h_uniform : ∀ gi (c₁ c₂ : ChainSpec), gi < groups.length →
        c₁ ∈ groupAt groups gi → c₂ ∈ groupAt groups gi →
        chainDelay c₁ = chainDelay c₂)
    (T : Nat)
    (actTick : Nat → Nat)
    (h_act : ∀ gi, gi < groups.length → groupAt groups gi ≠ [] →
        actTick gi + groupDelay (groupAt groups gi) = T)
    (groupOrd : List Nat)
    (h_ord : List.Perm groupOrd (List.range groups.length))
    (withinOrd : Nat → List Nat)
    (h_within : ∀ gi, gi < groups.length →
        List.Perm (withinOrd gi) (List.range (groupAt groups gi).length))
    (pos : Nat → List Nat) :
    let log := groupSimulate T groups actTick groupOrd withinOrd pos
    ∀ ga gb sa sb,
      ga < groups.length → gb < groups.length → ga ≠ gb →
      (∃ ca, ca < (groupAt groups ga).length ∧ chainAt groups ga ca = sa) →
      (∃ cb, cb < (groupAt groups gb).length ∧ chainAt groups gb cb = sa) →
      groupBeforeSpec log groups ga gb sa →
      groupBeforeSpec log groups ga gb sb := by
  exact group_order_preservation_core groups h_valid h_uniform T actTick h_act
    groupOrd h_ord withinOrd h_within pos
