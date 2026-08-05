import BasicProofs.PrefixChain.Part17

/-! # Group clustering and order preservation

Chains are prefix chains as in `BasicProofs.PrefixChain`
(Input → Observer → [Repeater(-3, d_i)]* → Repeater(-1, d_last) → Output).

A **group** is a list of chains whose last nodes all light up at a common tick `T`
and whose total repeater delays are all equal. **Activating** a group at tick
`T - D` means firing ALL of its observers directly (bypassing the event queue,
no observer +2 delay), in arbitrary order, **atomically**: one group's observers
fire consecutively, with no interleaved firings from other groups and no queue
processing in between. Between (atomic) group activations, an arbitrary number
of pending queue events may be processed (pos-style insertion).

Modeling note (2026-08-05): atomicity is essential. If observer firings from
different groups may interleave arbitrarily, order preservation is FALSE:
with specs a = delays [2, 4] and b = delays [4, 2] (equal totals), groups
A = {a_A, b_A}, B = {a_B, b_B}, firing order a_A, a_B, b_B, b_A gives output
order a_A, a_B, b_B, b_A — so a orders AB while b orders BA.

Claims:
1. **Clustering**: outputs of chains with identical `ChainSpec` are contiguous
   in the output order (nothing of a different spec appears between them).
2. **Order preservation**: for groups A, B and specs a, b present in both,
   if the a-instances order A-before-B then the b-instances also order
   A-before-B (the group-vs-group order is spec-independent).
-/

namespace GroupClustering

/-! ## Delays without the observer contribution -/

/-- Activation-to-output delay under direct observer firing:
    only the repeater delays contribute. -/
def chainDelay (c : ChainSpec) : Nat :=
  (c.middleDelays.map (fun d => (d : Nat))).sum + (c.lastDelay : Nat)

/-- A group is a list of chain specs. -/
def Group := List ChainSpec

/-- Delay of a group = delay of its head chain (well-defined under the
    uniformity hypothesis `h_uniform`); empty groups have delay 0. -/
def groupDelay (g : List ChainSpec) : Nat :=
  match g with
  | [] => 0
  | c :: _ => chainDelay c

/-! ## Indexing helpers (out-of-range access is junk data; bounds are hypotheses) -/

def defaultSpec : ChainSpec := { middleDelays := [], lastDelay := 2 }

def groupAt (groups : List Group) (gi : Nat) : List ChainSpec :=
  groups[gi]?.getD []

def chainAt (groups : List Group) (gi ci : Nat) : ChainSpec :=
  (groupAt groups gi)[ci]?.getD defaultSpec

/-- Output node name of chain `ci` in group `gi`. -/
def chainName (gi ci : Nat) : String := s!"{gi}:{ci}"

/-! ## Building the world -/

/-- Build the chains of one group; returns the new world and the observer node
    ids in chain order (observer of the chain built at input id `inp` is `inp + 1`). -/
def buildGroupChains (gi : Nat) (w : BasicRedstoneSim.World) (g : List ChainSpec) :
    BasicRedstoneSim.World × List Nat :=
  g.zipIdx.foldl (fun acc p =>
    let (c, ci) := p
    let (inp, w') := buildChain acc.1 (chainName gi ci) c
    (w', acc.2 ++ [inp + 1])) (w, [])

/-- Build all groups on `World.empty`; returns the world and, per group,
    the observer ids in chain order. -/
def buildGroups (groups : List Group) : BasicRedstoneSim.World × List (List Nat) :=
  groups.zipIdx.foldl (fun acc p =>
    let (g, gi) := p
    let (w', obs) := buildGroupChains gi acc.1 g
    (w', acc.2 ++ [obs])) (BasicRedstoneSim.World.empty, [])

/-! ## Group activation and simulation -/

/-- Fire observers directly (bypassing the queue), in list order. -/
def activateGroup (w : BasicRedstoneSim.World) (observers : List Nat) :
    BasicRedstoneSim.World :=
  observers.foldl (fun w nid => w.onScheduledTick nid) w

/-- One tick of the group simulation: log the tick; if some groups activate at
    this tick, first process up to `pos tick` pending events, then fire the
    active groups atomically in the order induced by `groupOrd`, then step to
    the next tick; otherwise just step to the next tick. -/
def gSimBody (actTick : Nat → Nat) (obsAll : List (List Nat))
    (groupOrd : List Nat) (withinOrd : Nat → List Nat) (pos : Nat → Nat)
    (w : BasicRedstoneSim.World) (_ : Nat) : BasicRedstoneSim.World :=
  let w := w.logOutput s!"tick {w.tick}"
  let active := groupOrd.filter (fun gi =>
    decide (gi < obsAll.length) && (actTick gi == w.tick))
  if active == [] then
    w.stepUntilNextTick
  else
    let w := processNEvents w (pos w.tick)
    let w := active.foldl (fun w gi =>
      let obs : List Nat := obsAll[gi]?.getD []
      let ordered := (withinOrd gi).foldl (fun acc ci =>
        match obs[ci]? with
        | some oid => acc ++ [oid]
        | none => acc) []
      activateGroup w ordered) w
    w.stepUntilNextTick

def gSimFoldl (actTick : Nat → Nat) (obsAll : List (List Nat))
    (groupOrd : List Nat) (withinOrd : Nat → List Nat) (pos : Nat → Nat)
    (w : BasicRedstoneSim.World) (n : Nat) : BasicRedstoneSim.World :=
  (List.range n).foldl (gSimBody actTick obsAll groupOrd withinOrd pos) w

/-- Run the group system through tick `T` (inclusive); returns the output log. -/
def groupSimulate (T : Nat) (groups : List Group) (actTick : Nat → Nat)
    (groupOrd : List Nat) (withinOrd : Nat → List Nat) (pos : Nat → Nat) :
    List String :=
  let (w₀, obsAll) := buildGroups groups
  (gSimFoldl actTick obsAll groupOrd withinOrd pos w₀ (T + 1)).outputLog

/-! ## Output order -/

def isOutputEntry (s : String) (gi ci : Nat) : Bool :=
  s == s!"{chainName gi ci}: 0" || s == s!"{chainName gi ci}: 15"

/-- Position of chain `(gi, ci)`'s output entry in the log, if present. -/
def outputPos (log : List String) (gi ci : Nat) : Option Nat :=
  findIdx? (fun s => isOutputEntry s gi ci) log

/-- Group `ga` precedes group `gb` on spec `s`: every s-instance of `ga`
    outputs before every s-instance of `gb`. -/
def groupBeforeSpec (log : List String) (groups : List Group)
    (ga gb : Nat) (s : ChainSpec) : Prop :=
  ∀ ca cb, ca < (groupAt groups ga).length → cb < (groupAt groups gb).length →
    chainAt groups ga ca = s → chainAt groups gb cb = s →
    ∃ p q, outputPos log ga ca = some p ∧ outputPos log gb cb = some q ∧ p < q

/-! ## Theorems -/

/-- **Clustering.** Run any group system in which every group activates at
    `T - groupDelay` (all last nodes light up at `T`), with arbitrary group
    order at equal ticks (`groupOrd`), arbitrary within-group firing order
    (`withinOrd`) and arbitrary pos-style insertion (`pos`). Then between any
    two outputs of chains with identical spec, only outputs of that same spec
    appear. -/
theorem group_output_clustering
    (groups : List Group)
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
    (pos : Nat → Nat) :
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
  sorry

/-- **Order preservation.** Under the same setup: if the instances of spec `sa`
    in group `ga` all output before the instances of `sa` in group `gb`
    (with `sa` present in both groups), then the same holds for every other
    spec `sb` — the relative order of two groups does not depend on the spec
    used to observe it. -/
theorem group_order_preservation
    (groups : List Group)
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
    (pos : Nat → Nat) :
    let log := groupSimulate T groups actTick groupOrd withinOrd pos
    ∀ ga gb sa sb,
      ga < groups.length → gb < groups.length → ga ≠ gb →
      (∃ ca, ca < (groupAt groups ga).length ∧ chainAt groups ga ca = sa) →
      (∃ cb, cb < (groupAt groups gb).length ∧ chainAt groups gb cb = sa) →
      groupBeforeSpec log groups ga gb sa →
      groupBeforeSpec log groups ga gb sb := by
  sorry

end GroupClustering
