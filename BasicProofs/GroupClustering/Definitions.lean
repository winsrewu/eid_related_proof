import BasicProofs.PrefixChain.Part17


open BasicRedstoneSim

/-! # Group clustering and order preservation — definitions

Chains are prefix chains as in `BasicProofs.PrefixChain`
(Input → Observer → [Repeater(-3, d_i)]* → Repeater(-1, d_last) → Output).

A **group** is a list of chains whose last nodes all light up at a common tick `T`
and whose activation-to-output delays are all equal. **Activating** a group at tick
`T - D` means directly enqueueing, for ALL of its observers, the observer's own
tick event (target = tick + 2, priority 0), in arbitrary order, **atomically**:
one group's observer events are enqueued consecutively, with no interleaved
enqueues from other groups and no queue processing in between. Between (atomic)
group activations, an arbitrary number of pending queue events may be processed
(pos-style insertion).

Modeling note (2026-08-05): atomicity is essential. If observer firings from
different groups may interleave arbitrarily, order preservation is FALSE:
with specs a = delays [2, 4] and b = delays [4, 2] (equal totals), groups
A = {a_A, b_A}, B = {a_B, b_B}, firing order a_A, a_B, b_B, b_A gives output
order a_A, a_B, b_B, b_A — so a orders AB while b orders BA.
-/

/-! ## Activation-to-output delay -/

/-- Activation-to-output delay under direct observer firing: the observer's
    own +2 tick event plus all repeater delays (equal to
    `ChainSpec.totalDelay`). -/
def chainDelay (c : ChainSpec) : Nat :=
  2 + (c.middleDelays.map (fun d => (d : Nat))).sum + (c.lastDelay : Nat)

/-- A group is a list of chain specs. -/
def GroupSpec := List ChainSpec

/-- Delay of a group = delay of its head chain (well-defined under the
    uniformity hypothesis `h_uniform`); empty groups have delay 0. -/
def groupDelay (g : List ChainSpec) : Nat :=
  match g with
  | [] => 0
  | c :: _ => chainDelay c

/-! ## Indexing helpers (out-of-range access is junk data; bounds are hypotheses) -/

def defaultSpec : ChainSpec := { middleDelays := [], lastDelay := 2 }

def groupAt (groups : List GroupSpec) (gi : Nat) : List ChainSpec :=
  groups[gi]?.getD []

def chainAt (groups : List GroupSpec) (gi ci : Nat) : ChainSpec :=
  (groupAt groups gi)[ci]?.getD defaultSpec

/-- Output node name of chain `ci` in group `gi`. -/
def chainName (gi ci : Nat) : String := s!"{gi}:{ci}"

/-! ## Building the world -/

/-- Build the chains of one group, naming them `gi:start`, `gi:start+1`, ...;
    returns the new world and the observer node ids in chain order
    (observer of the chain built at input id `inp` is `inp + 1`).
    `start` is a proof device: the real entry point uses `start := 0`, and
    induction over the group tail shifts it. -/
def buildGroupChainsFrom (gi start : Nat) (w : World) : List ChainSpec →
    World × List Nat
  | [] => (w, [])
  | c :: cs =>
    let w' := (buildChain w (chainName gi start) c).2
    let r := buildGroupChainsFrom gi (start + 1) w' cs
    (r.1, ((buildChain w (chainName gi start) c).1 + 1) :: r.2)

/-- Build the chains of one group; returns the new world and the observer node
    ids in chain order (observer of the chain built at input id `inp` is `inp + 1`). -/
def buildGroupChains (gi : Nat) (w : World) (g : List ChainSpec) : World × List Nat :=
  buildGroupChainsFrom gi 0 w g

/-- Build all groups on `w`, with group indices starting at `start`; returns
    the world and, per group, the observer ids in chain order. -/
def buildGroupsFrom (start : Nat) (w : World) : List GroupSpec →
    World × List (List Nat)
  | [] => (w, [])
  | g :: gs =>
    let w' := (buildGroupChains start w g).1
    let r := buildGroupsFrom (start + 1) w' gs
    (r.1, (buildGroupChains start w g).2 :: r.2)

/-- Build all groups on `World.empty`; returns the world and, per group,
    the observer ids in chain order. -/
def buildGroups (groups : List GroupSpec) : World × List (List Nat) :=
  buildGroupsFrom 0 World.empty groups

/-! ## Group activation and simulation -/

/-- Fire observers directly: enqueue each observer's own tick event
    (target = tick + 2, priority 0), in list order, without processing the
    queue. The observers then fire two ticks later through the normal queue. -/
def activateGroup (w : World) (observers : List Nat) : World :=
  observers.foldl (fun w nid =>
    w.scheduleEvent { targetTick := w.tick + 2, priority := 0, nodeId := nid }) w

/-- One burst phase: fire each active group atomically in turn. The list
    `pairs` is `active.zipIdx`, i.e. `(group index, burst position)` pairs.
    Before the k-th burst, process up to `(pos t)[k]` pending events
    (pos-style insertion between activations). -/
def gSimBurst (t : Nat) (obsAll : List (List Nat)) (withinOrd : Nat → List Nat)
    (pos : Nat → List Nat) (w : World) (pairs : List (Nat × Nat)) : World :=
  pairs.foldl (fun wAcc p =>
    let (gi, k) := p
    let wProc := processNEvents wAcc ((pos t)[k]?.getD 0)
    let obs : List Nat := obsAll[gi]?.getD []
    let ordered := (withinOrd gi).foldl (fun acc ci =>
      match obs[ci]? with
      | some oid => acc ++ [oid]
      | none => acc) []
    activateGroup wProc ordered) w

/-- One tick of the group simulation: log the tick; if some groups activate at
    this tick, fire them via `gSimBurst` (each atomically, in the order induced
    by `groupOrd`, with pos-style insertion between activations); then step to
    the next tick. Otherwise just step. -/
def gSimBody (actTick : Nat → Nat) (obsAll : List (List Nat))
    (groupOrd : List Nat) (withinOrd : Nat → List Nat) (pos : Nat → List Nat)
    (w : World) (_ : Nat) : World :=
  let w := w.logOutput s!"tick {w.tick}"
  let t := w.tick
  let active := groupOrd.filter (fun gi =>
    decide (gi < obsAll.length) && (actTick gi == t))
  if active == [] then
    w.stepUntilNextTick
  else
    (gSimBurst t obsAll withinOrd pos w active.zipIdx).stepUntilNextTick

def gSimFoldl (actTick : Nat → Nat) (obsAll : List (List Nat))
    (groupOrd : List Nat) (withinOrd : Nat → List Nat) (pos : Nat → List Nat)
    (w : World) (n : Nat) : World :=
  (List.range n).foldl (gSimBody actTick obsAll groupOrd withinOrd pos) w

/-- Run the group system through tick `T` (inclusive); returns the output log. -/
def groupSimulate (T : Nat) (groups : List GroupSpec) (actTick : Nat → Nat)
    (groupOrd : List Nat) (withinOrd : Nat → List Nat) (pos : Nat → List Nat) :
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
def groupBeforeSpec (log : List String) (groups : List GroupSpec)
    (ga gb : Nat) (s : ChainSpec) : Prop :=
  ∀ ca cb, ca < (groupAt groups ga).length → cb < (groupAt groups gb).length →
    chainAt groups ga ca = s → chainAt groups gb cb = s →
    ∃ p q, outputPos log ga ca = some p ∧ outputPos log gb cb = some q ∧ p < q
