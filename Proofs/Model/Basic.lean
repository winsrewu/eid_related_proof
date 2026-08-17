import BasicRedstoneSim.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Pairwise
import Mathlib.Data.List.Lemmas
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Convert
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push


open BasicRedstoneSim

/-! # No-group prefix-chain model — definitions

A chain is a prefix chain as in the retired `BasicProofs.PrefixChain`:
`Input → Observer → [Repeater(p_i, d_i)]* → Repeater(p_last, d_last) → Output`,
where every repeater carries its own priority (valid: `-3, -2, -1`) and delay
(valid: `2, 4, 6, 8`).

There is **no group**. Each chain activates individually: activating chain
`i` at tick `t` enqueues its observer's own tick event (target = `t + 2`,
priority `0`). Between any two consecutive activations an arbitrary number of
pending queue events may be processed (pos-style insertion), including between
same-spec chains that activate on the same tick.

All chains are assumed to output on a common tick `T`; chain `i` therefore
activates at tick `T - chainDelay (specs[i])`. `actOrd` is a global
permutation of the chain indices giving the activation order (only its
restriction to a single activation tick is physically observable). -/

/-! ## Valid delays and priorities -/

/-- Valid repeater delays in game ticks: 2, 4, 6, or 8. -/
def ValidDelay (d : PNat) : Prop := d = 2 ∨ d = 4 ∨ d = 6 ∨ d = 8

/-- Valid repeater priorities: -3, -2, or -1. -/
def ValidPriority (p : Int) : Prop := p = -3 ∨ p = -2 ∨ p = -1

/-- All delays in a valid chain are ≥ 2. -/
theorem ValidDelay.ge2 {d : PNat} (h : ValidDelay d) : (d : Nat) ≥ 2 := by
  rcases h with rfl | rfl | rfl | rfl <;> decide

/-- All valid delays are even. -/
theorem ValidDelay.even {d : PNat} (h : ValidDelay d) : (d : Nat) % 2 = 0 := by
  rcases h with rfl | rfl | rfl | rfl <;> decide

/-- Valid priorities are strictly negative. -/
theorem ValidPriority.neg {p : Int} (h : ValidPriority p) : p < 0 := by
  rcases h with rfl | rfl | rfl <;> decide

/-- Valid priorities are at least -3. -/
theorem ValidPriority.ge_neg3 {p : Int} (h : ValidPriority p) : p ≥ -3 := by
  rcases h with rfl | rfl | rfl <;> decide

/-- Valid priorities are below the queue sentinel 100. -/
theorem ValidPriority.lt100 {p : Int} (h : ValidPriority p) : p < 100 := by
  rcases h with rfl | rfl | rfl <;> decide

/-! ## Chain spec -/

/-- A prefix chain: Input → Observer → [Repeater(p_i, d_i)]* →
    Repeater(p_last, d_last) → Output. Every repeater carries its own
    priority (valid: -3, -2, -1) and delay (valid: 2, 4, 6, 8). -/
structure ChainSpec where
  middleDelays : List PNat
  middlePriorities : List Int
  lastDelay : PNat
  lastPriority : Int
  deriving BEq, DecidableEq

/-- The priority list matches the middle-delay list. -/
def ChainSpec.priLenOk (c : ChainSpec) : Prop :=
  c.middlePriorities.length = c.middleDelays.length

namespace ChainSpec

/-- Activation-to-output delay: the observer's +2 tick plus all repeater
    delays. -/
def totalDelay (c : ChainSpec) : Nat :=
  2 + (c.middleDelays.map (fun d => (d : Nat))).sum + (c.lastDelay : Nat)

end ChainSpec

/-- Activation-to-output delay; equal to `ChainSpec.totalDelay`. -/
def chainDelay (c : ChainSpec) : Nat := c.totalDelay

/-- A spec is valid when its priorities line up with its middle delays and
    every delay and priority is in range. -/
def ChainSpec.valid (c : ChainSpec) : Prop :=
  c.priLenOk ∧
  (∀ d ∈ c.middleDelays, ValidDelay d) ∧ ValidDelay c.lastDelay ∧
  (∀ p ∈ c.middlePriorities, ValidPriority p) ∧ ValidPriority c.lastPriority

/-- Out-of-range default spec (junk data; bounds are hypotheses). -/
def defaultSpec : ChainSpec :=
  { middleDelays := [], middlePriorities := [], lastDelay := 2,
    lastPriority := -1 }

/-- The spec of chain `i` (out-of-range gives `defaultSpec`). -/
def specAt (specs : List ChainSpec) (i : Nat) : ChainSpec :=
  specs[i]?.getD defaultSpec

/-! ## Building chains in a world -/

/-- Helper: create a repeater NodeData with the given delay and priority. -/
def mkRepNode (delay : PNat) (priority : Int) : NodeData :=
  { kind := NodeKind.repeater delay priority, sigLevel := 0, inputs := [],
    outputs := [] }

/-- One step of the buildChain foldl: add a repeater node. -/
def repFoldlStep (acc : List Nat × World) (dp : PNat × Int) : List Nat × World :=
  (acc.1 ++ [acc.2.nextId], (acc.2.addNode (mkRepNode dp.1 dp.2)).2)

/-- The addNode phase of buildChain: creates all nodes, returns
    (inputId, w_pre, chainIds).

    Written with projection-lets (not destructuring-lets) so that the lets
    reduce under `dsimp [buildChainPre]` WITHOUT unfolding `World.addNode`;
    this keeps the `getNode_addNode_*` rewrite patterns usable when proving
    node-kind lookups. Definitionally equal to the destructuring-let form. -/
def buildChainPre (w : World) (name : String) (c : ChainSpec) :
    Nat × World × List Nat :=
  let rIn := w.addNode
    { kind := .input, sigLevel := 0, inputs := [], outputs := [] }
  let inputId := rIn.1
  let rObs := rIn.2.addNode
    { kind := .observer, sigLevel := 0, inputs := [], outputs := [] }
  let obsId := rObs.1
  let repRes := (c.middleDelays.zip c.middlePriorities).foldl
    repFoldlStep ([], rObs.2)
  let repIds := repRes.1
  let rLast := repRes.2.addNode
    { kind := .repeater c.lastDelay c.lastPriority, sigLevel := 0,
      inputs := [], outputs := [] }
  let lastRepId := rLast.1
  let rOut := rLast.2.addNode
    { kind := .output name, sigLevel := 0, inputs := [], outputs := [] }
  let outId := rOut.1
  (inputId, rOut.2, [inputId, obsId] ++ repIds ++ [lastRepId, outId])

/-- Build a prefix chain in the world; returns (inputId, world). The chain's
    observer is node `inputId + 1`. -/
def buildChain (w : World) (name : String) (c : ChainSpec) : Nat × World :=
  let (inputId, wPre, chainIds) := buildChainPre w name c
  (inputId, connectChain wPre chainIds)

/-- Output node name of chain `i`. -/
def chainName (i : Nat) : String := toString i

/-- Build the chains in `specs` one after another; returns the new world and
    the observer node ids in chain-index order (observer of the chain built
    at input id `inp` is `inp + 1`). `start` is a proof device: the real
    entry point uses `start := 0`. -/
def buildChainsFrom (start : Nat) (w : World) : List ChainSpec →
    World × List Nat
  | [] => (w, [])
  | c :: cs =>
    let w' := (buildChain w (chainName start) c).2
    let r := buildChainsFrom (start + 1) w' cs
    (r.1, ((buildChain w (chainName start) c).1 + 1) :: r.2)

/-- Build all chains on `World.empty`; returns the world and the observer
    node ids in chain-index order. -/
def buildChains (specs : List ChainSpec) : World × List Nat :=
  buildChainsFrom 0 World.empty specs

/-! ## Processing pending events (pos-style insertion) -/

/-- Process up to `n` events at the current tick. -/
def processNEvents (w : World) (n : Nat) : World :=
  match n with
  | 0 => w
  | n' + 1 =>
    match w.step with
    | none => w
    | some w' => processNEvents w' n'

/-! ## Activation and simulation driver -/

/-- Fire one chain's observer directly: enqueue its own tick event
    (target = tick + 2, priority 0). -/
def activateChain (w : World) (obs : Nat) : World :=
  w.scheduleEvent { targetTick := w.tick + 2, priority := 0, nodeId := obs }

/-- One burst phase: fire each active chain in turn. `pairs` is
    `active.zipIdx`, i.e. `(chain index, activation position)` pairs. Before
    the k-th activation, process `pos t k` pending events (pos-style
    insertion between activations). -/
def simBurst (t : Nat) (observers : List Nat) (pos : Nat → Nat → Nat)
    (w : World) (pairs : List (Nat × Nat)) : World :=
  pairs.foldl (fun wAcc p =>
    let (i, k) := p
    let wProc := processNEvents wAcc (pos t k)
    match observers[i]? with
    | some oid => activateChain wProc oid
    | none => wProc) w

/-- One tick of the no-group simulation: log the tick; fire every chain whose
    activation tick is `t` (in `actOrd` order, with pos-style insertion
    between activations); then step to the next tick. -/
def simBody (actTick : Nat → Nat) (observers : List Nat) (actOrd : List Nat)
    (pos : Nat → Nat → Nat) (w : World) (_ : Nat) : World :=
  let w := w.logOutput s!"tick {w.tick}"
  let t := w.tick
  let active := actOrd.filter (fun i =>
    decide (i < observers.length) && (actTick i == t))
  (simBurst t observers pos w active.zipIdx).stepUntilNextTick

/-- Iterate `simBody` over `List.range n`. -/
def simFoldl (actTick : Nat → Nat) (observers : List Nat) (actOrd : List Nat)
    (pos : Nat → Nat → Nat) (w : World) (n : Nat) : World :=
  (List.range n).foldl (simBody actTick observers actOrd pos) w

/-- The activation tick of chain `i` when every chain outputs on tick `T`. -/
def actTickOf (T : Nat) (specs : List ChainSpec) (i : Nat) : Nat :=
  T - chainDelay (specAt specs i)

/-- Run the no-group system through tick `T` (inclusive); returns the output
    log. -/
def simulate (T : Nat) (specs : List ChainSpec) (actOrd : List Nat)
    (pos : Nat → Nat → Nat) : List String :=
  let (w₀, observers) := buildChains specs
  (simFoldl (actTickOf T specs) observers actOrd pos w₀ (T + 1)).outputLog

/-! ## Output and activation positions -/

/-- Is `s` the output-log entry of chain `i`? -/
def isOutputEntry (s : String) (i : Nat) : Bool :=
  s == s!"{chainName i}: 0" || s == s!"{chainName i}: 15"

/-- First index in `log` matching `p`, if any. -/
def findIdx? {α : Type} (p : α → Bool) : List α → Option Nat
  | [] => none
  | x :: xs => if p x then some 0 else (findIdx? p xs).map (fun n => n + 1)

/-- Position of chain `i`'s output entry in the log, if present. -/
def outputPos (log : List String) (i : Nat) : Option Nat :=
  findIdx? (fun s => isOutputEntry s i) log

/-- Activation position of chain `i` in the global activation order.
    Under the permutation hypothesis `i` occurs exactly once, so this is the
    genuine index; the `getD 0` default is junk data otherwise. -/
def actPos (actOrd : List Nat) (i : Nat) : Nat :=
  (findIdx? (fun x => x == i) actOrd).getD 0
