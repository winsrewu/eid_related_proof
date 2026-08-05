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

/-! # Prefix Chain Activation Order Theorem -/

/-- Valid repeater delays in game ticks: 2, 4, 6, or 8. -/
def ValidDelay (d : PNat) : Prop := d = 2 ∨ d = 4 ∨ d = 6 ∨ d = 8

/-- All delays in a valid chain are ≥ 2. -/
theorem ValidDelay.ge2 {d : PNat} (h : ValidDelay d) : (d : Nat) ≥ 2 := by
  rcases h with rfl | rfl | rfl | rfl <;> decide

/-- All valid delays are even. -/
theorem ValidDelay.even {d : PNat} (h : ValidDelay d) : (d : Nat) % 2 = 0 := by
  rcases h with rfl | rfl | rfl | rfl <;> decide

/-- A prefix chain: Input → Observer → [Repeater(-3, d_i)]* → Repeater(-1, d_last) → Output -/
structure ChainSpec where
  middleDelays : List PNat
  lastDelay : PNat

namespace ChainSpec

def totalDelay (c : ChainSpec) : Nat :=
  2 + (c.middleDelays.map (fun d => (d : Nat))).sum + (c.lastDelay : Nat)

def reverseDelays (c : ChainSpec) : List PNat :=
  c.lastDelay :: c.middleDelays.reverse

end ChainSpec

/-- Sum of a list of even numbers is even. -/
theorem List.sum_even (l : List Nat) (h : ∀ x ∈ l, x % 2 = 0) : l.sum % 2 = 0 := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    have h_hd : hd % 2 = 0 := h hd (List.mem_cons.mpr (Or.inl rfl))
    have h_tl : ∀ x ∈ tl, x % 2 = 0 := fun x hx => h x (List.mem_cons.mpr (Or.inr hx))
    have h_ih : tl.sum % 2 = 0 := ih h_tl
    rw [List.sum_cons, Nat.add_mod, h_hd, h_ih]

/-- `List.flatMap (fun a => [f a]) l = l.map f`. -/
theorem List.flatMap_singleton_eq_map {α β : Type} (l : List α) (f : α → β) :
    l.flatMap (fun a => [f a]) = l.map f := by
  induction l with
  | nil => rfl
  | cons hd tl ih => simp [List.flatMap_cons, ih]

/-- totalDelay is even when all delays are valid. -/
theorem ChainSpec.totalDelay_even (c : ChainSpec)
    (h_middle : ∀ d ∈ c.middleDelays, ValidDelay d) (h_last : ValidDelay c.lastDelay) :
    ChainSpec.totalDelay c % 2 = 0 := by
  have h_last' : (c.lastDelay : Nat) % 2 = 0 := ValidDelay.even h_last
  have h_sum : (c.middleDelays.map PNat.val).sum % 2 = 0 :=
    List.sum_even _ (fun x hx => by
      rcases List.mem_map.1 hx with ⟨d, hd, rfl⟩
      exact ValidDelay.even (h_middle d hd))
  dsimp [ChainSpec.totalDelay]
  rw [List.flatMap_singleton_eq_map]
  have h_id : (fun (d : Nat) => d) = id := rfl
  rw [h_id, List.map_id]
  omega

/-- Helper: create a repeater NodeData with the given delay and position -3. -/
def mkRepNode (delay : PNat) : NodeData :=
  { kind := NodeKind.repeater delay (-3), sigLevel := 0, inputs := [], outputs := [] }

/-- One step of the buildChain foldl: add a repeater node. -/
def repFoldlStep (acc : List Nat × World) (delay : PNat) : List Nat × World :=
  (acc.1 ++ [acc.2.nextId], (acc.2.addNode (mkRepNode delay)).2)

/-- The addNode phase of buildChain: creates all nodes, returns (inputId, w_pre, chainIds). -/
def buildChainPre (w : World) (name : String) (c : ChainSpec) : Nat × World × List Nat :=
  let (inputId, w) := w.addNode
    { kind := .input, sigLevel := 0, inputs := [], outputs := [] }
  let (obsId, w) := w.addNode
    { kind := .observer, sigLevel := 0, inputs := [], outputs := [] }
  let (repIds, w) := c.middleDelays.foldl repFoldlStep ([], w)
  let (lastRepId, w) := w.addNode
    { kind := .repeater c.lastDelay (-1), sigLevel := 0, inputs := [], outputs := [] }
  let (outId, w) := w.addNode
    { kind := .output name, sigLevel := 0, inputs := [], outputs := [] }
  (inputId, w, [inputId, obsId] ++ repIds ++ [lastRepId, outId])

/-- Build a prefix chain in the world. -/
def buildChain (w : World) (name : String) (c : ChainSpec) : Nat × World :=
  let (inputId, w_pre, chainIds) := buildChainPre w name c
  (inputId, connectChain w_pre chainIds)

/-- Process up to `n` events at the current tick. -/
def processNEvents (w : World) (n : Nat) : World :=
  match n with
  | 0 => w
  | n' + 1 =>
    match w.step with
    | none => w
    | some w' => processNEvents w' n'

/-- The simulation foldl body. -/
def simBody (t1 t2 pos in1 in2 : Nat) (w : World) (_ : Nat) : World :=
  let w := w.logOutput s!"tick {w.tick}"
  let w := if w.tick == t1 then w.setInput in1 15 else w
  if w.tick == t2 then
    let w := processNEvents w pos
    let w := w.setInput in2 15
    w.stepUntilNextTick
  else
    w.stepUntilNextTick

def simulateWithInsertion (c1 c2 : ChainSpec) (t1 t2 : Nat) (pos : Nat) : List String :=
  let w := World.empty
  let (in1, w) := buildChain w "A" c1
  let (in2, w) := buildChain w "B" c2
  let totalTicks := max (t1 + c1.totalDelay) (t2 + c2.totalDelay) + 1
  let w := (List.range totalTicks).foldl (simBody t1 t2 pos in1 in2) w
  w.outputLog

def findIdx? {α : Type} (p : α → Bool) : List α → Option Nat
  | [] => none
  | x :: xs => if p x then some 0 else (findIdx? p xs).map (fun n => n + 1)

def lexGt : List Nat → List Nat → Bool
  | [], [] => false
  | [], _  => false
  | _,  [] => true
  | x :: xs, y :: ys =>
    match compare x y with
    | .gt => true
    | .lt => false
    | .eq => lexGt xs ys

def aActivatesFirst (log : List String) : Option Bool :=
  let aIdx := findIdx? (fun s => s == "A: 0" || s == "A: 15") log
  let bIdx := findIdx? (fun s => s == "B: 0" || s == "B: 15") log
  match aIdx, bIdx with
  | some a, some b => some (a < b)
  | _, _ => none

/-! ## Abstract event schedule -/

structure AbsEvent where
  tick : Nat
  priority : Int
  chain : Nat
  deriving Repr, BEq, Inhabited

def mkEvt (tick : Nat) (pri : Int) (chainId : Nat) : AbsEvent :=
  { tick := tick, priority := pri, chain := chainId }

def chainSchedule (c : ChainSpec) (t : Nat) (chainId : Nat) : List AbsEvent :=
  let obsTick := t + 2
  let (evs, last) := (c.middleDelays.map (↑·)).foldl (fun (acc, prev) d =>
    (acc ++ [mkEvt (prev + d) (-3) chainId], prev + d)
  ) ([mkEvt obsTick 0 chainId], obsTick)
  evs ++ [mkEvt (last + ↑c.lastDelay) (-1) chainId]

/-! ## Cumulative sums helper

`cumSums [d₁, …, dₙ] s = [s, s+d₁, s+d₁+d₂, …, s+Σdᵢ]` -/

def cumSums : List Nat → Nat → List Nat
  | [], start => [start]
  | d :: rest, start => start :: cumSums rest (start + d)

/-- Every element of `cumSums delays start` is ≥ `start`. -/
theorem cumSums_ge_start (delays : List Nat) (start : Nat) :
    ∀ x ∈ cumSums delays start, x ≥ start := by
  induction delays generalizing start with
  | nil => simp [cumSums]
  | cons d rest ih =>
    simp only [cumSums]
    intro x hx
    simp only [List.mem_cons] at hx
    cases hx with
    | inl h => rw [h]
    | inr h =>
      have := ih (start + d) x h
      omega

/-- `cumSums` with delays ≥ 2 is strictly increasing (`Pairwise (· < ·)`). -/
theorem cumSums_pairwise_lt (delays : List Nat) (start : Nat)
    (h : ∀ d ∈ delays, d ≥ 2) :
    (cumSums delays start).Pairwise (· < ·) := by
  induction delays generalizing start with
  | nil => simp [cumSums]
  | cons d rest ih =>
    simp [cumSums]
    have hd : d ≥ 2 := h d (by simp)
    have hrest : ∀ d ∈ rest, d ≥ 2 := fun d hd' => h d (by simp [hd'])
    constructor
    · intro x hx
      have := cumSums_ge_start rest (start + d) x hx
      omega
    · exact ih (start + d) hrest

/-- The foldl that computes cumulative ticks. -/
def foldlTicks (delays : List Nat) (start : Nat) : List Nat × Nat :=
  delays.foldl (fun (ts, prev) d => (ts ++ [prev + d], prev + d)) ([start], start)

/-- The tick list for a chain. -/
def chainTickList (c : ChainSpec) (t : Nat) : List Nat :=
  let (ticks, last) := foldlTicks (c.middleDelays.map (↑·)) (t + 2)
  ticks ++ [last + ↑c.lastDelay]

/-- The `.tick` projection commutes with the schedule-building fold:
for any initial event list `evs₀` whose tick projection is `ts₀`,
running the AbsEvent-fold and the Nat-fold in parallel keeps them in sync. -/
theorem foldl_tick_proj (delays : List Nat)
    (evs₀ : List AbsEvent) (ts₀ : List Nat) (start : Nat)
    (h : evs₀.map (·.tick) = ts₀) :
    (delays.foldl (fun ((acc, prev) : List AbsEvent × Nat) d =>
      (acc ++ [mkEvt (prev + d) (-3) 0], prev + d)) (evs₀, start)).1.map (·.tick) =
    (delays.foldl (fun ((ts, prev) : List Nat × Nat) d =>
      (ts ++ [prev + d], prev + d)) (ts₀, start)).1 ∧
    (delays.foldl (fun ((acc, prev) : List AbsEvent × Nat) d =>
      (acc ++ [mkEvt (prev + d) (-3) 0], prev + d)) (evs₀, start)).2 =
    (delays.foldl (fun ((ts, prev) : List Nat × Nat) d =>
      (ts ++ [prev + d], prev + d)) (ts₀, start)).2 := by
  induction delays generalizing evs₀ ts₀ start with
  | nil => simp [h]
  | cons d rest ih =>
    simp only [List.foldl_cons, mkEvt]
    apply ih
    simp [List.map_append, h]

/-- `List.flatMap` with singleton is the identity. -/
theorem flatMap_singleton_id (l : List Nat) :
    List.flatMap (fun a => [a]) l = l := by
  induction l with
  | nil => rfl
  | cons hd tl ih => simp [List.flatMap_cons, ih]

/-- `List.map` with PNat coercion equals `List.flatMap` with singleton. -/
theorem map_pnat_eq_flatMap (l : List PNat) :
    List.map (fun x => (x : Nat)) l = List.flatMap (fun a => [(a : Nat)]) l := by
  induction l with
  | nil => rfl
  | cons d rest ih =>
    simp [List.map_cons, List.flatMap_cons]

/-- Same as `map_pnat_eq_flatMap` but with `↑` notation to match goal syntax. -/
theorem map_pnat_eq_flatMap' (l : List PNat) :
    List.map (fun x : PNat => ↑x) l = List.flatMap (fun a => [↑a]) l := by
  convert map_pnat_eq_flatMap l
  simp []

/-- Same but without type annotation on lambda, to match `fun x => ↑x` syntax. -/
theorem map_pnat_eq_flatMap'' (l : List PNat) :
    List.map (fun x => ↑x) l = List.flatMap (fun a => [↑a]) l :=
  map_pnat_eq_flatMap' l

/-- chainSchedule's ticks match chainTickList. -/
theorem chainSchedule_ticks_eq (c : ChainSpec) (t : Nat) :
    (chainSchedule c t 0).map (·.tick) = chainTickList c t := by
  have h := foldl_tick_proj (c.middleDelays.map (↑·))
    [mkEvt (t + 2) 0 0] [t + 2] (t + 2) (by simp [mkEvt])
  simp only [mkEvt] at h
  unfold chainSchedule chainTickList foldlTicks
  dsimp only [mkEvt]
  -- Split List.map over ++ explicitly
  rw [List.map_append]
  simp only [List.map_cons, List.map_nil]
  -- Goal: List.map (·.tick) (AbsFoldl(...)).1 ++ [AbsFoldl(...).2 + ↑c.lastDelay] =
  --       NatFoldl(...).1 ++ [NatFoldl(...).2 + ↑c.lastDelay]
  congr 1
  · convert h.1
    induction c.middleDelays with
    | nil => rfl
    | cons d rest ih =>
      rw [List.map_cons]
      conv => rhs; arg 2; dsimp
      rw [List.flatMap_cons]
      dsimp at ih
      simp [ih]
  · congr 1; congr 1
    convert h.2
    induction c.middleDelays with
    | nil => rfl
    | cons d rest ih =>
      rw [List.map_cons]
      conv => rhs; arg 2; dsimp
      rw [List.flatMap_cons]
      dsimp at ih
      simp [ih]

/-- The tick-fold's `.1` component prepends `ts₀` to the result starting from `[]`. -/
theorem foldl_fst_append (delays : List Nat) (ts₀ : List Nat) (start : Nat) :
    (delays.foldl (fun ((ts, prev) : List Nat × Nat) d => (ts ++ [prev + d], prev + d)) (ts₀, start)).1 =
    ts₀ ++ (delays.foldl (fun ((ts, prev) : List Nat × Nat) d => (ts ++ [prev + d], prev + d)) ([], start)).1 := by
  induction delays generalizing ts₀ start with
  | nil => simp
  | cons d rest ih =>
    simp [List.foldl_cons]
    rw [ih (ts₀ ++ [start + d]) (start + d), ih [start + d] (start + d)]
    simp [List.append_assoc]

/-- The tick-fold's `.2` component is independent of the initial `.1`. -/
theorem foldl_snd_indep (delays : List Nat) (ts₀ : List Nat) (start : Nat) :
    (delays.foldl (fun ((ts, prev) : List Nat × Nat) d => (ts ++ [prev + d], prev + d)) (ts₀, start)).2 =
    (delays.foldl (fun ((ts, prev) : List Nat × Nat) d => (ts ++ [prev + d], prev + d)) ([], start)).2 := by
  induction delays generalizing ts₀ start with
  | nil => simp
  | cons d rest ih =>
    simp [List.foldl_cons]
    rw [ih (ts₀ ++ [start + d]) (start + d), ih [start + d] (start + d)]

/-- The tick-fold's `.2` equals `start + sum`. -/
theorem foldl_snd_eq_sum (delays : List Nat) (start : Nat) :
    (delays.foldl (fun ((ts, prev) : List Nat × Nat) d => (ts ++ [prev + d], prev + d)) ([], start)).2 =
    start + delays.sum := by
  induction delays generalizing start with
  | nil => simp
  | cons d rest ih =>
    simp [List.foldl_cons]
    rw [foldl_snd_indep rest [start + d] (start + d), ih (start + d)]
    omega

/-- The tick-fold from `[]` produces a strictly increasing list whose elements are all > start. -/
theorem foldl_from_nil_props (delays : List Nat) (start : Nat)
    (h : ∀ d ∈ delays, d ≥ 2) :
    (delays.foldl (fun ((ts, prev) : List Nat × Nat) d => (ts ++ [prev + d], prev + d)) ([], start)).1.Pairwise (· < ·) ∧
    ∀ x ∈ (delays.foldl (fun ((ts, prev) : List Nat × Nat) d => (ts ++ [prev + d], prev + d)) ([], start)).1, x > start := by
  induction delays generalizing start with
  | nil => simp
  | cons d rest ih =>
    simp [List.foldl_cons]
    have hd : d ≥ 2 := h d (by simp)
    have hrest : ∀ d ∈ rest, d ≥ 2 := fun d hd' => h d (by simp [hd'])
    have ih' := ih (start + d) hrest
    have h_app := foldl_fst_append rest [start + d] (start + d)
    constructor
    · rw [h_app]
      apply List.pairwise_append.mpr
      constructor
      · simp
      · constructor
        · exact ih'.1
        · intro a ha b hb
          simp at ha; rw [ha]
          have := ih'.2 b hb
          omega
    · rw [h_app]
      intro x hx
      simp [] at hx
      cases hx with
      | inl h => rw [h]; omega
      | inr h =>
        have := ih'.2 x h
        omega

/-- foldlTicks produces strictly increasing ticks, correct last, and all ≥ start. -/
theorem foldlTicks_props (delays : List Nat) (start : Nat)
    (h : ∀ d ∈ delays, d ≥ 2) :
    (foldlTicks delays start).1.Pairwise (· < ·) ∧
    (foldlTicks delays start).2 = start + delays.sum ∧
    ∀ x ∈ (foldlTicks delays start).1, x ≥ start := by
  dsimp [foldlTicks]
  have h_app := foldl_fst_append delays [start] start
  have h_snd := foldl_snd_indep delays [start] start
  have h_sum := foldl_snd_eq_sum delays start
  have h_nil := foldl_from_nil_props delays start h
  simp only at h_app h_snd h_sum
  constructor
  · -- Pairwise (· < ·)
    rw [h_app]
    apply List.pairwise_append.mpr
    constructor
    · simp
    · constructor
      · exact h_nil.1
      · intro a ha b hb
        simp at ha; rw [ha]
        have := h_nil.2 b hb
        omega
  · constructor
    · -- .2 = start + sum
      rw [h_snd, h_sum]
    · -- ∀ x ∈ .1, x ≥ start
      rw [h_app]
      intro x hx
      simp [] at hx
      cases hx with
      | inl h => rw [h]
      | inr h =>
        have := h_nil.2 x h
        omega

/-- Every tick in `.1` is ≤ the final accumulated value `.2`. -/
theorem foldlTicks_all_le_last (delays : List Nat) (start : Nat) :
    ∀ x ∈ (foldlTicks delays start).1, x ≤ (foldlTicks delays start).2 := by
  suffices h : ∀ (ts : List Nat) (prev : Nat), (∀ x ∈ ts, x ≤ prev) →
    ∀ x ∈ (delays.foldl (fun (x : List Nat × Nat) d => (x.1 ++ [x.2 + d], x.2 + d)) (ts, prev)).1,
    x ≤ (delays.foldl (fun (x : List Nat × Nat) d => (x.1 ++ [x.2 + d], x.2 + d)) (ts, prev)).2 by
    have := h [start] start (by simp)
    simpa [foldlTicks] using this
  induction delays with
  | nil => simp
  | cons d rest ih =>
    intro ts prev h_inv
    simp only [List.foldl_cons]
    apply ih (ts ++ [prev + d]) (prev + d)
    intro x hx
    simp [List.mem_append] at hx
    cases hx with
    | inl h => exact Nat.le_trans (h_inv x h) (by omega)
    | inr h => omega

/-- chainTickList is strictly increasing for valid delays. -/
theorem chainTickList_pairwise_lt (c : ChainSpec) (t : Nat)
    (h_middle : ∀ d ∈ c.middleDelays, (d : Nat) ≥ 2)
    (h_last : (c.lastDelay : Nat) ≥ 2) :
    (chainTickList c t).Pairwise (· < ·) := by
  have h_mid : ∀ d ∈ c.middleDelays.map (fun d => (d : Nat)), d ≥ 2 := by
    intro d hd
    obtain ⟨d₀, hd₀, h_eq⟩ : ∃ d₀ : PNat, d₀ ∈ c.middleDelays ∧ d = (d₀ : Nat) := by
      simpa using hd
    rw [h_eq]
    exact h_middle d₀ hd₀
  have h := foldlTicks_props (c.middleDelays.map (↑·)) (t + 2) h_mid
  dsimp only [chainTickList, foldlTicks]
  -- Don't simp - just use h directly
  apply List.pairwise_append.mpr
  constructor
  · exact h.1
  · constructor
    · simp
    · intro a ha b hb
      simp at hb; rw [hb]
      have := foldlTicks_all_le_last (c.middleDelays.map (↑·)) (t + 2) a
        (by simpa [foldlTicks] using ha)
      simp [foldlTicks] at this
      omega

/-- The ticks in a chain schedule are strictly increasing. -/
theorem chainSchedule_ticks_strictMono (c : ChainSpec) (t : Nat)
    (h_middle : ∀ d ∈ c.middleDelays, ValidDelay d)
    (h_last : ValidDelay c.lastDelay) :
    ((chainSchedule c t 0).map (·.tick)).Pairwise (· < ·) := by
  rw [chainSchedule_ticks_eq]
  exact chainTickList_pairwise_lt c t
    (fun d hd => ValidDelay.ge2 (h_middle d hd))
    (ValidDelay.ge2 h_last)

/-- A prefix chain with valid delays has at most one event per tick. -/
theorem chainSchedule_nodup_ticks (c : ChainSpec) (t : Nat)
    (h_middle : ∀ d ∈ c.middleDelays, ValidDelay d)
    (h_last : ValidDelay c.lastDelay) :
    ((chainSchedule c t 0).map (·.tick)).Nodup :=
  (chainSchedule_ticks_strictMono c t h_middle h_last).nodup

/-- The activation tick of a chain. -/
def activationTick (c : ChainSpec) (t : Nat) : Nat :=
  t + c.totalDelay

/-- Observer priority (0) is strictly greater than repeater priorities (-3, -1). -/
theorem observer_priority_gt_repeater :
    (0 : Int) > -3 ∧ (0 : Int) > -1 := by
  constructor <;> omega

/-! ## Simulation lemmas -/

/-- `stepUntilNextTick` with no available events just advances the tick. -/
theorem stepUntilNextTick_of_step_none (w : World) (h : w.step = none) :
    w.stepUntilNextTick = { w with tick := w.tick + 1 } := by
  rw [World.stepUntilNextTick, h]

/-- `processNEvents w n` followed by `stepUntilNextTick` equals
`stepUntilNextTick`: both drain all events at the current tick. -/
theorem processNEvents_stepUntilNextTick_eq (w : World) (n : Nat) :
    (processNEvents w n).stepUntilNextTick = w.stepUntilNextTick := by
  induction n generalizing w with
  | zero => simp [processNEvents]
  | succ n' ih =>
    simp only [processNEvents]
    cases h : w.step with
    | none =>
      rw [stepUntilNextTick_of_step_none w h]
    | some w' =>
      have h_eq : w.stepUntilNextTick = w'.stepUntilNextTick := by
        rw [World.stepUntilNextTick, h]
      rw [ih w', h_eq]

/-! ### Layer 1: Tick tracking -/

/-- `onNeighborUpdate` preserves the tick. -/
theorem World.onNeighborUpdate_tick (w : World) (id : Nat) :
    (w.onNeighborUpdate id).tick = w.tick := by
  unfold World.onNeighborUpdate
  split
  · rfl
  · split
    · rfl
    · rfl
    · rfl
    · rfl

/-- A foldl of `onNeighborUpdate` preserves the tick. -/
theorem foldl_onNeighborUpdate_tick (l : List Nat) (w : World) :
    (l.foldl (fun w' outId => w'.onNeighborUpdate outId) w).tick = w.tick := by
  induction l generalizing w with
  | nil => rfl
  | cons hd tl ih => simp [List.foldl_cons]; rw [ih, World.onNeighborUpdate_tick]

/-- `notifyOutputs` preserves the tick. -/
theorem World.notifyOutputs_tick (w : World) (id : Nat) :
    (w.notifyOutputs id).tick = w.tick := by
  unfold World.notifyOutputs
  split
  · rfl
  · exact foldl_onNeighborUpdate_tick _ _

/-- `setInput` preserves the tick. -/
theorem World.setInput_tick (w : World) (id : Nat) (level : Nat) :
    (w.setInput id level).tick = w.tick := by
  dsimp [World.setInput]; rw [World.notifyOutputs_tick, World.updateNode_tick]

/-- `onScheduledTick` preserves the tick. -/
theorem World.onScheduledTick_tick (w : World) (id : Nat) :
    (w.onScheduledTick id).tick = w.tick := by
  unfold World.onScheduledTick
  split
  · rfl
  · split
    · dsimp [World.updateNode]; exact World.notifyOutputs_tick _ _
    · dsimp [World.updateNode]; exact World.notifyOutputs_tick _ _
    · rfl

/-- `popNextEvent` preserves the tick in its returned world. -/
theorem World.popNextEvent_tick (w : World) :
    ∀ ev w', w.popNextEvent = some (ev, w') → w'.tick = w.tick := by
  intro ev w' h
  unfold World.popNextEvent at h
  dsimp (config := { zeta := true }) at h
  split at h <;> try contradiction
  · split at h <;> try contradiction
    · rw [Option.some_inj, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      rfl

/-- `World.step` preserves the tick. -/
theorem World.step_tick (w : World) :
    ∀ w', w.step = some w' → w'.tick = w.tick := by
  intro w' h
  unfold World.step at h
  cases h_pop : w.popNextEvent with
  | none => simp [h_pop] at h
  | some p =>
    rcases p with ⟨ev, w''⟩
    simp [h_pop] at h
    rw [← h, World.onScheduledTick_tick, World.popNextEvent_tick w ev w'' h_pop]

/-- `stepUntilNextTick` always increments the tick by exactly 1. -/
theorem World.tick_stepUntilNextTick (w : World) :
    (w.stepUntilNextTick).tick = w.tick + 1 := by
  induction w using World.stepUntilNextTick.induct with
  | case1 x h =>
    rw [World.stepUntilNextTick, h]
  | case2 x w' h ih =>
    rw [World.stepUntilNextTick, h, ih, World.step_tick x w' h]

/-- `processNEvents` preserves the tick. -/
theorem processNEvents_tick (w : World) (n : Nat) :
    (processNEvents w n).tick = w.tick := by
  induction n generalizing w with
  | zero => rfl
  | succ n' ih =>
    simp only [processNEvents]
    cases h : w.step with
    | none => rfl
    | some w' => rw [ih w', World.step_tick w w' h]

/-! ### Layer 2: setInput scheduling -/

/-- `onNeighborUpdate` only appends events at ticks > w.tick, given delay ≥ 2 for repeaters. -/
theorem World.onNeighborUpdate_events_future (w : World) (id : Nat)
    (h_delay : ∀ nd, w.getNode id = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2) :
    ∀ ev ∈ (w.onNeighborUpdate id).events, ev ∉ w.events → ev.targetTick > w.tick := by
  cases h_getNode : w.getNode id with
  | none =>
    simp [World.onNeighborUpdate, h_getNode]
    intro ev h h'; contradiction
  | some nd =>
    cases h_kind : nd.kind with
    | repeater delay priority =>
      simp [World.onNeighborUpdate, h_getNode, h_kind, World.scheduleEvent_events,
            List.mem_append]
      intro ev h_ev h_new
      cases h_ev with
      | inl h => contradiction
      | inr h =>
        have h_tick : ev.targetTick = w.tick + (delay : Nat) := by rw [h]
        rw [h_tick]
        have hd : (delay : Nat) ≥ 2 := h_delay nd h_getNode delay priority h_kind
        omega
    | observer =>
      simp [World.onNeighborUpdate, h_getNode, h_kind, World.scheduleEvent_events,
            List.mem_append]
      intro ev h_ev h_new
      cases h_ev with
      | inl h => contradiction
      | inr h =>
        have h_tick : ev.targetTick = w.tick + 2 := by rw [h]
        rw [h_tick]; omega
    | output name =>
      simp [World.onNeighborUpdate, h_getNode, h_kind, World.logOutput_events]
      intro ev h h'; contradiction
    | input =>
      simp [World.onNeighborUpdate, h_getNode, h_kind]
      intro ev h h'; contradiction

/-- Stronger version: new events from `onNeighborUpdate` have targetTick ≥ w.tick + 2. -/
theorem World.onNeighborUpdate_events_future_ge2 (w : World) (id : Nat)
    (h_delay : ∀ nd, w.getNode id = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2) :
    ∀ ev ∈ (w.onNeighborUpdate id).events, ev ∉ w.events → ev.targetTick ≥ w.tick + 2 := by
  cases h_getNode : w.getNode id with
  | none => simp [World.onNeighborUpdate, h_getNode]; intro ev h h'; contradiction
  | some nd =>
    cases h_kind : nd.kind with
    | repeater delay priority =>
      simp [World.onNeighborUpdate, h_getNode, h_kind, World.scheduleEvent_events,
            List.mem_append]
      intro ev h_ev h_new
      cases h_ev with
      | inl h => contradiction
      | inr h =>
        have h_tick : ev.targetTick = w.tick + (delay : Nat) := by rw [h]
        rw [h_tick]
        have hd : (delay : Nat) ≥ 2 := h_delay nd h_getNode delay priority h_kind
        omega
    | observer =>
      simp [World.onNeighborUpdate, h_getNode, h_kind, World.scheduleEvent_events,
            List.mem_append]
      intro ev h_ev h_new
      cases h_ev with
      | inl h => contradiction
      | inr h =>
        have h_tick : ev.targetTick = w.tick + 2 := by rw [h]
        rw [h_tick]
    | output name =>
      simp [World.onNeighborUpdate, h_getNode, h_kind, World.logOutput_events]
      intro ev h h'; contradiction
    | input =>
      simp [World.onNeighborUpdate, h_getNode, h_kind]
      intro ev h h'; contradiction

/-- New events from `onNeighborUpdate` have targetTick % 2 = w.tick % 2 when delays are even. -/
theorem World.onNeighborUpdate_events_parity (w : World) (id : Nat)
    (h_even : ∀ nd, w.getNode id = some nd → ∀ d p, nd.kind = .repeater d p → (d : Nat) % 2 = 0) :
    ∀ ev ∈ (w.onNeighborUpdate id).events, ev ∉ w.events → ev.targetTick % 2 = w.tick % 2 := by
  cases h_getNode : w.getNode id with
  | none => simp [World.onNeighborUpdate, h_getNode]; intro ev h h'; contradiction
  | some nd =>
    cases h_kind : nd.kind with
    | repeater delay priority =>
      simp [World.onNeighborUpdate, h_getNode, h_kind, World.scheduleEvent_events,
            List.mem_append]
      intro ev h_ev h_new
      cases h_ev with
      | inl h => contradiction
      | inr h =>
        have h_tick : ev.targetTick = w.tick + (delay : Nat) := by rw [h]
        rw [h_tick, Nat.add_mod]
        have hd : (delay : Nat) % 2 = 0 := h_even nd h_getNode delay priority h_kind
        omega
    | observer =>
      simp [World.onNeighborUpdate, h_getNode, h_kind, World.scheduleEvent_events,
            List.mem_append]
      intro ev h_ev h_new
      cases h_ev with
      | inl h => contradiction
      | inr h =>
        have h_tick : ev.targetTick = w.tick + 2 := by rw [h]
        rw [h_tick, Nat.add_mod]
        norm_num
    | output name =>
      simp [World.onNeighborUpdate, h_getNode, h_kind, World.logOutput_events]
      intro ev h h'; contradiction
    | input =>
      simp [World.onNeighborUpdate, h_getNode, h_kind]
      intro ev h h'; contradiction

/-- `onNeighborUpdate` preserves the node list. -/
theorem World.onNeighborUpdate_nodes (w : World) (id : Nat) :
    (w.onNeighborUpdate id).nodes = w.nodes := by
  dsimp [World.onNeighborUpdate]
  split
  · rfl
  · rename_i nd; split
    · simp [World.scheduleEvent_nodes]
    · simp [World.scheduleEvent_nodes]
    · simp [World.logOutput_nodes]
    · rfl

/-- `onNeighborUpdate` preserves `getNode`. -/
theorem World.onNeighborUpdate_getNode (w : World) (id nid : Nat) :
    (w.onNeighborUpdate id).getNode nid = w.getNode nid := by
  rw [World.getNode, World.getNode, World.onNeighborUpdate_nodes]

/-- `notifyOutputs` preserves `getNode`. -/
theorem World.notifyOutputs_getNode (w : World) (id nid : Nat) :
    (w.notifyOutputs id).getNode nid = w.getNode nid := by
  unfold World.notifyOutputs
  cases h_getNode : w.getNode id with
  | none => rfl
  | some nd =>
    have h : ∀ (l : List Nat) (w : World),
        (l.foldl (fun w' outId => w'.onNeighborUpdate outId) w).getNode nid = w.getNode nid := by
      intro l
      induction l with
      | nil => intro w; rfl
      | cons hd tl ih =>
        intro w
        simp only [List.foldl_cons]
        rw [ih, World.onNeighborUpdate_getNode]
    exact h nd.outputs w

/-- `find?` commutes with `map` when the predicate is invariant under the mapping. -/
theorem List.find?_map_invariant {α : Type} (l : List α) (f : α → α) (p : α → Bool)
    (h : ∀ x, p (f x) = p x) :
    (l.map f).find? p = (l.find? p).map f := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, List.find?]
    rw [h hd]
    split
    · rfl
    · rw [ih]

/-- If `find?` returns `some a`, then `a` satisfies the predicate. -/
theorem List.find?_predicate_true {α : Type} (p : α → Bool) (l : List α) (a : α)
    (h : l.find? p = some a) : p a = true := by
  induction l generalizing a with
  | nil => simp [List.find?] at h
  | cons hd tl ih =>
    cases h_if : p hd with
    | true =>
      have h_eq : some hd = some a := by simpa [List.find?, h_if] using h
      injection h_eq with h_eq'
      subst h_eq'
      exact h_if
    | false =>
      have h' : tl.find? p = some a := by simpa [List.find?, h_if] using h
      exact ih a h'

/-- If `find?` returns `some a`, then `a` is at some position `i`, and no earlier element
    satisfies the predicate. -/
theorem List.find?_eq_some_getElem {α : Type} (p : α → Bool) (l : List α) (a : α)
    (h : l.find? p = some a) :
    ∃ (i : Nat) (h_i : i < l.length), l[i] = a ∧ ∀ (j : Nat) (h_j : j < i), p l[j] = false := by
  induction l generalizing a with
  | nil => simp [List.find?] at h
  | cons hd tl ih =>
    cases h_if : p hd with
    | true =>
      have h_eq : some hd = some a := by simpa [List.find?, h_if] using h
      injection h_eq with h_eq'
      subst h_eq'
      exact ⟨0, by simp, by simp, by simp⟩
    | false =>
      have h' : tl.find? p = some a := by simpa [List.find?, h_if] using h
      obtain ⟨i, h_i_lt, h_i_get, h_i_no⟩ := ih a h'
      have h_len : (hd :: tl).length = tl.length + 1 := by simp
      refine ⟨i + 1, by omega, ?_, ?_⟩
      · simpa using h_i_get
      · intro j h_j
        cases j with
        | zero => simpa using h_if
        | succ j' =>
          have h_j' : j' < i := by omega
          simpa [List.getElem_cons_succ] using h_i_no j' h_j'

/-- After `updateNode`, `getNode` returns a node whose kind is preserved. -/
theorem World.updateNode_getNode_kind (w : World) (id nid : Nat) (f : NodeData → NodeData)
    (h_kind : ∀ nd, (f nd).kind = nd.kind)
    (nd : NodeData) (h : (w.updateNode id f).getNode nid = some nd) :
    ∃ nd_orig, w.getNode nid = some nd_orig ∧ nd_orig.kind = nd.kind := by
  dsimp [World.updateNode, World.getNode] at h ⊢
  set g := fun (x : Nat × NodeData) => if x.1 == id then (x.1, f x.2) else x
  have h_inv : ∀ x, (fun (nid' : Nat × NodeData) => nid'.1 == nid) (g x) =
      (fun (nid' : Nat × NodeData) => nid'.1 == nid) x := by
    intro x; dsimp [g]; split <;> rfl
  rw [List.find?_map_invariant w.nodes g (fun x => x.1 == nid) h_inv] at h
  generalize h_opt : w.nodes.find? (fun x => x.1 == nid) = opt at h
  cases opt with
  | none => simp [] at h
  | some p =>
    rcases p with ⟨nid', nd_orig⟩
    dsimp [Option.map, g] at h
    split at h
    · -- nid' == id: h : some (f nd_orig) = some nd
      simp only [Option.some_inj] at h
      use nd_orig; constructor
      · simp []
      · rw [← h, h_kind]
    · -- nid' != id: h : some nd_orig = some nd
      simp only [Option.some_inj] at h
      use nd_orig; constructor
      · simp []
      · rw [← h]

/-- `onScheduledTick` preserves node kinds. -/
theorem World.onScheduledTick_getNode_kind (w : World) (id nid : Nat) :
    ∀ nd, (w.onScheduledTick id).getNode nid = some nd →
    ∃ nd_orig, w.getNode nid = some nd_orig ∧ nd_orig.kind = nd.kind := by
  intro nd h_nd
  dsimp [World.onScheduledTick] at h_nd
  split at h_nd
  · exact ⟨nd, h_nd, rfl⟩
  · rename_i nd_id; split at h_nd
    · -- repeater
      rw [World.notifyOutputs_getNode] at h_nd
      exact World.updateNode_getNode_kind w id nid
        (fun nd => { nd with sigLevel := if w.getInputSignal id > 0 then 15 else 0 })
        (fun nd => rfl) nd h_nd
    · -- observer
      rw [World.notifyOutputs_getNode] at h_nd
      exact World.updateNode_getNode_kind w id nid
        (fun nd => { nd with sigLevel := 15 })
        (fun nd => rfl) nd h_nd
    · -- output/input
      exact ⟨nd, h_nd, rfl⟩

/-- A foldl of `onNeighborUpdate` only appends events at ticks > w.tick. -/
theorem foldl_onNeighborUpdate_events_future (l : List Nat) (w : World)
    (h_delay : ∀ nid nd, w.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2) :
    ∀ ev ∈ (l.foldl (fun w' outId => w'.onNeighborUpdate outId) w).events,
      ev ∉ w.events → ev.targetTick > w.tick := by
  induction l generalizing w with
  | nil => intro ev h h'; contradiction
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    set w' := w.onNeighborUpdate hd
    have h_tick' : w'.tick = w.tick := World.onNeighborUpdate_tick w hd
    have h_delay' : ∀ nid nd, w'.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
      intro nid nd h_nd d p h_kind
      rw [World.onNeighborUpdate_getNode] at h_nd
      exact h_delay nid nd h_nd d p h_kind
    have h_new := World.onNeighborUpdate_events_future w hd
      (fun nd h_nd d p h_kind => h_delay hd nd h_nd d p h_kind)
    have h_ih := ih w' h_delay'
    intro ev h_ev h_notin
    by_cases h_mid : ev ∈ w'.events
    · exact h_new ev h_mid h_notin
    · have := h_ih ev h_ev h_mid
      rw [h_tick'] at this
      exact this

/-- `setInput` on an input node only adds events at ticks strictly greater
than the current tick (observer → tick+2, repeater → tick+delay with delay ≥ 2). -/
theorem setInput_events_future (w : World) (id level : Nat)
    (h_delay : ∀ nid nd, w.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2) :
    ∀ ev ∈ (w.setInput id level).events, ev ∉ w.events → ev.targetTick > w.tick := by
  dsimp [World.setInput, World.notifyOutputs]
  set w' := w.updateNode id (fun nd => { nd with sigLevel := level })
  have h_events' : w'.events = w.events := World.updateNode_events w id _
  have h_tick' : w'.tick = w.tick := World.updateNode_tick w id _
  cases h_getNode : w'.getNode id with
  | none =>
    simp [h_events']
    intro ev h h'; contradiction
  | some nd =>
    have h_delay' : ∀ nid nd, w'.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
      intro nid nd' h_nd' d p h_kind
      obtain ⟨nd_orig, h_getNode', h_kind_eq⟩ :=
        World.updateNode_getNode_kind w id nid
          (fun nd => { nd with sigLevel := level })
          (fun nd => rfl) nd' h_nd'
      rw [← h_kind_eq] at h_kind
      exact h_delay nid nd_orig h_getNode' d p h_kind
    simp only []
    have := foldl_onNeighborUpdate_events_future nd.outputs w' h_delay'
    rw [h_tick'] at this
    intro ev h_ev h_notin
    rw [← h_events'] at h_notin
    exact this ev h_ev h_notin

/-- Stronger: foldl `onNeighborUpdate` new events have targetTick ≥ w.tick + 2. -/
theorem foldl_onNeighborUpdate_events_future_ge2 (l : List Nat) (w : World)
    (h_delay : ∀ nid nd, w.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2) :
    ∀ ev ∈ (l.foldl (fun w' outId => w'.onNeighborUpdate outId) w).events,
      ev ∉ w.events → ev.targetTick ≥ w.tick + 2 := by
  induction l generalizing w with
  | nil => intro ev h h'; contradiction
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    set w' := w.onNeighborUpdate hd
    have h_tick' : w'.tick = w.tick := World.onNeighborUpdate_tick w hd
    have h_delay' : ∀ nid nd, w'.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
      intro nid nd h_nd d p h_kind
      rw [World.onNeighborUpdate_getNode] at h_nd
      exact h_delay nid nd h_nd d p h_kind
    have h_new := World.onNeighborUpdate_events_future_ge2 w hd
      (fun nd h_nd d p h_kind => h_delay hd nd h_nd d p h_kind)
    have h_ih := ih w' h_delay'
    intro ev h_ev h_notin
    by_cases h_mid : ev ∈ w'.events
    · exact h_new ev h_mid h_notin
    · have := h_ih ev h_ev h_mid
      rw [h_tick'] at this
      exact this
