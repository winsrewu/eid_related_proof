import BasicProofs.GroupClustering.QueueMembership


open BasicRedstoneSim

/-! # Group clustering — the log bridge

This file connects the simulation output log to the last-repeater firings.

Results:

* `tick_entry_not_output`: a `s!"tick {n}"` entry never matches
  `isOutputEntry`.
* `chain_entry_is_output`: the entries `s!"{chainName gi ci}: 0"` and
  `s!"{chainName gi ci}: 15"` match `isOutputEntry · gi ci`.
* `output_entry_is_chain`: every matching entry is one of those two.
* `gSimFoldl_log_char` and `groupSimulate_log_char`: every entry of the
  simulation log is a tick entry or a chain entry `s!"{chainName gi ci}: {v}"`
  with `v = 0` or `v = 15`.

The log characterization uses three world invariants: `OutputNamesOk`
(every output node carries a name `chainName gi ci`), `SigLevelsOk`
(every signal level is 0 or 15) and `LogOk` (every log entry is a tick
entry or a chain entry). All three hold for the built world and survive
every simulation operation.
-/

/-! ## Entry classes -/

/-- A log entry that records a tick number. -/
def IsTickEntry (s : String) : Prop := ∃ (t : Nat), s = s!"tick {t}"

/-- A log entry that records the output value of chain `(gi, ci)`. -/
def IsChainEntry (s : String) : Prop :=
  ∃ (gi : Nat) (ci : Nat) (v : Nat),
    (v = 0 ∨ v = 15) ∧ s = s!"{chainName gi ci}: {(v : Nat)}"

/-- Every log entry is a tick entry or a chain entry. -/
def LogOk (w : World) : Prop :=
  ∀ s ∈ w.outputLog, IsTickEntry s ∨ IsChainEntry s

/-- Every output node carries a name of the form `chainName gi ci`. -/
def OutputNamesOk (w : World) : Prop :=
  ∀ nid nd nm, w.getNode nid = some nd → nd.kind = NodeKind.output nm →
    ∃ gi ci, nm = chainName gi ci

/-- Every node signal level is 0 or 15. -/
def SigLevelsOk (w : World) : Prop :=
  ∀ nid nd, w.getNode nid = some nd → nd.sigLevel = 0 ∨ nd.sigLevel = 15

/-! ## Decimal strings carry no letter `t`

A tick entry starts with the letter `t`. A chain entry contains only
decimal digits, colons, a space and the value digits. The two never
match. The digit fact needs a small induction over `Nat.toDigitsCore`,
the engine behind `Nat.repr`.
-/

/-- `Nat.toDigitsCore` with fuel 0 returns the accumulator. -/
private theorem toDigitsCore_zero (b n : Nat) (l : List Char) :
    Nat.toDigitsCore b 0 n l = l := by
  simp only [Nat.toDigitsCore]

/-- One fuel step of `Nat.toDigitsCore` peels one digit. -/
private theorem toDigitsCore_succ (b f n : Nat) (l : List Char) :
    Nat.toDigitsCore b (f + 1) n l =
    if n / b = 0 then Nat.digitChar (n % b) :: l
    else Nat.toDigitsCore b f (n / b) (Nat.digitChar (n % b) :: l) := by
  simp only [Nat.toDigitsCore]

/-- Every character produced by `Nat.toDigitsCore` in base 10 is an
    accumulator character or a digit character. -/
private theorem toDigitsCore_mem (f n : Nat) (l : List Char) :
    ∀ c ∈ Nat.toDigitsCore 10 f n l, c ∈ l ∨ ∃ d, d < 10 ∧ c = Nat.digitChar d := by
  induction f generalizing n l with
  | zero =>
    intro c hc
    rw [toDigitsCore_zero] at hc
    exact Or.inl hc
  | succ f ih =>
    intro c hc
    rw [toDigitsCore_succ] at hc
    split_ifs at hc
    · rw [List.mem_cons] at hc
      rcases hc with h_eq | hc
      · right; exact ⟨n % 10, Nat.mod_lt n (by decide), h_eq⟩
      · left; exact hc
    · have h_ih := ih (n / 10) (Nat.digitChar (n % 10) :: l) c hc
      rcases h_ih with h_mem | ⟨d, hd, h_eq⟩
      · rw [List.mem_cons] at h_mem
        rcases h_mem with h_eq' | h_mem
        · right; exact ⟨n % 10, Nat.mod_lt n (by decide), h_eq'⟩
        · left; exact h_mem
      · right; exact ⟨d, hd, h_eq⟩

/-- A digit character below 10 is not the letter `t`. -/
private theorem digitChar_ne_t (d : Nat) (h : d < 10) : Nat.digitChar d ≠ 't' := by
  interval_cases d <;> decide

/-- The decimal representation of a number carries no letter `t`. -/
private theorem repr_toList_ne_t (n : Nat) :
    ∀ c ∈ (n.repr).toList, c ≠ 't' := by
  intro c hc
  rw [show n.repr = String.ofList (Nat.toDigits 10 n) from rfl] at hc
  rw [String.toList_ofList] at hc
  dsimp [Nat.toDigits] at hc
  have := toDigitsCore_mem (n + 1) n [] c hc
  rcases this with hc | ⟨d, hd, rfl⟩
  · cases hc
  · exact digitChar_ne_t d hd

/-- A tick string differs from `repr gi ++ ":" ++ repr ci ++ tail` when
    `tail` carries no letter `t`. -/
private theorem tick_ne_chain_entry (n gi ci : Nat) (tail : String)
    (h_tail : 't' ∉ tail.toList) :
    s!"tick {n}" ≠ gi.repr ++ ":" ++ ci.repr ++ tail := by
  intro h
  have h_t : 't' ∈ (s!"tick {n}" : String).toList := by
    show 't' ∈ (("tick " : String) ++ n.repr).toList
    rw [String.toList_append]
    left
  rw [h] at h_t
  rw [String.toList_append, String.toList_append, String.toList_append] at h_t
  rcases List.mem_append.mp h_t with h_t | h_t
  · rcases List.mem_append.mp h_t with h_t | h_t
    · rcases List.mem_append.mp h_t with h_t | h_t
      · exact repr_toList_ne_t gi 't' h_t rfl
      · simp at h_t
    · exact repr_toList_ne_t ci 't' h_t rfl
  · exact h_tail h_t

/-- A tick entry never matches `isOutputEntry`. -/
theorem tick_entry_not_output (n gi ci : Nat) :
    s!"tick {n}" ≠ s!"{chainName gi ci}: 0" ∧
    s!"tick {n}" ≠ s!"{chainName gi ci}: 15" := by
  constructor
  · intro h
    dsimp [chainName] at h
    exact tick_ne_chain_entry n gi ci ": 0" (by decide) h
  · intro h
    dsimp [chainName] at h
    exact tick_ne_chain_entry n gi ci ": 15" (by decide) h

/-! ## The Bool definition of `isOutputEntry` -/

/-- The two chain entries of `(gi, ci)` satisfy `isOutputEntry`. -/
theorem chain_entry_is_output (gi ci : Nat) :
    isOutputEntry s!"{chainName gi ci}: 0" gi ci = true ∧
    isOutputEntry s!"{chainName gi ci}: 15" gi ci = true := by
  constructor <;> simp [isOutputEntry, chainName]

/-- An entry that satisfies `isOutputEntry` is one of the two chain
    entries of `(gi, ci)`. -/
theorem output_entry_is_chain (s : String) (gi ci : Nat)
    (h : isOutputEntry s gi ci = true) :
    s = s!"{chainName gi ci}: 0" ∨ s = s!"{chainName gi ci}: 15" := by
  dsimp [isOutputEntry, chainName] at h
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · left; exact LawfulBEq.eq_of_beq h
  · right; exact LawfulBEq.eq_of_beq h

/-! ## Signal values are 0 or 15 -/

/-- The input signal of a node is 0 or 15 when all signal levels are. -/
theorem getInputSignal_zero_or_fifteen (w : World) (id : Nat)
    (hS : SigLevelsOk w) : w.getInputSignal id = 0 ∨ w.getInputSignal id = 15 := by
  dsimp [World.getInputSignal]
  cases h_gn : w.getNode id with
  | none => left; rfl
  | some nd =>
    have h_gen : ∀ (l : List Nat) (acc : Nat), acc = 0 ∨ acc = 15 →
        l.foldl (fun m i =>
          match w.getNode i with
          | none => m
          | some ndi => max m ndi.sigLevel) acc = 0 ∨
        l.foldl (fun m i =>
          match w.getNode i with
          | none => m
          | some ndi => max m ndi.sigLevel) acc = 15 := by
      intro l acc h_acc
      induction l generalizing acc with
      | nil => simpa using h_acc
      | cons i l ih =>
        simp only [List.foldl_cons]
        apply ih
        cases h_gi : w.getNode i with
        | none => exact h_acc
        | some ndi =>
          dsimp only
          have h_sig := hS i ndi h_gi
          rcases h_acc with h_a | h_a
          · rcases h_sig with h_s | h_s <;> rw [h_a, h_s] <;> simp [max]
          · rcases h_sig with h_s | h_s <;> rw [h_a, h_s] <;> simp [max]
    exact h_gen nd.inputs 0 (Or.inl rfl)

/-! ## The invariants survive node construction -/

/-- `getNode` after `addNode` returns the old node or the new node. -/
private theorem addNode_getNode_cases (w : World) (nd : NodeData) (nid : Nat)
    (nd' : NodeData) (h : (w.addNode nd).2.getNode nid = some nd') :
    w.getNode nid = some nd' ∨ nd' = nd := by
  dsimp [World.addNode, World.getNode] at h
  rw [List.find?_append] at h
  cases h_find : w.nodes.find? (fun (nid₀, _) => nid₀ == nid) with
  | none =>
    simp only [h_find] at h
    dsimp [List.find?] at h
    by_cases h_beq : w.nextId == nid
    · simp only [h_beq] at h
      right
      injection h with h_eq
      exact h_eq.symm
    · simp only [h_beq] at h
      cases h
  | some p =>
    rcases p with ⟨i, nd₀⟩
    simp only [h_find] at h
    left
    dsimp [World.getNode]
    rw [h_find]
    exact h

/-- `addNode` keeps the name and signal invariants when the new node
    satisfies them. -/
private theorem addNode_inv (w : World) (nd : NodeData)
    (h_name : ∀ nm, nd.kind = NodeKind.output nm → ∃ gi ci, nm = chainName gi ci)
    (h_sig : nd.sigLevel = 0 ∨ nd.sigLevel = 15)
    (hO : OutputNamesOk w) (hS : SigLevelsOk w) :
    OutputNamesOk (w.addNode nd).2 ∧ SigLevelsOk (w.addNode nd).2 := by
  constructor
  · intro nid nd' nm h_gn h_k
    rcases addNode_getNode_cases w nd nid nd' h_gn with h_old | h_new
    · exact hO nid nd' nm h_old h_k
    · exact h_name nm (by rw [← h_new]; exact h_k)
  · intro nid nd' h_gn
    rcases addNode_getNode_cases w nd nid nd' h_gn with h_old | h_new
    · exact hS nid nd' h_old
    · rw [h_new]
      exact h_sig

/-- `updateNode` with a signal-preserving function preserves signal
    levels. -/
private theorem updateNode_sigLevel_preserved (w : World) (id : Nat)
    (f : NodeData → NodeData) (h_f : ∀ nd', (f nd').sigLevel = nd'.sigLevel) :
    ∀ nid nd, (w.updateNode id f).getNode nid = some nd →
    ∃ nd₀, w.getNode nid = some nd₀ ∧ nd₀.sigLevel = nd.sigLevel := by
  intro nid nd h
  by_cases h_eq : nid = id
  · rw [h_eq] at h ⊢
    cases h_gn : w.getNode id with
    | none =>
      have h_none := World.updateNode_getNode_none w id f h_gn
      rw [h_none] at h
      cases h
    | some nd₀ =>
      have h_eq' := World.updateNode_getNode_eq w id f nd₀ h_gn
      rw [h_eq'] at h
      injection h with h_nd
      exact ⟨nd₀, rfl, by rw [← h_nd, h_f]⟩
  · have h_ne := World.updateNode_getNode_ne w id nid f (Ne.symm h_eq)
    rw [h_ne] at h
    exact ⟨nd, h, rfl⟩

/-- The foldl of `connectChain` preserves signal levels. -/
private theorem foldl_updateNode_sigLevel (pairs : List (Nat × Nat)) (w : World) :
    ∀ nid nd, (pairs.foldl (fun w' x =>
      (w'.updateNode x.2
        (fun nd' => ({ nd' with inputs := nd'.inputs ++ [x.1] } : NodeData))).updateNode x.1
        (fun nd' => ({ nd' with outputs := nd'.outputs ++ [x.2] } : NodeData))
    ) w).getNode nid = some nd →
    ∃ nd₀, w.getNode nid = some nd₀ ∧ nd₀.sigLevel = nd.sigLevel := by
  induction pairs generalizing w with
  | nil => intro nid nd h; exact ⟨nd, h, rfl⟩
  | cons p ps ih =>
    rcases p with ⟨prev, curr⟩
    intro nid nd h
    dsimp [List.foldl] at h
    set w₁ := (w.updateNode curr
      (fun nd' => ({ nd' with inputs := nd'.inputs ++ [prev] } : NodeData))).updateNode prev
      (fun nd' => ({ nd' with outputs := nd'.outputs ++ [curr] } : NodeData))
    obtain ⟨nd₁, h₁, h_lv₁⟩ := ih w₁ nid nd h
    obtain ⟨nd₂, h₂, h_lv₂⟩ := updateNode_sigLevel_preserved
      (w.updateNode curr
        (fun nd' => ({ nd' with inputs := nd'.inputs ++ [prev] } : NodeData))) prev
      (fun nd' => ({ nd' with outputs := nd'.outputs ++ [curr] } : NodeData))
      (fun nd' => rfl) nid nd₁ h₁
    obtain ⟨nd₀, h₀, h_lv₀⟩ := updateNode_sigLevel_preserved w curr
      (fun nd' => ({ nd' with inputs := nd'.inputs ++ [prev] } : NodeData))
      (fun nd' => rfl) nid nd₂ h₂
    exact ⟨nd₀, h₀, h_lv₀.trans (h_lv₂.trans h_lv₁)⟩

/-- `connectChain` preserves signal levels. -/
private theorem connectChain_sigLevel_preserved (w : World) (ids : List Nat) :
    ∀ nid nd, (connectChain w ids).getNode nid = some nd →
    ∃ nd₀, w.getNode nid = some nd₀ ∧ nd₀.sigLevel = nd.sigLevel := by
  dsimp [connectChain]
  exact foldl_updateNode_sigLevel (ids.zip (ids.drop 1)) w

/-- `connectChain` keeps the name and signal invariants. -/
private theorem connectChain_inv (w : World) (ids : List Nat)
    (hO : OutputNamesOk w) (hS : SigLevelsOk w) :
    OutputNamesOk (connectChain w ids) ∧ SigLevelsOk (connectChain w ids) := by
  constructor
  · intro nid nd nm h_gn h_k
    obtain ⟨nd₀, h₀, h_kind⟩ := connectChain_kind_preserved w ids nid nd h_gn
    exact hO nid nd₀ nm h₀ (by rw [h_kind, h_k])
  · intro nid nd h_gn
    obtain ⟨nd₀, h₀, h_lv⟩ := connectChain_sigLevel_preserved w ids nid nd h_gn
    have h_old := hS nid nd₀ h₀
    rw [← h_lv]
    exact h_old

/-- The middle-repeater foldl keeps the name and signal invariants. -/
private theorem repFoldlStep_inv (delays : List PNat) :
    ∀ (acc : List Nat × World), OutputNamesOk acc.2 ∧ SigLevelsOk acc.2 →
    OutputNamesOk (delays.foldl repFoldlStep acc).2 ∧
    SigLevelsOk (delays.foldl repFoldlStep acc).2 := by
  intro acc
  induction delays generalizing acc with
  | nil => intro h; simpa using h
  | cons d ds ih =>
    intro h_inv
    simp only [repFoldlStep, List.foldl_cons]
    apply ih
    dsimp [repFoldlStep]
    exact addNode_inv acc.2 (mkRepNode d)
      (fun nm h_k => by cases h_k) (Or.inl rfl)
      h_inv.1 h_inv.2

/-- `buildChainPre` keeps the name and signal invariants when the chain
    name is a `chainName`. -/
private theorem buildChainPre_inv (w : World) (name : String) (c : ChainSpec)
    (h_name : ∃ gi ci, name = chainName gi ci)
    (hO : OutputNamesOk w) (hS : SigLevelsOk w) :
    OutputNamesOk (buildChainPre w name c).2.1 ∧
    SigLevelsOk (buildChainPre w name c).2.1 := by
  dsimp (config := { zeta := true }) [buildChainPre]
  set w₁ := (w.addNode { kind := .input, sigLevel := 0, inputs := [], outputs := [] }).2
  set w₂ := (w₁.addNode { kind := .observer, sigLevel := 0, inputs := [], outputs := [] }).2
  set w₃ := (c.middleDelays.foldl repFoldlStep ([], w₂)).2
  set w₄ := (w₃.addNode { kind := .repeater c.lastDelay (-1), sigLevel := 0, inputs := [], outputs := [] }).2
  set w₅ := (w₄.addNode { kind := .output name, sigLevel := 0, inputs := [], outputs := [] }).2
  obtain ⟨hO₁, hS₁⟩ := addNode_inv w
    { kind := .input, sigLevel := 0, inputs := [], outputs := [] }
    (fun nm h_k => by cases h_k) (Or.inl rfl) hO hS
  obtain ⟨hO₂, hS₂⟩ := addNode_inv w₁
    { kind := .observer, sigLevel := 0, inputs := [], outputs := [] }
    (fun nm h_k => by cases h_k) (Or.inl rfl) hO₁ hS₁
  obtain ⟨hO₃, hS₃⟩ := repFoldlStep_inv c.middleDelays ([], w₂) ⟨hO₂, hS₂⟩
  obtain ⟨hO₄, hS₄⟩ := addNode_inv w₃
    { kind := .repeater c.lastDelay (-1), sigLevel := 0, inputs := [], outputs := [] }
    (fun nm h_k => by cases h_k) (Or.inl rfl) hO₃ hS₃
  obtain ⟨hO₅, hS₅⟩ := addNode_inv w₄
    { kind := .output name, sigLevel := 0, inputs := [], outputs := [] }
    (fun nm h_k => by
      injection h_k with h_eq
      rcases h_name with ⟨gi, ci, h_nm⟩
      exact ⟨gi, ci, by rw [← h_eq, h_nm]⟩) (Or.inl rfl) hO₄ hS₄
  exact ⟨hO₅, hS₅⟩

/-- `buildChain` keeps the name and signal invariants when the chain
    name is a `chainName`. -/
private theorem buildChain_inv (w : World) (name : String) (c : ChainSpec)
    (h_name : ∃ gi ci, name = chainName gi ci)
    (hO : OutputNamesOk w) (hS : SigLevelsOk w) :
    OutputNamesOk (buildChain w name c).2 ∧ SigLevelsOk (buildChain w name c).2 := by
  dsimp (config := { zeta := true }) [buildChain]
  obtain ⟨hO', hS'⟩ := buildChainPre_inv w name c h_name hO hS
  exact connectChain_inv (buildChainPre w name c).2.1 (buildChainPre w name c).2.2 hO' hS'

/-- Building one group keeps the name and signal invariants. -/
private theorem buildGroupChainsFrom_inv (gi start : Nat) (w : World)
    (g : List ChainSpec) (hO : OutputNamesOk w) (hS : SigLevelsOk w) :
    OutputNamesOk (buildGroupChainsFrom gi start w g).1 ∧
    SigLevelsOk (buildGroupChainsFrom gi start w g).1 := by
  induction g generalizing w start with
  | nil => simpa [buildGroupChainsFrom] using ⟨hO, hS⟩
  | cons c cs ih =>
    dsimp [buildGroupChainsFrom]
    obtain ⟨hO', hS'⟩ := buildChain_inv w (chainName gi start) c ⟨gi, start, rfl⟩ hO hS
    exact ih (start + 1) (buildChain w (chainName gi start) c).2 hO' hS'

/-- Building all groups keeps the name and signal invariants. -/
private theorem buildGroupsFrom_inv (start : Nat) (w : World)
    (groups : List GroupSpec) (hO : OutputNamesOk w) (hS : SigLevelsOk w) :
    OutputNamesOk (buildGroupsFrom start w groups).1 ∧
    SigLevelsOk (buildGroupsFrom start w groups).1 := by
  induction groups generalizing w start with
  | nil => simpa [buildGroupsFrom] using ⟨hO, hS⟩
  | cons g gs ih =>
    dsimp [buildGroupsFrom, buildGroupChains]
    obtain ⟨hO', hS'⟩ := buildGroupChainsFrom_inv start 0 w g hO hS
    exact ih (start + 1) (buildGroupChainsFrom start 0 w g).1 hO' hS'

/-- The empty world satisfies the name invariant. -/
private theorem empty_OutputNamesOk : OutputNamesOk World.empty := by
  intro nid nd nm h_gn
  dsimp [World.empty, World.getNode] at h_gn
  cases h_gn

/-- The empty world satisfies the signal invariant. -/
private theorem empty_SigLevelsOk : SigLevelsOk World.empty := by
  intro nid nd h_gn
  dsimp [World.empty, World.getNode] at h_gn
  cases h_gn

/-- Every output node of the built world carries a name `chainName gi ci`. -/
theorem buildGroups_OutputNamesOk (groups : List GroupSpec) :
    OutputNamesOk (buildGroups groups).1 := by
  dsimp [buildGroups]
  exact (buildGroupsFrom_inv 0 World.empty groups
    empty_OutputNamesOk empty_SigLevelsOk).1

/-- Every signal level of the built world is 0 or 15. -/
theorem buildGroups_SigLevelsOk (groups : List GroupSpec) :
    SigLevelsOk (buildGroups groups).1 := by
  dsimp [buildGroups]
  exact (buildGroupsFrom_inv 0 World.empty groups
    empty_OutputNamesOk empty_SigLevelsOk).2

/-! ## The invariants survive the simulation operations -/

/-- An `updateNode` that sets a signal level keeps the name invariant. -/
private theorem OutputNamesOk_updateNode_sigLevel (w : World) (updId : Nat)
    (level : Nat) (hO : OutputNamesOk w) :
    OutputNamesOk (w.updateNode updId
      (fun nd => ({ nd with sigLevel := level } : NodeData))) := by
  intro nid nd nm h_gn h_k
  obtain ⟨nd₀, h₀, h_kind⟩ := World.updateNode_getNode_kind w updId nid
    (fun nd' => ({ nd' with sigLevel := level } : NodeData)) (fun nd' => rfl) nd h_gn
  exact hO nid nd₀ nm h₀ (by rw [h_kind, h_k])

/-- An `updateNode` that sets a signal level to 0 or 15 keeps the signal
    invariant. -/
private theorem SigLevelsOk_updateNode_level (w : World) (updId : Nat) (level : Nat)
    (h_lv : level = 0 ∨ level = 15) (hS : SigLevelsOk w) :
    SigLevelsOk (w.updateNode updId
      (fun nd => ({ nd with sigLevel := level } : NodeData))) := by
  intro nid nd h
  by_cases h_eq : nid = updId
  · rw [h_eq] at h
    cases h_orig : w.getNode updId with
    | none =>
      have h_none := World.updateNode_getNode_none w updId
        (fun nd' => ({ nd' with sigLevel := level } : NodeData)) h_orig
      rw [h_none] at h
      cases h
    | some nd₁ =>
      have h_eq' := World.updateNode_getNode_eq w updId
        (fun nd' => ({ nd' with sigLevel := level } : NodeData)) nd₁ h_orig
      rw [h_eq'] at h
      injection h with h_nd
      rw [← h_nd]
      simpa using h_lv
  · have h_ne := World.updateNode_getNode_ne w updId nid
      (fun nd' => ({ nd' with sigLevel := level } : NodeData)) (Ne.symm h_eq)
    rw [h_ne] at h
    exact hS nid nd h

/-- An `updateNode` that sets a signal level keeps the log invariant. -/
private theorem LogOk_updateNode_sigLevel (w : World) (updId : Nat) (level : Nat)
    (hL : LogOk w) :
    LogOk (w.updateNode updId
      (fun nd => ({ nd with sigLevel := level } : NodeData))) := by
  intro s h_mem
  dsimp [World.updateNode] at h_mem
  exact hL s h_mem

/-- One neighbor update keeps the log invariant. -/
private theorem LogOk_onNeighborUpdate (w : World) (id : Nat)
    (hO : OutputNamesOk w) (hS : SigLevelsOk w) (hL : LogOk w) :
    LogOk (w.onNeighborUpdate id) := by
  intro s h_mem
  dsimp [World.onNeighborUpdate] at h_mem
  cases h_gn : w.getNode id with
  | none =>
    simp only [h_gn] at h_mem
    exact hL s h_mem
  | some nd =>
    simp only [h_gn] at h_mem
    cases h_kind : nd.kind with
    | input =>
      simp only [h_kind] at h_mem
      exact hL s h_mem
    | observer =>
      simp only [h_kind, World.scheduleEvent_outputLog] at h_mem
      exact hL s h_mem
    | repeater d p =>
      simp only [h_kind, World.scheduleEvent_outputLog] at h_mem
      exact hL s h_mem
    | output nm =>
      simp only [h_kind] at h_mem
      dsimp [World.logOutput] at h_mem
      rw [List.mem_append] at h_mem
      rcases h_mem with h_mem | h_mem
      · exact hL s h_mem
      · rw [List.mem_singleton] at h_mem
        subst h_mem
        right
        obtain ⟨gi, ci, h_nm⟩ := hO id nd nm h_gn h_kind
        refine ⟨gi, ci, w.getInputSignal id, ?_, ?_⟩
        · exact getInputSignal_zero_or_fifteen w id hS
        · rw [h_nm]

/-- A foldl of neighbor updates keeps the log invariant. -/
private theorem LogOk_foldl_onNeighborUpdate (l : List Nat) (w : World)
    (hO : OutputNamesOk w) (hS : SigLevelsOk w) (hL : LogOk w) :
    LogOk (l.foldl (fun w' outId => w'.onNeighborUpdate outId) w) := by
  induction l generalizing w with
  | nil => simpa using hL
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    apply ih
    · intro nid nd nm h_gn h_k
      rw [World.onNeighborUpdate_getNode] at h_gn
      exact hO nid nd nm h_gn h_k
    · intro nid nd h_gn
      rw [World.onNeighborUpdate_getNode] at h_gn
      exact hS nid nd h_gn
    · exact LogOk_onNeighborUpdate w hd hO hS hL

/-- Firing a node keeps the log invariant. -/
private theorem LogOk_onScheduledTick (w : World) (nodeId : Nat)
    (hO : OutputNamesOk w) (hS : SigLevelsOk w) (hL : LogOk w) :
    LogOk (w.onScheduledTick nodeId) := by
  intro s h_mem
  dsimp [World.onScheduledTick] at h_mem
  cases h_gn : w.getNode nodeId with
  | none =>
    simp only [h_gn] at h_mem
    exact hL s h_mem
  | some nd =>
    simp only [h_gn] at h_mem
    cases h_kind : nd.kind with
    | input =>
      simp only [h_kind] at h_mem
      exact hL s h_mem
    | output nm =>
      simp only [h_kind] at h_mem
      exact hL s h_mem
    | observer =>
      simp only [h_kind] at h_mem
      dsimp [World.notifyOutputs] at h_mem
      cases h_gn' : (w.updateNode nodeId
          (fun nd' => ({ nd' with sigLevel := 15 } : NodeData))).getNode nodeId with
      | none =>
        simp only [h_gn'] at h_mem
        dsimp [World.updateNode] at h_mem
        exact hL s h_mem
      | some nd' =>
        simp only [h_gn'] at h_mem
        exact LogOk_foldl_onNeighborUpdate nd'.outputs
          (w.updateNode nodeId (fun nd' => ({ nd' with sigLevel := 15 } : NodeData)))
          (OutputNamesOk_updateNode_sigLevel w nodeId 15 hO)
          (SigLevelsOk_updateNode_level w nodeId 15 (Or.inr rfl) hS)
          (LogOk_updateNode_sigLevel w nodeId 15 hL) s h_mem
    | repeater d p =>
      simp only [h_kind] at h_mem
      dsimp [World.notifyOutputs] at h_mem
      cases h_gn' : (w.updateNode nodeId
          (fun nd' => ({ nd' with
              sigLevel := if w.getInputSignal nodeId > 0 then 15 else 0 } : NodeData))).getNode nodeId with
      | none =>
        simp only [h_gn'] at h_mem
        dsimp [World.updateNode] at h_mem
        exact hL s h_mem
      | some nd' =>
        simp only [h_gn'] at h_mem
        exact LogOk_foldl_onNeighborUpdate nd'.outputs
          (w.updateNode nodeId (fun nd' => ({ nd' with
              sigLevel := if w.getInputSignal nodeId > 0 then 15 else 0 } : NodeData)))
          (OutputNamesOk_updateNode_sigLevel w nodeId
            (if w.getInputSignal nodeId > 0 then 15 else 0) hO)
          (SigLevelsOk_updateNode_level w nodeId
            (if w.getInputSignal nodeId > 0 then 15 else 0)
            (by split_ifs with h_c
                · right; rfl
                · left; rfl) hS)
          (LogOk_updateNode_sigLevel w nodeId
            (if w.getInputSignal nodeId > 0 then 15 else 0) hL) s h_mem

/-- Firing a node keeps the signal invariant. -/
private theorem SigLevelsOk_onScheduledTick (w : World) (nodeId : Nat)
    (hS : SigLevelsOk w) : SigLevelsOk (w.onScheduledTick nodeId) := by
  intro nid nd h
  dsimp [World.onScheduledTick] at h
  split at h
  · exact hS nid nd h
  · rename_i nd_id; split at h
    · rw [World.notifyOutputs_getNode] at h
      exact SigLevelsOk_updateNode_level w nodeId
        (if w.getInputSignal nodeId > 0 then 15 else 0)
        (by split_ifs with h_c
            · right; rfl
            · left; rfl) hS nid nd h
    · rw [World.notifyOutputs_getNode] at h
      exact SigLevelsOk_updateNode_level w nodeId 15 (Or.inr rfl) hS nid nd h
    · exact hS nid nd h

/-- Firing a node keeps the name invariant. -/
private theorem OutputNamesOk_onScheduledTick (w : World) (nodeId : Nat)
    (hO : OutputNamesOk w) : OutputNamesOk (w.onScheduledTick nodeId) := by
  intro nid nd nm h_gn h_k
  obtain ⟨nd₀, h₀, h_kind⟩ := World.onScheduledTick_getNode_kind w nodeId nid nd h_gn
  exact hO nid nd₀ nm h₀ (by rw [h_kind, h_k])

/-- One step keeps all three invariants. -/
private theorem inv_step (w w' : World) (h_step : w.step = some w')
    (hO : OutputNamesOk w) (hS : SigLevelsOk w) (hL : LogOk w) :
    OutputNamesOk w' ∧ SigLevelsOk w' ∧ LogOk w' := by
  dsimp [World.step] at h_step
  cases h_pop : w.popNextEvent with
  | none => simp [h_pop] at h_step
  | some p =>
    rcases p with ⟨ev, w_pop⟩
    simp only [h_pop] at h_step
    injection h_step with h_w'
    have h_nodes : w_pop.nodes = w.nodes := World.popNextEvent_nodes w ev w_pop h_pop
    have h_log : w_pop.outputLog = w.outputLog :=
      World.popNextEvent_outputLog w ev w_pop h_pop
    have hO_pop : OutputNamesOk w_pop := by
      intro nid nd nm h_gn h_k
      dsimp [World.getNode] at h_gn ⊢
      rw [h_nodes] at h_gn
      exact hO nid nd nm h_gn h_k
    have hS_pop : SigLevelsOk w_pop := by
      intro nid nd h_gn
      dsimp [World.getNode] at h_gn ⊢
      rw [h_nodes] at h_gn
      exact hS nid nd h_gn
    have hL_pop : LogOk w_pop := by
      intro s h_mem
      rw [h_log] at h_mem
      exact hL s h_mem
    rw [← h_w']
    exact ⟨OutputNamesOk_onScheduledTick w_pop ev.nodeId hO_pop,
      SigLevelsOk_onScheduledTick w_pop ev.nodeId hS_pop,
      LogOk_onScheduledTick w_pop ev.nodeId hO_pop hS_pop hL_pop⟩

/-- `stepUntilNextTick` keeps all three invariants. -/
private theorem inv_stepUntilNextTick (w : World)
    (hO : OutputNamesOk w) (hS : SigLevelsOk w) (hL : LogOk w) :
    OutputNamesOk w.stepUntilNextTick ∧ SigLevelsOk w.stepUntilNextTick ∧
    LogOk w.stepUntilNextTick := by
  revert hO hS hL
  induction w using World.stepUntilNextTick.induct with
  | case1 x h_step =>
    intro hO hS hL
    rw [stepUntilNextTick_of_step_none x h_step]
    refine ⟨?_, ?_, ?_⟩
    · intro nid nd nm h_gn h_k
      dsimp [World.getNode] at h_gn
      exact hO nid nd nm h_gn h_k
    · intro nid nd h_gn
      dsimp [World.getNode] at h_gn
      exact hS nid nd h_gn
    · intro s h_mem
      exact hL s h_mem
  | case2 x w' h_step ih =>
    intro hO hS hL
    have h_sunt : x.stepUntilNextTick = w'.stepUntilNextTick := by
      rw [World.stepUntilNextTick, h_step]
    rw [h_sunt]
    obtain ⟨hO', hS', hL'⟩ := inv_step x w' h_step hO hS hL
    exact ih hO' hS' hL'

/-- `processNEvents` keeps all three invariants. -/
private theorem inv_processNEvents (w : World) (n : Nat)
    (hO : OutputNamesOk w) (hS : SigLevelsOk w) (hL : LogOk w) :
    OutputNamesOk (processNEvents w n) ∧ SigLevelsOk (processNEvents w n) ∧
    LogOk (processNEvents w n) := by
  induction n generalizing w with
  | zero => simpa [processNEvents] using ⟨hO, hS, hL⟩
  | succ n' ih =>
    simp only [processNEvents]
    cases h_step : w.step with
    | none => simpa [h_step] using ⟨hO, hS, hL⟩
    | some w' =>
      obtain ⟨hO', hS', hL'⟩ := inv_step w w' h_step hO hS hL
      exact ih w' hO' hS' hL'

/-- `activateGroup` keeps all three invariants. -/
private theorem inv_activateGroup (w : World) (observers : List Nat)
    (hO : OutputNamesOk w) (hS : SigLevelsOk w) (hL : LogOk w) :
    OutputNamesOk (activateGroup w observers) ∧ SigLevelsOk (activateGroup w observers) ∧
    LogOk (activateGroup w observers) := by
  induction observers generalizing w with
  | nil => simpa [activateGroup] using ⟨hO, hS, hL⟩
  | cons oid os ih =>
    simp only [activateGroup, List.foldl_cons]
    apply ih
    · intro nid nd nm h_gn h_k
      rw [World.scheduleEvent_getNode] at h_gn
      exact hO nid nd nm h_gn h_k
    · intro nid nd h_gn
      rw [World.scheduleEvent_getNode] at h_gn
      exact hS nid nd h_gn
    · intro s h_mem
      rw [World.scheduleEvent_outputLog] at h_mem
      exact hL s h_mem

/-- The burst phase keeps all three invariants. -/
private theorem inv_gSimBurst (t : Nat) (obsAll : List (List Nat))
    (withinOrd pos : Nat → List Nat) (w : World) (pairs : List (Nat × Nat))
    (hO : OutputNamesOk w) (hS : SigLevelsOk w) (hL : LogOk w) :
    OutputNamesOk (gSimBurst t obsAll withinOrd pos w pairs) ∧
    SigLevelsOk (gSimBurst t obsAll withinOrd pos w pairs) ∧
    LogOk (gSimBurst t obsAll withinOrd pos w pairs) := by
  induction pairs generalizing w with
  | nil => simpa [gSimBurst] using ⟨hO, hS, hL⟩
  | cons p ps ih =>
    simp only [gSimBurst, List.foldl_cons]
    rcases p with ⟨gi, k⟩
    simp only
    obtain ⟨hO₁, hS₁, hL₁⟩ := inv_processNEvents w ((pos t)[k]?.getD 0) hO hS hL
    obtain ⟨hO₂, hS₂, hL₂⟩ := inv_activateGroup
      (processNEvents w ((pos t)[k]?.getD 0))
      ((withinOrd gi).foldl (fun acc ci =>
        match (obsAll[gi]?.getD [])[ci]? with
        | some oid => acc ++ [oid]
        | none => acc) []) hO₁ hS₁ hL₁
    exact ih
      (activateGroup (processNEvents w ((pos t)[k]?.getD 0))
        ((withinOrd gi).foldl (fun acc ci =>
          match (obsAll[gi]?.getD [])[ci]? with
          | some oid => acc ++ [oid]
          | none => acc) [])) hO₂ hS₂ hL₂

/-- One `gSimBody` call keeps all three invariants. -/
private theorem inv_gSimBody (actTick : Nat → Nat) (obsAll : List (List Nat))
    (groupOrd : List Nat) (withinOrd pos : Nat → List Nat) (w : World) (i : Nat)
    (hO : OutputNamesOk w) (hS : SigLevelsOk w) (hL : LogOk w) :
    OutputNamesOk (gSimBody actTick obsAll groupOrd withinOrd pos w i) ∧
    SigLevelsOk (gSimBody actTick obsAll groupOrd withinOrd pos w i) ∧
    LogOk (gSimBody actTick obsAll groupOrd withinOrd pos w i) := by
  dsimp [gSimBody]
  set W₁ := w.logOutput s!"tick {w.tick}"
  set A := groupOrd.filter (fun gi =>
    decide (gi < obsAll.length) && (actTick gi == w.tick))
  have hO_log : OutputNamesOk W₁ := by
    intro nid nd nm h_gn h_k
    change (w.logOutput s!"tick {w.tick}").getNode nid = some nd at h_gn
    rw [World.logOutput_getNode] at h_gn
    exact hO nid nd nm h_gn h_k
  have hS_log : SigLevelsOk W₁ := by
    intro nid nd h_gn
    change (w.logOutput s!"tick {w.tick}").getNode nid = some nd at h_gn
    rw [World.logOutput_getNode] at h_gn
    exact hS nid nd h_gn
  have hL_log : LogOk W₁ := by
    intro s h_mem
    change s ∈ (w.logOutput s!"tick {w.tick}").outputLog at h_mem
    dsimp [World.logOutput] at h_mem
    rw [List.mem_append] at h_mem
    rcases h_mem with h_mem | h_mem
    · exact hL s h_mem
    · rw [List.mem_singleton] at h_mem
      subst h_mem
      left
      exact ⟨w.tick, rfl⟩
  split_ifs with h_active
  · exact inv_stepUntilNextTick W₁ hO_log hS_log hL_log
  · obtain ⟨hO₁, hS₁, hL₁⟩ := inv_gSimBurst w.tick obsAll withinOrd pos W₁
      A.zipIdx hO_log hS_log hL_log
    exact inv_stepUntilNextTick _ hO₁ hS₁ hL₁

/-- The `n`-tick simulation keeps all three invariants. -/
private theorem gSimFoldl_inv (actTick : Nat → Nat) (obsAll : List (List Nat))
    (groupOrd : List Nat) (withinOrd pos : Nat → List Nat) (w : World) (n : Nat)
    (hO : OutputNamesOk w) (hS : SigLevelsOk w) (hL : LogOk w) :
    OutputNamesOk (gSimFoldl actTick obsAll groupOrd withinOrd pos w n) ∧
    SigLevelsOk (gSimFoldl actTick obsAll groupOrd withinOrd pos w n) ∧
    LogOk (gSimFoldl actTick obsAll groupOrd withinOrd pos w n) := by
  induction n generalizing w with
  | zero => simpa [gSimFoldl] using ⟨hO, hS, hL⟩
  | succ n' ih =>
    simp only [gSimFoldl, List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil]
    obtain ⟨hO', hS', hL'⟩ := ih w hO hS hL
    exact inv_gSimBody actTick obsAll groupOrd withinOrd pos
      ((List.range n').foldl (gSimBody actTick obsAll groupOrd withinOrd pos) w)
      n' hO' hS' hL'

/-- The `n`-tick simulation keeps the log invariant. -/
theorem gSimFoldl_LogOk (actTick : Nat → Nat) (obsAll : List (List Nat))
    (groupOrd : List Nat) (withinOrd pos : Nat → List Nat) (w : World) (n : Nat)
    (hO : OutputNamesOk w) (hS : SigLevelsOk w) (hL : LogOk w) :
    LogOk (gSimFoldl actTick obsAll groupOrd withinOrd pos w n) :=
  (gSimFoldl_inv actTick obsAll groupOrd withinOrd pos w n hO hS hL).2.2

/-! ## The built world has an empty log -/

private theorem updateNode_outputLog (w : World) (id : Nat) (f : NodeData → NodeData) :
    (w.updateNode id f).outputLog = w.outputLog := rfl

private theorem addNode_outputLog (w : World) (nd : NodeData) :
    (w.addNode nd).2.outputLog = w.outputLog := rfl

private theorem foldl_updateNode_outputLog (pairs : List (Nat × Nat)) (w : World) :
    (pairs.foldl (fun w' x =>
      (w'.updateNode x.2
        (fun nd' => ({ nd' with inputs := nd'.inputs ++ [x.1] } : NodeData))).updateNode x.1
        (fun nd' => ({ nd' with outputs := nd'.outputs ++ [x.2] } : NodeData))
    ) w).outputLog = w.outputLog := by
  induction pairs generalizing w with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨prev, curr⟩
    dsimp [List.foldl]
    rw [ih, updateNode_outputLog, updateNode_outputLog]

private theorem connectChain_outputLog (w : World) (ids : List Nat) :
    (connectChain w ids).outputLog = w.outputLog := by
  dsimp [connectChain]
  exact foldl_updateNode_outputLog (ids.zip (ids.drop 1)) w

private theorem repFoldl_outputLog (delays : List PNat) (acc : List Nat × World) :
    (delays.foldl repFoldlStep acc).2.outputLog = acc.2.outputLog := by
  induction delays generalizing acc with
  | nil => rfl
  | cons d ds ih =>
    simp only [repFoldlStep, List.foldl_cons]
    rw [ih, addNode_outputLog]

private theorem buildChainPre_outputLog (w : World) (name : String) (c : ChainSpec) :
    (buildChainPre w name c).2.1.outputLog = w.outputLog := by
  dsimp (config := { zeta := true }) [buildChainPre]
  rw [addNode_outputLog, addNode_outputLog, repFoldl_outputLog, addNode_outputLog,
    addNode_outputLog]

private theorem buildChain_outputLog (w : World) (name : String) (c : ChainSpec) :
    (buildChain w name c).2.outputLog = w.outputLog := by
  dsimp (config := { zeta := true }) [buildChain]
  rw [connectChain_outputLog, buildChainPre_outputLog]

private theorem buildGroupChainsFrom_outputLog (gi start : Nat) (w : World)
    (g : List ChainSpec) :
    (buildGroupChainsFrom gi start w g).1.outputLog = w.outputLog := by
  induction g generalizing w start with
  | nil => rfl
  | cons c cs ih =>
    dsimp [buildGroupChainsFrom]
    rw [ih, buildChain_outputLog]

private theorem buildGroupsFrom_outputLog (start : Nat) (w : World)
    (groups : List GroupSpec) :
    (buildGroupsFrom start w groups).1.outputLog = w.outputLog := by
  induction groups generalizing w start with
  | nil => rfl
  | cons g gs ih =>
    dsimp [buildGroupsFrom, buildGroupChains]
    rw [ih, buildGroupChainsFrom_outputLog]

/-- Building the groups writes nothing to the output log. -/
theorem buildGroups_outputLog (groups : List GroupSpec) :
    (buildGroups groups).1.outputLog = [] := by
  dsimp [buildGroups]
  rw [buildGroupsFrom_outputLog]
  exact rfl

/-! ## Log characterization of the group simulation -/

/-- Every entry of the `n`-tick simulation log over the built world is a
    tick entry or a chain entry with value 0 or 15. -/
theorem gSimFoldl_log_char (actTick : Nat → Nat) (groups : List GroupSpec)
    (groupOrd : List Nat) (withinOrd pos : Nat → List Nat) (n : Nat) (s : String)
    (h_mem : s ∈ (gSimFoldl actTick (buildGroups groups).2 groupOrd withinOrd pos
        (buildGroups groups).1 n).outputLog) :
    IsTickEntry s ∨ IsChainEntry s := by
  apply gSimFoldl_LogOk actTick (buildGroups groups).2 groupOrd withinOrd pos
    (buildGroups groups).1 n (buildGroups_OutputNamesOk groups)
    (buildGroups_SigLevelsOk groups) _ s h_mem
  dsimp [LogOk]
  rw [buildGroups_outputLog]
  intro s' h_mem'
  cases h_mem'

/-- `groupSimulate` unfolds to `gSimFoldl` over the built world. -/
private theorem groupSimulate_eq (T : Nat) (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) :
    groupSimulate T groups actTick groupOrd withinOrd pos =
    (gSimFoldl actTick (buildGroups groups).2 groupOrd withinOrd pos
      (buildGroups groups).1 (T + 1)).outputLog := by
  dsimp [groupSimulate]

/-- Every entry of the `groupSimulate` log is a tick entry or a chain
    entry with value 0 or 15. -/
theorem groupSimulate_log_char (T : Nat) (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (s : String)
    (h_mem : s ∈ groupSimulate T groups actTick groupOrd withinOrd pos) :
    IsTickEntry s ∨ IsChainEntry s := by
  rw [groupSimulate_eq] at h_mem
  exact gSimFoldl_log_char actTick groups groupOrd withinOrd pos (T + 1) s h_mem
