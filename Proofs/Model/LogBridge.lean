import Proofs.Model.DescentStep
import Std.Data.String.ToNat

open BasicRedstoneSim
open World
open List

/-! # Log bridge: output log order = last-repeater firing order -/

/-- `simulate` is the final world's output log. -/
theorem simulate_eq_simWorld_log (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat) :
    simulate T specs actOrd pos = (simWorld T specs actOrd pos (T + 1)).outputLog := by
  dsimp [simulate, simWorld, simFoldl]

/-- A node whose only input is `inp` reads exactly `inp`'s signal. -/
theorem getInputSignal_of_singleton (w : World) (id inp : Nat)
    (nd : NodeData) (hget : w.getNode id = some nd)
    (hinputs : nd.inputs = [inp]) :
    w.getInputSignal id = ((w.getNode inp).map NodeData.sigLevel).getD 0 := by
  dsimp [getInputSignal]
  simp [hget, hinputs]
  cases h : w.getNode inp with
  | none => simp
  | some ndi => simp

/-- After firing the last repeater, the output node's input signal is the
    `if _ then 15 else 0` value set on the repeater. -/
theorem getInputSignal_fired_lastRep (w : World)
    (lastRep outputNode : Nat) (ndLast ndOut : NodeData)
    (hne : lastRep ≠ outputNode)
    (hgetLast : w.getNode lastRep = some ndLast)
    (hgetOut : w.getNode outputNode = some ndOut)
    (hinputsOut : ndOut.inputs = [lastRep]) :
    (w.updateNode lastRep (fun nd =>
        { nd with sigLevel := if w.getInputSignal lastRep > 0 then 15 else 0 })).getInputSignal
        outputNode = if w.getInputSignal lastRep > 0 then 15 else 0 := by
  dsimp [getInputSignal]
  simp [getNode_updateNode_ne, hne.symm, hgetOut, hinputsOut,
    getNode_updateNode_self, hgetLast]

/-- A message `"{chainName i}: {sig}"` with `sig ∈ {0, 15}` is chain `i`'s
    output entry. -/
private theorem nat_repr_zero : Nat.repr 0 = "0" := by native_decide
private theorem nat_repr_fifteen : Nat.repr 15 = "15" := by native_decide

theorem isOutputEntry_of_sig (i sig : Nat) (hsig : sig = 0 ∨ sig = 15) :
    isOutputEntry (s!"{chainName i}: {sig}") i = true := by
  dsimp [isOutputEntry]
  rcases hsig with rfl | rfl
  · have hstr : s!"{chainName i}: {0}" = s!"{chainName i}: 0" := by
      ext : 1
      simp [nat_repr_zero]
      native_decide
    rw [hstr]
    simp
  · have hstr : s!"{chainName i}: {15}" = s!"{chainName i}: 15" := by
      ext : 1
      simp [nat_repr_fifteen]
      native_decide
    rw [hstr]
    simp

/-- Firing the last repeater appends chain `i`'s output entry. -/
theorem onScheduledTick_lastRep_isOutput (w : World) (specs : List ChainSpec)
    (i : Nat) (ndLast ndOut : NodeData)
    (hne : chainOutputId specs i ≠ chainRepId specs i (repLenAt specs i))
    (hgetLast : w.getNode (chainRepId specs i (repLenAt specs i)) = some ndLast)
    (hkindLast : ndLast.kind = NodeKind.repeater (stageDelayAt specs i (repLenAt specs i))
        (stagePriAt specs i (repLenAt specs i)))
    (houtsLast : ndLast.outputs = [chainOutputId specs i])
    (hgetOut : w.getNode (chainOutputId specs i) = some ndOut)
    (hkindOut : ndOut.kind = NodeKind.output (chainName i))
    (hinputsOut : ndOut.inputs = [chainRepId specs i (repLenAt specs i)]) :
    ∃ msg, (w.onScheduledTick (chainRepId specs i (repLenAt specs i))).outputLog =
        w.outputLog ++ [msg] ∧
      (w.onScheduledTick (chainRepId specs i (repLenAt specs i))).events = w.events ∧
      isOutputEntry msg i = true := by
  set w1 := w.updateNode (chainRepId specs i (repLenAt specs i)) (fun nd =>
    { nd with sigLevel := if w.getInputSignal (chainRepId specs i (repLenAt specs i)) > 0 then 15 else 0 }) with hw1
  have hrep : w.onScheduledTick (chainRepId specs i (repLenAt specs i)) =
      w1.onNeighborUpdate (chainOutputId specs i) := by
    rw [onScheduledTick_repeater_notify w (chainRepId specs i (repLenAt specs i))
      (chainOutputId specs i) ndLast (stageDelayAt specs i (repLenAt specs i))
      (stagePriAt specs i (repLenAt specs i)) hgetLast hkindLast houtsLast]
  have hgetOut1 : w1.getNode (chainOutputId specs i) = some ndOut := by
    dsimp [w1]
    rw [getNode_updateNode_ne w (chainRepId specs i (repLenAt specs i))
      (chainOutputId specs i)
      (fun nd => { nd with sigLevel := if w.getInputSignal (chainRepId specs i (repLenAt specs i)) > 0 then 15 else 0 }) hne]
    exact hgetOut
  have hon : w1.onNeighborUpdate (chainOutputId specs i) =
      w1.logOutput s!"{chainName i}: {w1.getInputSignal (chainOutputId specs i)}" := by
    dsimp [onNeighborUpdate]
    simp [hgetOut1, hkindOut]
  have hsig : w1.getInputSignal (chainOutputId specs i) = 0 ∨
      w1.getInputSignal (chainOutputId specs i) = 15 := by
    dsimp [w1]
    have hgi := getInputSignal_fired_lastRep w
      (chainRepId specs i (repLenAt specs i)) (chainOutputId specs i)
      ndLast ndOut hne.symm hgetLast hgetOut hinputsOut
    rw [hgi]
    by_cases h : w.getInputSignal (chainRepId specs i (repLenAt specs i)) > 0
    · simp [h]
    · simp [h]
  refine ⟨s!"{chainName i}: {w1.getInputSignal (chainOutputId specs i)}", ?_, ?_, ?_⟩
  · rw [hrep, hon]
    dsimp [w1, World.logOutput]
    rfl
  · rw [hrep, hon]
    dsimp [w1, World.logOutput]
  · exact isOutputEntry_of_sig i (w1.getInputSignal (chainOutputId specs i)) hsig

/-! ## String injectivity

`chainName i = toString i = Nat.repr i`, so equal names come from equal
indices, and a chain's output message uniquely determines its index. -/

/-- `chainName` is injective. -/
theorem chainName_inj {i j : Nat} (h : chainName i = chainName j) : i = j := by
  dsimp [chainName] at h
  exact Nat.repr_inj.mp h

/-- Every char of `Nat.repr n` is a decimal digit. -/
private theorem repr_toList_isDigit (n : Nat) :
    ∀ c ∈ (Nat.repr n).toList, c.isDigit = true := by
  intro c hc
  rw [Nat.toList_repr] at hc
  exact Nat.isDigit_of_mem_toDigits (b := 10) (by decide) (by decide) hc

/-- `List.takeWhile` of a digit prefix stops at the first `':'`. -/
private theorem takeWhile_digit_prefix {di rest : List Char}
    (hdi : ∀ c ∈ di, c.isDigit = true) (hcolon : (':').isDigit = false) :
    (di ++ ':' :: rest).takeWhile (fun c => c.isDigit) = di := by
  induction di with
  | nil => simp [hcolon]
  | cons d ds ih =>
    have hd : d.isDigit = true := hdi d (List.mem_cons.mpr (Or.inl rfl))
    simp [hd, ih (fun c hc => hdi c (List.mem_cons.mpr (Or.inr hc)))]

/-- The digit prefix of a chain message is the chain's own repr. -/
private theorem digit_prefix_eq (di dj si sj : List Char)
    (hdi : ∀ c ∈ di, c.isDigit = true) (hdj : ∀ c ∈ dj, c.isDigit = true)
    (h : (di ++ [':', ' ']) ++ si = (dj ++ [':', ' ']) ++ sj) :
    di = dj := by
  have hcolon : (':').isDigit = false := by native_decide
  have hcons : di ++ ':' :: ' ' :: si = dj ++ ':' :: ' ' :: sj := by
    simpa [List.append_assoc] using h
  have htake : di = (di ++ ':' :: ' ' :: si).takeWhile (fun c => c.isDigit) :=
    (takeWhile_digit_prefix hdi hcolon).symm
  have htake' : dj = (dj ++ ':' :: ' ' :: sj).takeWhile (fun c => c.isDigit) :=
    (takeWhile_digit_prefix hdj hcolon).symm
  rw [hcons] at htake
  exact htake.trans htake'.symm

/-- `(": ").toList` is `[':', ' ']`. -/
private theorem toList_colon_space : (": ").toList = [':', ' '] := by native_decide

/-- A chain's output message reduces to its repr, separator, and signal. -/
theorem chainMsg_repr (i sig : Nat) :
    s!"{chainName i}: {sig}" = Nat.repr i ++ ": " ++ Nat.repr sig := by
  rfl

/-- `{0}` interpolates to the literal `"0"`. -/
theorem chainMsg_lit_zero (i : Nat) :
    s!"{chainName i}: {0}" = s!"{chainName i}: 0" := by
  ext : 1
  simp [nat_repr_zero]
  native_decide

/-- `{15}` interpolates to the literal `"15"`. -/
theorem chainMsg_lit_fifteen (i : Nat) :
    s!"{chainName i}: {15}" = s!"{chainName i}: 15" := by
  ext : 1
  simp [nat_repr_fifteen]
  native_decide

/-- A chain's output message uniquely determines its index. -/
theorem chainMsg_inj (i j sig sig' : Nat) :
    s!"{chainName i}: {sig}" = s!"{chainName j}: {sig'}" → i = j := by
  intro h
  have hred : Nat.repr i ++ ": " ++ Nat.repr sig = Nat.repr j ++ ": " ++ Nat.repr sig' := by
    rw [← chainMsg_repr i sig, ← chainMsg_repr j sig']
    exact h
  apply Nat.repr_inj.mp
  apply String.ext
  have hlist := congrArg String.toList hred
  have hsep : (Nat.repr i).toList ++ [':', ' '] ++ (Nat.repr sig).toList =
      (Nat.repr j).toList ++ [':', ' '] ++ (Nat.repr sig').toList := by
    simpa [String.toList_append, toList_colon_space] using hlist
  exact digit_prefix_eq (Nat.repr i).toList (Nat.repr j).toList
    (Nat.repr sig).toList (Nat.repr sig').toList
    (repr_toList_isDigit i) (repr_toList_isDigit j) hsep

/-- If chain `j`'s message is an output entry of chain `i`, then `i = j`. -/
theorem isOutputEntry_of_msg (i j sig : Nat)
    (h : isOutputEntry (s!"{chainName j}: {sig}") i = true) : i = j := by
  dsimp [isOutputEntry] at h
  cases hb : s!"{chainName j}: {sig}" == s!"{chainName i}: 0" with
  | true =>
      have heq : s!"{chainName j}: {sig}" = s!"{chainName i}: 0" :=
        LawfulBEq.eq_of_beq hb
      rw [← chainMsg_lit_zero i] at heq
      exact chainMsg_inj i j 0 sig heq.symm
  | false =>
      rw [hb] at h
      simp at h
      rw [← chainMsg_lit_fifteen i] at h
      exact chainMsg_inj i j 15 sig h.symm

/-- A chain's output message is not an output entry of a different chain. -/
theorem isOutputEntry_of_ne (i j sig : Nat) (hij : i ≠ j) :
    isOutputEntry (s!"{chainName j}: {sig}") i = false := by
  cases hb : isOutputEntry (s!"{chainName j}: {sig}") i with
  | true => exact False.elim (hij (isOutputEntry_of_msg i j sig hb))
  | false => rfl

/-! ## `findIdx?` list lemmas -/

/-- `findIdx?` commutes with `map`. -/
theorem findIdx?_map {α β : Type} (p : β → Bool) (f : α → β)
    (l : List α) :
    _root_.findIdx? p (l.map f) = _root_.findIdx? (p ∘ f) l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    dsimp [_root_.findIdx?, List.map]
    by_cases h : p (f x)
    · simp [h]
    · simp [h, ih]

/-- `findIdx?` over an append. -/
theorem findIdx?_append {α : Type} (p : α → Bool) (l₁ l₂ : List α) :
    _root_.findIdx? p (l₁ ++ l₂) =
      match _root_.findIdx? p l₁ with
      | some k => some k
      | none => (_root_.findIdx? p l₂).map (fun k => l₁.length + k) := by
  induction l₁ with
  | nil => simp [_root_.findIdx?]
  | cons x xs ih =>
    dsimp [_root_.findIdx?]
    by_cases h : p x
    · simp [h]
    · simp [h]
      rw [ih]
      cases hxs : _root_.findIdx? p xs with
      | none =>
          simp
          congr 1
          funext k
          dsimp [List.length]
          omega
      | some k => simp

/-- `findIdx?` is `none` iff no element satisfies the predicate. -/
theorem findIdx?_eq_none_iff {α : Type} (p : α → Bool) (l : List α) :
    _root_.findIdx? p l = none ↔ ∀ a ∈ l, p a = false := by
  induction l with
  | nil => simp [_root_.findIdx?]
  | cons x xs ih =>
    dsimp [_root_.findIdx?]
    by_cases h : p x
    · simp [h]
    · simp [h, ih]

/-- The output position of chain `i` in a log formed as a prefix followed
    by one entry per firing chain. -/
theorem outputPos_prefix_map (pre : List String) (order : List Nat)
    (entry : Nat → String) (i : Nat)
    (h_pre : ∀ a ∈ pre, isOutputEntry a i = false)
    (h_entry : ∀ k : Nat, isOutputEntry (entry k) i = (k == i)) :
    outputPos (pre ++ order.map entry) i =
      (_root_.findIdx? (fun k => k == i) order).map (fun r => pre.length + r) := by
  dsimp [outputPos]
  have hmain : _root_.findIdx? ((fun s => isOutputEntry s i) ∘ entry) order =
      _root_.findIdx? (fun k => k == i) order := by
    congr 1
    funext k
    exact h_entry k
  rw [_root_.findIdx?_append, _root_.findIdx?_map]
  have hnone : _root_.findIdx? (fun s => isOutputEntry s i) pre = none := by
    rw [_root_.findIdx?_eq_none_iff]
    intro a ha
    exact h_pre a ha
  rw [hnone]
  simp [hmain]

/-! ## Output-node wiring and the last-repeater message -/

/-- Matching wiring transfers a full `(kind, inputs, outputs)` triple
    between worlds. -/
theorem wiring_full_exists (v w : World) (id : Nat)
    (K : NodeKind) (I O : List Nat)
    (hwv : (v.getNode id).map wiring = (w.getNode id).map wiring)
    (hbuild : ∃ nd, w.getNode id = some nd ∧ nd.kind = K ∧
      nd.inputs = I ∧ nd.outputs = O) :
    ∃ nd, v.getNode id = some nd ∧ nd.kind = K ∧
      nd.inputs = I ∧ nd.outputs = O := by
  obtain ⟨nd, hget, hkind, hinputs, houts⟩ := hbuild
  cases hgetV : v.getNode id with
  | none =>
    rw [hgetV, hget] at hwv
    dsimp [Option.map] at hwv
    cases hwv
  | some nd' =>
    rw [hgetV, hget] at hwv
    dsimp [Option.map] at hwv
    injection hwv with htriple
    dsimp [wiring] at htriple
    refine ⟨nd', rfl, ?_, ?_, ?_⟩
    · rw [← hkind]
      exact congrArg Prod.fst htriple
    · have := congrArg Prod.snd htriple
      rw [Prod.mk.injEq] at this
      rw [← hinputs]
      exact this.1
    · have := congrArg Prod.snd htriple
      rw [Prod.mk.injEq] at this
      rw [← houts]
      exact this.2

/-- The output node keeps its full wiring (kind, inputs, outputs) in every
    tick-start world. -/
theorem simWorld_output_wiring_full (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat) (t i : Nat)
    (hi : i < specs.length) (hpri : (specAt specs i).priLenOk) :
    ∃ nd, (simWorld T specs actOrd pos t).getNode (chainOutputId specs i) =
        some nd ∧
      nd.kind = NodeKind.output (chainName i) ∧
      nd.inputs = [chainRepId specs i (repLenAt specs i)] ∧
      nd.outputs = [] := by
  have hw := simWorld_getNode_wiring T specs actOrd pos t (chainOutputId specs i)
  rw [buildChains_getNode_output' specs i hi hpri] at hw
  dsimp [wiring] at hw
  cases hget : (simWorld T specs actOrd pos t).getNode
      (chainOutputId specs i) with
  | none =>
    rw [hget] at hw
    dsimp [Option.map] at hw
    cases hw
  | some nd =>
    rw [hget] at hw
    dsimp [Option.map] at hw
    injection hw with htriple
    dsimp [wiring] at htriple
    have hkind := congrArg Prod.fst htriple
    have hrest := congrArg Prod.snd htriple
    rw [Prod.mk.injEq] at hrest
    refine ⟨nd, rfl, hkind, ?_, hrest.2⟩
    rw [hrest.1]
    dsimp [chainRepId, repLenAt]

/-- Firing chain `i`'s last repeater (when its wiring is intact) appends
    exactly one output entry of chain `i`. -/
theorem fire_lastRep_isOutput (u : World) (_T : Nat)
    (specs : List ChainSpec) (i : Nat) (hi : i < specs.length)
    (hpri : (specAt specs i).priLenOk)
    (hwRep : (u.getNode (chainRepId specs i (repLenAt specs i))).map wiring =
      ((buildChains specs).1.getNode (chainRepId specs i (repLenAt specs i))).map wiring)
    (hwOut : (u.getNode (chainOutputId specs i)).map wiring =
      ((buildChains specs).1.getNode (chainOutputId specs i)).map wiring) :
    ∃ msg, (u.onScheduledTick (chainRepId specs i (repLenAt specs i))).outputLog =
        u.outputLog ++ [msg] ∧
      isOutputEntry msg i = true := by
  have hbRep := buildChains_getNode_rep specs i (repLenAt specs i) hi hpri
    (by dsimp [repLenAt]; omega)
  obtain ⟨ndRep, hgetRep, hkindRep, _, houtsRep⟩ := wiring_full_exists u
    (buildChains specs).1 (chainRepId specs i (repLenAt specs i))
    (NodeKind.repeater (stageDelayAt specs i (repLenAt specs i))
      (stagePriAt specs i (repLenAt specs i)))
    [chainBaseId specs i + 1 + repLenAt specs i]
    [chainBaseId specs i + 3 + repLenAt specs i]
    hwRep
    ⟨{ kind := NodeKind.repeater (stageDelayAt specs i (repLenAt specs i))
         (stagePriAt specs i (repLenAt specs i)),
       sigLevel := 0,
       inputs := [chainBaseId specs i + 1 + repLenAt specs i],
       outputs := [chainBaseId specs i + 3 + repLenAt specs i] },
     hbRep, rfl, rfl, rfl⟩
  have hbOut := buildChains_getNode_output' specs i hi hpri
  obtain ⟨ndOut, hgetOut, hkindOut, hinputsOut, _⟩ := wiring_full_exists u
    (buildChains specs).1 (chainOutputId specs i)
    (NodeKind.output (chainName i))
    [chainBaseId specs i + 2 + repLenAt specs i] []
    hwOut
    ⟨{ kind := NodeKind.output (chainName i), sigLevel := 0,
       inputs := [chainBaseId specs i + 2 + repLenAt specs i],
       outputs := [] },
     hbOut, rfl, rfl, rfl⟩
  have hne : chainOutputId specs i ≠ chainRepId specs i (repLenAt specs i) := by
    dsimp [chainOutputId, chainRepId, repLenAt]
    omega
  have houtsRep' : ndRep.outputs = [chainOutputId specs i] := by
    rw [houtsRep]
    dsimp [chainOutputId]
  have hinputsOut' : ndOut.inputs = [chainRepId specs i (repLenAt specs i)] := by
    rw [hinputsOut]
    dsimp [chainRepId]
  obtain ⟨msg, hlog, _, hisOut⟩ := onScheduledTick_lastRep_isOutput u specs i
    ndRep ndOut hne hgetRep hkindRep houtsRep' hgetOut hkindOut hinputsOut'
  exact ⟨msg, hlog, hisOut⟩

/-! ## The drain's last-repeater messages -/

/-- Firing the k-th pop of a tick-invariant world, when it is a
    last-repeater event, appends exactly one output entry of that
    chain. -/
theorem drain_fire_lastRep_msg (T : Nat) (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (t : Nat) (q₀ acts : List ScheduledEvent) (v : World)
    (htick : v.tick = t) (hinv : TickInv T specs t q₀ acts v) :
    ∀ (k : Nat) (hk : k < (popSeq v).length) (u : World),
      u.tick = v.tick →
      u.events = eraseEvents v.events ((popSeq v).take (k + 1)) ++
        spawnFold (cascadeSpawn T specs) ((popSeq v).take k) →
      (∀ id, id ∉ ((popSeq v).take k).map (fun e => e.nodeId) →
        u.getNode id = v.getNode id) →
      lastRepOf T specs ((popSeq v)[k]'hk) →
      ∃ msg,
        (u.onScheduledTick ((popSeq v)[k]'hk).nodeId).outputLog =
          u.outputLog ++ [msg] ∧
        ∃ i < specs.length,
          (popSeq v)[k]'hk = stageEventOf T specs i (repLenAt specs i) ∧
          isOutputEntry msg i = true := by
  rcases hinv with ⟨hnd, hwir, hgood, hsrc, hfresh⟩
  intro k hk u hutik hevs hframe hlast
  rcases hlast with ⟨i, hi, heq⟩
  rw [heq]
  have hmem : stageEventOf T specs i (repLenAt specs i) ∈ popSeq v := by
    rw [← heq]
    exact List.getElem_mem hk
  have hdue := popSeq_mem_due v (stageEventOf T specs i (repLenAt specs i)) hmem
  have hcl' : IsCascadeEv T specs (stageEventOf T specs i (repLenAt specs i)) :=
    hgood _ hdue.2
  have hnp := popSeq_nodup_of_tickInv T specs h_valid t q₀ acts v htick
    ⟨hnd, hwir, hgood, hsrc, hfresh⟩
  have hnotTake : (popSeq v)[k]'hk ∉ (popSeq v).take k :=
    getElem_not_mem_take_of_nodup (popSeq v) k hk hnp
  have hfRep : chainRepId specs i (repLenAt specs i) ∉
      ((popSeq v).take k).map (fun ev => ev.nodeId) := by
    intro hm
    obtain ⟨p, hp, hpN⟩ := List.mem_map.mp hm
    have hpPop : p ∈ popSeq v := mem_of_take (popSeq v) k p hp
    have hpdue := popSeq_mem_due v p hpPop
    have hpc : IsCascadeEv T specs p := hgood p hpdue.2
    have hpe : p = stageEventOf T specs i (repLenAt specs i) := by
      apply cascade_nodeId_inj T specs h_valid p
        (stageEventOf T specs i (repLenAt specs i)) hpc hcl'
      rw [hpN]
      simp [stageEventOf]
    exact hnotTake (by simpa [hpe, heq] using hp)
  have hfOut : chainOutputId specs i ∉
      ((popSeq v).take k).map (fun ev => ev.nodeId) := by
    intro hm
    obtain ⟨p, hp, hpN⟩ := List.mem_map.mp hm
    have hpPop : p ∈ popSeq v := mem_of_take (popSeq v) k p hp
    have hpdue := popSeq_mem_due v p hpPop
    have hpc : IsCascadeEv T specs p := hgood p hpdue.2
    exact chainOutputId_not_cascade_nodeId T specs h_valid i hi p hpc hpN
  have hwRep : (u.getNode (chainRepId specs i (repLenAt specs i))).map wiring =
      ((buildChains specs).1.getNode (chainRepId specs i (repLenAt specs i))).map wiring := by
    rw [hframe (chainRepId specs i (repLenAt specs i)) hfRep,
      hwir (chainRepId specs i (repLenAt specs i))]
  have hwOut : (u.getNode (chainOutputId specs i)).map wiring =
      ((buildChains specs).1.getNode (chainOutputId specs i)).map wiring := by
    rw [hframe (chainOutputId specs i) hfOut, hwir (chainOutputId specs i)]
  obtain ⟨msg, hlog, hisOut⟩ := fire_lastRep_isOutput u T specs i hi
    (h_valid i hi).1 hwRep hwOut
  refine ⟨msg, ?_, ?_⟩
  · simpa [stageEventOf] using hlog
  · refine ⟨i, hi, rfl, hisOut⟩

/-- Draining a tick whose pop sequence consists entirely of last-repeater
    events appends, in pop order, exactly one output entry per pop,
    each matching its chain. -/
theorem stepUntilNextTick_lastRep_messages (w : World) (T : Nat)
    (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (t : Nat) (q₀ acts : List ScheduledEvent)
    (htick : w.tick = t) (hinv : TickInv T specs t q₀ acts w)
    (h_all : ∀ e ∈ popSeq w, lastRepOf T specs e) :
    ∃ msgs : List String,
      w.stepUntilNextTick.outputLog = w.outputLog ++ msgs ∧
      msgs.length = (popSeq w).length ∧
      ∀ (k : Nat) (hk : k < (popSeq w).length),
        ∃ i < specs.length,
          (popSeq w)[k]'hk = stageEventOf T specs i (repLenAt specs i) ∧
          isOutputEntry (msgs[k]?.getD "") i = true := by
  induction w using World.stepUntilNextTick.induct with
  | case1 x hstep =>
    have hnone : x.popNextEvent = none := by
      dsimp [World.step] at hstep
      cases hp : x.popNextEvent <;> simp_all
    have hseq : popSeq x = [] := popSeq_of_popNextEvent_none x hnone
    rw [stepUntilNextTick_of_step_none x hstep]
    refine ⟨[], ?_, ?_, ?_⟩
    · rw [List.append_nil]
    · simp [hseq]
    · intro k hk
      simp [hseq] at hk
  | case2 x w' hstep ih =>
    dsimp [World.step] at hstep
    cases hpop : x.popNextEvent with
    | none => simp [hpop] at hstep
    | some pr =>
      rcases pr with ⟨e0, wp⟩
      have hw' : w' = wp.onScheduledTick e0.nodeId := by
        apply Eq.symm
        simpa [World.step, hpop] using hstep
      subst hw'
      set es := popSeq (wp.onScheduledTick e0.nodeId) with hesdef
      have hseq : popSeq x = e0 :: es := by
        rw [popSeq_of_popNextEvent_some x e0 wp hpop, hesdef]
      have hstepUNT : x.stepUntilNextTick =
          (wp.onScheduledTick e0.nodeId).stepUntilNextTick := by
        rw [World.stepUntilNextTick]
        dsimp [World.step]
        rw [hpop]
      have he0last : lastRepOf T specs e0 :=
        h_all e0 (by rw [hseq]; exact List.mem_cons.mpr (Or.inl rfl))
      have hlast0 : lastRepOf T specs ((popSeq x)[0]'(by
          rw [hseq]; exact Nat.zero_lt_succ _)) := by
        simpa [hseq] using he0last
      obtain ⟨idx, hidx, herase, hget, htickE, _, hfirst⟩ :=
        popNextEvent_first_occ x e0 wp hpop
      have hwpEv : wp.events = eraseEvents x.events ((popSeq x).take 1) := by
        rw [hseq]
        change wp.events = eraseEvents x.events [e0]
        rw [herase, eraseIdx_eq_eraseEv x.events idx hidx e0 hget hfirst]
        dsimp [eraseEvents]
      -- firing e0 (k = 0)
      have htick0 := World.popNextEvent_tick x e0 wp hpop
      have hframe0 : ∀ id, id ∉ ((popSeq x).take 0).map (fun e => e.nodeId) →
          wp.getNode id = x.getNode id := by
        intro id _
        dsimp [World.getNode]
        rw [popNextEvent_nodes x e0 wp hpop]
      have hfire0 := drain_fire_lastRep_msg T specs h_valid t q₀ acts x
        htick hinv 0 (by rw [hseq]; exact Nat.zero_lt_succ _) wp
        htick0 (by rw [hwpEv]; dsimp [spawnFold]; rw [List.append_nil])
        hframe0 hlast0
      obtain ⟨msg0, hlog0, i0, hi0, heq0, hisOut0⟩ := hfire0
      have hlog0' : (wp.onScheduledTick e0.nodeId).outputLog =
          wp.outputLog ++ [msg0] := by
        simpa [hseq] using hlog0
      -- the IH applies to the tail
      have htick' : (wp.onScheduledTick e0.nodeId).tick = t := by
        rw [World.onScheduledTick_tick, htick0, htick]
      have hinv' : TickInv T specs t q₀ acts (wp.onScheduledTick e0.nodeId) := by
        exact tickInv_pop_fire T specs h_valid t q₀ acts x
          (wp.onScheduledTick e0.nodeId) htick
          (by dsimp [World.step]; rw [hpop]) hinv
      have h_all' : ∀ e ∈ popSeq (wp.onScheduledTick e0.nodeId),
          lastRepOf T specs e := by
        intro e he
        exact h_all e (by rw [hseq]; exact List.mem_cons.mpr (Or.inr he))
      obtain ⟨msgs', hlog', hlen', hcont'⟩ := ih htick' hinv' h_all'
      -- assemble
      refine ⟨msg0 :: msgs', ?_, ?_, ?_⟩
      · rw [hstepUNT, hlog', hlog0']
        rw [popNextEvent_outputLog x e0 wp hpop]
        simp
      · rw [List.length_cons, hlen', hseq]
        rfl
      · intro k hk
        rw [hseq] at hk
        cases k with
        | zero =>
          refine ⟨i0, hi0, ?_, ?_⟩
          · simpa [hseq] using heq0
          · simpa using hisOut0
        | succ k' =>
          have hk' : k' < es.length := by
            dsimp at hk
            omega
          obtain ⟨i, hi, heqi, hisOuti⟩ := hcont' k' hk'
          refine ⟨i, hi, ?_, ?_⟩
          · simpa [hseq, hesdef] using heqi
          · simpa using hisOuti

/-! ## The tick-`T` pop sequence is the last-repeater cohort -/

/-- `stageTickOf` is strictly increasing below `repLenAt`. -/
theorem stageTickOf_strictMono (T : Nat) (specs : List ChainSpec)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (i s t : Nat) (hi : i < specs.length) (hst : s < t)
    (ht : t ≤ repLenAt specs i) :
    stageTickOf T specs i s < stageTickOf T specs i t := by
  induction t generalizing s with
  | zero => cases hst
  | succ t' ih =>
    by_cases hsucc : s = t'
    · subst s
      rw [stageTickOf_succ T specs i t' (by dsimp [repLenAt] at ht; omega)]
      have hd := ValidDelay.ge2 (stageDelayAt_valid specs h_valid i (t' + 1) hi)
      omega
    · have hslt : s < t' := by omega
      have ht' : t' ≤ repLenAt specs i := by omega
      have hrest := ih s hslt ht'
      have hsuccE := stageTickOf_succ T specs i t' (by dsimp [repLenAt] at ht; omega)
      have hd := ValidDelay.ge2 (stageDelayAt_valid specs h_valid i (t' + 1) hi)
      omega

/-- Every pop at tick `T` is a last-repeater event. -/
theorem popSeq_simWorld_lastRep (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (h_fit : ∀ i < specs.length, chainDelay (specAt specs i) ≤ T) :
    ∀ e ∈ popSeq (simWorld T specs actOrd pos T), lastRepOf T specs e := by
  intro e he
  have hdue := popSeq_mem_due (simWorld T specs actOrd pos T) e he
  have hcl := simWorld_classification T specs actOrd pos h_valid h_perm T e hdue.2
  rcases hcl with ⟨i, hi, heq⟩ | ⟨i, hi, s, hs, heq⟩
  · exfalso
    rw [heq] at hdue
    have hd : 2 < chainDelay (specAt specs i) := by
      dsimp [chainDelay, ChainSpec.totalDelay]
      have hlast : 2 ≤ ((specAt specs i).lastDelay : Nat) :=
        ValidDelay.ge2 (h_valid i hi).2.2.1
      have hsum : 0 ≤ ((specAt specs i).middleDelays.map (fun d => (d : Nat))).sum :=
        Nat.zero_le _
      omega
    have htick : obsTickOf T specs i < T := by
      simp [obsTickOf, actTickOf]
      have hfiti : chainDelay (specAt specs i) ≤ T := h_fit i hi
      omega
    have htick_eq : obsTickOf T specs i = T := by
      dsimp [obsEventOf] at hdue
      exact hdue.1.trans (simWorld_tick T specs actOrd pos T)
    omega
  · rw [heq]
    have htickE : stageTickOf T specs i s = T := by
      rw [heq] at hdue
      dsimp [stageEventOf] at hdue
      exact hdue.1.trans (simWorld_tick T specs actOrd pos T)
    by_cases hlt : s < repLenAt specs i
    · exfalso
      have hmono := stageTickOf_strictMono T specs h_valid i s
        (repLenAt specs i) hi hlt le_rfl
      rw [stageTickOf_last T specs i (h_fit i hi)] at hmono
      rw [htickE] at hmono
      exact (Nat.lt_irrefl _ hmono)
    · have hs' : s ≤ repLenAt specs i := by simpa [repLenAt] using hs
      have heq_s : s = repLenAt specs i := by omega
      rw [heq_s]
      exact ⟨i, hi, rfl⟩

/-- `"tick k"` is never a chain output message. -/
private theorem tick_ne_msg (k i sig : Nat) :
    s!"tick {k}" ≠ s!"{chainName i}: {sig}" := by
  intro h
  have hhead := congrArg (fun s : String => s.toList[0]?) h
  have hk : (s!"tick {k}").toList[0]? = some 't' := by
    change (("tick " ++ Nat.repr k).toList)[0]? = some 't'
    rw [String.toList_append]
    simp
  have hne : (Nat.repr i).toList ≠ [] := by
    intro he
    exact (Nat.repr_ne_empty (n := i)) ((String.toList_eq_nil_iff).mp he)
  have h0 : 0 < (Nat.repr i).toList.length := by
    cases hh : (Nat.repr i).toList with
    | nil => exact False.elim (hne hh)
    | cons c cs => simp [List.length]
  have hd : ∃ c, (s!"{chainName i}: {sig}").toList[0]? = some c ∧
      c.isDigit = true := by
    refine ⟨(Nat.repr i).toList[0]'h0, ?_, ?_⟩
    · rw [chainMsg_repr i sig, String.toList_append, String.toList_append]
      rw [List.append_assoc]
      rw [List.getElem?_append_left h0, List.getElem?_eq_getElem h0]
    · exact (repr_toList_isDigit i) _ (List.getElem_mem h0)
  rw [hk] at hhead
  rcases hd with ⟨c, hchead, hcdigit⟩
  rw [hchead] at hhead
  injection hhead with htc
  have ht_not_digit : ('t').isDigit = false := by native_decide
  rw [← htc] at hcdigit
  rw [ht_not_digit] at hcdigit
  contradiction

/-- `isOutputEntry` never matches a tick marker. -/
theorem isOutputEntry_tick (k i : Nat) :
    isOutputEntry (s!"tick {k}") i = false := by
  dsimp [isOutputEntry]
  have h0 : (s!"tick {k}" == s!"{chainName i}: 0") = false := by
    rw [beq_eq_false_iff_ne, ← chainMsg_lit_zero i]
    exact tick_ne_msg k i 0
  have h15 : (s!"tick {k}" == s!"{chainName i}: 15") = false := by
    rw [beq_eq_false_iff_ne, ← chainMsg_lit_fifteen i]
    exact tick_ne_msg k i 15
  rw [h0, h15]
  rfl
