import BasicProofs.PrefixChain.Part06


open BasicRedstoneSim

/-- After `buildChain`, every newly-created node has `outputs.length ≤ 1`.

**Human proof:** `buildChain` creates all nodes with `outputs := []` via `addNode`,
then calls `connectChain` which adds at most 1 output per node (by
`connectChain_outputs_length_le` + `buildChain_chainIds_nodup`).
So `outputs.length ≤ 0 + 1 = 1`. -/
theorem buildChain_outputs_le_one (w : World) (name : String) (c : ChainSpec)
    (h_ids : ∀ p ∈ w.nodes, p.1 < w.nextId) :
    let (_, w') := buildChain w name c
    ∀ id nd, w'.getNode id = some nd → w.getNode id = none → nd.outputs.length ≤ 1 := by
  dsimp only [buildChain, buildChainPre]
  dsimp (config := { zeta := true })
  intro id nd₁ h_getNode h_fresh
  refine connectChain_all_outputs_le_one _ ?h_nodup _ id ?h_w nd₁ h_getNode
  · -- Nodup: chainIds are consecutive integers
    simp only [foldl_repFoldlStep_repIds_eq, foldl_repFoldlStep_nextId,
      World.addNode_fst, World.addNode_nextId, List.nil_append]
    suffices h : ∀ (a n : Nat),
        ([a, a + 1] ++ (List.range n).map (fun i => a + 2 + i) ++
        [a + 2 + n, a + 3 + n]).Nodup by
      simpa [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm] using
        h w.nextId c.middleDelays.length
    intro a n
    suffices h_eq : [a, a + 1] ++ (List.range n).map (fun i => a + 2 + i) ++
        [a + 2 + n, a + 3 + n] = (List.range (n + 4)).map (fun i => a + i) by
      rw [h_eq]
      exact List.Nodup.map (fun _ _ hij => Nat.add_left_cancel hij) (@List.nodup_range (n + 4))
    induction n with
    | zero => simp [List.range, List.range.loop]
    | succ k ih =>
      have h_rhs : (List.range (k + 5)).map (fun i => a + i) =
          (List.range (k + 4)).map (fun i => a + i) ++ [a + (k + 4)] := by
        rw [show k + 5 = (k + 4) + 1 from by omega, List.range_succ, List.map_append,
          List.map_singleton]
      rw [h_rhs]
      have h_lhs : [a, a + 1] ++ (List.range (k + 1)).map (fun i => a + 2 + i) ++
          [a + 2 + (k + 1), a + 3 + (k + 1)] =
          ([a, a + 1] ++ (List.range k).map (fun i => a + 2 + i) ++ [a + 2 + k, a + 3 + k]) ++
          [a + 4 + k] := by
        simp [List.range_succ, List.map_append, List.append_assoc]
        omega
      rw [h_lhs, ih]
      have : a + 4 + k = a + (k + 4) := by omega
      simp [this]
  · -- h_w: ∀ nd, w_pre.getNode id = some nd → nd.outputs = []
    intro nd₀ h_getNode₀
    have h_w₀ : ∀ nd', w.getNode id = some nd' → nd'.outputs = [] := by
      intro nd' h; rw [h_fresh] at h; cases h
    have h₁ := World.addNode_all_outputs_nil w
      ({ kind := NodeKind.input, sigLevel := 0, inputs := [], outputs := [] } : NodeData)
      id rfl h_w₀ (World.getNode_nextId_none w h_ids)
    have h_ids₁ := World.addNode_ids_lt_nextId w
      ({ kind := NodeKind.input, sigLevel := 0, inputs := [], outputs := [] } : NodeData) h_ids
    have h₂ := World.addNode_all_outputs_nil _
      ({ kind := NodeKind.observer, sigLevel := 0, inputs := [], outputs := [] } : NodeData)
      id rfl h₁ (World.getNode_nextId_none _ h_ids₁)
    have h_ids₂ := World.addNode_ids_lt_nextId _
      ({ kind := NodeKind.observer, sigLevel := 0, inputs := [], outputs := [] } : NodeData) h_ids₁
    have h₃ := buildChain_addNode_foldl_all_outputs_nil c.middleDelays []
      ((w.addNode { kind := NodeKind.input, sigLevel := 0, inputs := [], outputs := [] }).2.addNode
        { kind := NodeKind.observer, sigLevel := 0, inputs := [], outputs := [] }).2
      id h₂ h_ids₂
    have h_ids₃ := foldl_repFoldlStep_ids_lt_nextId c.middleDelays []
      ((w.addNode { kind := NodeKind.input, sigLevel := 0, inputs := [], outputs := [] }).2.addNode
        { kind := NodeKind.observer, sigLevel := 0, inputs := [], outputs := [] }).2 h_ids₂
    have h₄ := World.addNode_all_outputs_nil _
      ({ kind := NodeKind.repeater c.lastDelay (-1), sigLevel := 0, inputs := [], outputs := [] } : NodeData)
      id rfl h₃ (World.getNode_nextId_none _ h_ids₃)
    have h_ids₄ := World.addNode_ids_lt_nextId _
      ({ kind := NodeKind.repeater c.lastDelay (-1), sigLevel := 0, inputs := [], outputs := [] } : NodeData) h_ids₃
    exact World.addNode_all_outputs_nil _
      ({ kind := NodeKind.output name, sigLevel := 0, inputs := [], outputs := [] } : NodeData)
      id rfl h₄ (World.getNode_nextId_none _ h_ids₄) nd₀ h_getNode₀

/-! ## Main theorems -/

/-- If two foldl bodies are extensionally equal, the foldl results are equal. -/
theorem foldl_body_congr {α β : Type} (f g : α → β → α) (l : List β) (a : α)
    (h : ∀ a b, f a b = g a b) :
    l.foldl f a = l.foldl g a := by
  induction l generalizing a with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.foldl_cons, h, ih]

/-- The simulation foldl body always increments tick by 1. -/
theorem simBody_tick (w : World) (t1 t2 pos : Nat) (in1 in2 : Nat) (i : Nat) :
    (simBody t1 t2 pos in1 in2 w i).tick = w.tick + 1 := by
  dsimp (config := { zeta := true }) [simBody]
  split_ifs
  all_goals
    rw [World.tick_stepUntilNextTick]
    repeat
      first
      | rw [World.setInput_tick]
      | rw [processNEvents_tick]
      | rw [World.logOutput_tick]

/-- After `k` foldl iterations the tick equals `w₀.tick + k`. -/
theorem simFoldl_tick (w₀ : World) (t1 t2 pos : Nat) (in1 in2 : Nat) (k : Nat) :
    ((List.range k).foldl (simBody t1 t2 pos in1 in2) w₀).tick = w₀.tick + k := by
  induction k generalizing w₀ with
  | zero => simp
  | succ k' ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [simBody_tick, ih]
    omega

/-- The foldl body is independent of `pos` when `w.tick ≠ t₂`. -/
theorem simBody_pos_indep (w : World) (t1 t2 pos pos' : Nat) (in1 in2 : Nat)
    (h : w.tick ≠ t2) (i : Nat) :
    simBody t1 t2 pos in1 in2 w i = simBody t1 t2 pos' in1 in2 w i := by
  dsimp (config := { zeta := true }) [simBody]
  by_cases h₂ : w.tick = t2
  · contradiction
  · split_ifs
    <;> simp [World.setInput_tick, World.logOutput_tick] at *
    <;> try omega

/-- If `f` ignores its second argument, `foldl f` depends only on list length. -/
theorem foldl_ignore_second {α : Type} (f : α → Nat → α)
    (h_ignore : ∀ w i j, f w i = f w j) :
    ∀ (w : α) (l₁ l₂ : List Nat), l₁.length = l₂.length → l₁.foldl f w = l₂.foldl f w := by
  intro w l₁
  induction l₁ generalizing w with
  | nil =>
    intro l₂ h_len
    cases l₂ with
    | nil => rfl
    | cons _ _ => simp at h_len
  | cons hd tl ih =>
    intro l₂ h_len
    cases l₂ with
    | nil => simp at h_len
    | cons hd₂ tl₂ =>
      simp [List.foldl_cons]
      have h_len' : tl.length = tl₂.length := by simp at h_len; omega
      rw [h_ignore w hd hd₂]
      exact ih (f w hd₂) tl₂ h_len'

/-- Split a foldl over `range m` at position `n`, for `simBody` which ignores its index. -/
theorem foldl_split_simBody (t1 t2 pos in1 in2 : Nat) (w₀ : World) (n m : Nat)
    (h : n ≤ m) :
    (List.range m).foldl (simBody t1 t2 pos in1 in2) w₀ =
    (List.range (m - n)).foldl (simBody t1 t2 pos in1 in2)
      ((List.range n).foldl (simBody t1 t2 pos in1 in2) w₀) := by
  have h_range : List.range m = List.range n ++ (List.range (m - n)).map (· + n) := by
    have : m = n + (m - n) := by omega
    rw [this, List.range_add]
    simp [Nat.add_comm]
  rw [h_range, List.foldl_append]
  apply foldl_ignore_second
  · intro w i j; dsimp (config := { zeta := true }) [simBody]
  · simp

/-- After `connectChain w ids`, if a node had no inputs before, all its inputs are from `ids`. -/
theorem connectChain_inputs_subset (w : World) (ids : List Nat) (nid : Nat) (nd : NodeData)
    (h_nd : (connectChain w ids).getNode nid = some nd)
    (h_w : ∀ nd₀, w.getNode nid = some nd₀ → nd₀.inputs = []) :
    ∀ inputId ∈ nd.inputs, inputId ∈ ids := by
  dsimp [connectChain] at h_nd
  have h_foldl : ∀ (pairs : List (Nat × Nat)) (w' : World) (nd' : NodeData),
      (pairs.foldl (fun w'' (prev, curr) =>
        (w''.updateNode curr (fun nd => { nd with inputs := nd.inputs ++ [prev] })).updateNode prev
          (fun nd => { nd with outputs := nd.outputs ++ [curr] })
      ) w').getNode nid = some nd' →
      ∀ inputId ∈ nd'.inputs, inputId ∈ pairs.map (·.1) ∨ ∃ nd₀, w'.getNode nid = some nd₀ ∧ inputId ∈ nd₀.inputs := by
    intro pairs
    induction pairs with
    | nil =>
      intro w' nd' h_nd' inputId h_mem
      right; exact ⟨nd', h_nd', h_mem⟩
    | cons p rest ih =>
      intro w' nd' h_nd' inputId h_mem
      cases p with
      | mk prev curr =>
        simp only [List.foldl_cons] at h_nd'
        have h_ih := ih _ nd' h_nd' inputId h_mem
        cases h_ih with
        | inl h_in_rest =>
          left; exact List.mem_cons.mpr (Or.inr h_in_rest)
        | inr h_in_w1 =>
          obtain ⟨nd₁, h_nd₁, h_mem₁⟩ := h_in_w1
          -- Key: nd₁.inputs = nd₀.inputs ++ [prev] (if nid=curr) or nd₀.inputs (if nid≠curr)
          by_cases h_eq : nid = curr
          · -- nid = curr case
            have h_exists : ∃ nd₀, w'.getNode curr = some nd₀ := by
              by_contra h
              push Not at h
              have h_none : w'.getNode curr = none := by
                cases h' : w'.getNode curr <;> simp_all
              have := World.updateNode_preserves_getNode_none w' curr curr
                (fun nd => { nd with inputs := nd.inputs ++ [prev] }) h_none
              have := World.updateNode_preserves_getNode_none
                (w'.updateNode curr (fun nd => { nd with inputs := nd.inputs ++ [prev] }))
                curr prev (fun nd => { nd with outputs := nd.outputs ++ [curr] }) this
              rw [h_eq] at h_nd₁; simp_all
            obtain ⟨nd₀, h_nd₀⟩ := h_exists
            have h1 : (w'.updateNode curr (fun nd => { nd with inputs := nd.inputs ++ [prev] })).getNode curr =
                some { nd₀ with inputs := nd₀.inputs ++ [prev] } :=
              World.updateNode_getNode_eq w' curr _ nd₀ h_nd₀
            have h_inputs : nd₁.inputs = nd₀.inputs ++ [prev] := by
              have h_nd₁' := h_nd₁
              rw [h_eq] at h_nd₁'
              by_cases h_cp : curr = prev
              · have h2 := World.updateNode_getNode_eq
                  (w'.updateNode curr (fun nd => { nd with inputs := nd.inputs ++ [prev] }))
                  prev (fun nd => { nd with outputs := nd.outputs ++ [curr] })
                  { nd₀ with inputs := nd₀.inputs ++ [prev] } (by simpa [h_cp] using h1)
                have h_nd₁'' : ((w'.updateNode curr (fun nd => { nd with inputs := nd.inputs ++ [prev] })).updateNode
                    prev (fun nd => { nd with outputs := nd.outputs ++ [curr] })).getNode prev = some nd₁ := by
                  simpa [h_cp] using h_nd₁'
                have h_nd_eq := Option.some_inj.mp (h_nd₁''.symm.trans h2)
                rw [h_nd_eq]
              · have h2 := World.updateNode_getNode_ne
                  (w'.updateNode curr (fun nd => { nd with inputs := nd.inputs ++ [prev] }))
                  prev curr (fun nd => { nd with outputs := nd.outputs ++ [curr] }) (fun h => h_cp h.symm)
                rw [h2, h1] at h_nd₁'
                have h_nd_eq := (Option.some_inj.mp h_nd₁').symm
                rw [h_nd_eq]
            rw [h_inputs] at h_mem₁
            simp only [List.mem_append, List.mem_singleton] at h_mem₁
            cases h_mem₁ with
            | inl h => right; exact ⟨nd₀, by rwa [h_eq], h⟩
            | inr h => left; exact List.mem_cons.mpr (Or.inl h)
          · -- nid ≠ curr case
            have h1 : (w'.updateNode curr (fun nd => { nd with inputs := nd.inputs ++ [prev] })).getNode nid =
                w'.getNode nid :=
              World.updateNode_getNode_ne w' curr nid _ (fun h => h_eq h.symm)
            have h_exists : ∃ nd₀, w'.getNode nid = some nd₀ := by
              by_contra h
              push Not at h
              have h_none : w'.getNode nid = none := by
                cases h' : w'.getNode nid <;> simp_all
              have := World.updateNode_preserves_getNode_none w' nid curr
                (fun nd => { nd with inputs := nd.inputs ++ [prev] }) h_none
              have := World.updateNode_preserves_getNode_none
                (w'.updateNode curr (fun nd => { nd with inputs := nd.inputs ++ [prev] }))
                nid prev (fun nd => { nd with outputs := nd.outputs ++ [curr] }) this
              simp_all
            obtain ⟨nd₀, h_nd₀⟩ := h_exists
            have h_inputs : nd₁.inputs = nd₀.inputs := by
              have h2 : (w'.updateNode curr (fun nd => { nd with inputs := nd.inputs ++ [prev] })).getNode nid =
                  some nd₀ := by rw [h1, h_nd₀]
              by_cases h_np : nid = prev
              · have h3 := World.updateNode_getNode_eq
                  (w'.updateNode curr (fun nd => { nd with inputs := nd.inputs ++ [prev] }))
                  prev (fun nd => { nd with outputs := nd.outputs ++ [curr] }) nd₀ (by simpa [h_np] using h2)
                have h_nd₁' : ((w'.updateNode curr (fun nd => { nd with inputs := nd.inputs ++ [prev] })).updateNode
                    prev (fun nd => { nd with outputs := nd.outputs ++ [curr] })).getNode prev = some nd₁ := by
                  simpa [h_np] using h_nd₁
                have h_nd_eq := Option.some_inj.mp (h_nd₁'.symm.trans h3)
                rw [h_nd_eq]
              · have h3 := World.updateNode_getNode_ne
                  (w'.updateNode curr (fun nd => { nd with inputs := nd.inputs ++ [prev] }))
                  prev nid (fun nd => { nd with outputs := nd.outputs ++ [curr] }) (fun h => h_np h.symm)
                rw [h3, h2] at h_nd₁
                have h_nd_eq := (Option.some_inj.mp h_nd₁).symm
                rw [h_nd_eq]
            rw [h_inputs] at h_mem₁
            right; exact ⟨nd₀, h_nd₀, h_mem₁⟩
  have h_pairs := h_foldl (ids.zip (ids.drop 1)) w nd h_nd
  intro inputId h_mem
  have h_or := h_pairs inputId h_mem
  cases h_or with
  | inl h_in_pairs =>
    obtain ⟨⟨a, b⟩, h_mem_zip, h_eq⟩ := List.mem_map.mp h_in_pairs
    have h_a := List.fst_mem_of_mem_zip ids (ids.drop 1) a b h_mem_zip
    rwa [← h_eq]
  | inr h_in_w =>
    obtain ⟨nd₀, h_nd₀, h_mem₀⟩ := h_in_w
    have h_inputs := h_w nd₀ h_nd₀
    rw [h_inputs] at h_mem₀
    contradiction

/-- `setInput id level` doesn't affect `getInputSignal nid` when `id ∉ nd.inputs`. -/
theorem setInput_getInputSignal_ne (w : World) (sid nid : Nat) (level : Nat)
    (h : ∀ nd, w.getNode nid = some nd → sid ∉ nd.inputs) :
    (w.setInput sid level).getInputSignal nid = w.getInputSignal nid := by
  -- h_getNode_ne: setInput preserves getNode for nid' ≠ sid
  have h_getNode_ne : ∀ nid', sid ≠ nid' →
      (w.setInput sid level).getNode nid' = w.getNode nid' := by
    intro nid' h_ne
    dsimp [World.setInput]; rw [World.notifyOutputs_getNode]
    exact World.updateNode_getNode_ne w sid nid' _ h_ne
  -- Unfold getInputSignal only (NOT setInput)
  dsimp [World.getInputSignal]
  cases h_nd : w.getNode nid with
  | none =>
    have h_none : (w.setInput sid level).getNode nid = none := by
      by_cases h_eq : nid = sid
      · rw [h_eq]; dsimp [World.setInput]; rw [World.notifyOutputs_getNode]
        exact World.updateNode_preserves_getNode_none w sid sid _ (by rwa [← h_eq])
      · rw [h_getNode_ne nid (fun h_eq' => h_eq h_eq'.symm), h_nd]
    simp [h_none]
  | some nd =>
    have h_inputs : sid ∉ nd.inputs := h nd h_nd
    -- Foldl equality: for inputId ∈ nd.inputs, sid ≠ inputId → getNode unchanged
    have h_foldl : ∀ (l : List Nat) (acc : Nat), (∀ inputId ∈ l, inputId ∈ nd.inputs) →
        l.foldl (fun maxSig inputId =>
          match (w.setInput sid level).getNode inputId with
          | none => maxSig
          | some inputNd => max maxSig inputNd.sigLevel) acc =
        l.foldl (fun maxSig inputId =>
          match w.getNode inputId with
          | none => maxSig
          | some inputNd => max maxSig inputNd.sigLevel) acc := by
      intro l acc h_sub
      induction l generalizing acc with
      | nil => rfl
      | cons inputId rest ih =>
        simp only [List.foldl_cons]
        have h_ne : sid ≠ inputId := by
          intro h_eq
          have : inputId ∈ nd.inputs := h_sub inputId (List.mem_cons.mpr (Or.inl rfl))
          rw [← h_eq] at this
          exact h_inputs this
        rw [h_getNode_ne inputId h_ne]
        exact ih _ (fun inputId h_mem => h_sub inputId (List.mem_cons.mpr (Or.inr h_mem)))
    by_cases h_eq : nid = sid
    · -- nid = sid: getNode returns updated node (same inputs)
      have h_upd : (w.setInput sid level).getNode nid = some { nd with sigLevel := level } := by
        rw [h_eq]; dsimp [World.setInput]; rw [World.notifyOutputs_getNode]
        exact World.updateNode_getNode_eq w sid _ nd (by rwa [← h_eq])
      simp only [h_upd]
      have : { nd with sigLevel := level }.inputs = nd.inputs := rfl
      rw [this]
      exact h_foldl nd.inputs 0 (fun _ h_mem => h_mem)
    · -- nid ≠ sid: getNode unchanged
      rw [h_getNode_ne nid (fun h_eq' => h_eq h_eq'.symm), h_nd]
      exact h_foldl nd.inputs 0 (fun _ h_mem => h_mem)

theorem World.onNeighborUpdate_nextId (w : World) (id : Nat) :
    (w.onNeighborUpdate id).nextId = w.nextId := by
  dsimp [World.onNeighborUpdate]
  split
  · rfl
  · rename_i nd
    split
    · simp [World.scheduleEvent]
    · simp [World.scheduleEvent]
    · simp [World.logOutput]
    · rfl

theorem World.notifyOutputs_nextId (w : World) (id : Nat) :
    (w.notifyOutputs id).nextId = w.nextId := by
  dsimp [World.notifyOutputs]
  cases h : w.getNode id with
  | none => rfl
  | some nd =>
    simp only
    have h_fold : ∀ (l : List Nat) (w' : World),
        (l.foldl (fun w'' outId => w''.onNeighborUpdate outId) w').nextId = w'.nextId := by
      intro l
      induction l with
      | nil => intro w'; rfl
      | cons hd tl ih =>
        intro w'
        simp only [List.foldl_cons]
        rw [ih, World.onNeighborUpdate_nextId]
    exact h_fold nd.outputs w

/-- `l[i] :: l.eraseIdx i ~ l` -/
theorem List.perm_cons_eraseIdx {l : List α} {i : Nat} (hi : i < l.length) :
    List.Perm (l[i] :: l.eraseIdx i) l := by
  induction l generalizing i with
  | nil => simp at hi
  | cons hd tl ih =>
    cases i with
    | zero => simp [List.eraseIdx]
    | succ i' =>
      have hi' : i' < tl.length := by simp at hi; omega
      simp only [List.eraseIdx_cons_succ, List.getElem_cons_succ]
      exact (Perm.swap _ _ _).trans (Perm.cons _ (ih hi'))

/-- `l.eraseIdx i ~ l.erase l[i]` when `i < l.length`. -/
theorem List.eraseIdx_perm_erase {α : Type} [DecidableEq α]
    (l : List α) (i : Nat) (hi : i < l.length) :
    List.Perm (l.eraseIdx i) (l.erase l[i]) := by
  induction l generalizing i with
  | nil => simp at hi
  | cons hd tl ih =>
    cases i with
    | zero => simp [List.eraseIdx, List.getElem_cons_zero, List.erase]
    | succ i' =>
      have hi' : i' < tl.length := by simp at hi; omega
      simp only [List.eraseIdx_cons_succ, List.getElem_cons_succ]
      by_cases h_eq : hd = tl[i']
      · subst h_eq
        simp only [List.erase]
        split
        · exact List.perm_cons_eraseIdx hi'
        · exfalso; simp_all
      · simp only [List.erase]
        split
        · exfalso; apply h_eq
          rename_i h
          simpa using h
        · exact Perm.cons hd (ih i' hi')

/-- Replacing the events list doesn't change what `onNeighborUpdate` appends. -/
theorem World.onNeighborUpdate_events_replace (w : World) (id : Nat) (e : List ScheduledEvent) :
    ({w with events := e}.onNeighborUpdate id).events =
    e ++ ({w with events := []}.onNeighborUpdate id).events := by
  dsimp [World.onNeighborUpdate]
  have h : {w with events := e}.getNode id = {w with events := []}.getNode id := by
    dsimp [World.getNode]
  rw [h]
  cases h_nd : {w with events := []}.getNode id with
  | none => simp
  | some nd =>
    cases h_kind : nd.kind with
    | repeater delay priority => simp [h_kind, World.scheduleEvent_events]
    | observer => simp [h_kind, World.scheduleEvent_events]
    | output name => simp [h_kind, World.logOutput_events]
    | input => simp [h_kind]

/-- `foldl onNeighborUpdate` appends events transparently over the initial list
(general form: works for any two worlds that agree on nodes/tick). -/
theorem foldl_onNeighborUpdate_events_replace_gen (l : List Nat) (w₁ w₂ : World) (e : List ScheduledEvent)
    (h_nodes : w₁.nodes = w₂.nodes) (h_tick : w₁.tick = w₂.tick)
    (h_events : w₁.events = e ++ w₂.events) :
    (l.foldl (fun (w' : World) outId => w'.onNeighborUpdate outId) w₁).events =
    e ++ (l.foldl (fun (w' : World) outId => w'.onNeighborUpdate outId) w₂).events := by
  induction l generalizing w₁ w₂ e with
  | nil => simp [h_events]
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    apply ih
    · rw [World.onNeighborUpdate_nodes, World.onNeighborUpdate_nodes]; exact h_nodes
    · rw [World.onNeighborUpdate_tick, World.onNeighborUpdate_tick]; exact h_tick
    · -- (w₁.onNeighborUpdate hd).events = e ++ (w₂.onNeighborUpdate hd).events
      have h₁ := World.onNeighborUpdate_events_replace w₁ hd e
      have h₂ := World.onNeighborUpdate_events_replace w₂ hd []
      -- h₁ : ({w₁ with events := e}.onNeighborUpdate hd).events = e ++ ({w₁ with events := []}.onNeighborUpdate hd).events
      -- But we need (w₁.onNeighborUpdate hd).events, not ({w₁ with events := e}.onNeighborUpdate hd).events
      -- Use the fact that onNeighborUpdate's new events depend only on nodes/tick
      have h_new_eq : ({w₁ with events := []}.onNeighborUpdate hd).events =
          ({w₂ with events := []}.onNeighborUpdate hd).events := by
        dsimp [World.onNeighborUpdate, World.getNode]
        simp only [h_nodes]
        split
        · simp
        · split <;> simp [World.scheduleEvent_events, World.logOutput_events, h_tick]
      -- Now decompose using onNeighborUpdate_events_replace
      have h₁' : (w₁.onNeighborUpdate hd).events =
          w₁.events ++ ({w₁ with events := []}.onNeighborUpdate hd).events := by
        have := World.onNeighborUpdate_events_replace w₁ hd w₁.events
        simpa using this
      have h₂' : (w₂.onNeighborUpdate hd).events =
          w₂.events ++ ({w₂ with events := []}.onNeighborUpdate hd).events := by
        have := World.onNeighborUpdate_events_replace w₂ hd w₂.events
        simpa using this
      rw [h₁', h₂', h_new_eq, h_events]
      simp [List.append_assoc]

/-- `foldl onNeighborUpdate` appends events transparently over the initial list. -/
theorem foldl_onNeighborUpdate_events_replace (l : List Nat) (w : World) (e : List ScheduledEvent) :
    (l.foldl (fun (w' : World) outId => w'.onNeighborUpdate outId) {w with events := e}).events =
    e ++ (l.foldl (fun (w' : World) outId => w'.onNeighborUpdate outId) {w with events := []}).events :=
  foldl_onNeighborUpdate_events_replace_gen l {w with events := e} {w with events := []} e
    (by rfl) (by rfl) (by simp)

/-- Replacing the events list doesn't change what `notifyOutputs` appends. -/
theorem World.notifyOutputs_events_replace (w : World) (id : Nat) (e : List ScheduledEvent) :
    ({w with events := e}.notifyOutputs id).events =
    e ++ ({w with events := []}.notifyOutputs id).events := by
  dsimp [World.notifyOutputs]
  have h : {w with events := e}.getNode id = {w with events := []}.getNode id := by
    dsimp [World.getNode]
  rw [h]
  cases h_nd : {w with events := []}.getNode id with
  | none => simp
  | some nd => exact foldl_onNeighborUpdate_events_replace nd.outputs w e

/-- `notifyOutputs` preserves the node list. -/
theorem World.notifyOutputs_nodes (w : World) (id : Nat) :
    (w.notifyOutputs id).nodes = w.nodes := by
  dsimp [World.notifyOutputs]
  cases h : w.getNode id with
  | none => rfl
  | some nd =>
    simp only
    have h_fold : ∀ (l : List Nat) (w' : World),
        (l.foldl (fun w'' outId => w''.onNeighborUpdate outId) w').nodes = w'.nodes := by
      intro l
      induction l with
      | nil => intro w'; rfl
      | cons hd tl ih =>
        intro w'
        simp only [List.foldl_cons]
        rw [ih, World.onNeighborUpdate_nodes]
    exact h_fold nd.outputs w

/-- `onNeighborUpdate` gives the same outputLog for worlds with the same nodes and outputLog. -/
theorem World.onNeighborUpdate_outputLog_congr (w₁ w₂ : World) (id : Nat)
    (h_nodes : w₁.nodes = w₂.nodes) (h_log : w₁.outputLog = w₂.outputLog) :
    (w₁.onNeighborUpdate id).outputLog = (w₂.onNeighborUpdate id).outputLog := by
  dsimp [World.onNeighborUpdate]
  have h_getNode : w₁.getNode id = w₂.getNode id := by dsimp [World.getNode]; rw [h_nodes]
  rw [h_getNode]
  split
  · exact h_log
  · rename_i nd; split
    · simp [World.scheduleEvent_outputLog, h_log]
    · simp [World.scheduleEvent_outputLog, h_log]
    · have h_gis : w₁.getInputSignal id = w₂.getInputSignal id := by
        dsimp [World.getInputSignal]
        have : w₁.getNode id = w₂.getNode id := by dsimp [World.getNode]; rw [h_nodes]
        rw [this]; split
        · rfl
        · rename_i nd'; congr 1; ext _ inputId
          have : w₁.getNode inputId = w₂.getNode inputId := by dsimp [World.getNode]; rw [h_nodes]
          rw [this]
      simp [World.logOutput, h_log, h_gis]
    · exact h_log

/-- `notifyOutputs` gives the same outputLog for worlds with the same nodes and outputLog. -/
theorem World.notifyOutputs_outputLog_congr (w₁ w₂ : World) (id : Nat)
    (h_nodes : w₁.nodes = w₂.nodes) (h_log : w₁.outputLog = w₂.outputLog) :
    (w₁.notifyOutputs id).outputLog = (w₂.notifyOutputs id).outputLog := by
  dsimp [World.notifyOutputs]
  have h_getNode : w₁.getNode id = w₂.getNode id := by dsimp [World.getNode]; rw [h_nodes]
  rw [h_getNode]
  cases h_nd : w₂.getNode id with
  | none => exact h_log
  | some nd =>
    have h_fold : ∀ (l : List Nat) (w₁' w₂' : World),
        w₁'.nodes = w₂'.nodes → w₁'.outputLog = w₂'.outputLog →
        (l.foldl (fun (w'' : World) outId => w''.onNeighborUpdate outId) w₁').outputLog =
        (l.foldl (fun (w'' : World) outId => w''.onNeighborUpdate outId) w₂').outputLog := by
      intro l
      induction l with
      | nil => intro w₁' w₂' hn hl; exact hl
      | cons hd tl ih =>
        intro w₁' w₂' hn hl
        simp only [List.foldl_cons]
        apply ih
        · rw [World.onNeighborUpdate_nodes, World.onNeighborUpdate_nodes]
          exact hn
        · exact World.onNeighborUpdate_outputLog_congr _ _ _ hn hl
    exact h_fold nd.outputs w₁ w₂ h_nodes h_log

/-- `getInputSignal` is unchanged when a non-input node's sigLevel changes. -/
theorem getInputSignal_congr_except (w₁ w₂ : World) (id excluded : Nat)
    (h_id_ne : id ≠ excluded)
    (h_nodes : ∀ nid, nid ≠ excluded → w₁.getNode nid = w₂.getNode nid)
    (h_not_input : ∀ nd, w₁.getNode id = some nd → excluded ∉ nd.inputs) :
    w₁.getInputSignal id = w₂.getInputSignal id := by
  have h_getNode : w₁.getNode id = w₂.getNode id := h_nodes id h_id_ne
  dsimp [World.getInputSignal]
  rw [h_getNode]
  cases h : w₂.getNode id with
  | none => rfl
  | some nd =>
    have h_nd : w₁.getNode id = some nd := by rw [h_getNode, h]
    suffices h_fold : ∀ (l : List Nat) (a : Nat), (∀ x ∈ l, x ∈ nd.inputs) →
        l.foldl (fun maxSig inputId =>
          match w₁.getNode inputId with
          | none => maxSig
          | some inputNd => max maxSig inputNd.sigLevel) a =
        l.foldl (fun maxSig inputId =>
          match w₂.getNode inputId with
          | none => maxSig
          | some inputNd => max maxSig inputNd.sigLevel) a by
      exact h_fold nd.inputs 0 (by simp)
    intro l a h_sub
    revert h_sub
    induction l generalizing a with
    | nil =>
      intro _; rfl
    | cons inputId rest ih =>
      intro h_sub'
      simp only [List.foldl_cons]
      have h_mem : inputId ∈ nd.inputs := h_sub' inputId (by simp)
      have h_ne : inputId ≠ excluded := by
        intro h_eq; subst h_eq
        exact h_not_input nd h_nd h_mem
      have h_eq : w₁.getNode inputId = w₂.getNode inputId := h_nodes inputId h_ne
      dsimp [World.getNode] at h_eq ⊢
      rw [h_eq]
      apply ih
      intro x hx; exact h_sub' x (by simp [hx])

/-- `onScheduledTick` appends the same new events for worlds with the same nodes and tick,
and produces the same nodes/tick/outputLog/nextId. -/
theorem World.onScheduledTick_congr_fields (w₁ w₂ : World) (id : Nat)
    (h_nodes : w₁.nodes = w₂.nodes) (h_tick : w₁.tick = w₂.tick)
    (h_log : w₁.outputLog = w₂.outputLog) (h_nextId : w₁.nextId = w₂.nextId) :
    (w₁.onScheduledTick id).nodes = (w₂.onScheduledTick id).nodes ∧
    (w₁.onScheduledTick id).tick = (w₂.onScheduledTick id).tick ∧
    (w₁.onScheduledTick id).outputLog = (w₂.onScheduledTick id).outputLog ∧
    (w₁.onScheduledTick id).nextId = (w₂.onScheduledTick id).nextId ∧
    ∃ new, (w₁.onScheduledTick id).events = w₁.events ++ new ∧
           (w₂.onScheduledTick id).events = w₂.events ++ new := by
  dsimp [World.onScheduledTick]
  have h_getNode : w₁.getNode id = w₂.getNode id := by dsimp [World.getNode]; rw [h_nodes]
  rw [h_getNode]
  split
  · exact ⟨h_nodes, h_tick, h_log, h_nextId, [], by simp, by simp⟩
  · rename_i nd; split
    · -- repeater
      have h_gis : w₁.getInputSignal id = w₂.getInputSignal id := by
        dsimp [World.getInputSignal]
        have : w₁.getNode id = w₂.getNode id := by dsimp [World.getNode]; rw [h_nodes]
        rw [this]; split
        · rfl
        · rename_i nd'; congr 1; ext _ inputId
          have : w₁.getNode inputId = w₂.getNode inputId := by dsimp [World.getNode]; rw [h_nodes]
          rw [this]
      rw [h_gis]
      -- After updateNode, worlds share nodes/tick/outputLog/nextId
      have h_upd_nodes : (w₁.updateNode id (fun nd' => { nd' with sigLevel := if w₂.getInputSignal id > 0 then 15 else 0 })).nodes =
          (w₂.updateNode id (fun nd' => { nd' with sigLevel := if w₂.getInputSignal id > 0 then 15 else 0 })).nodes := by
        dsimp [World.updateNode]; rw [h_nodes]
      have h_upd_log : (w₁.updateNode id (fun nd' => { nd' with sigLevel := if w₂.getInputSignal id > 0 then 15 else 0 })).outputLog =
          (w₂.updateNode id (fun nd' => { nd' with sigLevel := if w₂.getInputSignal id > 0 then 15 else 0 })).outputLog := by
        dsimp [World.updateNode]; rw [h_log]
      constructor
      · rw [World.notifyOutputs_nodes, World.notifyOutputs_nodes]; exact h_upd_nodes
      · constructor
        · rw [World.notifyOutputs_tick, World.notifyOutputs_tick]
          dsimp [World.updateNode]; rw [h_tick]
        · constructor
          · exact World.notifyOutputs_outputLog_congr _ _ _ h_upd_nodes h_upd_log
          · constructor
            · rw [World.notifyOutputs_nextId, World.notifyOutputs_nextId]
              dsimp [World.updateNode]; rw [h_nextId]
            · use ({w₁.updateNode id (fun nd' => { nd' with sigLevel := if w₂.getInputSignal id > 0 then 15 else 0 }) with events := []}.notifyOutputs id).events
              constructor
              · rw [World.notifyOutputs_events_replace]; simp []
              · have h_eq : {w₁.updateNode id (fun nd' => { nd' with sigLevel := if w₂.getInputSignal id > 0 then 15 else 0 }) with events := []} =
                    {w₂.updateNode id (fun nd' => { nd' with sigLevel := if w₂.getInputSignal id > 0 then 15 else 0 }) with events := []} := by
                  ext <;> simp [World.updateNode, h_nodes, h_tick, h_log, h_nextId]
                rw [h_eq, World.notifyOutputs_events_replace]; simp []
    · -- observer
      have h_upd_nodes : (w₁.updateNode id (fun nd' => { nd' with sigLevel := 15 })).nodes =
          (w₂.updateNode id (fun nd' => { nd' with sigLevel := 15 })).nodes := by
        dsimp [World.updateNode]; rw [h_nodes]
      have h_upd_log : (w₁.updateNode id (fun nd' => { nd' with sigLevel := 15 })).outputLog =
          (w₂.updateNode id (fun nd' => { nd' with sigLevel := 15 })).outputLog := by
        dsimp [World.updateNode]; rw [h_log]
      constructor
      · rw [World.notifyOutputs_nodes, World.notifyOutputs_nodes]; exact h_upd_nodes
      · constructor
        · rw [World.notifyOutputs_tick, World.notifyOutputs_tick]
          dsimp [World.updateNode]; rw [h_tick]
        · constructor
          · exact World.notifyOutputs_outputLog_congr _ _ _ h_upd_nodes h_upd_log
          · constructor
            · rw [World.notifyOutputs_nextId, World.notifyOutputs_nextId]
              dsimp [World.updateNode]; rw [h_nextId]
            · use ({w₁.updateNode id (fun nd' => { nd' with sigLevel := 15 }) with events := []}.notifyOutputs id).events
              constructor
              · rw [World.notifyOutputs_events_replace]; simp []
              · have h_eq : {w₁.updateNode id (fun nd' => { nd' with sigLevel := 15 }) with events := []} =
                    {w₂.updateNode id (fun nd' => { nd' with sigLevel := 15 }) with events := []} := by
                  ext <;> simp [World.updateNode, h_nodes, h_tick, h_log, h_nextId]
                rw [h_eq, World.notifyOutputs_events_replace]; simp []
    · -- output/input (onScheduledTick returns w unchanged)
      exact ⟨h_nodes, h_tick, h_log, h_nextId, [], by simp, by simp⟩

/-- If `a ∈ l` and `a ≠ l[i]`, then `a ∈ l.eraseIdx i`. -/
theorem List.mem_eraseIdx_of_mem_ne {α : Type} (l : List α) (i : Nat) (a : α)
    (h_lt : i < l.length) (h_mem : a ∈ l) (h_ne : a ≠ l[i]) : a ∈ l.eraseIdx i := by
  induction l generalizing i a with
  | nil => simp at h_lt
  | cons hd tl ih =>
    cases i with
    | zero =>
      simp only [List.eraseIdx, List.getElem_cons_zero] at h_ne ⊢
      simp [List.mem_cons] at h_mem
      cases h_mem with
      | inl h => exfalso; exact h_ne h
      | inr h => exact h
    | succ i' =>
      have h_lt' : i' < tl.length := by simp [List.length] at h_lt; omega
      simp only [List.eraseIdx_cons_succ, List.getElem_cons_succ] at h_ne ⊢
      simp [List.mem_cons] at h_mem ⊢
      cases h_mem with
      | inl h => left; exact h
      | inr h => right; exact ih i' a h_lt' h (by simpa using h_ne)
