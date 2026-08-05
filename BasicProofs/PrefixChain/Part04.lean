import BasicProofs.PrefixChain.Part03


open BasicRedstoneSim

/-- After `connectChain w ids`, every output of every node is either from `ids.drop 1`
or was already an output in `w`. (Stronger than `connectChain_outputs_subset`.) -/
theorem connectChain_outputs_subset_drop1 (ids : List Nat) :
    ∀ (w : World) id nd, (connectChain w ids).getNode id = some nd →
    ∀ out ∈ nd.outputs, out ∈ ids.drop 1 ∨ ∃ nd₀, w.getNode id = some nd₀ ∧ out ∈ nd₀.outputs := by
  induction ids with
  | nil =>
    intro w id nd h_getNode out h_out
    dsimp [connectChain] at h_getNode
    right; exact ⟨nd, h_getNode, h_out⟩
  | cons hd tl ih =>
    cases tl with
    | nil =>
      intro w id nd h_getNode out h_out
      dsimp [connectChain] at h_getNode
      right; exact ⟨nd, h_getNode, h_out⟩
    | cons hd₂ tl₂ =>
      intro w id nd h_getNode out h_out
      set w₁ := (w.updateNode hd₂ (fun nd => { nd with inputs := nd.inputs ++ [hd] })).updateNode hd
        (fun nd => { nd with outputs := nd.outputs ++ [hd₂] })
      have h_decomp : connectChain w (hd :: hd₂ :: tl₂) = connectChain w₁ (hd₂ :: tl₂) := by
        dsimp [connectChain, w₁]
      rw [h_decomp] at h_getNode
      have h_ih := ih w₁ id nd h_getNode out h_out
      cases h_ih with
      | inl h_in_tl =>
        -- out ∈ (hd₂ :: tl₂).drop 1 = tl₂ ⊆ hd₂ :: tl₂ = (hd :: hd₂ :: tl₂).drop 1
        left; exact List.mem_cons_of_mem hd₂ h_in_tl
      | inr h_in_w₁ =>
        rcases h_in_w₁ with ⟨nd₁, h_getNode₁, h_out₁⟩
        by_cases h_id_hd : id = hd
        · cases h_orig : w.getNode hd with
          | none =>
            have h₂ : w₁.getNode hd = none := by
              dsimp [w₁]
              by_cases h_eq : hd = hd₂
              · cases h_eq
                have h₃ : (w.updateNode hd (fun nd => { nd with inputs := nd.inputs ++ [hd] })).getNode hd = none :=
                  World.updateNode_getNode_none w hd _ h_orig
                exact World.updateNode_getNode_none _ hd _ h₃
              · have h₃ : (w.updateNode hd₂ (fun nd => { nd with inputs := nd.inputs ++ [hd] })).getNode hd = none := by
                  rw [World.updateNode_getNode_ne w hd₂ hd _ (by omega)]; exact h_orig
                exact World.updateNode_getNode_none _ hd _ h₃
            rw [h_id_hd] at h_getNode₁; rw [h₂] at h_getNode₁; contradiction
          | some nd₀ =>
            have h_outputs : nd₁.outputs = nd₀.outputs ++ [hd₂] := by
              rw [h_id_hd] at h_getNode₁
              dsimp [w₁] at h_getNode₁
              by_cases h_eq : hd = hd₂
              · cases h_eq
                have h₁ := World.updateNode_getNode_eq w hd
                  (fun nd => { nd with inputs := nd.inputs ++ [hd] }) nd₀ h_orig
                have h₂ := World.updateNode_getNode_eq _ hd
                  (fun nd => { nd with outputs := nd.outputs ++ [hd] }) _ h₁
                have h_eq₂ := h₂.symm.trans h_getNode₁
                injection h_eq₂ with h_nd; cases h_nd; rfl
              · have h₁ : (w.updateNode hd₂ (fun nd => { nd with inputs := nd.inputs ++ [hd] })).getNode hd =
                    some nd₀ := by
                  rw [World.updateNode_getNode_ne w hd₂ hd _ (by omega)]; exact h_orig
                have h₂ := World.updateNode_getNode_eq _ hd
                  (fun nd => { nd with outputs := nd.outputs ++ [hd₂] }) nd₀ h₁
                have h_eq₂ := h₂.symm.trans h_getNode₁
                injection h_eq₂ with h_nd; cases h_nd; rfl
            have h_out' : out ∈ nd₀.outputs ∨ out = hd₂ := by
              rw [h_outputs] at h_out₁
              simp [List.mem_append] at h_out₁ ⊢; exact h_out₁
            cases h_out' with
            | inl h_old => right; exact ⟨nd₀, by rw [h_id_hd]; exact h_orig, h_old⟩
            | inr h_eq => left; rw [h_eq]; simp
        · by_cases h_id_hd₂ : id = hd₂
          · cases h_orig : w.getNode hd₂ with
            | none =>
              have h₁ : (w.updateNode hd₂ (fun nd => { nd with inputs := nd.inputs ++ [hd] })).getNode hd₂ = none :=
                World.updateNode_getNode_none w hd₂ _ h_orig
              have h₂ : w₁.getNode hd₂ = none := by
                dsimp [w₁]
                rw [World.updateNode_getNode_ne _ hd hd₂ _ (by omega)]
                exact h₁
              rw [h_id_hd₂] at h_getNode₁; rw [h₂] at h_getNode₁; contradiction
            | some nd₀ =>
              have h₁ : (w.updateNode hd₂ (fun nd => { nd with inputs := nd.inputs ++ [hd] })).getNode hd₂ =
                  some ({ nd₀ with inputs := nd₀.inputs ++ [hd] } : NodeData) :=
                World.updateNode_getNode_eq w hd₂ _ nd₀ h_orig
              have h₂ : w₁.getNode hd₂ =
                  some ({ nd₀ with inputs := nd₀.inputs ++ [hd] } : NodeData) := by
                dsimp [w₁]
                rw [World.updateNode_getNode_ne _ hd hd₂ _ (by omega)]
                exact h₁
              rw [h_id_hd₂] at h_getNode₁
              dsimp [w₁] at h_getNode₁
              have h_eq₂ := h₂.symm.trans h_getNode₁
              injection h_eq₂ with h_nd
              have h_out' : out ∈ nd₀.outputs := by
                have : nd₁.outputs = nd₀.outputs := by cases h_nd; rfl
                rw [this] at h_out₁; exact h_out₁
              right; exact ⟨nd₀, by rw [h_id_hd₂]; exact h_orig, h_out'⟩
          · have h₁ : w₁.getNode id = w.getNode id := by
              dsimp [w₁]
              rw [World.updateNode_getNode_ne _ hd id _ (by omega)]
              exact World.updateNode_getNode_ne w hd₂ id _ (by omega)
            rw [h₁] at h_getNode₁
            right; exact ⟨nd₁, h_getNode₁, h_out₁⟩

/-- After `connectChain w ids`, every input of every node is either from `ids`
or was already an input in `w`. -/
theorem connectChain_inputs_mem (ids : List Nat) :
    ∀ (w : World) id nd, (connectChain w ids).getNode id = some nd →
    ∀ inp ∈ nd.inputs, inp ∈ ids ∨ ∃ nd₀, w.getNode id = some nd₀ ∧ inp ∈ nd₀.inputs := by
  induction ids with
  | nil =>
    intro w id nd h_getNode inp h_inp
    dsimp [connectChain] at h_getNode
    right; exact ⟨nd, h_getNode, h_inp⟩
  | cons hd tl ih =>
    cases tl with
    | nil =>
      intro w id nd h_getNode inp h_inp
      dsimp [connectChain] at h_getNode
      right; exact ⟨nd, h_getNode, h_inp⟩
    | cons hd₂ tl₂ =>
      intro w id nd h_getNode inp h_inp
      set w₁ := (w.updateNode hd₂ (fun nd => { nd with inputs := nd.inputs ++ [hd] })).updateNode hd
        (fun nd => { nd with outputs := nd.outputs ++ [hd₂] })
      have h_decomp : connectChain w (hd :: hd₂ :: tl₂) = connectChain w₁ (hd₂ :: tl₂) := by
        dsimp [connectChain, w₁]
      rw [h_decomp] at h_getNode
      have h_ih := ih w₁ id nd h_getNode inp h_inp
      cases h_ih with
      | inl h_in_tl =>
        -- inp ∈ hd₂ :: tl₂ ⊆ hd :: hd₂ :: tl₂
        left; exact List.mem_cons_of_mem hd h_in_tl
      | inr h_in_w₁ =>
        rcases h_in_w₁ with ⟨nd₁, h_getNode₁, h_inp₁⟩
        -- inp is an input of id in w₁. Show: inp ∈ ids or input in w.
        by_cases h_id_hd₂ : id = hd₂
        · -- id = hd₂: w₁ appends [hd] to hd₂'s inputs
          cases h_orig : w.getNode hd₂ with
          | none =>
            have h₂ : w₁.getNode hd₂ = none := by
              dsimp [w₁]
              by_cases h_eq : hd = hd₂
              · cases h_eq
                exact World.updateNode_getNode_none _ hd _
                  (World.updateNode_getNode_none w hd _ h_orig)
              · have h₃ : (w.updateNode hd₂ (fun nd => { nd with inputs := nd.inputs ++ [hd] })).getNode hd₂ = none :=
                  World.updateNode_getNode_none w hd₂ _ h_orig
                rw [World.updateNode_getNode_ne _ hd hd₂ _ (by omega)]
                exact h₃
            rw [h_id_hd₂] at h_getNode₁; rw [h₂] at h_getNode₁; contradiction
          | some nd₀ =>
            have h_inputs : nd₁.inputs = nd₀.inputs ++ [hd] := by
              rw [h_id_hd₂] at h_getNode₁
              dsimp [w₁] at h_getNode₁
              by_cases h_eq : hd = hd₂
              · cases h_eq
                have h₁ := World.updateNode_getNode_eq w hd
                  (fun nd => { nd with inputs := nd.inputs ++ [hd] }) nd₀ h_orig
                have h₂ := World.updateNode_getNode_eq _ hd
                  (fun nd => { nd with outputs := nd.outputs ++ [hd] }) _ h₁
                have h_eq₂ := h₂.symm.trans h_getNode₁
                injection h_eq₂ with h_nd; cases h_nd; rfl
              · have h₁ : (w.updateNode hd₂ (fun nd => { nd with inputs := nd.inputs ++ [hd] })).getNode hd₂ =
                    some ({ nd₀ with inputs := nd₀.inputs ++ [hd] } : NodeData) :=
                  World.updateNode_getNode_eq w hd₂ _ nd₀ h_orig
                have h₂ : w₁.getNode hd₂ =
                    some ({ nd₀ with inputs := nd₀.inputs ++ [hd] } : NodeData) := by
                  dsimp [w₁]
                  rw [World.updateNode_getNode_ne _ hd hd₂ _ (by omega)]
                  exact h₁
                have h_eq₂ := h₂.symm.trans h_getNode₁
                injection h_eq₂ with h_nd; cases h_nd; rfl
            have h_inp' : inp ∈ nd₀.inputs ∨ inp = hd := by
              rw [h_inputs] at h_inp₁
              simp [List.mem_append] at h_inp₁ ⊢; exact h_inp₁
            cases h_inp' with
            | inl h_old => right; exact ⟨nd₀, by rw [h_id_hd₂]; exact h_orig, h_old⟩
            | inr h_eq => left; rw [h_eq]; simp
        · -- id ≠ hd₂
          by_cases h_id_hd : id = hd
          · -- id = hd: w₁ changes hd's outputs, not inputs
            cases h_orig : w.getNode hd with
            | none =>
              have h₁ : (w.updateNode hd₂ (fun nd => { nd with inputs := nd.inputs ++ [hd] })).getNode hd = none := by
                rw [World.updateNode_getNode_ne w hd₂ hd _ (by omega)]; exact h_orig
              have h₂ : w₁.getNode hd = none := by
                dsimp [w₁]
                exact World.updateNode_getNode_none _ hd _ h₁
              rw [h_id_hd] at h_getNode₁; rw [h₂] at h_getNode₁; contradiction
            | some nd₀ =>
              -- w₁ changes hd's outputs, not inputs (since hd ≠ hd₂).
              rw [h_id_hd] at h_getNode₁
              have h_nd₁ : nd₁ = { nd₀ with outputs := nd₀.outputs ++ [hd₂] } := by
                have h₁ : (w.updateNode hd₂ (fun nd => { nd with inputs := nd.inputs ++ [hd] })).getNode hd =
                    some nd₀ := by
                  rw [World.updateNode_getNode_ne w hd₂ hd _ (by omega)]; exact h_orig
                have h₂ : w₁.getNode hd =
                    some ({ nd₀ with outputs := nd₀.outputs ++ [hd₂] } : NodeData) := by
                  dsimp [w₁]
                  exact World.updateNode_getNode_eq _ hd
                    (fun nd => { nd with outputs := nd.outputs ++ [hd₂] }) nd₀ h₁
                have := h₂.symm.trans h_getNode₁
                injection this with h; exact h.symm
              rw [h_nd₁] at h_inp₁
              right; exact ⟨nd₀, by rw [h_id_hd]; exact h_orig, h_inp₁⟩
          · -- id ≠ hd and id ≠ hd₂: w₁.getNode id = w.getNode id
            have h₁ : w₁.getNode id = w.getNode id := by
              dsimp [w₁]
              rw [World.updateNode_getNode_ne _ hd id _ (by omega)]
              exact World.updateNode_getNode_ne w hd₂ id _ (by omega)
            rw [h₁] at h_getNode₁
            right; exact ⟨nd₁, h_getNode₁, h_inp₁⟩

/-- New events from `setInput id level` have `nodeId` in the outputs of `id`
    (in the updated world). -/
theorem setInput_nodeId_mem (w : World) (id level : Nat) :
    ∀ ev ∈ (w.setInput id level).events, ev ∉ w.events →
    ∃ nd, (w.updateNode id (fun nd => { nd with sigLevel := level })).getNode id = some nd ∧
    ev.nodeId ∈ nd.outputs := by
  intro ev h_ev h_old
  dsimp [World.setInput] at h_ev
  dsimp [World.notifyOutputs] at h_ev
  by_cases h_gn : (w.updateNode id (fun nd => { nd with sigLevel := level })).getNode id = none
  · have : ev ∈ w.events := by simpa [World.notifyOutputs, h_gn] using h_ev
    contradiction
  · obtain ⟨nd, h_nd⟩ := Option.ne_none_iff_exists'.mp h_gn
    have h_ev' : ev ∈ (nd.outputs.foldl (fun w' outId => w'.onNeighborUpdate outId)
        (w.updateNode id (fun nd => { nd with sigLevel := level }))).events := by
      simpa [World.notifyOutputs, h_nd] using h_ev
    have h_nodeId := foldl_onNeighborUpdate_nodeId_mem nd.outputs
      (w.updateNode id (fun nd => { nd with sigLevel := level })) ev h_ev' h_old
    exact ⟨nd, h_nd, h_nodeId⟩

/-- New events from `foldl onNeighborUpdate` have nodeId in the foldl list,
    or were already in the original world. -/
theorem foldl_onNeighborUpdate_nodeId_mem_or (l : List Nat) (w : World) :
    ∀ ev ∈ (l.foldl (fun w' outId => w'.onNeighborUpdate outId) w).events,
    ev.nodeId ∈ l ∨ ev ∈ w.events := by
  induction l generalizing w with
  | nil =>
    intro ev h_ev
    simp at h_ev
    right; exact h_ev
  | cons hd tl ih =>
    intro ev h_ev
    simp only [List.foldl_cons] at h_ev
    by_cases h_old : ev ∈ (w.onNeighborUpdate hd).events
    · by_cases h_old' : ev ∈ w.events
      · right; exact h_old'
      · left
        have h_nodeId := World.onNeighborUpdate_events_nodeId w hd ev h_old h_old'
        rw [h_nodeId]; exact List.mem_cons.mpr (Or.inl rfl)
    · have h_ih := ih (w.onNeighborUpdate hd) ev h_ev
      cases h_ih with
      | inl h_mem => left; exact List.mem_cons.mpr (Or.inr h_mem)
      | inr h_mem =>
        -- ev ∈ (w.onNeighborUpdate hd).events, but h_old says it's not
        contradiction

/-- New events from `onScheduledTick id` have `nodeId` in the outputs of `id`
    (in the original world), or were already in the original world. -/
theorem World.onScheduledTick_events_nodeId_mem_or (w : World) (id : Nat) :
    ∀ ev ∈ (w.onScheduledTick id).events,
    (∃ nd, w.getNode id = some nd ∧ ev.nodeId ∈ nd.outputs) ∨ ev ∈ w.events := by
  intro ev h_ev
  dsimp [World.onScheduledTick, World.notifyOutputs] at h_ev
  by_cases h_gn : w.getNode id = none
  · right; simpa [h_gn] using h_ev
  · obtain ⟨nd, h_nd⟩ := Option.ne_none_iff_exists'.mp h_gn
    by_cases h_kind : nd.kind = .input
    · right; simpa [h_nd, h_kind] using h_ev
    · by_cases h_kind_out : ∃ name, nd.kind = .output name
      · right
        obtain ⟨name, h_name⟩ := h_kind_out
        simpa [h_nd, h_name] using h_ev
      · -- nd.kind is repeater or observer
        have h_kind_ro : nd.kind ≠ .input ∧ ¬∃ name, nd.kind = .output name := ⟨h_kind, h_kind_out⟩
        -- In both repeater and observer cases, new events come from foldl on outputs
        -- after updateNode. updateNode doesn't change events.
        have h_ev' : ev ∈ (nd.outputs.foldl (fun w' outId => w'.onNeighborUpdate outId)
            (w.updateNode id (fun nd' => { nd' with sigLevel :=
              match nd.kind with
              | .repeater _ _ => if w.getInputSignal id > 0 then 15 else 0
              | .observer => 15
              | _ => 0 }))).events ∨ ev ∈ w.events := by
          cases h_k : nd.kind with
          | repeater delay priority =>
            have h_gn'' : (w.updateNode id (fun nd' => { nd' with sigLevel := if w.getInputSignal id > 0 then 15 else 0 })).getNode id =
                some ({ nd with sigLevel := if w.getInputSignal id > 0 then 15 else 0 }) :=
              World.updateNode_getNode_eq w id _ nd h_nd
            have h_ev'' : ev ∈ (({ nd with sigLevel := if w.getInputSignal id > 0 then 15 else 0 }).outputs.foldl
                (fun (w' : World) outId => World.onNeighborUpdate w' outId)
                (w.updateNode id (fun nd' => { nd' with sigLevel := if w.getInputSignal id > 0 then 15 else 0 }))).events := by
              simpa [h_nd, h_k, h_gn''] using h_ev
            left
            simpa [h_k] using h_ev''
          | observer =>
            have h_gn'' : (w.updateNode id (fun nd' => { nd' with sigLevel := 15 })).getNode id =
                some ({ nd with sigLevel := 15 }) :=
              World.updateNode_getNode_eq w id _ nd h_nd
            have h_ev'' : ev ∈ (({ nd with sigLevel := 15 }).outputs.foldl
                (fun (w' : World) outId => World.onNeighborUpdate w' outId)
                (w.updateNode id (fun nd' => { nd' with sigLevel := 15 }))).events := by
              simpa [h_nd, h_k, h_gn''] using h_ev
            left
            simpa [h_k] using h_ev''
          | output name => exfalso; exact h_kind_out ⟨name, h_k⟩
          | input => exfalso; exact h_kind h_k
        cases h_ev' with
        | inl h_foldl =>
          have h_or := foldl_onNeighborUpdate_nodeId_mem_or nd.outputs
            (w.updateNode id (fun nd' => { nd' with sigLevel :=
              match nd.kind with
              | .repeater _ _ => if w.getInputSignal id > 0 then 15 else 0
              | .observer => 15
              | _ => 0 })) ev h_foldl
          cases h_or with
          | inl h_mem =>
            left
            exact ⟨nd, h_nd, by simpa using h_mem⟩
          | inr h_old =>
            right
            have : (w.updateNode id (fun nd' => { nd' with sigLevel :=
                match nd.kind with
                | .repeater _ _ => if w.getInputSignal id > 0 then 15 else 0
                | .observer => 15
                | _ => 0 })).events = w.events := by simp
            rwa [this] at h_old
        | inr h_old => right; exact h_old

/-- `connectChain` preserves `getNode` for nodes not in the ID list. -/
theorem connectChain_getNode_of_not_mem :
    ∀ (ids : List Nat) (id : Nat), id ∉ ids →
    ∀ (w : World), (connectChain w ids).getNode id = w.getNode id := by
  intro ids
  induction ids with
  | nil => intro id _ w; dsimp [connectChain]
  | cons hd tl ih =>
    intro id h_not_mem w
    cases tl with
    | nil => dsimp [connectChain]; rfl
    | cons hd₂ tl₂ =>
      have h_id_ne_hd : id ≠ hd := by intro h; apply h_not_mem; simp [h]
      have h_id_ne_hd₂ : id ≠ hd₂ := by intro h; apply h_not_mem; simp [h, List.mem_cons]
      have h_not_mem_tl : id ∉ hd₂ :: tl₂ := by
        intro h; apply h_not_mem; exact List.mem_cons_of_mem hd h
      set w₁ := (w.updateNode hd₂ (fun nd => { nd with inputs := nd.inputs ++ [hd] })).updateNode hd
        (fun nd => { nd with outputs := nd.outputs ++ [hd₂] })
      have h_decomp : connectChain w (hd :: hd₂ :: tl₂) = connectChain w₁ (hd₂ :: tl₂) := by
        dsimp [connectChain, w₁]
      rw [h_decomp, ih id h_not_mem_tl w₁]
      dsimp [w₁]
      rw [World.updateNode_getNode_ne _ hd id _ (by omega)]
      exact World.updateNode_getNode_ne w hd₂ id _ (by omega)

/-- `connectChain` preserves `getNode = none`. -/
theorem connectChain_preserves_getNode_none (ids : List Nat) :
    ∀ (w : World) (id : Nat), w.getNode id = none → (connectChain w ids).getNode id = none := by
  induction ids with
  | nil => intro w id h; dsimp [connectChain]; exact h
  | cons hd tl ih =>
    intro w id h
    cases tl with
    | nil => dsimp [connectChain]; exact h
    | cons hd₂ tl₂ =>
      set w₁ := (w.updateNode hd₂ (fun nd => { nd with inputs := nd.inputs ++ [hd] })).updateNode hd
        (fun nd => { nd with outputs := nd.outputs ++ [hd₂] })
      have h_decomp : connectChain w (hd :: hd₂ :: tl₂) = connectChain w₁ (hd₂ :: tl₂) := by
        dsimp [connectChain, w₁]
      rw [h_decomp]
      have h_w₁ : w₁.getNode id = none := by
        dsimp [w₁]
        have h₁ : (w.updateNode hd₂ (fun nd => { nd with inputs := nd.inputs ++ [hd] })).getNode id = none := by
          by_cases h₂ : id = hd₂
          · rw [h₂]
            exact World.updateNode_getNode_none w hd₂ _ (by rw [← h₂]; exact h)
          · rw [World.updateNode_getNode_ne w hd₂ id _ (by omega)]; exact h
        by_cases h₂ : id = hd
        · cases h₂ -- id becomes hd
          exact World.updateNode_getNode_none _ hd _ h₁
        · rw [World.updateNode_getNode_ne _ hd id _ (by omega)]; exact h₁
      exact ih w₁ id h_w₁

/-- After `connectChain w ids` with `ids.Nodup`, each node gains at most 1 output. -/
theorem connectChain_outputs_length_le (ids : List Nat) (h_nodup : ids.Nodup) :
    ∀ (w : World) (id : Nat) (nd₀ nd₁ : NodeData),
    w.getNode id = some nd₀ →
    (connectChain w ids).getNode id = some nd₁ →
    nd₁.outputs.length ≤ nd₀.outputs.length + 1 := by
  induction ids with
  | nil =>
    intro w id nd₀ nd₁ h₀ h₁
    dsimp [connectChain] at h₁
    have : nd₁ = nd₀ := by injection h₀.symm.trans h₁ with h; exact h.symm
    rw [this]; omega
  | cons hd tl ih =>
    cases tl with
    | nil =>
      intro w id nd₀ nd₁ h₀ h₁
      dsimp [connectChain] at h₁
      have : nd₁ = nd₀ := by injection h₀.symm.trans h₁ with h; exact h.symm
      rw [this]; omega
    | cons hd₂ tl₂ =>
      -- h_nodup : (hd :: hd₂ :: tl₂).Nodup, so hd ∉ hd₂ :: tl₂
      have h_hd_not_mem : hd ∉ hd₂ :: tl₂ := h_nodup.notMem
      have h_tl_nodup : (hd₂ :: tl₂).Nodup := h_nodup.of_cons
      intro w id nd₀ nd₁ h₀ h₁
      set w₁ := (w.updateNode hd₂ (fun nd => { nd with inputs := nd.inputs ++ [hd] })).updateNode hd
        (fun nd => { nd with outputs := nd.outputs ++ [hd₂] })
      have h_decomp : connectChain w (hd :: hd₂ :: tl₂) = connectChain w₁ (hd₂ :: tl₂) := by
        dsimp [connectChain, w₁]
      rw [h_decomp] at h₁
      by_cases h_id_hd : id = hd
      · -- id = hd: w₁ adds [hd₂] to hd's outputs; connectChain w₁ (hd₂::tl₂) doesn't touch hd
        have h_hd_ne_hd₂ : hd ≠ hd₂ := by
          intro h; apply h_hd_not_mem; rw [h]; simp
        cases h_orig : w.getNode hd with
        | none => rw [h_id_hd] at h₀; rw [h_orig] at h₀; contradiction
        | some nd₀' =>
          have h_w₁ : w₁.getNode hd =
              some ({ nd₀' with outputs := nd₀'.outputs ++ [hd₂] } : NodeData) := by
            dsimp [w₁]
            have h₁' : (w.updateNode hd₂ (fun nd => { nd with inputs := nd.inputs ++ [hd] })).getNode hd =
                some nd₀' := by
              rw [World.updateNode_getNode_ne w hd₂ hd _ (by omega)]; exact h_orig
            exact World.updateNode_getNode_eq _ hd _ nd₀' h₁'
          -- connectChain w₁ (hd₂::tl₂) preserves getNode hd since hd ∉ hd₂::tl₂
          have h_preserved : (connectChain w₁ (hd₂ :: tl₂)).getNode hd = w₁.getNode hd :=
            connectChain_getNode_of_not_mem (hd₂ :: tl₂) hd h_hd_not_mem w₁
          rw [h_id_hd] at h₁
          rw [h_preserved, h_w₁] at h₁
          injection h₁ with h_nd
          have : nd₁.outputs = nd₀'.outputs ++ [hd₂] := by cases h_nd; rfl
          rw [this, List.length_append, List.length_singleton]
          have : nd₀ = nd₀' := by
            rw [h_id_hd] at h₀
            injection h₀.symm.trans h_orig
          rw [this]
      · -- id ≠ hd: w₁ preserves outputs of id; apply IH
        have h_w₁_outputs : ∀ nd', w₁.getNode id = some nd' → nd'.outputs.length = nd₀.outputs.length := by
          intro nd' h_getNode'
          by_cases h_id_hd₂ : id = hd₂
          · -- id = hd₂: inputs changed, outputs unchanged
            cases h_orig : w.getNode hd₂ with
            | none =>
              have h₂ : w₁.getNode hd₂ = none := by
                dsimp [w₁]
                rw [World.updateNode_getNode_ne _ hd hd₂ _ (by omega)]
                exact World.updateNode_getNode_none w hd₂ _ h_orig
              rw [h_id_hd₂] at h_getNode'; rw [h₂] at h_getNode'; contradiction
            | some nd₀₂ =>
              have h₂ : w₁.getNode hd₂ =
                  some ({ nd₀₂ with inputs := nd₀₂.inputs ++ [hd] } : NodeData) := by
                dsimp [w₁]
                rw [World.updateNode_getNode_ne _ hd hd₂ _ (by omega)]
                exact World.updateNode_getNode_eq w hd₂ _ nd₀₂ h_orig
              rw [h_id_hd₂] at h_getNode'; rw [h₂] at h_getNode'
              injection h_getNode' with h_nd
              have : nd'.outputs = nd₀₂.outputs := by cases h_nd; rfl
              rw [this]
              have : nd₀ = nd₀₂ := by
                rw [h_id_hd₂] at h₀; injection h₀.symm.trans h_orig
              rw [this]
          · -- id ≠ hd₂: getNode unchanged
            have h₂ : w₁.getNode id = w.getNode id := by
              dsimp [w₁]
              rw [World.updateNode_getNode_ne _ hd id _ (by omega)]
              exact World.updateNode_getNode_ne w hd₂ id _ (by omega)
            rw [h₂] at h_getNode'
            have : nd' = nd₀ := by injection h₀.symm.trans h_getNode' with h; exact h.symm
            rw [this]
        -- Apply IH to w₁ and (hd₂ :: tl₂)
        cases h_w₁ : w₁.getNode id with
        | none =>
          have h₂ : (connectChain w₁ (hd₂ :: tl₂)).getNode id = none :=
            connectChain_preserves_getNode_none (hd₂ :: tl₂) w₁ id h_w₁
          rw [h₂] at h₁; contradiction
        | some nd₁' =>
          have h_len := h_w₁_outputs nd₁' h_w₁
          have h_ih := ih h_tl_nodup w₁ id nd₁' nd₁ h_w₁ h₁
          omega
theorem World.onNeighborUpdate_events_length_le (w : World) (id : Nat) :
    (w.onNeighborUpdate id).events.length ≤ w.events.length + 1 := by
  cases h_getNode : w.getNode id with
  | none => simp [World.onNeighborUpdate, h_getNode]
  | some nd =>
    cases h_kind : nd.kind with
    | repeater delay priority =>
      simp [World.onNeighborUpdate, h_getNode, h_kind, World.scheduleEvent_events]
    | observer =>
      simp [World.onNeighborUpdate, h_getNode, h_kind, World.scheduleEvent_events]
    | output name =>
      simp [World.onNeighborUpdate, h_getNode, h_kind, World.logOutput_events]
    | input =>
      simp [World.onNeighborUpdate, h_getNode, h_kind]

/-- A foldl of `onNeighborUpdate` increases event count by at most the list length. -/
theorem foldl_onNeighborUpdate_events_length_le (l : List Nat) (w : World) :
    (l.foldl (fun w' outId => w'.onNeighborUpdate outId) w).events.length ≤
    w.events.length + l.length := by
  induction l generalizing w with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.length]
    have h₁ := World.onNeighborUpdate_events_length_le w hd
    have h₂ := ih (w.onNeighborUpdate hd)
    omega

/-- `notifyOutputs` increases event count by at most the number of outputs. -/
theorem World.notifyOutputs_events_length_le (w : World) (id : Nat) :
    (w.notifyOutputs id).events.length ≤
    w.events.length + (w.getNode id).elim 0 (fun nd => nd.outputs.length) := by
  unfold World.notifyOutputs
  cases h_getNode : w.getNode id with
  | none => simp []
  | some nd =>
    simp only []
    exact foldl_onNeighborUpdate_events_length_le nd.outputs w

/-- `onScheduledTick` increases event count by at most the node's output count. -/
theorem World.onScheduledTick_events_length_le (w : World) (id : Nat) :
    (w.onScheduledTick id).events.length ≤
    w.events.length + (w.getNode id).elim 0 (fun nd => nd.outputs.length) := by
  cases h_go : w.getNode id with
  | none => simp [World.onScheduledTick, h_go]
  | some nd =>
    cases h_kind : nd.kind with
    | repeater delay priority =>
      have h_go_saved := h_go
      simp only [World.onScheduledTick, h_go, h_kind]
      set w' := w.updateNode id
        (fun nd' => { nd' with sigLevel := if w.getInputSignal id > 0 then 15 else 0 })
      have h_ev' : w'.events = w.events := World.updateNode_events w id _
      have h_go' : w'.getNode id =
          some ({ nd with sigLevel := if w.getInputSignal id > 0 then 15 else 0 } : NodeData) := by
        dsimp [w']; exact World.updateNode_getNode_eq w id _ nd h_go_saved
      simp only [World.notifyOutputs, h_go']
      change (nd.outputs.foldl (fun w₂ outId => w₂.onNeighborUpdate outId) w').events.length ≤
        w.events.length + nd.outputs.length
      have h_len := foldl_onNeighborUpdate_events_length_le nd.outputs w'
      rw [h_ev'] at h_len; exact h_len
    | observer =>
      have h_go_saved := h_go
      simp only [World.onScheduledTick, h_go, h_kind]
      set w' := w.updateNode id (fun nd' => { nd' with sigLevel := 15 })
      have h_ev' : w'.events = w.events := World.updateNode_events w id _
      have h_go' : w'.getNode id = some ({ nd with sigLevel := 15 } : NodeData) := by
        dsimp [w']; exact World.updateNode_getNode_eq w id _ nd h_go_saved
      simp only [World.notifyOutputs, h_go']
      change (nd.outputs.foldl (fun w₂ outId => w₂.onNeighborUpdate outId) w').events.length ≤
        w.events.length + nd.outputs.length
      have h_len := foldl_onNeighborUpdate_events_length_le nd.outputs w'
      rw [h_ev'] at h_len; exact h_len
    | output name => simp [World.onScheduledTick, h_go, h_kind]
    | input => simp [World.onScheduledTick, h_go, h_kind]

/-- `onScheduledTick` adds at most 1 event when the node has ≤ 1 output. -/
theorem World.onScheduledTick_events_le_one (w : World) (id : Nat)
    (h_le : (w.getNode id).elim 0 (fun nd => nd.outputs.length) ≤ 1) :
    (w.onScheduledTick id).events.length ≤ w.events.length + 1 := by
  have h := World.onScheduledTick_events_length_le w id
  omega

/-- `updateNode` changing only `sigLevel` preserves `outputs`. -/
theorem World.updateNode_sigLevel_preserves_outputs (w : World) (id : Nat) (level : Nat)
    (nd : NodeData) (h : w.getNode id = some nd) :
    ((w.updateNode id (fun nd => { nd with sigLevel := level })).getNode id).map (·.outputs) =
    some nd.outputs := by
  rw [World.updateNode_getNode_eq w id (fun nd => { nd with sigLevel := level }) nd h]
  rfl

/-! ### Layer 6b: Simulation preserves node inputs/outputs -/

/-- Transitivity of inputs/outputs preservation across two world transitions. -/
theorem inputs_preserved_trans (w₁ w₂ w₃ : World)
    (h₁₂ : ∀ nid nd, w₂.getNode nid = some nd →
      ∃ nd₀, w₁.getNode nid = some nd₀ ∧ nd.inputs = nd₀.inputs ∧ nd.outputs = nd₀.outputs)
    (h₂₃ : ∀ nid nd, w₃.getNode nid = some nd →
      ∃ nd₀, w₂.getNode nid = some nd₀ ∧ nd.inputs = nd₀.inputs ∧ nd.outputs = nd₀.outputs) :
    ∀ nid nd, w₃.getNode nid = some nd →
    ∃ nd₀, w₁.getNode nid = some nd₀ ∧ nd.inputs = nd₀.inputs ∧ nd.outputs = nd₀.outputs := by
  intro nid nd h
  obtain ⟨nd₁, h₁, hin₁, hout₁⟩ := h₂₃ nid nd h
  obtain ⟨nd₀, h₀, hin₀, hout₀⟩ := h₁₂ nid nd₁ h₁
  exact ⟨nd₀, h₀, hin₁.trans hin₀, hout₁.trans hout₀⟩

/-- `scheduleEvent` preserves `getNode`. -/
theorem World.scheduleEvent_getNode (w : World) (ev : ScheduledEvent) (nid : Nat) :
    (w.scheduleEvent ev).getNode nid = w.getNode nid := by
  simp [World.getNode, World.scheduleEvent_nodes]

/-- `logOutput` preserves `getNode`. -/
theorem World.logOutput_getNode (w : World) (msg : String) (nid : Nat) :
    (w.logOutput msg).getNode nid = w.getNode nid := by
  simp [World.getNode, World.logOutput_nodes]

/-- `logOutput` preserves node inputs and outputs. -/
theorem World.logOutput_inputs_preserved (w : World) (msg : String) :
    ∀ nid nd, (w.logOutput msg).getNode nid = some nd →
    ∃ nd₀, w.getNode nid = some nd₀ ∧ nd.inputs = nd₀.inputs ∧ nd.outputs = nd₀.outputs := by
  intro nid nd h
  rw [World.logOutput_getNode] at h
  exact ⟨nd, h, rfl, rfl⟩

/-- `updateNode` changing only `sigLevel` preserves node inputs and outputs. -/
theorem World.updateNode_sigLevel_inputs_preserved (w : World) (updId : Nat) (level : Nat) :
    ∀ nid nd, (w.updateNode updId (fun nd => { nd with sigLevel := level })).getNode nid = some nd →
    ∃ nd₀, w.getNode nid = some nd₀ ∧ nd.inputs = nd₀.inputs ∧ nd.outputs = nd₀.outputs := by
  intro nid nd h
  by_cases h_eq : nid = updId
  · rw [h_eq] at h ⊢
    cases h_orig : w.getNode updId with
    | none =>
      have h₂ := World.updateNode_getNode_none w updId (fun nd => { nd with sigLevel := level }) h_orig
      simp [h₂] at h
    | some nd₁ =>
      have h₂ : (w.updateNode updId (fun nd => { nd with sigLevel := level })).getNode updId =
          some ({ nd₁ with sigLevel := level } : NodeData) :=
        World.updateNode_getNode_eq w updId (fun nd => { nd with sigLevel := level }) nd₁ h_orig
      have h_nd_eq : nd = { nd₁ with sigLevel := level } := by
        have h_eq : some ({ nd₁ with sigLevel := level } : NodeData) = some nd := h₂.symm.trans h
        injection h_eq with h_nd; exact h_nd.symm
      exact ⟨nd₁, rfl, by simp [h_nd_eq], by simp [h_nd_eq]⟩
  · have h₂ := World.updateNode_getNode_ne w updId nid (fun nd => { nd with sigLevel := level }) (Ne.symm h_eq)
    rw [h₂] at h
    exact ⟨nd, h, rfl, rfl⟩

/-- `setInput` preserves node inputs and outputs. -/
theorem World.setInput_inputs_preserved (w : World) (nodeId level : Nat) :
    ∀ nid nd, (w.setInput nodeId level).getNode nid = some nd →
    ∃ nd₀, w.getNode nid = some nd₀ ∧ nd.inputs = nd₀.inputs ∧ nd.outputs = nd₀.outputs := by
  intro nid nd h
  dsimp [World.setInput] at h
  rw [World.notifyOutputs_getNode] at h
  exact World.updateNode_sigLevel_inputs_preserved w nodeId level nid nd h

/-- `onScheduledTick` preserves node inputs and outputs. -/
theorem World.onScheduledTick_inputs_preserved (w : World) (nodeId : Nat) :
    ∀ nid nd, (w.onScheduledTick nodeId).getNode nid = some nd →
    ∃ nd₀, w.getNode nid = some nd₀ ∧ nd.inputs = nd₀.inputs ∧ nd.outputs = nd₀.outputs := by
  intro nid nd h
  dsimp [World.onScheduledTick] at h
  split at h
  · -- getNode nodeId = none → result is w
    exact ⟨nd, h, rfl, rfl⟩
  · rename_i nd_id; split at h
    · -- repeater case
      rw [World.notifyOutputs_getNode] at h
      exact World.updateNode_sigLevel_inputs_preserved w nodeId _ nid nd h
    · -- observer case
      rw [World.notifyOutputs_getNode] at h
      exact World.updateNode_sigLevel_inputs_preserved w nodeId 15 nid nd h
    · -- output/input case: result is w
      exact ⟨nd, h, rfl, rfl⟩

/-- `step` preserves node inputs and outputs. -/
theorem World.step_inputs_preserved (w : World) :
    ∀ w', w.step = some w' →
    ∀ nid nd, w'.getNode nid = some nd →
    ∃ nd₀, w.getNode nid = some nd₀ ∧ nd.inputs = nd₀.inputs ∧ nd.outputs = nd₀.outputs := by
  intro w' h_step nid nd h_nd
  dsimp [World.step] at h_step
  cases h_pop : w.popNextEvent with
  | none => simp [h_pop] at h_step
  | some p =>
    rcases p with ⟨ev, w_pop⟩
    simp only [h_pop] at h_step
    injection h_step with h_w'
    subst h_w'
    have h_nodes : w_pop.nodes = w.nodes := World.popNextEvent_nodes w ev w_pop h_pop
    have h_getNode_eq : ∀ nid, w_pop.getNode nid = w.getNode nid := by
      intro nid; dsimp [World.getNode]; rw [h_nodes]
    obtain ⟨nd₀, h₀, hin, hout⟩ := World.onScheduledTick_inputs_preserved w_pop ev.nodeId nid nd h_nd
    rw [h_getNode_eq] at h₀
    exact ⟨nd₀, h₀, hin, hout⟩

/-- `stepUntilNextTick` preserves node inputs and outputs. -/
theorem World.stepUntilNextTick_inputs_preserved (w : World) :
    ∀ nid nd, (w.stepUntilNextTick).getNode nid = some nd →
    ∃ nd₀, w.getNode nid = some nd₀ ∧ nd.inputs = nd₀.inputs ∧ nd.outputs = nd₀.outputs := by
  induction w using World.stepUntilNextTick.induct with
  | case1 w h_step =>
    intro nid nd h
    rw [stepUntilNextTick_of_step_none w h_step] at h
    dsimp [World.getNode] at h ⊢
    exact ⟨nd, h, rfl, rfl⟩
  | case2 w w' h_step' ih =>
    intro nid nd h
    have h_sunt : w.stepUntilNextTick = w'.stepUntilNextTick := by
      rw [World.stepUntilNextTick, h_step']
    rw [h_sunt] at h
    obtain ⟨nd₁, h₁, hin₁, hout₁⟩ := ih nid nd h
    obtain ⟨nd₀, h₀, hin₀, hout₀⟩ := World.step_inputs_preserved w w' h_step' nid nd₁ h₁
    exact ⟨nd₀, h₀, hin₁.trans hin₀, hout₁.trans hout₀⟩

/-- `processNEvents` preserves node inputs and outputs. -/
theorem processNEvents_inputs_preserved (w : World) (n : Nat) :
    ∀ nid nd, (processNEvents w n).getNode nid = some nd →
    ∃ nd₀, w.getNode nid = some nd₀ ∧ nd.inputs = nd₀.inputs ∧ nd.outputs = nd₀.outputs := by
  induction n generalizing w with
  | zero =>
    intro nid nd h
    exact ⟨nd, h, rfl, rfl⟩
  | succ n' ih =>
    intro nid nd h
    dsimp [processNEvents] at h
    cases h_step : w.step with
    | none =>
      simp [h_step] at h
      exact ⟨nd, h, rfl, rfl⟩
    | some w' =>
      simp [h_step] at h
      have h_ih := ih w' nid nd h
      obtain ⟨nd₁, h₁, hin₁, hout₁⟩ := h_ih
      obtain ⟨nd₀, h₀, hin₀, hout₀⟩ := World.step_inputs_preserved w w' h_step nid nd₁ h₁
      exact ⟨nd₀, h₀, hin₁.trans hin₀, hout₁.trans hout₀⟩

/-- `simBody` preserves node inputs and outputs. -/
theorem simBody_inputs_preserved (t1 t2 pos in1 in2 : Nat) (w : World) (i : Nat) :
    ∀ nid nd, (simBody t1 t2 pos in1 in2 w i).getNode nid = some nd →
    ∃ nd₀, w.getNode nid = some nd₀ ∧ nd.inputs = nd₀.inputs ∧ nd.outputs = nd₀.outputs := by
  intro nid nd h
  -- simBody is a composition of logOutput, setInput, processNEvents, stepUntilNextTick
  -- All preserve inputs/outputs. We prove by chaining the preservation lemmas.
  dsimp (config := { zeta := true }) [simBody] at h
  split_ifs at h with h_t1 h_t2
  · -- tick == t1, tick == t2: logOutput + setInput in1 + processNEvents + setInput in2 + stepUntilNextTick
    obtain ⟨nd₁, h₁, hin₁, hout₁⟩ := World.stepUntilNextTick_inputs_preserved _ nid nd h
    obtain ⟨nd₂, h₂, hin₂, hout₂⟩ := World.setInput_inputs_preserved _ in2 15 nid nd₁ h₁
    obtain ⟨nd₃, h₃, hin₃, hout₃⟩ := processNEvents_inputs_preserved _ pos nid nd₂ h₂
    obtain ⟨nd₄, h₄, hin₄, hout₄⟩ := World.setInput_inputs_preserved _ in1 15 nid nd₃ h₃
    obtain ⟨nd₅, h₅, hin₅, hout₅⟩ := World.logOutput_inputs_preserved w _ nid nd₄ h₄
    exact ⟨nd₅, h₅, hin₁.trans (hin₂.trans (hin₃.trans (hin₄.trans hin₅))), hout₁.trans (hout₂.trans (hout₃.trans (hout₄.trans hout₅)))⟩
  · -- tick == t1, tick ≠ t2: logOutput + setInput in1 + stepUntilNextTick
    obtain ⟨nd₁, h₁, hin₁, hout₁⟩ := World.stepUntilNextTick_inputs_preserved _ nid nd h
    obtain ⟨nd₂, h₂, hin₂, hout₂⟩ := World.setInput_inputs_preserved _ in1 15 nid nd₁ h₁
    obtain ⟨nd₃, h₃, hin₃, hout₃⟩ := World.logOutput_inputs_preserved w _ nid nd₂ h₂
    exact ⟨nd₃, h₃, hin₁.trans (hin₂.trans hin₃), hout₁.trans (hout₂.trans hout₃)⟩
  · -- tick ≠ t1, tick == t2: logOutput + processNEvents + setInput in2 + stepUntilNextTick
    obtain ⟨nd₁, h₁, hin₁, hout₁⟩ := World.stepUntilNextTick_inputs_preserved _ nid nd h
    obtain ⟨nd₂, h₂, hin₂, hout₂⟩ := World.setInput_inputs_preserved _ in2 15 nid nd₁ h₁
    obtain ⟨nd₃, h₃, hin₃, hout₃⟩ := processNEvents_inputs_preserved _ pos nid nd₂ h₂
    obtain ⟨nd₄, h₄, hin₄, hout₄⟩ := World.logOutput_inputs_preserved w _ nid nd₃ h₃
    exact ⟨nd₄, h₄, hin₁.trans (hin₂.trans (hin₃.trans hin₄)), hout₁.trans (hout₂.trans (hout₃.trans hout₄))⟩
  · -- tick ≠ t1, tick ≠ t2: logOutput + stepUntilNextTick
    obtain ⟨nd₁, h₁, hin₁, hout₁⟩ := World.stepUntilNextTick_inputs_preserved _ nid nd h
    obtain ⟨nd₂, h₂, hin₂, hout₂⟩ := World.logOutput_inputs_preserved w _ nid nd₁ h₁
    exact ⟨nd₂, h₂, hin₁.trans hin₂, hout₁.trans hout₂⟩

/-- `simFoldl` (foldl of simBody over range n) preserves node inputs and outputs. -/
theorem simFoldl_inputs_preserved (w : World) (t1 t2 pos in1 in2 : Nat) (n : Nat) :
    ∀ nid nd, ((List.range n).foldl (simBody t1 t2 pos in1 in2) w).getNode nid = some nd →
    ∃ nd₀, w.getNode nid = some nd₀ ∧ nd.inputs = nd₀.inputs ∧ nd.outputs = nd₀.outputs := by
  induction n generalizing w with
  | zero =>
    intro nid nd h
    simp at h
    exact ⟨nd, h, rfl, rfl⟩
  | succ n' ih =>
    intro nid nd h
    rw [List.range_succ, List.foldl_append] at h
    simp only [List.foldl_cons, List.foldl_nil] at h
    -- h : (simBody t1 t2 pos in1 in2 ((List.range n').foldl (simBody ...) w) n').getNode nid = some nd
    set w_mid := (List.range n').foldl (simBody t1 t2 pos in1 in2) w
    obtain ⟨nd₁, h₁, hin₁, hout₁⟩ := simBody_inputs_preserved t1 t2 pos in1 in2 w_mid n' nid nd h
    obtain ⟨nd₀, h₀, hin₀, hout₀⟩ := ih w nid nd₁ h₁
    exact ⟨nd₀, h₀, hin₁.trans hin₀, hout₁.trans hout₀⟩

/-- `logOutput` preserves node kind. -/
theorem World.logOutput_kind_preserved (w : World) (msg : String) :
    ∀ nid nd, (w.logOutput msg).getNode nid = some nd →
    ∃ nd₀, w.getNode nid = some nd₀ ∧ nd.kind = nd₀.kind := by
  intro nid nd h; rw [World.logOutput_getNode] at h; exact ⟨nd, h, rfl⟩

/-- `setInput` preserves node kind. -/
theorem World.setInput_kind_preserved (w : World) (nodeId level : Nat) :
    ∀ nid nd, (w.setInput nodeId level).getNode nid = some nd →
    ∃ nd₀, w.getNode nid = some nd₀ ∧ nd.kind = nd₀.kind := by
  intro nid nd h
  dsimp [World.setInput] at h
  rw [World.notifyOutputs_getNode] at h
  -- updateNode with sigLevel change preserves kind
  by_cases h_eq : nid = nodeId
  · rw [h_eq] at h ⊢
    cases h_orig : w.getNode nodeId with
    | none =>
      have h₂ := World.updateNode_getNode_none w nodeId (fun nd => { nd with sigLevel := level }) h_orig
      simp [h₂] at h
    | some nd₁ =>
      have h₂ : (w.updateNode nodeId (fun nd => { nd with sigLevel := level })).getNode nodeId =
          some ({ nd₁ with sigLevel := level } : NodeData) :=
        World.updateNode_getNode_eq w nodeId (fun nd => { nd with sigLevel := level }) nd₁ h_orig
      have h_nd_eq : nd = { nd₁ with sigLevel := level } := by
        have h_eq : some ({ nd₁ with sigLevel := level } : NodeData) = some nd := h₂.symm.trans h
        injection h_eq with h_nd; exact h_nd.symm
      exact ⟨nd₁, rfl, by simp [h_nd_eq]⟩
  · have h₂ := World.updateNode_getNode_ne w nodeId nid (fun nd => { nd with sigLevel := level }) (Ne.symm h_eq)
    rw [h₂] at h
    exact ⟨nd, h, rfl⟩

/-- `onScheduledTick` preserves node kind. -/
theorem World.onScheduledTick_kind_preserved (w : World) (nodeId : Nat) :
    ∀ nid nd, (w.onScheduledTick nodeId).getNode nid = some nd →
    ∃ nd₀, w.getNode nid = some nd₀ ∧ nd.kind = nd₀.kind := by
  intro nid nd h
  cases h_getNode : w.getNode nodeId with
  | none =>
    simp [World.onScheduledTick, h_getNode] at h; exact ⟨nd, h, rfl⟩
  | some nd₀ =>
    cases h_kind : nd₀.kind with
    | repeater d p =>
      simp only [World.onScheduledTick, h_getNode, h_kind] at h
      rw [World.notifyOutputs_getNode] at h
      -- h : (w.updateNode nodeId (fun nd => { nd with sigLevel := ... })).getNode nid = some nd
      by_cases h_eq : nid = nodeId
      · rw [h_eq] at h ⊢
        cases h_orig : w.getNode nodeId with
        | none =>
          have h₂ := World.updateNode_getNode_none w nodeId (fun nd => { nd with sigLevel := if w.getInputSignal nodeId > 0 then 15 else 0 }) h_orig
          simp [h₂] at h
        | some nd₁ =>
          have h₂ := World.updateNode_getNode_eq w nodeId (fun nd => { nd with sigLevel := if w.getInputSignal nodeId > 0 then 15 else 0 }) nd₁ h_orig
          have h_nd_eq : nd = { nd₁ with sigLevel := if w.getInputSignal nodeId > 0 then 15 else 0 } := by
            have := h₂.symm.trans h; injection this with h_nd; exact h_nd.symm
          exact ⟨nd₁, rfl, by simp [h_nd_eq]⟩
      · have h₂ := World.updateNode_getNode_ne w nodeId nid (fun nd => { nd with sigLevel := if w.getInputSignal nodeId > 0 then 15 else 0 }) (Ne.symm h_eq)
        rw [h₂] at h; exact ⟨nd, h, rfl⟩
    | observer =>
      simp [World.onScheduledTick, h_getNode, h_kind] at h
      rw [World.notifyOutputs_getNode] at h
      by_cases h_eq : nid = nodeId
      · rw [h_eq] at h ⊢
        cases h_orig : w.getNode nodeId with
        | none => simp [World.updateNode_getNode_none w nodeId (fun nd => { nd with sigLevel := 15 }) h_orig] at h
        | some nd₁ =>
          have h₂ := World.updateNode_getNode_eq w nodeId (fun nd => { nd with sigLevel := 15 }) nd₁ h_orig
          have h_nd_eq : nd = { nd₁ with sigLevel := 15 } := by
            have := h₂.symm.trans h; injection this with h_nd; exact h_nd.symm
          exact ⟨nd₁, rfl, by simp [h_nd_eq]⟩
      · have h₂ := World.updateNode_getNode_ne w nodeId nid (fun nd => { nd with sigLevel := 15 }) (Ne.symm h_eq)
        rw [h₂] at h; exact ⟨nd, h, rfl⟩
    | output _ =>
      simp [World.onScheduledTick, h_getNode, h_kind] at h; exact ⟨nd, h, rfl⟩
    | input =>
      simp [World.onScheduledTick, h_getNode, h_kind] at h; exact ⟨nd, h, rfl⟩
