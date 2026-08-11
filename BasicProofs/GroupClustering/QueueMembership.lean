import BasicProofs.GroupClustering.StageEvents


open BasicRedstoneSim

/-! # Group clustering — queue membership characterization (forward direction)

Every event in the queue at the start of tick `t` is the stage event of some
valid chain and satisfies `stageWindow ... t`: its predecessor stage has
fired and it has not fired yet.

The invariant maintained within a tick (`StageMemAt ... t`) is slightly
weaker (predecessor fired before `t + 1`, own target at least `t`); at the
end of the tick no events targeting the tick remain, so the invariant
sharpens to `stageWindow (t + 1)`.
-/

/-! ## The invariants -/

/-- Queue-membership invariant relative to an explicit tick `t`: every queued
    event is a stage event of a valid chain, its predecessor fired strictly
    before `t + 1` and its own target is at least `t`. -/
def StageMemAt (groups : List GroupSpec) (actTick : Nat → Nat) (w : World)
    (t : Nat) : Prop :=
  ∀ ev ∈ w.events, ∃ gi ci j, gi < groups.length ∧ ci < (groupAt groups gi).length ∧
    j ≤ (chainAt groups gi ci).middleDelays.length + 1 ∧
    ev = stageEvent actTick groups gi ci j ∧
    (if j = 0 then actTick gi else stageTarget actTick groups gi ci (j - 1)) < t + 1 ∧
    t ≤ stageTarget actTick groups gi ci j

/-- The chain-node layout persists: observers, middle repeaters, last repeater
    and output node keep their kind and outputs. -/
def NodeLayoutOk (groups : List GroupSpec) (w : World) : Prop :=
  (∀ gi ci, gi < groups.length → ci < (groupAt groups gi).length →
    ∃ nd, w.getNode (chainBaseId groups gi ci + 1) = some nd ∧
      nd.kind = NodeKind.observer ∧ nd.outputs = [chainBaseId groups gi ci + 2]) ∧
  (∀ gi ci k, gi < groups.length → ci < (groupAt groups gi).length →
    ∀ h_k : k < (chainAt groups gi ci).middleDelays.length,
    ∃ nd, w.getNode (chainBaseId groups gi ci + 2 + k) = some nd ∧
      nd.kind = NodeKind.repeater ((chainAt groups gi ci).middleDelays[k]'(h_k)) (-3) ∧
      nd.outputs = [chainBaseId groups gi ci + 3 + k]) ∧
  (∀ gi ci, gi < groups.length → ci < (groupAt groups gi).length →
    ∃ nd, w.getNode
        (chainBaseId groups gi ci + (chainAt groups gi ci).middleDelays.length + 2) =
      some nd ∧
      nd.kind = NodeKind.repeater (chainAt groups gi ci).lastDelay (-1) ∧
      nd.outputs = [chainBaseId groups gi ci +
        (chainAt groups gi ci).middleDelays.length + 3]) ∧
  (∀ gi ci, gi < groups.length → ci < (groupAt groups gi).length →
    ∃ nd, w.getNode
        (chainBaseId groups gi ci + (chainAt groups gi ci).middleDelays.length + 3) =
      some nd ∧ nd.kind = NodeKind.output (chainName gi ci) ∧ nd.outputs = [])

/-! ## Small list and build helpers -/

private theorem buildGroupsFrom_snd_length (start : Nat) (w : World)
    (groups : List GroupSpec) :
    (buildGroupsFrom start w groups).2.length = groups.length := by
  induction groups generalizing w start with
  | nil => simp [buildGroupsFrom]
  | cons g gs ih =>
    dsimp [buildGroupsFrom]
    rw [ih]

theorem buildGroups_snd_length (groups : List GroupSpec) :
    (buildGroups groups).2.length = groups.length := by
  simpa [buildGroups] using buildGroupsFrom_snd_length 0 World.empty groups

private theorem buildGroupsFrom_snd_getD_length (start : Nat) (w : World)
    (groups : List GroupSpec) (gi : Nat) :
    ((buildGroupsFrom start w groups).2[gi]?.getD []).length =
    (groupAt groups gi).length := by
  revert gi
  induction groups generalizing w start with
  | nil => intro gi; simp [buildGroupsFrom, groupAt]
  | cons g gs ih =>
    intro gi
    cases gi with
    | zero =>
      dsimp [buildGroupsFrom, groupAt]
      simp
      rw [buildGroupChains, buildGroupChainsFrom_snd_length]
    | succ gi' =>
      dsimp [buildGroupsFrom, groupAt]
      exact ih (start + 1) (buildGroupChains start w g).1 gi'

theorem buildGroups_obs_length (groups : List GroupSpec) (gi : Nat) :
    ((buildGroups groups).2[gi]?.getD []).length = (groupAt groups gi).length := by
  simpa [buildGroups] using buildGroupsFrom_snd_getD_length 0 World.empty groups gi

/-- Observer id at index `ci` of group `gi`'s observer list (`none` when out of
    range). Hides the `getElem?` behind an explicit `Option Nat` return type so
    that statements with an `∃`-bound index elaborate (a bare `getElem?` under an
    `∃` binder leaves the element type metavariable unresolved). -/
private def obsAtIdx (obsAll : List (List Nat)) (gi ci : Nat) : Option Nat :=
  (obsAll[gi]?.getD [])[ci]?

/-- Every element of the ordered-observer fold comes from some entry of the
    group's observer list. -/
private theorem mem_foldl_observers (obsAll : List (List Nat))
    (withinOrd : Nat → List Nat) (gi oid : Nat) :
    oid ∈ (withinOrd gi).foldl (fun acc ci =>
      match obsAtIdx obsAll gi ci with
      | some o => acc ++ [o]
      | none => acc) [] →
    ∃ ci, some oid = obsAtIdx obsAll gi ci := by
  intro h
  have h_gen : ∀ (l acc : List Nat),
      (∀ oid' ∈ acc, ∃ ci, some oid' = obsAtIdx obsAll gi ci) →
      oid ∈ l.foldl (fun acc' ci =>
        match obsAtIdx obsAll gi ci with
        | some o => acc' ++ [o]
        | none => acc') acc →
      ∃ ci, some oid = obsAtIdx obsAll gi ci := by
    intro l acc
    induction l generalizing acc with
    | nil =>
      intro h_acc h_oid
      have h_oid' : oid ∈ acc := by simpa using h_oid
      exact h_acc oid h_oid'
    | cons hd tl ih =>
      intro h_acc h_oid
      simp only [List.foldl_cons] at h_oid
      split at h_oid
      · rename_i o h_split
        refine ih (acc ++ [o]) ?_ h_oid
        intro oid' h'
        rw [List.mem_append] at h'
        rcases h' with h' | h'
        · exact h_acc oid' h'
        · have h_eq : oid' = o := by simpa using h'
          subst h_eq
          exact ⟨hd, h_split.symm⟩
      · exact ih acc h_acc h_oid
  exact h_gen (withinOrd gi) [] (by simp) h

/-! ## Reverse field preservation

A node that exists in the input world still exists after each simulation
operator, with unchanged kind/inputs/outputs (joining PrefixChain's reverse
existence lemmas with Dynamics's forward preservation). -/

theorem processNEvents_getNode_fields (w : World) (n nid : Nat) (nd₀ : NodeData)
    (h₀ : w.getNode nid = some nd₀) :
    ∃ nd, (processNEvents w n).getNode nid = some nd ∧ nd.kind = nd₀.kind ∧
      nd.inputs = nd₀.inputs ∧ nd.outputs = nd₀.outputs := by
  obtain ⟨nd₁, h₁⟩ := processNEvents_getNode_some w n nid ⟨nd₀, h₀⟩
  obtain ⟨nd₂, h₂, hk, hi, ho⟩ := processNEvents_fields_preserved w n nid nd₁ h₁
  have h_eq : nd₂ = nd₀ := Option.some_inj.mp (h₂.symm.trans h₀)
  exact ⟨nd₁, h₁, by rw [hk, h_eq], by rw [hi, h_eq], by rw [ho, h_eq]⟩

theorem World.stepUntilNextTick_getNode_fields (w : World) (nid : Nat)
    (nd₀ : NodeData) (h₀ : w.getNode nid = some nd₀) :
    ∃ nd, w.stepUntilNextTick.getNode nid = some nd ∧ nd.kind = nd₀.kind ∧
      nd.inputs = nd₀.inputs ∧ nd.outputs = nd₀.outputs := by
  obtain ⟨nd₁, h₁⟩ := World.stepUntilNextTick_getNode_some w nid ⟨nd₀, h₀⟩
  obtain ⟨nd₂, h₂, hk, hi, ho⟩ := World.stepUntilNextTick_fields_preserved w nid nd₁ h₁
  have h_eq : nd₂ = nd₀ := Option.some_inj.mp (h₂.symm.trans h₀)
  exact ⟨nd₁, h₁, by rw [hk, h_eq], by rw [hi, h_eq], by rw [ho, h_eq]⟩

theorem World.step_getNode_fields (w w' : World) (h_step : w.step = some w')
    (nid : Nat) (nd₀ : NodeData) (h₀ : w.getNode nid = some nd₀) :
    ∃ nd, w'.getNode nid = some nd ∧ nd.kind = nd₀.kind ∧
      nd.outputs = nd₀.outputs := by
  obtain ⟨nd₁, h₁⟩ := World.step_getNode_some w nid ⟨nd₀, h₀⟩ w' h_step
  obtain ⟨nd₂, h₂, hk, _, ho⟩ := step_fields_preserved w w' h_step nid nd₁ h₁
  have h_eq : nd₂ = nd₀ := Option.some_inj.mp (h₂.symm.trans h₀)
  exact ⟨nd₁, h₁, by rw [hk, h_eq], by rw [ho, h_eq]⟩

theorem gSimBurst_getNode_fields (t : Nat) (obsAll : List (List Nat))
    (withinOrd : Nat → List Nat) (pos : Nat → List Nat) (w : World)
    (pairs : List (Nat × Nat)) (nid : Nat) :
    ∀ nd₀, w.getNode nid = some nd₀ →
    ∃ nd, (gSimBurst t obsAll withinOrd pos w pairs).getNode nid = some nd ∧
      nd.kind = nd₀.kind ∧ nd.inputs = nd₀.inputs ∧ nd.outputs = nd₀.outputs := by
  induction pairs generalizing w with
  | nil =>
    intro nd₀ h₀
    exact ⟨nd₀, by simpa [gSimBurst] using h₀, rfl, rfl, rfl⟩
  | cons p ps ih =>
    simp only [gSimBurst, List.foldl_cons]
    rcases p with ⟨gi, k⟩
    simp only
    intro nd₀ h₀
    obtain ⟨nd₁, h₁, hk, hi, ho⟩ :=
      processNEvents_getNode_fields w ((pos t)[k]?.getD 0) nid nd₀ h₀
    obtain ⟨nd₂, h₂, hk₂, hi₂, ho₂⟩ :=
      ih (activateGroup (processNEvents w ((pos t)[k]?.getD 0))
        ((withinOrd gi).foldl (fun acc ci =>
          match ((obsAll[gi]?.getD [])[ci]?) with
          | some oid => acc ++ [oid]
          | none => acc) [])) nd₁ (by
        dsimp [World.getNode]
        rw [activateGroup_nodes]
        exact h₁)
    exact ⟨nd₂, h₂, by rw [hk₂, hk], by rw [hi₂, hi], by rw [ho₂, ho]⟩

theorem gSimBody_getNode_fields (actTick : Nat → Nat) (obsAll : List (List Nat))
    (groupOrd : List Nat) (withinOrd pos : Nat → List Nat) (w : World)
    (i nid : Nat) :
    ∀ nd₀, w.getNode nid = some nd₀ →
    ∃ nd, (gSimBody actTick obsAll groupOrd withinOrd pos w i).getNode nid = some nd ∧
      nd.kind = nd₀.kind ∧ nd.inputs = nd₀.inputs ∧ nd.outputs = nd₀.outputs := by
  intro nd₀ h₀
  dsimp [gSimBody]
  split_ifs with h_active
  · exact World.stepUntilNextTick_getNode_fields (w.logOutput s!"tick {w.tick}") nid
      nd₀ (by rw [World.logOutput_getNode]; exact h₀)
  · set W₁ := w.logOutput s!"tick {w.tick}"
    set active := groupOrd.filter (fun gi =>
      decide (gi < obsAll.length) && (actTick gi == w.tick))
    obtain ⟨nd₁, h₁, hk, hi, ho⟩ :=
      gSimBurst_getNode_fields w.tick obsAll withinOrd pos W₁ (active.zipIdx) nid nd₀
        (by rw [World.logOutput_getNode]; exact h₀)
    obtain ⟨nd₂, h₂, hk₂, hi₂, ho₂⟩ :=
      World.stepUntilNextTick_getNode_fields
        (gSimBurst w.tick obsAll withinOrd pos W₁ (active.zipIdx)) nid nd₁ h₁
    exact ⟨nd₂, h₂, by rw [hk₂, hk], by rw [hi₂, hi], by rw [ho₂, ho]⟩

theorem gSimFoldl_getNode_fields (actTick : Nat → Nat) (obsAll : List (List Nat))
    (groupOrd : List Nat) (withinOrd pos : Nat → List Nat) (w : World)
    (n nid : Nat) :
    ∀ nd₀, w.getNode nid = some nd₀ →
    ∃ nd, (gSimFoldl actTick obsAll groupOrd withinOrd pos w n).getNode nid = some nd ∧
      nd.kind = nd₀.kind ∧ nd.inputs = nd₀.inputs ∧ nd.outputs = nd₀.outputs := by
  induction n generalizing w with
  | zero =>
    intro nd₀ h₀
    exact ⟨nd₀, by simpa [gSimFoldl] using h₀, rfl, rfl, rfl⟩
  | succ n' ih =>
    intro nd₀ h₀
    simp only [gSimFoldl, List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil]
    obtain ⟨nd₁, h₁, hk, hi, ho⟩ := ih w nd₀ h₀
    obtain ⟨nd₂, h₂, hk₂, hi₂, ho₂⟩ :=
      gSimBody_getNode_fields actTick obsAll groupOrd withinOrd pos
        ((List.range n').foldl (gSimBody actTick obsAll groupOrd withinOrd pos) w) n'
        nid nd₁ h₁
    exact ⟨nd₂, h₂, by rw [hk₂, hk], by rw [hi₂, hi], by rw [ho₂, ho]⟩

/-! ## Layout preservation -/

private theorem NodeLayoutOk_preserved (groups : List GroupSpec) (w w' : World)
    (h : ∀ nid nd₀, w.getNode nid = some nd₀ → ∃ nd, w'.getNode nid = some nd ∧
        nd.kind = nd₀.kind ∧ nd.outputs = nd₀.outputs) :
    NodeLayoutOk groups w → NodeLayoutOk groups w' := by
  intro H
  rcases H with ⟨hO, hM, hL, hOut⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro gi ci h_gi h_ci
    obtain ⟨nd₀, h₀, hk, ho⟩ := hO gi ci h_gi h_ci
    obtain ⟨nd, h₁, hk₁, ho₁⟩ := h (chainBaseId groups gi ci + 1) nd₀ h₀
    exact ⟨nd, h₁, by rw [hk₁, hk], by rw [ho₁, ho]⟩
  · intro gi ci k h_gi h_ci h_k
    obtain ⟨nd₀, h₀, hk, ho⟩ := hM gi ci k h_gi h_ci h_k
    obtain ⟨nd, h₁, hk₁, ho₁⟩ := h (chainBaseId groups gi ci + 2 + k) nd₀ h₀
    exact ⟨nd, h₁, by rw [hk₁, hk], by rw [ho₁, ho]⟩
  · intro gi ci h_gi h_ci
    obtain ⟨nd₀, h₀, hk, ho⟩ := hL gi ci h_gi h_ci
    obtain ⟨nd, h₁, hk₁, ho₁⟩ := h _ nd₀ h₀
    exact ⟨nd, h₁, by rw [hk₁, hk], by rw [ho₁, ho]⟩
  · intro gi ci h_gi h_ci
    obtain ⟨nd₀, h₀, hk, ho⟩ := hOut gi ci h_gi h_ci
    obtain ⟨nd, h₁, hk₁, ho₁⟩ := h _ nd₀ h₀
    exact ⟨nd, h₁, by rw [hk₁, hk], by rw [ho₁, ho]⟩

theorem NodeLayoutOk_buildGroups (groups : List GroupSpec) :
    NodeLayoutOk groups (buildGroups groups).1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun gi ci h_gi h_ci => buildGroups_observer_node groups gi ci h_gi h_ci
  · exact fun gi ci k h_gi h_ci h_k =>
      buildGroups_middleRep_node groups gi ci k h_gi h_ci h_k
  · exact fun gi ci h_gi h_ci => buildGroups_lastRep_node groups gi ci h_gi h_ci
  · exact fun gi ci h_gi h_ci => buildGroups_output_node groups gi ci h_gi h_ci

theorem NodeLayoutOk_logOutput (groups : List GroupSpec) (w : World) (msg : String) :
    NodeLayoutOk groups w → NodeLayoutOk groups (w.logOutput msg) :=
  NodeLayoutOk_preserved groups w (w.logOutput msg) (fun nid nd₀ h₀ =>
    ⟨nd₀, by rw [World.logOutput_getNode]; exact h₀, rfl, rfl⟩)

theorem NodeLayoutOk_activateGroup (groups : List GroupSpec) (w : World)
    (observers : List Nat) :
    NodeLayoutOk groups w → NodeLayoutOk groups (activateGroup w observers) :=
  NodeLayoutOk_preserved groups w (activateGroup w observers) (fun nid nd₀ h₀ =>
    ⟨nd₀, by dsimp [World.getNode]; rw [activateGroup_nodes]; exact h₀, rfl, rfl⟩)

theorem NodeLayoutOk_processNEvents (groups : List GroupSpec) (w : World) (n : Nat) :
    NodeLayoutOk groups w → NodeLayoutOk groups (processNEvents w n) :=
  NodeLayoutOk_preserved groups w (processNEvents w n) (fun nid nd₀ h₀ => by
    obtain ⟨nd, h, hk, _, ho⟩ := processNEvents_getNode_fields w n nid nd₀ h₀
    exact ⟨nd, h, hk, ho⟩)

theorem NodeLayoutOk_step (groups : List GroupSpec) (w w' : World)
    (h_step : w.step = some w') :
    NodeLayoutOk groups w → NodeLayoutOk groups w' :=
  NodeLayoutOk_preserved groups w w' (fun nid nd₀ h₀ => by
    obtain ⟨nd, h, hk, ho⟩ := World.step_getNode_fields w w' h_step nid nd₀ h₀
    exact ⟨nd, h, hk, ho⟩)

theorem NodeLayoutOk_stepUntilNextTick (groups : List GroupSpec) (w : World) :
    NodeLayoutOk groups w → NodeLayoutOk groups w.stepUntilNextTick :=
  NodeLayoutOk_preserved groups w w.stepUntilNextTick (fun nid nd₀ h₀ => by
    obtain ⟨nd, h, hk, _, ho⟩ := World.stepUntilNextTick_getNode_fields w nid nd₀ h₀
    exact ⟨nd, h, hk, ho⟩)

theorem NodeLayoutOk_gSimBurst (groups : List GroupSpec) (t : Nat)
    (obsAll : List (List Nat)) (withinOrd : Nat → List Nat) (pos : Nat → List Nat)
    (w : World) (pairs : List (Nat × Nat)) :
    NodeLayoutOk groups w →
    NodeLayoutOk groups (gSimBurst t obsAll withinOrd pos w pairs) :=
  NodeLayoutOk_preserved groups w (gSimBurst t obsAll withinOrd pos w pairs)
    (fun nid nd₀ h₀ => by
      obtain ⟨nd, h, hk, _, ho⟩ :=
        gSimBurst_getNode_fields t obsAll withinOrd pos w pairs nid nd₀ h₀
      exact ⟨nd, h, hk, ho⟩)

theorem NodeLayoutOk_gSimBody (groups : List GroupSpec) (actTick : Nat → Nat)
    (obsAll : List (List Nat)) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (w : World) (i : Nat) :
    NodeLayoutOk groups w →
    NodeLayoutOk groups (gSimBody actTick obsAll groupOrd withinOrd pos w i) :=
  NodeLayoutOk_preserved groups w (gSimBody actTick obsAll groupOrd withinOrd pos w i)
    (fun nid nd₀ h₀ => by
      obtain ⟨nd, h, hk, _, ho⟩ :=
        gSimBody_getNode_fields actTick obsAll groupOrd withinOrd pos w i nid nd₀ h₀
      exact ⟨nd, h, hk, ho⟩)

theorem NodeLayoutOk_gSimFoldl (groups : List GroupSpec) (actTick : Nat → Nat)
    (obsAll : List (List Nat)) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (w : World) (n : Nat) :
    NodeLayoutOk groups w →
    NodeLayoutOk groups (gSimFoldl actTick obsAll groupOrd withinOrd pos w n) :=
  NodeLayoutOk_preserved groups w (gSimFoldl actTick obsAll groupOrd withinOrd pos w n)
    (fun nid nd₀ h₀ => by
      obtain ⟨nd, h, hk, _, ho⟩ :=
        gSimFoldl_getNode_fields actTick obsAll groupOrd withinOrd pos w n nid nd₀ h₀
      exact ⟨nd, h, hk, ho⟩)

/-! ## `StageMemAt` preservation -/

private theorem logOutput_stageMemAt (groups : List GroupSpec)
    (actTick : Nat → Nat) (w : World) (msg : String) (t : Nat) :
    StageMemAt groups actTick w t → StageMemAt groups actTick (w.logOutput msg) t := by
  intro h_inv ev h_ev
  have h_ev' : ev ∈ w.events := by rwa [World.logOutput_events] at h_ev
  exact h_inv ev h_ev'

/-- Activating group `gi` at tick `t` appends exactly the stage-0 events of
    that group's chains, which satisfy the tick-`t` invariant. -/
private theorem activateGroup_stageMemAt (groups : List GroupSpec)
    (actTick : Nat → Nat) (w : World) (observers : List Nat) (gi t : Nat)
    (h_inv : StageMemAt groups actTick w t)
    (h_tick : w.tick = t)
    (h_gi : gi < groups.length)
    (h_act : actTick gi = t)
    (h_obs : ∀ oid ∈ observers, ∃ ci, ci < (groupAt groups gi).length ∧
        oid = chainBaseId groups gi ci + 1) :
    StageMemAt groups actTick (activateGroup w observers) t := by
  intro ev h_ev
  rw [activateGroup_events_map] at h_ev
  simp only [List.mem_append, List.mem_map] at h_ev
  rcases h_ev with h_ev | h_ev
  · exact h_inv ev h_ev
  · rcases h_ev with ⟨nid, h_mem, h_eq⟩
    obtain ⟨ci, h_ci, h_id⟩ := h_obs nid h_mem
    refine ⟨gi, ci, 0, h_gi, h_ci, by omega, ?_, ?_, ?_⟩
    · rw [← h_eq]
      dsimp [stageEvent, stageTarget, stagePri]
      simp [h_tick, h_act, stageCumDelay_zero, h_id]
    · dsimp
      rw [h_act]
      omega
    · dsimp [stageTarget]
      rw [stageCumDelay_zero, h_act]
      omega

/-- One pop-and-fire step preserves the tick-`t` invariant: old events stay,
    and the fired stage event's successor (if any) satisfies it too. -/
private theorem step_stageMemAt (groups : List GroupSpec) (actTick : Nat → Nat)
    (w w' : World) (t : Nat) (h_step : w.step = some w')
    (h_tick : w.tick ≤ t)
    (h_inv : StageMemAt groups actTick w t)
    (h_layout : NodeLayoutOk groups w) :
    StageMemAt groups actTick w' t := by
  cases h_pop : w.popNextEvent with
  | none => simp [World.step, h_pop] at h_step
  | some p =>
    rcases p with ⟨ev₀, w_pop⟩
    have h_tick_w' : w'.tick = w.tick := World.step_tick w w' h_step
    simp only [World.step, h_pop] at h_step
    obtain ⟨idx, h_idx, h_erase, h_tick₀, h_mem₀, h_idx_eq⟩ :=
      World.popNextEvent_eraseIdx w ev₀ w_pop h_pop
    obtain ⟨gi, ci, j, h_gi, h_ci, h_j, h_ev₀, h_prev, h_due⟩ := h_inv ev₀ h_mem₀
    set c := chainAt groups gi ci
    set m := c.middleDelays.length
    have h_m_def : m = (chainAt groups gi ci).middleDelays.length := by dsimp [m, c]
    have h_target : stageTarget actTick groups gi ci j = w.tick := by
      rw [h_ev₀] at h_tick₀
      dsimp [stageEvent] at h_tick₀
      exact h_tick₀
    have h_tick_le : t ≤ w.tick := by rwa [h_target] at h_due
    have h_tick_eq : w.tick = t := by omega
    have h_nodeId : ev₀.nodeId = chainBaseId groups gi ci + 1 + j := by
      rw [h_ev₀]
      dsimp [stageEvent]
    have h_gn_pop : ∀ nid, w_pop.getNode nid = w.getNode nid := by
      intro nid
      dsimp [World.getNode]
      rw [World.popNextEvent_nodes w ev₀ w_pop h_pop]
    have h_pop_tick : w_pop.tick = w.tick := World.popNextEvent_tick w ev₀ w_pop h_pop
    injection h_step with h_w'_eq
    have h_old_mem : ∀ ev' ∈ w_pop.events,
        ∃ gi' ci' j', gi' < groups.length ∧ ci' < (groupAt groups gi').length ∧
          j' ≤ (chainAt groups gi' ci').middleDelays.length + 1 ∧
          ev' = stageEvent actTick groups gi' ci' j' ∧
          (if j' = 0 then actTick gi' else
            stageTarget actTick groups gi' ci' (j' - 1)) < t + 1 ∧
          t ≤ stageTarget actTick groups gi' ci' j' := by
      intro ev' h_ev'
      rw [h_erase] at h_ev'
      exact h_inv ev' (List.mem_of_mem_eraseIdx h_ev')
    intro ev h_ev
    rw [← h_w'_eq, h_nodeId] at h_ev
    cases j with
    | zero =>
      obtain ⟨nd_obs, h_obs_node, h_obs_kind, h_obs_out⟩ := h_layout.1 gi ci h_gi h_ci
      have h_obs_node' : w_pop.getNode (chainBaseId groups gi ci + 1) = some nd_obs := by
        rw [h_gn_pop]; exact h_obs_node
      by_cases h_m0 : m = 0
      · -- no middle repeaters: the observer's output is the last repeater
        have h_len0 : (chainAt groups gi ci).middleDelays.length = 0 := by
          rw [← h_m_def]; exact h_m0
        obtain ⟨nd_nxt, h_nxt_node, h_nxt_kind, h_nxt_out⟩ :=
          h_layout.2.2.1 gi ci h_gi h_ci
        have h_idx : chainBaseId groups gi ci + 2 =
            chainBaseId groups gi ci + (chainAt groups gi ci).middleDelays.length + 2 := by
          omega
        have h_nxt_node' : w_pop.getNode (chainBaseId groups gi ci + 2) = some nd_nxt := by
          rw [h_gn_pop, h_idx]
          exact h_nxt_node
        have h_spawn := World.onScheduledTick_observer_spawns w_pop
          (chainBaseId groups gi ci + 1) (chainBaseId groups gi ci + 2) nd_obs nd_nxt
          c.lastDelay (-1) h_obs_node' h_obs_kind h_obs_out h_nxt_node' h_nxt_kind
        rw [h_spawn] at h_ev
        rw [List.mem_append] at h_ev
        rcases h_ev with h_ev | h_ev
        · exact h_old_mem ev h_ev
        · simp only [List.mem_singleton] at h_ev
          subst h_ev
          dsimp [c, m]
          have h_cum1 : stageCumDelay (chainAt groups gi ci) 1 =
              ((chainAt groups gi ci).lastDelay : Nat) := by
            dsimp [stageCumDelay]
            simp [List.eq_nil_of_length_eq_zero h_len0]
          have h_wtick : w.tick = actTick gi + 2 := by
            rw [← h_target]
            dsimp [stageTarget]
            rw [stageCumDelay_zero]
          refine ⟨gi, ci, 1, h_gi, h_ci, by omega, ?_, ?_, ?_⟩
          · dsimp [stageEvent, stageTarget, stagePri]
            simp [h_pop_tick, h_wtick, h_cum1, h_len0]
          · dsimp
            rw [h_target, h_tick_eq]
            omega
          · dsimp [stageTarget]
            rw [h_cum1]
            omega
      · -- at least one middle repeater: the observer's output is the first one
        have h_0lt : 0 < (chainAt groups gi ci).middleDelays.length := by omega
        obtain ⟨nd_nxt, h_nxt_node, h_nxt_kind, h_nxt_out⟩ :=
          h_layout.2.1 gi ci 0 h_gi h_ci h_0lt
        have h_nxt_node' : w_pop.getNode (chainBaseId groups gi ci + 2) = some nd_nxt := by
          rw [h_gn_pop]; exact h_nxt_node
        have h_spawn := World.onScheduledTick_observer_spawns w_pop
          (chainBaseId groups gi ci + 1) (chainBaseId groups gi ci + 2) nd_obs nd_nxt
          ((chainAt groups gi ci).middleDelays[0]'h_0lt) (-3) h_obs_node'
          h_obs_kind h_obs_out h_nxt_node' h_nxt_kind
        rw [h_spawn] at h_ev
        rw [List.mem_append] at h_ev
        rcases h_ev with h_ev | h_ev
        · exact h_old_mem ev h_ev
        · simp only [List.mem_singleton] at h_ev
          subst h_ev
          have h_cum1 : stageCumDelay (chainAt groups gi ci) 1 =
              ((chainAt groups gi ci).middleDelays[0]'h_0lt : Nat) := by
            rw [stageCumDelay_succ_middle (chainAt groups gi ci) 0 h_0lt,
              stageCumDelay_zero]
            omega
          have h_wtick : w.tick = actTick gi + 2 := by
            rw [← h_target]
            dsimp [stageTarget]
            rw [stageCumDelay_zero]
          have h_st1 : stageTarget actTick groups gi ci 1 =
              w.tick + ((chainAt groups gi ci).middleDelays[0]'h_0lt : Nat) := by
            dsimp [stageTarget]
            rw [h_cum1]
            omega
          have h_pri : stagePri groups gi ci 1 = (-3 : Int) := by
            dsimp [stagePri]
            split_ifs <;> omega
          refine ⟨gi, ci, 1, h_gi, h_ci, by omega, ?_, ?_, ?_⟩
          · dsimp [stageEvent]
            simp [h_pop_tick, h_st1, h_pri]
          · dsimp
            rw [h_target, h_tick_eq]
            omega
          · dsimp [stageTarget]
            rw [h_cum1]
            omega
    | succ j' =>
      by_cases h_jm : j' = m
      · -- stage j' + 1 = m + 1: the last repeater fires, logs, spawns nothing
        obtain ⟨nd_rep, h_rep_node, h_rep_kind, h_rep_out⟩ :=
          h_layout.2.2.1 gi ci h_gi h_ci
        obtain ⟨nd_out, h_out_node, h_out_kind, h_out_out⟩ :=
          h_layout.2.2.2 gi ci h_gi h_ci
        have h_idx : chainBaseId groups gi ci + 1 + (j' + 1) =
            chainBaseId groups gi ci + (chainAt groups gi ci).middleDelays.length + 2 := by
          omega
        have h_rep_node' : w_pop.getNode (chainBaseId groups gi ci + 1 + (j' + 1)) =
            some nd_rep := by
          rw [h_gn_pop, h_idx]
          exact h_rep_node
        have h_out_node' : w_pop.getNode
            (chainBaseId groups gi ci + (chainAt groups gi ci).middleDelays.length + 3) =
            some nd_out := by
          rw [h_gn_pop]
          exact h_out_node
        obtain ⟨v, h_log, h_events⟩ := World.onScheduledTick_lastRep_logs w_pop
          (chainBaseId groups gi ci + 1 + (j' + 1))
          (chainBaseId groups gi ci + (chainAt groups gi ci).middleDelays.length + 3)
          nd_rep nd_out c.lastDelay (chainName gi ci) h_rep_node' h_rep_kind h_rep_out
          h_out_node' h_out_kind
        rw [h_events] at h_ev
        exact h_old_mem ev h_ev
      · -- middle repeater j' fires: spawns the next stage event
        have h_j_lt : j' < m := by omega
        have h_j_lt' : j' < (chainAt groups gi ci).middleDelays.length := by omega
        obtain ⟨nd_rep, h_rep_node, h_rep_kind, h_rep_out⟩ :=
          h_layout.2.1 gi ci j' h_gi h_ci h_j_lt'
        have h_idx : chainBaseId groups gi ci + 1 + (j' + 1) =
            chainBaseId groups gi ci + 2 + j' := by omega
        have h_rep_node' : w_pop.getNode (chainBaseId groups gi ci + 1 + (j' + 1)) =
            some nd_rep := by
          rw [h_gn_pop, h_idx]
          exact h_rep_node
        have h_stprev : stageTarget actTick groups gi ci (j' + 1) = w.tick := h_target
        by_cases h_next : j' + 1 < m
        · -- next node is middle repeater j'+1
          have h_next_lt : j' + 1 < (chainAt groups gi ci).middleDelays.length := by omega
          obtain ⟨nd_nxt, h_nxt_node, h_nxt_kind, h_nxt_out⟩ :=
            h_layout.2.1 gi ci (j' + 1) h_gi h_ci h_next_lt
          have h_idx_nxt : chainBaseId groups gi ci + 3 + j' =
              chainBaseId groups gi ci + 2 + (j' + 1) := by omega
          have h_nxt_node' : w_pop.getNode (chainBaseId groups gi ci + 3 + j') =
              some nd_nxt := by
            rw [h_gn_pop, h_idx_nxt]
            exact h_nxt_node
          have h_spawn := World.onScheduledTick_repeater_spawns w_pop
            (chainBaseId groups gi ci + 1 + (j' + 1)) (chainBaseId groups gi ci + 3 + j')
            nd_rep nd_nxt ((chainAt groups gi ci).middleDelays[j']'h_j_lt')
            (-3) (-3) ((chainAt groups gi ci).middleDelays[j' + 1]'h_next_lt)
            h_rep_node' h_rep_kind h_rep_out (by omega) h_nxt_node' h_nxt_kind
          rw [h_spawn] at h_ev
          rw [List.mem_append] at h_ev
          rcases h_ev with h_ev | h_ev
          · exact h_old_mem ev h_ev
          · simp only [List.mem_singleton] at h_ev
            subst h_ev
            have h_cum : stageCumDelay (chainAt groups gi ci) (j' + 2) =
                stageCumDelay (chainAt groups gi ci) (j' + 1) +
                  ((chainAt groups gi ci).middleDelays[j' + 1]'h_next_lt : Nat) :=
              stageCumDelay_succ_middle (chainAt groups gi ci) (j' + 1) h_next_lt
            have h_st2 : stageTarget actTick groups gi ci (j' + 2) =
                w.tick +
                  ((chainAt groups gi ci).middleDelays[j' + 1]'h_next_lt : Nat) := by
              dsimp [stageTarget] at h_stprev ⊢
              rw [h_cum]
              omega
            have h_pri : stagePri groups gi ci (j' + 2) = (-3 : Int) := by
              dsimp [stagePri]
              split_ifs <;> omega
            refine ⟨gi, ci, j' + 2, h_gi, h_ci, by omega, ?_, ?_, ?_⟩
            · dsimp [stageEvent]
              simp [h_pop_tick, h_st2, h_pri]
              omega
            · dsimp
              rw [h_stprev, h_tick_eq]
              omega
            · rw [h_st2, h_tick_eq]
              omega
        · -- next node is the last repeater
          have h_jp1_eq_m : j' + 1 = m := by omega
          obtain ⟨nd_nxt, h_nxt_node, h_nxt_kind, h_nxt_out⟩ :=
            h_layout.2.2.1 gi ci h_gi h_ci
          have h_idx_nxt : chainBaseId groups gi ci + 3 + j' =
              chainBaseId groups gi ci + (chainAt groups gi ci).middleDelays.length + 2 := by
            omega
          have h_nxt_node' : w_pop.getNode (chainBaseId groups gi ci + 3 + j') =
              some nd_nxt := by
            rw [h_gn_pop, h_idx_nxt]
            exact h_nxt_node
          have h_spawn := World.onScheduledTick_repeater_spawns w_pop
            (chainBaseId groups gi ci + 1 + (j' + 1)) (chainBaseId groups gi ci + 3 + j')
            nd_rep nd_nxt ((chainAt groups gi ci).middleDelays[j']'h_j_lt')
            (-3) (-1) c.lastDelay h_rep_node' h_rep_kind h_rep_out (by omega)
            h_nxt_node' h_nxt_kind
          rw [h_spawn] at h_ev
          rw [List.mem_append] at h_ev
          rcases h_ev with h_ev | h_ev
          · exact h_old_mem ev h_ev
          · simp only [List.mem_singleton] at h_ev
            subst h_ev
            dsimp [c, m]
            have h_stm : stageTarget actTick groups gi ci m = w.tick := by
              rw [← h_jp1_eq_m]
              exact h_stprev
            have h_st2 : stageTarget actTick groups gi ci (m + 1) =
                w.tick + ((chainAt groups gi ci).lastDelay : Nat) := by
              dsimp [stageTarget, c, m] at h_stm ⊢
              rw [stageCumDelay_succ_last (chainAt groups gi ci)]
              omega
            have h_pri : stagePri groups gi ci (m + 1) = (-1 : Int) := by
              dsimp [stagePri]
              split_ifs <;> omega
            refine ⟨gi, ci, m + 1, h_gi, h_ci, by omega, ?_, ?_, ?_⟩
            · dsimp [stageEvent]
              simp [h_pop_tick, h_st2, h_pri]
              omega
            · dsimp
              rw [h_stm, h_tick_eq]
              omega
            · rw [h_st2]
              omega

/-- `processNEvents` preserves the tick-`t` invariant. -/
private theorem processNEvents_stageMemAt (groups : List GroupSpec)
    (actTick : Nat → Nat) (w : World) (n t : Nat) (h_tick : w.tick ≤ t)
    (h_inv : StageMemAt groups actTick w t)
    (h_layout : NodeLayoutOk groups w) :
    StageMemAt groups actTick (processNEvents w n) t := by
  induction n generalizing w with
  | zero => simpa [processNEvents] using h_inv
  | succ n' ih =>
    simp only [processNEvents]
    cases h_step : w.step with
    | none => simpa [h_step] using h_inv
    | some w' =>
      apply ih
      · rw [World.step_tick w w' h_step]; exact h_tick
      · exact step_stageMemAt groups actTick w w' t h_step h_tick h_inv h_layout
      · exact NodeLayoutOk_step groups w w' h_step h_layout

/-- After `stepUntilNextTick`, every remaining event satisfies
    `stageWindow (t + 1)`. -/
private theorem stepUntilNextTick_stageWindow (groups : List GroupSpec)
    (actTick : Nat → Nat) (w : World) (t : Nat)
    (h_tick : w.tick = t)
    (h_inv : StageMemAt groups actTick w t)
    (h_layout : NodeLayoutOk groups w) :
    ∀ ev ∈ w.stepUntilNextTick.events, ∃ gi ci j,
      gi < groups.length ∧ ci < (groupAt groups gi).length ∧
      j ≤ (chainAt groups gi ci).middleDelays.length + 1 ∧
      ev = stageEvent actTick groups gi ci j ∧
      stageWindow actTick groups gi ci j (t + 1) := by
  revert h_tick h_inv h_layout
  induction w using World.stepUntilNextTick.induct with
  | case1 x h_step =>
    intro h_tick h_inv h_layout
    rw [stepUntilNextTick_of_step_none x h_step]
    intro ev h_ev
    obtain ⟨gi, ci, j, h_gi, h_ci, h_j, h_ev₀, h_prev, h_due⟩ := h_inv ev h_ev
    have h_no_due : ∀ ev' ∈ x.events, ev'.targetTick ≠ x.tick := by
      dsimp [World.step] at h_step
      cases h_pop : x.popNextEvent with
      | none => exact popNextEvent_none_no_events x h_pop
      | some p => simp [h_pop] at h_step
    have h_ne : stageTarget actTick groups gi ci j ≠ x.tick := by
      have := h_no_due ev h_ev
      rw [h_ev₀] at this
      dsimp [stageEvent] at this
      exact this
    refine ⟨gi, ci, j, h_gi, h_ci, h_j, h_ev₀, ?_⟩
    dsimp [stageWindow]
    rw [h_tick] at h_ne
    exact ⟨h_prev, by omega⟩
  | case2 x x' h_step ih =>
    intro h_tick h_inv h_layout
    have h_sunt : x.stepUntilNextTick = x'.stepUntilNextTick := by
      rw [World.stepUntilNextTick, h_step]
    rw [h_sunt]
    apply ih
    · rw [World.step_tick x x' h_step]; exact h_tick
    · exact step_stageMemAt groups actTick x x' t h_step (le_of_eq h_tick) h_inv
        h_layout
    · exact NodeLayoutOk_step groups x x' h_step h_layout

/-- The burst phase preserves the tick-`t` invariant: processed old events
    survive with their bounds, and every activated group's stage-0 events
    satisfy the bounds. -/
private theorem gSimBurst_stageMemAt (groups : List GroupSpec) (actTick : Nat → Nat)
    (t : Nat) (withinOrd : Nat → List Nat) (pos : Nat → List Nat) (w : World)
    (pairs : List (Nat × Nat))
    (h_tick : w.tick = t)
    (h_inv : StageMemAt groups actTick w t)
    (h_layout : NodeLayoutOk groups w)
    (h_active : ∀ gi k, (gi, k) ∈ pairs → gi < groups.length ∧ actTick gi = t) :
    StageMemAt groups actTick (gSimBurst t (buildGroups groups).2 withinOrd pos w pairs)
      t := by
  induction pairs generalizing w with
  | nil => simpa [gSimBurst] using h_inv
  | cons p ps ih =>
    simp only [gSimBurst, List.foldl_cons]
    rcases p with ⟨gi, k⟩
    simp only
    have ⟨h_gi, h_act_gi⟩ := h_active gi k (by simp)
    set m := (pos t)[k]?.getD 0
    set obsAll : List (List Nat) := (buildGroups groups).2
    set ordered := (withinOrd gi).foldl (fun acc ci =>
      match (obsAll[gi]?.getD [])[ci]? with
      | some oid => acc ++ [oid]
      | none => acc) []
    have h_gi_obs : gi < obsAll.length := by
      dsimp [obsAll]; rw [buildGroups_snd_length]; exact h_gi
    have h_obs_char : ∀ oid ∈ ordered, ∃ ci, ci < (groupAt groups gi).length ∧
        oid = chainBaseId groups gi ci + 1 := by
      intro oid h_oid
      obtain ⟨ci, h_ci_some⟩ := mem_foldl_observers obsAll withinOrd gi oid h_oid
      dsimp [obsAtIdx] at h_ci_some
      have h_ci_lt' : ci < (obsAll[gi]?.getD []).length := by
        by_contra h_ge
        have h_none : (obsAll[gi]?.getD [])[ci]? = none :=
          List.getElem?_eq_none (Nat.le_of_not_lt h_ge)
        exact Option.some_ne_none oid (h_ci_some.trans h_none)
      have h_ci_lt : ci < (groupAt groups gi).length := by
        rwa [← buildGroups_obs_length groups gi]
      have h_official := buildGroups_snd_getElem_getElem? groups gi ci h_gi h_ci_lt
      rw [← h_ci_some] at h_official
      injection h_official with h_oid_eq
      exact ⟨ci, h_ci_lt, h_oid_eq⟩
    have h_tick_proc : (processNEvents w m).tick = t := by
      rw [processNEvents_tick, h_tick]
    have h_inv_proc : StageMemAt groups actTick (processNEvents w m) t :=
      processNEvents_stageMemAt groups actTick w m t (by omega) h_inv h_layout
    have h_inv_act : StageMemAt groups actTick
        (activateGroup (processNEvents w m) ordered) t :=
      activateGroup_stageMemAt groups actTick (processNEvents w m) ordered gi t
        h_inv_proc h_tick_proc h_gi h_act_gi h_obs_char
    apply ih
    · rw [activateGroup_tick, h_tick_proc]
    · exact h_inv_act
    · exact NodeLayoutOk_activateGroup groups (processNEvents w m) ordered
        (NodeLayoutOk_processNEvents groups w m h_layout)
    · intro gi' k' h_mem
      exact h_active gi' k' (by simp [h_mem])

/-- One full `gSimBody` tick: every event in the next tick-start queue
    satisfies `stageWindow (t + 1)`. -/
private theorem gSimBody_stageWindow (groups : List GroupSpec) (actTick : Nat → Nat)
    (groupOrd : List Nat) (withinOrd pos : Nat → List Nat) (w : World) (i t : Nat)
    (h_tick : w.tick = t)
    (h_inv : StageMemAt groups actTick w t)
    (h_layout : NodeLayoutOk groups w) :
    ∀ ev ∈ (gSimBody actTick (buildGroups groups).2 groupOrd withinOrd pos w i).events,
      ∃ gi ci j, gi < groups.length ∧ ci < (groupAt groups gi).length ∧
        j ≤ (chainAt groups gi ci).middleDelays.length + 1 ∧
        ev = stageEvent actTick groups gi ci j ∧
        stageWindow actTick groups gi ci j (t + 1) := by
  dsimp [gSimBody]
  split_ifs with h_active
  · exact stepUntilNextTick_stageWindow groups actTick (w.logOutput s!"tick {w.tick}")
      t (by rw [World.logOutput_tick]; exact h_tick)
      (logOutput_stageMemAt groups actTick w s!"tick {w.tick}" t h_inv)
      (NodeLayoutOk_logOutput groups w s!"tick {w.tick}" h_layout)
  · set W₁ := w.logOutput s!"tick {w.tick}"
    set active := groupOrd.filter (fun gi =>
      decide (gi < (buildGroups groups).2.length) && (actTick gi == w.tick))
    have h_active_char : ∀ gi k, (gi, k) ∈ active.zipIdx →
        gi < groups.length ∧ actTick gi = w.tick := by
      intro gi k h_mem
      have h_zip := List.mem_zipIdx h_mem
      obtain ⟨_, h_k_lt, h_gi_eq⟩ := h_zip
      have h_k_lt' : k < active.length := by simpa using h_k_lt
      have h_gi_mem : gi ∈ active := by
        have h_gi_eq' : gi = active[k] := by simpa using h_gi_eq
        rw [h_gi_eq']
        exact List.getElem_mem h_k_lt'
      dsimp [active] at h_gi_mem
      rw [List.mem_filter] at h_gi_mem
      obtain ⟨_, h_cond⟩ := h_gi_mem
      rw [Bool.and_eq_true] at h_cond
      obtain ⟨h_dec, h_beq⟩ := h_cond
      have h_gi_lt : gi < (buildGroups groups).2.length := of_decide_eq_true h_dec
      have h_act_eq : actTick gi = w.tick := by simpa [Nat.beq_eq] using h_beq
      exact ⟨by rwa [buildGroups_snd_length] at h_gi_lt, h_act_eq⟩
    have h_inv_log : StageMemAt groups actTick W₁ w.tick :=
      h_tick.symm ▸ logOutput_stageMemAt groups actTick w s!"tick {w.tick}" t h_inv
    have h_layout_log : NodeLayoutOk groups W₁ :=
      NodeLayoutOk_logOutput groups w s!"tick {w.tick}" h_layout
    have h_inv_burst : StageMemAt groups actTick
        (gSimBurst w.tick (buildGroups groups).2 withinOrd pos W₁ (active.zipIdx))
        w.tick :=
      gSimBurst_stageMemAt groups actTick w.tick withinOrd pos W₁ (active.zipIdx) rfl
        h_inv_log h_layout_log h_active_char
    have h_layout_burst : NodeLayoutOk groups
        (gSimBurst w.tick (buildGroups groups).2 withinOrd pos W₁ (active.zipIdx)) :=
      NodeLayoutOk_gSimBurst groups w.tick (buildGroups groups).2 withinOrd pos W₁
        (active.zipIdx) h_layout_log
    have h_win := stepUntilNextTick_stageWindow groups actTick
      (gSimBurst w.tick (buildGroups groups).2 withinOrd pos W₁ (active.zipIdx))
      w.tick
      (gSimBurst_tick w.tick (buildGroups groups).2 withinOrd pos W₁ (active.zipIdx))
      h_inv_burst h_layout_burst
    intro ev h_ev
    obtain ⟨gi, ci, j, h_gi, h_ci, h_j, h_ev₀, h_win'⟩ := h_win ev h_ev
    exact ⟨gi, ci, j, h_gi, h_ci, h_j, h_ev₀, h_tick ▸ h_win'⟩

/-! ## The characterization at every tick-start -/

/-- At the start of tick `t`, every queued event is the stage event of a valid
    chain satisfying `stageWindow ... t`. -/
theorem gSimWorld_events_stageWindow (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (t : Nat) :
    ∀ ev ∈ (gSimWorld groups actTick groupOrd withinOrd pos t).events,
      ∃ gi ci j, gi < groups.length ∧ ci < (groupAt groups gi).length ∧
        j ≤ (chainAt groups gi ci).middleDelays.length + 1 ∧
        ev = stageEvent actTick groups gi ci j ∧
        stageWindow actTick groups gi ci j t := by
  dsimp [gSimWorld]
  induction t with
  | zero =>
    dsimp [gSimFoldl]
    intro ev h_ev
    rw [buildGroups_no_events] at h_ev
    cases h_ev
  | succ t ih =>
    simp only [gSimFoldl, List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil]
    intro ev h_ev
    set W : World := List.foldl
      (gSimBody actTick (buildGroups groups).2 groupOrd withinOrd pos)
      (buildGroups groups).1 (List.range t)
    have h_tick_W : W.tick = t := by
      change (gSimFoldl actTick (buildGroups groups).2 groupOrd withinOrd pos
        (buildGroups groups).1 t).tick = t
      rw [gSimFoldl_tick, buildGroups_tick]
      omega
    have h_mem_at : StageMemAt groups actTick W t := by
      intro ev' h_ev'
      obtain ⟨gi, ci, j, h_gi, h_ci, h_j, h_ev₀, h_win⟩ := ih ev' h_ev'
      refine ⟨gi, ci, j, h_gi, h_ci, h_j, h_ev₀, by
        dsimp [stageWindow] at h_win; omega, h_win.2⟩
    have h_layout_W : NodeLayoutOk groups W := by
      change NodeLayoutOk groups (gSimFoldl actTick (buildGroups groups).2 groupOrd
        withinOrd pos (buildGroups groups).1 t)
      exact NodeLayoutOk_gSimFoldl groups actTick (buildGroups groups).2 groupOrd
        withinOrd pos (buildGroups groups).1 t (NodeLayoutOk_buildGroups groups)
    exact gSimBody_stageWindow groups actTick groupOrd withinOrd pos W t t h_tick_W
      h_mem_at h_layout_W ev h_ev
