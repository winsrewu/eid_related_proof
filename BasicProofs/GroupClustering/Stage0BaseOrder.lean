import BasicProofs.GroupClustering.OrderPreservationPremises

open BasicRedstoneSim List

/-! # Group clustering — stage-0 base order at the activation tick

SameSpecBeforeness and QSideOrder keep the base-order premise `h_base` open: at the pop
tick of stage 0, the two stage-0 events of two same-spec chains must
already stand in the burst order in the queue. This file discharges that
premise.

The stage-0 events are the observer events. `activateGroup` appends them
at the end of the queue, one event per observer, in the order of the
ordered observer list. `gSimBurst` fires the active groups in burst
order. Each group appends its observer batch after all earlier events.
A batch targets tick `actTick + 2`, so the burst tick does not pop it.

Contents:

* `activateGroup_stage0_order` — one `activateGroup` call orders its
  stage-0 events in `withinOrd` order;
* `gSimBurst_stage0_cross_group_order` — one burst phase orders the
  stage-0 events of two groups in burst order;
* `sameSpec_stage_evBefore_base` — the `h_base` premise of SameSpecBeforeness: at
  the stage-0 pop tick, the two stage-0 events of two same-spec chains
  stand in burst order in the tick-start queue.
-/

/-! ## List helpers -/

/-- A list that contains a member splits at that member. -/
theorem split_at_mem {α : Type} (l : List α) (a : α)
    (h : a ∈ l) : ∃ pre post, l = pre ++ a :: post := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.mem_cons] at h
    cases h with
    | inl h_eq =>
      subst h_eq
      exact ⟨[], xs, rfl⟩
    | inr h_mem =>
      obtain ⟨pre, post, h_split⟩ := ih h_mem
      exact ⟨x :: pre, post, by rw [h_split]; rfl⟩

/-- A foldl that appends one element per kept index preserves
    membership of the accumulator. -/
private theorem foldl_obs_append_mem (obs : List Nat)
    (post : List Nat) (acc : List Nat) (x : Nat) (h : x ∈ acc) :
    x ∈ post.foldl (fun acc ci =>
        match obs[ci]? with
        | some oid => acc ++ [oid]
        | none => acc) acc := by
  induction post generalizing acc with
  | nil => exact h
  | cons ci cs ih =>
    simp only [foldl_cons]
    cases h_val : obs[ci]? with
    | none =>
      simp only
      exact ih acc h
    | some oid =>
      simp only
      exact ih (acc ++ [oid]) (List.mem_append_left _ h)

/-- The observer foldl appends at each step; the start accumulator
    factors out as a prefix. -/
private theorem foldl_obs_append_prefix (obs : List Nat) (l : List Nat)
    (acc : List Nat) :
    l.foldl (fun acc ci =>
        match obs[ci]? with
        | some oid => acc ++ [oid]
        | none => acc) acc =
    acc ++ l.foldl (fun acc ci =>
        match obs[ci]? with
        | some oid => acc ++ [oid]
        | none => acc) [] := by
  induction l generalizing acc with
  | nil => simp
  | cons ci l ih =>
    cases h : obs[ci]? with
    | none =>
      simp only [List.foldl_cons, h]
      exact ih acc
    | some oid =>
      simp only [List.foldl_cons, h, List.nil_append]
      rw [ih (acc ++ [oid]), ih [oid], ← List.append_assoc]

/-- The observer foldl equals a filterMap over the index list. -/
private theorem foldl_obs_eq_filterMap (obs : List Nat) (l : List Nat)
    (acc : List Nat) :
    l.foldl (fun acc ci =>
        match obs[ci]? with
        | some oid => acc ++ [oid]
        | none => acc) acc =
    acc ++ l.filterMap fun ci => obs[ci]? := by
  induction l generalizing acc with
  | nil => simp
  | cons ci l ih =>
    cases h : obs[ci]? with
    | none =>
      simp only [List.foldl_cons, List.filterMap, h]
      exact ih acc
    | some oid =>
      simp only [List.foldl_cons, List.filterMap, h]
      rw [ih (acc ++ [oid])]
      simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- The ordered observer list splits at two chains that appear in
    order in the index list and have valid lookups. -/
private theorem ordered_obs_split (obs : List Nat)
    (pre mid post : List Nat) (ci₁ ci₂ oid₁ oid₂ : Nat)
    (h₁ : obs[ci₁]? = some oid₁) (h₂ : obs[ci₂]? = some oid₂) :
    ∃ P M Q,
      (pre ++ ci₁ :: mid ++ ci₂ :: post).foldl
          (fun acc ci => match obs[ci]? with
            | some oid => acc ++ [oid]
            | none => acc) [] =
        P ++ oid₁ :: M ++ oid₂ :: Q := by
  refine ⟨pre.filterMap (fun ci => obs[ci]?),
    mid.filterMap (fun ci => obs[ci]?),
    post.filterMap (fun ci => obs[ci]?), ?_⟩
  rw [foldl_obs_eq_filterMap obs (pre ++ ci₁ :: mid ++ ci₂ :: post) [],
    List.nil_append]
  simp only [List.filterMap_append, List.filterMap_cons_some h₁,
    List.filterMap_cons_some h₂]

/-- If `ci` appears in `withinOrd gi` and is a valid chain index, then
    the observer id `chainBaseId groups gi ci + 1` is in the ordered
    observer list. -/
theorem obsId_mem_ordered (withinOrd : Nat → List Nat)
    (groups : List GroupSpec) (gi ci : Nat)
    (h_gi : gi < groups.length)
    (h_ci : ci < (groupAt groups gi).length)
    (h_ci_in : ci ∈ withinOrd gi) :
    chainBaseId groups gi ci + 1 ∈
      (withinOrd gi).foldl (fun acc ci' =>
          match (((buildGroups groups).2)[gi]?.getD [])[ci']? with
          | some oid => acc ++ [oid]
          | none => acc) [] := by
  set obsAll := (buildGroups groups).2
  set obs := obsAll[gi]?.getD []
  -- Split withinOrd gi at ci
  obtain ⟨pre, post, h_split⟩ := split_at_mem (withinOrd gi) ci h_ci_in
  rw [h_split]
  -- foldl of (pre ++ ci :: post)
  simp only [foldl_append, foldl_cons]
  -- The lookup for ci succeeds
  have h_lookup : obs[ci]? = some (chainBaseId groups gi ci + 1) :=
    obsId_eq groups gi ci h_gi h_ci
  rw [h_lookup]
  -- After ci, the accumulator contains the observer id
  have h_base : chainBaseId groups gi ci + 1 ∈
      pre.foldl (fun acc ci' =>
          match obs[ci']? with
          | some oid => acc ++ [oid]
          | none => acc) [] ++
        [chainBaseId groups gi ci + 1] := by
    apply List.mem_append_right
    simp
  -- The post foldl preserves membership
  exact foldl_obs_append_mem obs post _ _ h_base

/-! ## Stage-0 event membership through activateGroup and bursts -/

/-- A stage-0 event is in the appended part of the activateGroup result
    when its observer id is in the ordered list. -/
theorem stageEvent0_mem_activateGroup_append
    (w : World) (ordered : List Nat) (actTick : Nat → Nat)
    (groups : List GroupSpec) (gi ci : Nat)
    (h_nid : chainBaseId groups gi ci + 1 ∈ ordered)
    (h_tick : w.tick = actTick gi) :
    stageEvent actTick groups gi ci 0 ∈
      ordered.map (fun nid =>
        ({ targetTick := w.tick + 2, priority := 0, nodeId := nid } :
          ScheduledEvent)) := by
  rw [stageEvent_zero_fields]
  apply List.mem_map.mpr
  refine ⟨chainBaseId groups gi ci + 1, h_nid, ?_⟩
  simp [h_tick]

/-- A stage-0 event is in the activateGroup result when its observer id
    is in the ordered list. -/
theorem stageEvent0_mem_activateGroup
    (w : World) (ordered : List Nat) (actTick : Nat → Nat)
    (groups : List GroupSpec) (gi ci : Nat)
    (h_nid : chainBaseId groups gi ci + 1 ∈ ordered)
    (h_tick : w.tick = actTick gi) :
    stageEvent actTick groups gi ci 0 ∈
      (activateGroup w ordered).events := by
  rw [activateGroup_events_map]
  apply List.mem_append_right
  exact stageEvent0_mem_activateGroup_append w ordered actTick groups gi ci
    h_nid h_tick

/-- The stage-0 event of chain `(gi, ci)` is in the burst result when
    the burst contains a step of group `gi` and `ci` is in the
    withinOrd list. The event targets tick `actTick gi + 2`, which is
    strictly after the burst tick, so it survives all later burst
    steps. -/
theorem stageEvent0_mem_burst (t : Nat)
    (withinOrd pos : Nat → List Nat)
    (w : World) (pairs : List (Nat × Nat))
    (gi k : Nat)
    (actTick : Nat → Nat) (groups : List GroupSpec) (ci : Nat)
    (h_tick_w : w.tick = t) (h_tick_act : t = actTick gi)
    (h_gi : gi < groups.length) (h_ci : ci < (groupAt groups gi).length)
    (h_ci_in : ci ∈ withinOrd gi)
    (h_pair : (gi, k) ∈ pairs) :
    stageEvent actTick groups gi ci 0 ∈
      (gSimBurst t (buildGroups groups).2 withinOrd pos w pairs).events := by
  set obsAll := (buildGroups groups).2
  -- Split the burst at the (gi, k) step
  obtain ⟨pre, post, h_split⟩ := split_at_mem pairs (gi, k) h_pair
  -- Rewrite the burst using the split
  have h_burst_eq :
      gSimBurst t obsAll withinOrd pos w pairs =
        gSimBurst t obsAll withinOrd pos
          (gSimBurst t obsAll withinOrd pos w pre)
          ((gi, k) :: post) := by
    rw [h_split]
    simp [gSimBurst, List.foldl_append]
  rw [h_burst_eq]
  -- At the (gi, k) step
  simp only [gSimBurst, List.foldl_cons]
  set W_at := gSimBurst t obsAll withinOrd pos w pre
  set m := (pos t)[k]?.getD 0
  set Wproc := processNEvents W_at m
  -- Build the ordered list
  set ordered := (withinOrd gi).foldl (fun acc ci' =>
      match (obsAll[gi]?.getD [])[ci']? with
      | some oid => acc ++ [oid]
      | none => acc) []
  set Wact := activateGroup Wproc ordered
  set ev := stageEvent actTick groups gi ci 0
  -- tick of W_at is t
  have h_tick_Wat : W_at.tick = t := by
    dsimp [W_at]; rw [gSimBurst_tick, h_tick_w]
  -- tick of Wproc is t
  have h_tick_Wproc : Wproc.tick = t := by
    dsimp [Wproc]; rw [processNEvents_tick, h_tick_Wat]
  -- tick of Wact is t
  have h_tick_Wact : Wact.tick = t := by
    dsimp [Wact]; rw [activateGroup_tick, h_tick_Wproc]
  -- The observer id is in ordered
  have h_nid : chainBaseId groups gi ci + 1 ∈ ordered :=
    obsId_mem_ordered withinOrd groups gi ci h_gi h_ci h_ci_in
  -- ev is in Wact.events
  have h_ev_Wact : ev ∈ Wact.events :=
    stageEvent0_mem_activateGroup Wproc ordered actTick groups gi ci
      h_nid (by rw [h_tick_Wproc, h_tick_act])
  -- ev.targetTick ≠ Wact.tick
  have h_nd : ev.targetTick ≠ Wact.tick := by
    dsimp [ev, stageEvent]
    rw [stageTarget_zero_eq, h_tick_Wact, h_tick_act]
    omega
  -- ev survives the remaining burst
  exact mem_gSimBurst_of_notDue t obsAll withinOrd pos Wact post ev
    h_ev_Wact h_nd

/-! ## Order inside one group activation -/

/-- One `activateGroup` call appends the stage-0 events in the order of
    the withinOrd list. If `ci₁` appears before `ci₂` in `withinOrd gi`
    and both chains are valid, then the stage-0 event of `ci₁` is
    before the stage-0 event of `ci₂` in the output queue. -/
theorem activateGroup_stage0_order (actTick : Nat → Nat)
    (groups : List GroupSpec) (withinOrd : Nat → List Nat) (w : World)
    (gi ci₁ ci₂ : Nat)
    (h_gi : gi < groups.length)
    (h_c₁ : ci₁ < (groupAt groups gi).length)
    (h_c₂ : ci₂ < (groupAt groups gi).length)
    (h_tick : w.tick = actTick gi)
    (h_ord : ∃ pre mid post,
        withinOrd gi = pre ++ ci₁ :: mid ++ ci₂ :: post) :
    evBefore
      ((activateGroup w
          ((withinOrd gi).foldl (fun acc ci =>
              match (((buildGroups groups).2)[gi]?.getD [])[ci]? with
              | some oid => acc ++ [oid]
              | none => acc) [])).events)
      (stageEvent actTick groups gi ci₁ 0)
      (stageEvent actTick groups gi ci₂ 0) := by
  set obs : List Nat := ((buildGroups groups).2)[gi]?.getD []
  set ordered : List Nat := (withinOrd gi).foldl
    (fun acc ci => match obs[ci]? with
      | some oid => acc ++ [oid]
      | none => acc) []
  set oid₁ : Nat := chainBaseId groups gi ci₁ + 1
  set oid₂ : Nat := chainBaseId groups gi ci₂ + 1
  set mkEv : Nat → ScheduledEvent := fun nid =>
    { targetTick := w.tick + 2, priority := 0, nodeId := nid }
  obtain ⟨pre, mid, post, h_within⟩ := h_ord
  have h_obs₁ : obs[ci₁]? = some oid₁ := by
    dsimp [obs, oid₁]
    exact obsId_eq groups gi ci₁ h_gi h_c₁
  have h_obs₂ : obs[ci₂]? = some oid₂ := by
    dsimp [obs, oid₂]
    exact obsId_eq groups gi ci₂ h_gi h_c₂
  -- The ordered list splits at the two observer ids
  obtain ⟨P, M, Q, h_ord_split⟩ :
      ∃ P M Q, ordered = P ++ oid₁ :: M ++ oid₂ :: Q := by
    dsimp [ordered]
    rw [h_within]
    exact ordered_obs_split obs pre mid post ci₁ ci₂ oid₁ oid₂ h_obs₁
      h_obs₂
  -- The two stage-0 events are the images of oid₁ and oid₂
  have h_ev₁ : stageEvent actTick groups gi ci₁ 0 = mkEv oid₁ := by
    rw [stageEvent_zero_fields]
    dsimp [mkEv, oid₁]
    rw [← h_tick]
  have h_ev₂ : stageEvent actTick groups gi ci₂ 0 = mkEv oid₂ := by
    rw [stageEvent_zero_fields]
    dsimp [mkEv, oid₂]
    rw [← h_tick]
  rw [activateGroup_events_map, h_ev₁, h_ev₂]
  change evBefore (w.events ++ ordered.map mkEv) (mkEv oid₁) (mkEv oid₂)
  -- Split the queue at the two events
  have h_events : w.events ++ ordered.map mkEv =
      (w.events ++ P.map mkEv ++ [mkEv oid₁] ++ M.map mkEv) ++
      (mkEv oid₂ :: Q.map mkEv) := by
    rw [h_ord_split]
    simp only [List.map_append, List.map_cons, List.append_assoc,
      List.cons_append, List.nil_append]
  rw [h_events]
  apply evBefore.of_mem_append
  · -- mkEv oid₁ sits in the left part
    apply List.mem_append_left (M.map mkEv)
    apply List.mem_append_right
    exact List.mem_cons.mpr (Or.inl rfl)
  · -- mkEv oid₂ sits in the right part
    exact List.mem_cons.mpr (Or.inl rfl)

/-! ## Cross-group order through one burst phase -/

/-- One burst phase appends the stage-0 events of group `ga` before the
    stage-0 events of group `gb` when the burst steps put `ga` before
    `gb`. Both batches target tick `t + 2`, so no burst step pops
    them. -/
theorem gSimBurst_stage0_cross_group_order (t : Nat)
    (withinOrd pos : Nat → List Nat) (w : World)
    (pairs : List (Nat × Nat)) (actTick : Nat → Nat)
    (groups : List GroupSpec) (ga ca ka gb cb kb : Nat)
    (h_tick_w : w.tick = t)
    (h_act_a : actTick ga = t) (h_act_b : actTick gb = t)
    (h_ga : ga < groups.length) (h_ca : ca < (groupAt groups ga).length)
    (h_gb : gb < groups.length) (h_cb : cb < (groupAt groups gb).length)
    (h_ca_in : ca ∈ withinOrd ga) (h_cb_in : cb ∈ withinOrd gb)
    (h_split : ∃ pre post,
        pairs = pre ++ (gb, kb) :: post ∧ (ga, ka) ∈ pre) :
    evBefore (gSimBurst t (buildGroups groups).2 withinOrd pos w pairs).events
      (stageEvent actTick groups ga ca 0)
      (stageEvent actTick groups gb cb 0) := by
  set obsAll : List (List Nat) := (buildGroups groups).2
  obtain ⟨pre, post, h_pairs, h_a_pre⟩ := h_split
  -- Split the burst at the (gb, kb) step
  have h_burst_split :
      gSimBurst t obsAll withinOrd pos w (pre ++ (gb, kb) :: post) =
        gSimBurst t obsAll withinOrd pos
          (gSimBurst t obsAll withinOrd pos w pre)
          ((gb, kb) :: post) := by
    simp only [gSimBurst, List.foldl_append]
  rw [h_pairs, h_burst_split, gSimBurst, List.foldl_cons]
  set W_pre : World := gSimBurst t obsAll withinOrd pos w pre
  set m : Nat := (pos t)[kb]?.getD 0
  set Wproc : World := processNEvents W_pre m
  set ordered_b : List Nat := (withinOrd gb).foldl (fun acc ci =>
      match (obsAll[gb]?.getD [])[ci]? with
      | some oid => acc ++ [oid]
      | none => acc) []
  set W_b : World := activateGroup Wproc ordered_b
  change evBefore (gSimBurst t obsAll withinOrd pos W_b post).events
    (stageEvent actTick groups ga ca 0)
    (stageEvent actTick groups gb cb 0)
  -- tick bookkeeping
  have h_tick_Wpre : W_pre.tick = t := by
    dsimp [W_pre]
    rw [gSimBurst_tick, h_tick_w]
  have h_tick_Wproc : Wproc.tick = t := by
    dsimp [Wproc]
    rw [processNEvents_tick, h_tick_Wpre]
  have h_tick_Wb : W_b.tick = t := by
    dsimp [W_b]
    rw [activateGroup_tick, h_tick_Wproc]
  -- the stage-0 event of (ga, ca) was appended at the burst step of ga
  have h_a_pre_ev : stageEvent actTick groups ga ca 0 ∈ W_pre.events :=
    stageEvent0_mem_burst t withinOrd pos w pre ga ka actTick groups ca
      h_tick_w h_act_a.symm h_ga h_ca h_ca_in h_a_pre
  -- it survives the processNEvents part of the (gb, kb) step
  have h_nd_a : (stageEvent actTick groups ga ca 0).targetTick ≠
      W_pre.tick := by
    dsimp [stageEvent]
    rw [stageTarget_zero_eq, h_act_a, h_tick_Wpre]
    omega
  have h_a_proc : stageEvent actTick groups ga ca 0 ∈ Wproc.events :=
    mem_processNEvents_of_notDue W_pre m _ h_a_pre_ev h_nd_a
  -- the stage-0 event of (gb, cb) is in the appended observer batch
  have h_nid_b : chainBaseId groups gb cb + 1 ∈ ordered_b :=
    obsId_mem_ordered withinOrd groups gb cb h_gb h_cb h_cb_in
  have h_b_app : stageEvent actTick groups gb cb 0 ∈
      ordered_b.map (fun nid =>
        ({ targetTick := Wproc.tick + 2, priority := 0, nodeId := nid } :
          ScheduledEvent)) := by
    apply stageEvent0_mem_activateGroup_append Wproc ordered_b actTick
      groups gb cb h_nid_b
    rw [h_tick_Wproc]
    exact h_act_b.symm
  -- order at W_b: the ga event sits in the old part, the gb event in
  -- the appended part
  have h_order_Wb : evBefore W_b.events
      (stageEvent actTick groups ga ca 0)
      (stageEvent actTick groups gb cb 0) := by
    dsimp [W_b]
    rw [activateGroup_events_map]
    exact evBefore.of_mem_append h_a_proc h_b_app
  -- the remaining burst steps keep the order: both events target t + 2
  apply evBefore_gSimBurst_of_notDue t obsAll withinOrd pos W_b post
    (stageEvent actTick groups ga ca 0)
    (stageEvent actTick groups gb cb 0)
  · dsimp [stageEvent]
    rw [stageTarget_zero_eq, h_act_a, h_tick_Wb]
    omega
  · dsimp [stageEvent]
    rw [stageTarget_zero_eq, h_act_b, h_tick_Wb]
    omega
  · exact h_order_Wb

/-! ## The h_base premise at the stage-0 pop tick -/

/-- A split of a list gives a split of its zipIdx: the element `b` and
    its index appear after the pair of element `a`. -/
private theorem zipIdx_split_of_split {α : Type} (preA midA postA : List α)
    (a b : α) :
    ∃ preP postP,
      (preA ++ a :: midA ++ b :: postA).zipIdx =
        preP ++ (b, preA.length + (midA.length + 1)) :: postP ∧
      (a, preA.length) ∈ preP := by
  refine ⟨preA.zipIdx ++ (a, preA.length) ::
      midA.zipIdx (preA.length + 1),
    postA.zipIdx (preA.length + (midA.length + (1 + 1))), ?_, ?_⟩
  · have h : (preA ++ a :: midA ++ b :: postA).zipIdx =
        preA.zipIdx ++ (a, preA.length) ::
          (midA.zipIdx (preA.length + 1) ++
            (b, preA.length + (midA.length + 1)) ::
            postA.zipIdx (preA.length + (midA.length + (1 + 1)))) := by
      rw [List.zipIdx_append, List.zipIdx_cons, List.zipIdx_append,
        List.zipIdx_cons]
      simp only [Nat.zero_add, Nat.add_assoc, List.length_append,
        List.length_cons, List.append_assoc, List.cons_append]
    rw [h]
    simp only [List.append_assoc, List.cons_append]
  · apply List.mem_append_right
    exact List.mem_cons.mpr (Or.inl rfl)

/-- The tick-start queue at tick `t + 1` equals the queue after one
    `gSimBody` call at tick `t`. -/
private theorem gSimWorld_succ_events_eq_body (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (t : Nat) :
    (gSimWorld groups actTick groupOrd withinOrd pos (t + 1)).events =
    (gSimBody actTick (buildGroups groups).2 groupOrd withinOrd pos
      (gSimWorld groups actTick groupOrd withinOrd pos t) t).events := by
  dsimp [gSimWorld, gSimFoldl]
  simp only [List.range_succ, List.foldl_append, List.foldl_cons,
    List.foldl_nil]

/-- The h_base premise of SameSpecBeforeness: at the stage-0 pop tick, the stage-0
    events of two same-spec chains stand in burst order in the
    tick-start queue. The activation list at tick `actTick g₁` must
    contain `g₁` before `g₂`. Both chains must appear in their
    withinOrd lists. -/
theorem sameSpec_stage_evBefore_base (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (g₁ c₁ g₂ c₂ : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_c₁_in : c₁ ∈ withinOrd g₁) (h_c₂_in : c₂ ∈ withinOrd g₂)
    (h_act_eq : actTick g₁ = actTick g₂)
    (h_burst : ∃ pre mid post,
        groupOrd.filter (fun gi =>
            decide (gi < (buildGroups groups).2.length) &&
            (actTick gi == actTick g₁)) =
        pre ++ g₁ :: mid ++ g₂ :: post) :
    evBefore
      ((popQueueWorld groups actTick groupOrd withinOrd pos g₁ c₁ 0).events)
      (stageEvent actTick groups g₁ c₁ 0)
      (stageEvent actTick groups g₂ c₂ 0) := by
  set t₀ : Nat := actTick g₁
  obtain ⟨preA, midA, postA, h_active⟩ := h_burst
  set W₀ : World := gSimWorld groups actTick groupOrd withinOrd pos t₀
  have h_tick_W₀ : W₀.tick = t₀ := by
    change (gSimFoldl actTick (buildGroups groups).2 groupOrd withinOrd pos
      (buildGroups groups).1 t₀).tick = t₀
    rw [gSimFoldl_tick, buildGroups_tick]
    omega
  -- g₁ is in the activation list, so the list is not empty
  have h_g₁_active : g₁ ∈ groupOrd.filter (fun gi =>
      decide (gi < (buildGroups groups).2.length) && (actTick gi == t₀)) := by
    have h_eq : groupOrd.filter (fun gi =>
        decide (gi < (buildGroups groups).2.length) && (actTick gi == t₀)) =
      preA ++ g₁ :: midA ++ g₂ :: postA := by
      dsimp [t₀]
      exact h_active
    rw [h_eq]
    simp
  -- the order at the tick-start queue of tick t₀ + 1
  have h_order_succ : evBefore
      ((gSimWorld groups actTick groupOrd withinOrd pos (t₀ + 1)).events)
      (stageEvent actTick groups g₁ c₁ 0)
      (stageEvent actTick groups g₂ c₂ 0) := by
    rw [gSimWorld_succ_events_eq_body groups actTick groupOrd withinOrd pos
      t₀]
    change evBefore
      ((gSimBody actTick (buildGroups groups).2 groupOrd withinOrd pos W₀
          t₀).events)
      (stageEvent actTick groups g₁ c₁ 0)
      (stageEvent actTick groups g₂ c₂ 0)
    dsimp [gSimBody]
    simp only [h_tick_W₀]
    split_ifs with h_empty
    · -- the activation list is empty: contradicts g₁ ∈ active
      exfalso
      have h_act_nil : groupOrd.filter (fun gi =>
          decide (gi < (buildGroups groups).2.length) &&
          (actTick gi == t₀)) = [] := by
        simpa using h_empty
      rw [h_act_nil] at h_g₁_active
      cases h_g₁_active
    · -- the burst branch
      set W₁ : World := W₀.logOutput s!"tick {t₀}"
      set active_b : List Nat := groupOrd.filter (fun gi =>
        decide (gi < (buildGroups groups).2.length) && (actTick gi == t₀))
      set W_B : World := gSimBurst t₀ (buildGroups groups).2 withinOrd pos
        W₁ (active_b.zipIdx)
      have h_tick_W₁ : W₁.tick = t₀ := by
        dsimp [W₁]
        exact h_tick_W₀
      have h_active_eq : active_b = preA ++ g₁ :: midA ++ g₂ :: postA := by
        dsimp [active_b, t₀]
        exact h_active
      -- split active_b.zipIdx at the step of g₂
      obtain ⟨preP, postP, h_zip_split, h_a_preP⟩ :
          ∃ preP postP, active_b.zipIdx =
              preP ++ (g₂, preA.length + (midA.length + 1)) :: postP ∧
            (g₁, preA.length) ∈ preP := by
        obtain ⟨preP, postP, h_z, h_mem⟩ :=
          zipIdx_split_of_split preA midA postA g₁ g₂
        refine ⟨preP, postP, ?_, h_mem⟩
        rw [h_active_eq]
        exact h_z
      -- the cross-group burst order
      have h_order_B : evBefore W_B.events
          (stageEvent actTick groups g₁ c₁ 0)
          (stageEvent actTick groups g₂ c₂ 0) :=
        gSimBurst_stage0_cross_group_order t₀ withinOrd pos W₁
          (active_b.zipIdx) actTick groups g₁ c₁ (preA.length) g₂ c₂
          (preA.length + (midA.length + 1)) h_tick_W₁
          (show actTick g₁ = t₀ from rfl) h_act_eq.symm
          h_g₁ h_c₁ h_g₂ h_c₂ h_c₁_in h_c₂_in
          ⟨preP, postP, h_zip_split, h_a_preP⟩
      -- both events target t₀ + 2, so the drain step keeps the order
      have h_tick_WB : W_B.tick = t₀ := by
        dsimp [W_B]
        rw [gSimBurst_tick, h_tick_W₁]
      have h_ev₁ : stageEvent actTick groups g₁ c₁ 0 ∈ W_B.events :=
        evBefore.mem_left h_order_B
      have h_ev₂ : stageEvent actTick groups g₂ c₂ 0 ∈ W_B.events :=
        evBefore.mem_right h_order_B
      have h_nd₁ : (stageEvent actTick groups g₁ c₁ 0).targetTick ≠
          W_B.tick := by
        dsimp [stageEvent]
        rw [stageTarget_zero_eq, h_tick_WB]
        omega
      have h_nd₂ : (stageEvent actTick groups g₂ c₂ 0).targetTick ≠
          W_B.tick := by
        dsimp [stageEvent]
        rw [stageTarget_zero_eq, ← h_act_eq, h_tick_WB]
        omega
      exact World.stepUntilNextTick_notDue_order W_B _ _ h_ev₁ h_ev₂
        h_nd₁ h_nd₂ h_order_B
  -- transport from tick t₀ + 1 to the pop tick t₀ + 2
  dsimp [popQueueWorld]
  rw [stageTarget_zero_eq]
  apply evBefore_gSimWorld_const groups actTick groupOrd withinOrd pos
    (t₀ + 1) (t₀ + 2) (stageEvent actTick groups g₁ c₁ 0)
    (stageEvent actTick groups g₂ c₂ 0) (by omega) h_order_succ
  · -- bound for chain (g₁, c₁)
    show t₀ + 2 ≤ (stageEvent actTick groups g₁ c₁ 0).targetTick
    rw [show (stageEvent actTick groups g₁ c₁ 0).targetTick = t₀ + 2 from by
      dsimp [stageEvent, t₀]
      rw [stageTarget_zero_eq]]
  · -- bound for chain (g₂, c₂): same spec means same activation tick
    show t₀ + 2 ≤ (stageEvent actTick groups g₂ c₂ 0).targetTick
    rw [show (stageEvent actTick groups g₂ c₂ 0).targetTick = t₀ + 2 from by
      dsimp [stageEvent, t₀]
      rw [stageTarget_zero_eq, ← h_act_eq]]

/-! ## What remains toward the order-preservation capstone

`sameSpec_stage_evBefore_base` discharges the `h_base` premise of
QSideOrder.sameSpec_orderPreservation whenever the burst order supplies the
group split of the activation list. The two remaining premises are:

1. **h_nodup** (due-filter Nodup at every pop tick): documented in
   StageEventNodup and NodupChain; needs the structural Nodup invariant of
   `stepUntilNextTick`.
2. **h_surv** (burst-phase survival at every pop tick): documented in
   BurstSurvival and SuccessorSurvival; SuccessorSurvival supplies the successor-event form, the
   full discharge is still open.
-/
