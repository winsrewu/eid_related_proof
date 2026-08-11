import BasicProofs.GroupClustering.FinalStageAssemblySetup
import BasicProofs.GroupClustering.ConverseSpawn
import BasicProofs.GroupClustering.MiddleBlockOkTicks
import BasicProofs.GroupClustering.ConverseSpawnFinal
import BasicProofs.GroupClustering.ActivationListOrder
import BasicProofs.GroupClustering.BackwardTransport
import BasicProofs.GroupClustering.CrossPriorityPopDiscipline
import BasicProofs.GroupClustering.ConverseStageJ
import BasicProofs.GroupClustering.SamePriorityPopOrder
import BasicProofs.GroupClustering.StageEventCompleteness
import BasicProofs.GroupClustering.StageEventNodup

open BasicRedstoneSim List

/-! # Group clustering — mixed phase of the final converse

At the last middle stage, the first reference event pops during the
burst while the second survives it (the only mixed fate compatible
with the same-priority correlation of SamePriorityPopOrder). The middle final lies
between the two reference finals after the drain. Tracing it back to
its parent pop — a burst pop in one case, a drain pop in the other —
places the parent between the two reference stage-`m` events in the
tick-start due filter, where the MiddleBlockOkLastMiddleStage invariant classifies it.

The pop-classification and burst-split helpers are reproven from
MiddleBlockOkActiveTick (private there).
-/

/-- `(l₁ ++ l₂).drop l₁.length = l₂`. -/
private theorem drop_append_self' {α : Type} (l₁ l₂ : List α) :
    (l₁ ++ l₂).drop l₁.length = l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a l ih => simp [ih]

/-- Append cancellation on the left. -/
private theorem append_left_cancel'' {α : Type} (l l₁ l₂ : List α)
    (h : l ++ l₁ = l ++ l₂) : l₁ = l₂ := by
  induction l generalizing l₁ l₂ with
  | nil => simpa using h
  | cons a l ih =>
    simp only [List.cons_append] at h
    exact ih l₁ l₂ (by simpa using congrArg List.tail h)

/-- In a split `l ++ r = p ++ s` with `p` at least as long as `l`, the
    prefix `p` starts with `l`. -/
private theorem append_prefix_of_length_le' {α : Type} (l r p s : List α)
    (h_eq : l ++ r = p ++ s) (h_len : l.length ≤ p.length) :
    ∃ p₁, p = l ++ p₁ ∧ r = p₁ ++ s := by
  revert h_eq h_len
  induction l generalizing p with
  | nil =>
    intro h_eq _
    simp only [List.nil_append] at h_eq
    exact ⟨p, by simp, h_eq⟩
  | cons a l ih =>
    intro h_eq h_len
    cases p with
    | nil => simp at h_len
    | cons b p' =>
      simp only [List.cons_append, List.length_cons] at h_eq h_len
      injection h_eq with h_ab h_rest
      obtain ⟨p₁, h_p', h_r⟩ := ih p' h_rest (by omega)
      refine ⟨p₁, ?_, h_r⟩
      rw [h_p', ← h_ab]
      rfl

/-- In `l ++ r = p ++ x :: q` with a short `p`, `x` lies in `l`. -/
private theorem mem_left_of_short_prefix_split' {α : Type}
    (l r p q : List α) (x : α) (h_eq : l ++ r = p ++ x :: q)
    (h_lt : p.length < l.length) : x ∈ l := by
  induction p generalizing l with
  | nil =>
    simp only [List.nil_append] at h_eq
    cases l with
    | nil => exfalso; omega
    | cons a l' =>
      simp only [List.cons_append] at h_eq
      injection h_eq with h_ax _
      rw [← h_ax]
      exact List.mem_cons.mpr (Or.inl rfl)
  | cons b p' ih =>
    cases l with
    | nil => simp at h_lt
    | cons a l' =>
      simp only [List.cons_append, List.length_cons] at h_eq h_lt
      injection h_eq with _ h_rest
      have h_mem := ih l' h_rest (by omega)
      exact List.mem_cons.mpr (Or.inr h_mem)

/-- If the left anchor is absent from `l`, then `evBefore (l ++ r) x y`
    already holds in `r`. -/
private theorem evBefore_append_left_absent' {l r : List ScheduledEvent}
    {x y : ScheduledEvent} (h_x : x ∉ l) (h : evBefore (l ++ r) x y) :
    evBefore r x y := by
  obtain ⟨p, q, h_eq, h_y⟩ := h
  have h_len : l.length ≤ p.length := by
    by_contra h_lt
    exact h_x (mem_left_of_short_prefix_split' l r p q x h_eq (by omega))
  obtain ⟨p₁, _, h_r⟩ := append_prefix_of_length_le' l r p (x :: q) h_eq h_len
  exact ⟨p₁, q, h_r, h_y⟩

/-- With `y` in the split of `evBefore (l ++ r) x y`, either `x` lies in
    `l` or the betweenness already holds in `r`. -/
private theorem evBefore_append_split_right' {l r : List ScheduledEvent}
    {x y : ScheduledEvent} (h : evBefore (l ++ r) x y) :
    x ∈ l ∨ evBefore r x y := by
  obtain ⟨p, q, h_eq, h_yq⟩ := h
  by_cases h_lt : p.length < l.length
  · exact Or.inl (mem_left_of_short_prefix_split' l r p q x h_eq h_lt)
  · obtain ⟨p₁, _, h_r⟩ :=
      append_prefix_of_length_le' l r p (x :: q) h_eq (by omega)
    exact Or.inr ⟨p₁, q, h_r, h_yq⟩

/-- A filter is empty when no member satisfies the predicate. -/
private theorem filter_empty_of_none' {α : Type} (p : α → Bool)
    (l : List α) (h : ∀ x ∈ l, p x = false) : l.filter p = [] := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp [List.filter, h x (List.mem_cons.mpr (Or.inl rfl)),
      ih (fun y hy => h y (List.mem_cons.mpr (Or.inr hy)))]

/-- A Nat inequality decides the `==` comparison to false. -/
private theorem nat_beq_false_of_ne' (a b : Nat) (h : a ≠ b) :
    (a == b) = false := by
  simp [h]

/-- Equal node lists give equal node lists after one
    `onScheduledTick`. Only signal levels change. -/
private theorem onScheduledTick_nodes_of_nodes_eq' (w₁ w₂ : World)
    (id : Nat) (h_nodes : w₁.nodes = w₂.nodes) :
    (w₁.onScheduledTick id).nodes = (w₂.onScheduledTick id).nodes := by
  have h_get : w₁.getNode id = w₂.getNode id := by
    dsimp [World.getNode]
    rw [h_nodes]
  cases h₁ : w₁.getNode id with
  | none =>
    have h₂ : w₂.getNode id = none := by rwa [← h_get]
    have h_e₁ : w₁.onScheduledTick id = w₁ := by
      simp only [World.onScheduledTick, h₁]
    have h_e₂ : w₂.onScheduledTick id = w₂ := by
      simp only [World.onScheduledTick, h₂]
    rw [h_e₁, h_e₂]
    exact h_nodes
  | some nd =>
    have h₂ : w₂.getNode id = some nd := by rwa [← h_get]
    cases h_kind : nd.kind with
    | input =>
      have h_e₁ : w₁.onScheduledTick id = w₁ := by
        simp only [World.onScheduledTick, h₁, h_kind]
      have h_e₂ : w₂.onScheduledTick id = w₂ := by
        simp only [World.onScheduledTick, h₂, h_kind]
      rw [h_e₁, h_e₂]
      exact h_nodes
    | output name =>
      have h_e₁ : w₁.onScheduledTick id = w₁ := by
        simp only [World.onScheduledTick, h₁, h_kind]
      have h_e₂ : w₂.onScheduledTick id = w₂ := by
        simp only [World.onScheduledTick, h₂, h_kind]
      rw [h_e₁, h_e₂]
      exact h_nodes
    | observer =>
      have h_e₁ : w₁.onScheduledTick id =
          (w₁.updateNode id
            (fun nd' =>
              ({ nd' with sigLevel := 15 } : NodeData))).notifyOutputs id :=
        by simp only [World.onScheduledTick, h₁, h_kind]
      have h_e₂ : w₂.onScheduledTick id =
          (w₂.updateNode id
            (fun nd' =>
              ({ nd' with sigLevel := 15 } : NodeData))).notifyOutputs id :=
        by simp only [World.onScheduledTick, h₂, h_kind]
      rw [h_e₁, h_e₂, World.notifyOutputs_nodes, World.notifyOutputs_nodes]
      dsimp [World.updateNode]
      rw [h_nodes]
    | repeater d p =>
      have h_e₁ : w₁.onScheduledTick id =
          (w₁.updateNode id (fun nd' =>
            ({ nd' with
              sigLevel := if w₁.getInputSignal id > 0 then 15 else 0 } :
              NodeData))).notifyOutputs id := by
        simp only [World.onScheduledTick, h₁, h_kind]
      have h_e₂ : w₂.onScheduledTick id =
          (w₂.updateNode id (fun nd' =>
            ({ nd' with
              sigLevel := if w₂.getInputSignal id > 0 then 15 else 0 } :
              NodeData))).notifyOutputs id := by
        simp only [World.onScheduledTick, h₂, h_kind]
      have h_sig : w₁.getInputSignal id = w₂.getInputSignal id := by
        dsimp [World.getInputSignal, World.getNode]
        rw [h_nodes]
      have h_upd : (w₁.updateNode id (fun nd' =>
            ({ nd' with
              sigLevel := if w₂.getInputSignal id > 0 then 15 else 0 } :
              NodeData))).nodes =
          (w₂.updateNode id (fun nd' =>
            ({ nd' with
              sigLevel := if w₂.getInputSignal id > 0 then 15 else 0 } :
              NodeData))).nodes := by
        dsimp [World.updateNode]
        rw [h_nodes]
      rw [h_e₁, h_e₂, World.notifyOutputs_nodes, World.notifyOutputs_nodes,
        h_sig, h_upd]

/-- With no due events the spawn accumulator is empty. -/
private theorem popSpawnAcc_of_no_due' (w : World) (fuel : Nat)
    (h_no : ∀ ev ∈ w.events, ev.targetTick ≠ w.tick) :
    World.popSpawnAcc w fuel = [] := by
  induction fuel with
  | zero => dsimp [World.popSpawnAcc]
  | succ fuel ih =>
    dsimp only [World.popSpawnAcc]
    rw [World.popNextEvent_none_of_no_due w h_no]

/-- The spawn accumulator splits over a fuel sum. -/
private theorem popSpawnAcc_concat' (w : World) (a b : Nat) :
    World.popSpawnAcc w (a + b) =
      World.popSpawnAcc w a ++
        World.popSpawnAcc (World.popSeqWorldFuel w a) b := by
  induction a generalizing w b with
  | zero =>
    rw [Nat.zero_add]
    dsimp [World.popSpawnAcc, World.popSeqWorldFuel]
  | succ a ih =>
    rw [Nat.succ_add]
    cases h_pop : w.popNextEvent with
    | none =>
      have h_no : ∀ ev ∈ w.events, ev.targetTick ≠ w.tick :=
        popNextEvent_none_no_events w h_pop
      rw [popSpawnAcc_of_no_due' w (a + b + 1) h_no]
      have h_acc : World.popSpawnAcc w (a + 1) = [] := by
        dsimp [World.popSpawnAcc]
        simp only [h_pop]
      have h_world : World.popSeqWorldFuel w (a + 1) = w := by
        dsimp [World.popSeqWorldFuel]
        simp only [h_pop]
      rw [h_acc, h_world, List.nil_append]
      exact (popSpawnAcc_of_no_due' w b h_no).symm
    | some p =>
      rcases p with ⟨ev₀, w_pop⟩
      set w' := w_pop.onScheduledTick ev₀.nodeId
      have h_lhs : World.popSpawnAcc w (a + b + 1) =
          w'.events.drop w_pop.events.length ++ World.popSpawnAcc w' (a + b) :=
        by
        dsimp [World.popSpawnAcc, w']
        simp only [h_pop]
      have h_acc : World.popSpawnAcc w (a + 1) =
          w'.events.drop w_pop.events.length ++ World.popSpawnAcc w' a := by
        dsimp [World.popSpawnAcc, w']
        simp only [h_pop]
      have h_world : World.popSeqWorldFuel w (a + 1) =
          World.popSeqWorldFuel w' a := by
        dsimp [World.popSeqWorldFuel, w']
        simp only [h_pop]
      rw [h_lhs, h_acc, h_world, ih w' b, List.append_assoc]

/-- The spawn accumulator depends only on the tick, the node list, and
    the due filter. Two such worlds accumulate the same spawns. -/
private theorem popSpawnAcc_congr' (w₁ w₂ : World)
    (h_tick : w₁.tick = w₂.tick)
    (h_filter : w₁.events.filter (fun e => e.targetTick == w₁.tick) =
        w₂.events.filter (fun e => e.targetTick == w₂.tick))
    (h_nodes : w₁.nodes = w₂.nodes) (fuel : Nat) :
    World.popSpawnAcc w₁ fuel = World.popSpawnAcc w₂ fuel := by
  induction fuel generalizing w₁ w₂ h_tick h_filter h_nodes with
  | zero => dsimp [World.popSpawnAcc]
  | succ fuel ih =>
    dsimp only [World.popSpawnAcc]
    cases h_pop₁ : w₁.popNextEvent with
    | none =>
      have h_pop₂ : w₂.popNextEvent = none := by
        by_contra h_ne
        cases h_pop₂ : w₂.popNextEvent with
        | none => exact h_ne h_pop₂
        | some q =>
          rcases q with ⟨ev, w_pop₂⟩
          obtain ⟨_, _, _, h_due, h_mem, _⟩ :=
            World.popNextEvent_eraseIdx w₂ ev w_pop₂ h_pop₂
          have h_ev_f : ev ∈
              w₂.events.filter (fun e => e.targetTick == w₂.tick) := by
            rw [List.mem_filter]
            exact ⟨h_mem, by rw [h_due]; simp⟩
          rw [← h_filter] at h_ev_f
          exact popNextEvent_none_no_events w₁ h_pop₁ ev
            (List.mem_filter.mp h_ev_f).1 (by
              simpa using (List.mem_filter.mp h_ev_f).2)
      simp only [h_pop₂]
    | some p =>
      rcases p with ⟨ev₀, w_pop₁⟩
      obtain ⟨w_pop₂, h_pop₂⟩ :=
        popNextEvent_same_of_same_filter w₁ w₂ h_tick h_filter ev₀ w_pop₁
          h_pop₁
      simp only [h_pop₂]
      set v₁ := w_pop₁.onScheduledTick ev₀.nodeId
      set v₂ := w_pop₂.onScheduledTick ev₀.nodeId
      have h_tick_pop : w_pop₁.tick = w_pop₂.tick := by
        rw [World.popNextEvent_tick w₁ ev₀ w_pop₁ h_pop₁,
          World.popNextEvent_tick w₂ ev₀ w_pop₂ h_pop₂, h_tick]
      have h_nodes_pop : w_pop₁.nodes = w_pop₂.nodes := by
        rw [World.popNextEvent_nodes w₁ ev₀ w_pop₁ h_pop₁,
          World.popNextEvent_nodes w₂ ev₀ w_pop₂ h_pop₂, h_nodes]
      have h_node_id : w_pop₁.getNode ev₀.nodeId =
          w_pop₂.getNode ev₀.nodeId := by
        dsimp [World.getNode]
        rw [h_nodes_pop]
      have h_kinds : ∀ nid,
          (w_pop₁.getNode nid).map (·.kind) =
            (w_pop₂.getNode nid).map (·.kind) := by
        intro nid
        dsimp [World.getNode]
        rw [h_nodes_pop]
      obtain ⟨new, h_new₁, h_new₂⟩ :=
        onScheduledTick_events_congr w_pop₁ w_pop₂ ev₀.nodeId h_tick_pop
          h_node_id h_kinds
      have h_drop : v₁.events.drop w_pop₁.events.length =
          v₂.events.drop w_pop₂.events.length := by
        dsimp only [v₁, v₂]
        rw [h_new₁, h_new₂, drop_append_self', drop_append_self']
      rw [h_drop]
      have h_tick_v : v₁.tick = v₂.tick := by
        dsimp only [v₁, v₂]
        rw [World.onScheduledTick_tick, World.onScheduledTick_tick,
          h_tick_pop]
      have h_filter_v :
          v₁.events.filter (fun e => e.targetTick == v₁.tick) =
            v₂.events.filter (fun e => e.targetTick == v₂.tick) := by
        dsimp only [v₁, v₂]
        rw [World.onScheduledTick_tick, World.onScheduledTick_tick]
        obtain ⟨new₁, h_app₁, h_fut₁⟩ :=
          World.onScheduledTick_appends_future w_pop₁ ev₀.nodeId
        obtain ⟨new₂, h_app₂, h_fut₂⟩ :=
          World.onScheduledTick_appends_future w_pop₂ ev₀.nodeId
        rw [h_app₁, h_app₂, List.filter_append, List.filter_append]
        have h_nil₁ :
            new₁.filter (fun e => e.targetTick == w_pop₁.tick) = [] := by
          apply filter_empty_of_none'
          intro e h_e
          have h_gt := h_fut₁ e h_e
          exact nat_beq_false_of_ne' e.targetTick w_pop₁.tick (by omega)
        have h_nil₂ :
            new₂.filter (fun e => e.targetTick == w_pop₂.tick) = [] := by
          apply filter_empty_of_none'
          intro e h_e
          have h_gt := h_fut₂ e h_e
          exact nat_beq_false_of_ne' e.targetTick w_pop₂.tick (by omega)
        rw [h_nil₁, h_nil₂, List.append_nil, List.append_nil]
        exact popNextEvent_filter_eq w₁ w₂ h_tick h_filter ev₀ w_pop₁
          w_pop₂ h_pop₁ h_pop₂
      have h_nodes_v : v₁.nodes = v₂.nodes :=
        onScheduledTick_nodes_of_nodes_eq' w_pop₁ w_pop₂ ev₀.nodeId
          h_nodes_pop
      rw [ih v₁ v₂ h_tick_v h_filter_v h_nodes_v]

/-- Total pop fuel spent by the `processNEvents` phases of a burst. -/
private def burstFuel' (t : Nat) (pos : Nat → List Nat) :
    List (Nat × Nat) → Nat
  | [] => 0
  | (_, k) :: ps => (pos t)[k]?.getD 0 + burstFuel' t pos ps

/-- The non-due, non-zero-priority part of the burst result: the old
    filtered queue plus the filtered spawn accumulator of the popped
    due events. The observer batches drop out of the filter. -/
private theorem gSimBurst_filter_split' (t : Nat)
    (obsAll : List (List Nat)) (withinOrd pos : Nat → List Nat)
    (w : World) (pairs : List (Nat × Nat)) :
    ((gSimBurst t obsAll withinOrd pos w pairs).events.filter
        (fun ev => ev.targetTick ≠ w.tick)).filter
      (fun ev => decide (ev.priority ≠ (0 : Int))) =
      (w.events.filter (fun ev => ev.targetTick ≠ w.tick)).filter
        (fun ev => decide (ev.priority ≠ (0 : Int))) ++
      (World.popSpawnAcc w (burstFuel' t pos pairs)).filter
        (fun ev => decide (ev.priority ≠ (0 : Int))) := by
  set pPri : ScheduledEvent → Bool :=
    fun ev => decide (ev.priority ≠ (0 : Int))
  induction pairs generalizing w with
  | nil =>
    dsimp [gSimBurst, burstFuel', World.popSpawnAcc]
    simp [pPri]
  | cons p ps ih =>
    rcases p with ⟨gi, k⟩
    dsimp only [gSimBurst, List.foldl_cons, burstFuel']
    set m := (pos t)[k]?.getD 0
    set ordered : List Nat := (withinOrd gi).foldl (fun acc ci =>
      match (obsAll[gi]?.getD [])[ci]? with
      | some oid => acc ++ [oid]
      | none => acc) []
    set Wp := processNEvents w m
    set W₁ := activateGroup Wp ordered
    have h_ih := ih W₁
    have h_tick_Wp : Wp.tick = w.tick := by
      dsimp [Wp]; exact processNEvents_tick w m
    have h_tick_W₁ : W₁.tick = w.tick := by
      dsimp [W₁, Wp]; rw [activateGroup_tick, h_tick_Wp]
    rw [h_tick_W₁] at h_ih
    set obsEv : List ScheduledEvent := ordered.map (fun nid =>
      ({ targetTick := Wp.tick + 2, priority := 0, nodeId := nid } :
        ScheduledEvent))
    have h_W₁_events : W₁.events = Wp.events ++ obsEv := by
      dsimp [W₁, obsEv]
      exact activateGroup_events_map Wp ordered
    have h_W₁_filter :
        (W₁.events.filter (fun ev => ev.targetTick ≠ w.tick)).filter pPri =
          (Wp.events.filter
            (fun ev => ev.targetTick ≠ w.tick)).filter pPri := by
      rw [h_W₁_events, List.filter_append, List.filter_append]
      have h_obs_nil :
          (obsEv.filter (fun ev => ev.targetTick ≠ w.tick)).filter pPri =
            [] := by
        apply filter_empty_of_none'
        intro ev h_ev
        rcases List.mem_filter.mp h_ev with ⟨h_mem, _⟩
        dsimp [obsEv] at h_mem
        rcases List.mem_map.mp h_mem with ⟨nid, _, h_ev_eq⟩
        rw [← h_ev_eq]
        dsimp [pPri]
        exact decide_eq_false (by omega)
      rw [h_obs_nil, List.append_nil]
    have h_Wp_filter :
        (Wp.events.filter (fun ev => ev.targetTick ≠ w.tick)).filter pPri =
          (w.events.filter (fun ev => ev.targetTick ≠ w.tick)).filter pPri
            ++ (World.popSpawnAcc w m).filter pPri := by
      have h_f := (World.popSeqWorldFuel_filter_split w m).1
      rw [← processNEvents_eq_popSeqWorldFuel] at h_f
      dsimp [Wp]
      rw [h_f, List.filter_append]
    have h_acc : World.popSpawnAcc W₁ (burstFuel' t pos ps) =
        World.popSpawnAcc Wp (burstFuel' t pos ps) := by
      refine popSpawnAcc_congr' W₁ Wp ?_ ?_ (activateGroup_nodes Wp ordered)
        (burstFuel' t pos ps)
      · dsimp [W₁]
        exact activateGroup_tick Wp ordered
      · dsimp [W₁]
        rw [activateGroup_tick]
        exact activateGroup_due_filter Wp ordered
    change ((gSimBurst t obsAll withinOrd pos W₁ ps).events.filter
        (fun ev => ev.targetTick ≠ w.tick)).filter pPri =
      (w.events.filter (fun ev => ev.targetTick ≠ w.tick)).filter pPri ++
        (World.popSpawnAcc w (m + burstFuel' t pos ps)).filter pPri
    rw [h_ih, h_W₁_filter, h_acc, h_Wp_filter]
    rw [List.append_assoc, ← List.filter_append]
    congr 1
    rw [popSpawnAcc_concat' w m (burstFuel' t pos ps)]
    have h_tail : World.popSpawnAcc Wp (burstFuel' t pos ps) =
        World.popSpawnAcc (World.popSeqWorldFuel w m)
          (burstFuel' t pos ps) := by
      congr 1
      dsimp [Wp]
      exact processNEvents_eq_popSeqWorldFuel w m
    rw [h_tail]

/-- Every popped event spawns at most one event. -/
private theorem pops_single_spawn' (groups : List GroupSpec)
    (actTick : Nat → Nat) (w : World) (n : Nat)
    (h_stage_due : ∀ ev ∈ w.events, ev.targetTick = w.tick →
      ∃ gi ci j, gi < groups.length ∧ ci < (groupAt groups gi).length ∧
        j ≤ (chainAt groups gi ci).middleDelays.length + 1 ∧
        ev = stageEvent actTick groups gi ci j ∧
        (if j = 0 then actTick gi else
          stageTarget actTick groups gi ci (j - 1)) < w.tick + 1 ∧
        w.tick ≤ stageTarget actTick groups gi ci j) :
    ∀ ev ∈ World.popSeqFuel w n, ∀ (v : World),
      v.tick = w.tick → NodeLayoutOk groups v →
      ∃ s, (v.onScheduledTick ev.nodeId).events = v.events ++ [s] ∨
        (v.onScheduledTick ev.nodeId).events = v.events := by
  intro ev h_ev v h_v h_lay
  have h_ev_w : ev ∈ w.events :=
    World.mem_popSeqFuel_mem_events w n ev h_ev
  have h_ev_due : ev.targetTick = w.tick :=
    World.mem_popSeqFuel_due w n ev h_ev
  obtain ⟨gi₀, ci₀, k₀, h_gi₀, h_ci₀, _, h_ev_eq₀, _, _⟩ :=
    h_stage_due ev h_ev_w h_ev_due
  by_cases h_last :
      k₀ = (chainAt groups gi₀ ci₀).middleDelays.length + 1
  · refine ⟨ev, Or.inr ?_⟩
    rw [h_ev_eq₀, h_last]
    exact lastStage_spawn_nil groups actTick v gi₀ ci₀ h_gi₀ h_ci₀ h_lay
  · refine ⟨stageEvent actTick groups gi₀ ci₀ (k₀ + 1), Or.inl ?_⟩
    have h_mid : k₀ ≤ (chainAt groups gi₀ ci₀).middleDelays.length := by
      omega
    have h_tick : v.tick = stageTarget actTick groups gi₀ ci₀ k₀ := by
      rw [h_v, ← h_ev_due]
      have := congr_arg ScheduledEvent.targetTick h_ev_eq₀
      dsimp [stageEvent] at this
      exact this
    rw [h_ev_eq₀]
    exact stage_spawn groups actTick v gi₀ ci₀ k₀ h_gi₀ h_ci₀ h_mid
      h_tick h_lay

/-- Only the reference stage event spawns its reference successor. -/
private theorem pops_unique_spawn' (groups : List GroupSpec)
    (actTick : Nat → Nat) (w : World) (n : Nat)
    (A sA : ScheduledEvent) (gA cA jA : Nat)
    (h_gA : gA < groups.length) (h_cA : cA < (groupAt groups gA).length)
    (h_jA : jA ≤ (chainAt groups gA cA).middleDelays.length)
    (h_A : A = stageEvent actTick groups gA cA jA)
    (h_sA : sA = stageEvent actTick groups gA cA (jA + 1))
    (h_stage_due : ∀ ev ∈ w.events, ev.targetTick = w.tick →
      ∃ gi ci j, gi < groups.length ∧ ci < (groupAt groups gi).length ∧
        j ≤ (chainAt groups gi ci).middleDelays.length + 1 ∧
        ev = stageEvent actTick groups gi ci j ∧
        (if j = 0 then actTick gi else
          stageTarget actTick groups gi ci (j - 1)) < w.tick + 1 ∧
        w.tick ≤ stageTarget actTick groups gi ci j) :
    ∀ ev ∈ World.popSeqFuel w n, ∀ (v : World),
      v.tick = w.tick → NodeLayoutOk groups v → ∀ s,
      (v.onScheduledTick ev.nodeId).events = v.events ++ [s] →
      s = sA → ev = A := by
  intro ev h_ev v h_v h_lay s h_sp h_s
  have h_ev_w : ev ∈ w.events :=
    World.mem_popSeqFuel_mem_events w n ev h_ev
  have h_ev_due : ev.targetTick = w.tick :=
    World.mem_popSeqFuel_due w n ev h_ev
  obtain ⟨gi₀, ci₀, k₀, h_gi₀, h_ci₀, _, h_ev_eq₀, _, _⟩ :=
    h_stage_due ev h_ev_w h_ev_due
  by_cases h_last :
      k₀ = (chainAt groups gi₀ ci₀).middleDelays.length + 1
  · have h_nil : (v.onScheduledTick ev.nodeId).events = v.events := by
      rw [h_ev_eq₀, h_last]
      exact lastStage_spawn_nil groups actTick v gi₀ ci₀ h_gi₀ h_ci₀ h_lay
    rw [h_nil] at h_sp
    have h_len := congrArg List.length h_sp
    simp at h_len
  · have h_mid : k₀ ≤ (chainAt groups gi₀ ci₀).middleDelays.length := by
      omega
    have h_tick : v.tick = stageTarget actTick groups gi₀ ci₀ k₀ := by
      rw [h_v, ← h_ev_due]
      have := congr_arg ScheduledEvent.targetTick h_ev_eq₀
      dsimp [stageEvent] at this
      exact this
    have h_sp' : (v.onScheduledTick ev.nodeId).events =
        v.events ++ [stageEvent actTick groups gi₀ ci₀ (k₀ + 1)] := by
      rw [h_ev_eq₀]
      exact stage_spawn groups actTick v gi₀ ci₀ k₀ h_gi₀ h_ci₀ h_mid
        h_tick h_lay
    rw [h_sp'] at h_sp
    have h_inj := append_left_cancel'' v.events
      [stageEvent actTick groups gi₀ ci₀ (k₀ + 1)] [s] h_sp
    injection h_inj with h_one
    rw [h_s, h_sA] at h_one
    obtain ⟨h_g_eq, h_c_eq, h_k_eq⟩ :=
      stageEvent_injective actTick groups gi₀ ci₀ (k₀ + 1) gA cA (jA + 1)
        h_gi₀ h_ci₀ h_gA h_cA (by omega) (by omega) h_one
    rw [h_ev_eq₀, h_g_eq, h_c_eq, h_A]
    congr 1
    omega

/-- Distinct pops spawn distinct events. -/
private theorem pops_distinct_spawn' (groups : List GroupSpec)
    (actTick : Nat → Nat) (w : World) (n : Nat)
    (h_stage_due : ∀ ev ∈ w.events, ev.targetTick = w.tick →
      ∃ gi ci j, gi < groups.length ∧ ci < (groupAt groups gi).length ∧
        j ≤ (chainAt groups gi ci).middleDelays.length + 1 ∧
        ev = stageEvent actTick groups gi ci j ∧
        (if j = 0 then actTick gi else
          stageTarget actTick groups gi ci (j - 1)) < w.tick + 1 ∧
        w.tick ≤ stageTarget actTick groups gi ci j) :
    ∀ ev₁ ∈ World.popSeqFuel w n,
      ∀ ev₂ ∈ World.popSeqFuel w n, ev₁ ≠ ev₂ →
      ∀ (v₁ v₂ : World), v₁.tick = w.tick → v₂.tick = w.tick →
      NodeLayoutOk groups v₁ → NodeLayoutOk groups v₂ →
      ∀ s₁ s₂, (v₁.onScheduledTick ev₁.nodeId).events = v₁.events ++ [s₁] →
      (v₂.onScheduledTick ev₂.nodeId).events = v₂.events ++ [s₂] →
      s₁ ≠ s₂ := by
  intro ev₁ h₁ ev₂ h₂ h_ne v₁ v₂ h_v₁ h_v₂ h_l₁ h_l₂ s₁ s₂ h_sp₁ h_sp₂
      h_s_eq
  obtain ⟨gi₁, ci₁, k₁, h_gi₁, h_ci₁, _, h_ev₁, _, _⟩ :=
    h_stage_due ev₁ (World.mem_popSeqFuel_mem_events w n ev₁ h₁)
      (World.mem_popSeqFuel_due w n ev₁ h₁)
  obtain ⟨gi₂, ci₂, k₂, h_gi₂, h_ci₂, _, h_ev₂, _, _⟩ :=
    h_stage_due ev₂ (World.mem_popSeqFuel_mem_events w n ev₂ h₂)
      (World.mem_popSeqFuel_due w n ev₂ h₂)
  have h_k₁_mid : k₁ ≤ (chainAt groups gi₁ ci₁).middleDelays.length := by
    by_contra h_last
    have h_last' :
        k₁ = (chainAt groups gi₁ ci₁).middleDelays.length + 1 := by omega
    have h_nil : (v₁.onScheduledTick ev₁.nodeId).events = v₁.events := by
      rw [h_ev₁, h_last']
      exact lastStage_spawn_nil groups actTick v₁ gi₁ ci₁ h_gi₁ h_ci₁
        h_l₁
    rw [h_nil] at h_sp₁
    have h_len := congrArg List.length h_sp₁
    simp at h_len
  have h_k₂_mid : k₂ ≤ (chainAt groups gi₂ ci₂).middleDelays.length := by
    by_contra h_last
    have h_last' :
        k₂ = (chainAt groups gi₂ ci₂).middleDelays.length + 1 := by omega
    have h_nil : (v₂.onScheduledTick ev₂.nodeId).events = v₂.events := by
      rw [h_ev₂, h_last']
      exact lastStage_spawn_nil groups actTick v₂ gi₂ ci₂ h_gi₂ h_ci₂
        h_l₂
    rw [h_nil] at h_sp₂
    have h_len := congrArg List.length h_sp₂
    simp at h_len
  have h_due₁ : ev₁.targetTick = w.tick :=
    World.mem_popSeqFuel_due w n ev₁ h₁
  have h_due₂ : ev₂.targetTick = w.tick :=
    World.mem_popSeqFuel_due w n ev₂ h₂
  have h_tick₁ : v₁.tick = stageTarget actTick groups gi₁ ci₁ k₁ := by
    rw [h_v₁, ← h_due₁]
    have := congr_arg ScheduledEvent.targetTick h_ev₁
    dsimp [stageEvent] at this
    exact this
  have h_tick₂ : v₂.tick = stageTarget actTick groups gi₂ ci₂ k₂ := by
    rw [h_v₂, ← h_due₂]
    have := congr_arg ScheduledEvent.targetTick h_ev₂
    dsimp [stageEvent] at this
    exact this
  have h_sp₁' : (v₁.onScheduledTick ev₁.nodeId).events =
      v₁.events ++ [stageEvent actTick groups gi₁ ci₁ (k₁ + 1)] := by
    rw [h_ev₁]
    exact stage_spawn groups actTick v₁ gi₁ ci₁ k₁ h_gi₁ h_ci₁ h_k₁_mid
      h_tick₁ h_l₁
  have h_sp₂' : (v₂.onScheduledTick ev₂.nodeId).events =
      v₂.events ++ [stageEvent actTick groups gi₂ ci₂ (k₂ + 1)] := by
    rw [h_ev₂]
    exact stage_spawn groups actTick v₂ gi₂ ci₂ k₂ h_gi₂ h_ci₂ h_k₂_mid
      h_tick₂ h_l₂
  rw [h_sp₁'] at h_sp₁
  rw [h_sp₂'] at h_sp₂
  have h_inj₁ := append_left_cancel'' v₁.events
    [stageEvent actTick groups gi₁ ci₁ (k₁ + 1)] [s₁] h_sp₁
  have h_inj₂ := append_left_cancel'' v₂.events
    [stageEvent actTick groups gi₂ ci₂ (k₂ + 1)] [s₂] h_sp₂
  injection h_inj₁ with h_s₁
  injection h_inj₂ with h_s₂
  rw [← h_s₁, ← h_s₂] at h_s_eq
  obtain ⟨h_g, h_c, h_k⟩ := stageEvent_injective actTick groups gi₁ ci₁
    (k₁ + 1) gi₂ ci₂ (k₂ + 1) h_gi₁ h_ci₁ h_gi₂ h_ci₂ (by omega)
    (by omega) h_s_eq
  rw [h_ev₁, h_ev₂, h_g, h_c] at h_ne
  exact h_ne (by congr 1; omega)

/-- A filter that keeps every element of a list is the identity
    (reproven; private in ConverseFinalUnconditional). -/
private theorem filter_eq_self_of_forall' {α : Type} (p : α → Bool)
    (l : List α) (h : ∀ x ∈ l, p x = true) : l.filter p = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have h_x := h x (List.mem_cons.mpr (Or.inl rfl))
    simp [List.filter, h_x, ih (fun y hy => h y (List.mem_cons.mpr (Or.inr hy)))]

/-- The drain of any world splits the result queue into the non-due
    survivors followed by the spawn accumulator (reproven; private in
    FinalConverseDrainPhase). -/
private theorem stepUNT_filter_split' (w : World) :
    w.stepUntilNextTick.events =
      w.events.filter (fun ev => ev.targetTick ≠ w.tick) ++
        World.popSpawnAcc w
          ((w.events.filter (fun e => e.targetTick == w.tick)).length) := by
  set n := (w.events.filter (fun e => e.targetTick == w.tick)).length
  set W := processNEvents w n
  have h_drain : W.events.filter (fun ev => ev.targetTick == w.tick) = [] :=
    drain_due_filter w
  have h_no : ∀ ev ∈ W.events, ev.targetTick ≠ W.tick := by
    intro ev h_ev h_eq
    have h_mem : ev ∈ W.events.filter (fun e => e.targetTick == w.tick) := by
      rw [List.mem_filter]
      exact ⟨h_ev, by
        rw [processNEvents_tick] at h_eq
        rw [h_eq]
        simp⟩
    rw [h_drain] at h_mem
    cases h_mem
  have h_post_events : w.stepUntilNextTick.events = W.events := by
    have h_pop_none : W.popNextEvent = none :=
      World.popNextEvent_none_of_no_due W h_no
    have h_step_none : W.step = none := by
      simp only [World.step, h_pop_none]
    rw [← processNEvents_stepUntilNextTick_eq w n,
      stepUntilNextTick_of_step_none W h_step_none]
  have h_split : W.events =
      w.events.filter (fun ev => ev.targetTick ≠ w.tick) ++
        World.popSpawnAcc w n := by
    have h_f := (World.popSeqWorldFuel_filter_split w n).1
    rw [← processNEvents_eq_popSeqWorldFuel] at h_f
    have h_keep : W.events.filter (fun ev => ev.targetTick ≠ w.tick) =
        W.events := by
      apply filter_eq_self_of_forall'
      intro ev h_ev
      have h_ne : ev.targetTick ≠ w.tick := by
        have h := h_no ev h_ev
        rwa [processNEvents_tick] at h
      rw [decide_eq_true_eq]
      exact h_ne
    rw [← h_keep]
    exact h_f
  rw [h_post_events, h_split]

/-- `NodeLayoutOk` holds at every tick-start queue (reproven; private
    in SideHypothesisDischarge/FinalStageAssemblySetup/FinalConverseBurstPhase). -/
private theorem NodeLayoutOk_gSimWorld (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (t : Nat) :
    NodeLayoutOk groups
      (gSimWorld groups actTick groupOrd withinOrd pos t) := by
  dsimp [gSimWorld]
  exact NodeLayoutOk_gSimFoldl groups actTick (buildGroups groups).2 groupOrd
    withinOrd pos (buildGroups groups).1 t (NodeLayoutOk_buildGroups groups)


/-- Taking beyond the length of a list is the whole list
    (`List.take_all_of_le` under a private name). -/
private theorem take_all_of_length_le {α : Type} (l : List α) (n : Nat)
    (h : l.length ≤ n) : l.take n = l := by
  induction l generalizing n with
  | nil => cases n <;> simp
  | cons a l ih =>
    cases n with
    | zero => simp at h
    | succ n =>
      simp only [List.take, List.length_cons] at h ⊢
      rw [ih n (by omega)]

/-- The mixed phase of the final converse. The first reference stage-`m`
    event pops during the burst (its final sits in the post-burst
    queue); the second survives the burst (its final is absent). The
    middle final lies between the two reference finals after the
    drain. Concludes `ConverseSpawnFinal` at the pre-burst tick-start
    queue. -/
theorem mixedPhase_ConverseSpawnFinal (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat)
    (h_valid : ∀ gi (c : ChainSpec), gi < groups.length →
        c ∈ groupAt groups gi →
        (∀ d ∈ c.middleDelays, ValidDelay d) ∧ ValidDelay c.lastDelay)
    (h_uniform : ∀ gi (c₁ c₂ : ChainSpec), gi < groups.length →
        c₁ ∈ groupAt groups gi → c₂ ∈ groupAt groups gi →
        chainDelay c₁ = chainDelay c₂)
    (T : Nat)
    (h_act : ∀ gi, gi < groups.length → groupAt groups gi ≠ [] →
        actTick gi + groupDelay (groupAt groups gi) = T)
    (h_ord : List.Perm groupOrd (List.range groups.length))
    (h_within : ∀ gi, gi < groups.length →
        List.Perm (withinOrd gi) (List.range (groupAt groups gi).length))
    (g₁ c₁ gm cm g₂ c₂ m : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_gm : gm < groups.length) (h_cm : cm < (groupAt groups gm).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_spec : chainAt groups g₁ c₁ = chainAt groups g₂ c₂)
    (h_act_eq : actTick g₁ = actTick g₂)
    (h_m₁ : (chainAt groups g₁ c₁).middleDelays.length = m)
    (h_m₂ : (chainAt groups g₂ c₂).middleDelays.length = m)
    (h_m_ge : 1 ≤ m)
    (h_mb_full : MiddleBlockOk groups actTick T
        ((gSimWorld groups actTick groupOrd withinOrd pos
          (stageTarget actTick groups g₁ c₁ m)).events) g₁ c₁ g₂ c₂ m)
    (h_sA_in : stageEvent actTick groups g₁ c₁ (m + 1) ∈
        (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ m).events)
    (h_sD_out : stageEvent actTick groups g₂ c₂ (m + 1) ∉
        (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ m).events)
    (h_spawn_e : stageTarget actTick groups gm cm
        ((chainAt groups gm cm).middleDelays.length) =
      stageTarget actTick groups g₁ c₁ m)
    (h_ne_left : stageEvent actTick groups g₁ c₁ (m + 1) ≠
      stageEvent actTick groups gm cm
        ((chainAt groups gm cm).middleDelays.length + 1))
    (h_ne_right : stageEvent actTick groups gm cm
        ((chainAt groups gm cm).middleDelays.length + 1) ≠
      stageEvent actTick groups g₂ c₂ (m + 1))
    (h_b1 : evBefore
        ((gSimWorld groups actTick groupOrd withinOrd pos
          (stageTarget actTick groups g₁ c₁ m + 1)).events)
        (stageEvent actTick groups g₁ c₁ (m + 1))
        (stageEvent actTick groups gm cm
          ((chainAt groups gm cm).middleDelays.length + 1)))
    (h_b2 : evBefore
        ((gSimWorld groups actTick groupOrd withinOrd pos
          (stageTarget actTick groups g₁ c₁ m + 1)).events)
        (stageEvent actTick groups gm cm
          ((chainAt groups gm cm).middleDelays.length + 1))
        (stageEvent actTick groups g₂ c₂ (m + 1))) :
    ConverseSpawnFinal groups actTick
      (popQueueWorld groups actTick groupOrd withinOrd pos g₁ c₁ m)
      g₁ c₁ g₂ c₂ m
      (stageEvent actTick groups gm cm
        ((chainAt groups gm cm).middleDelays.length + 1)) := by
  set τ := stageTarget actTick groups g₁ c₁ m
  set wQ := gSimWorld groups actTick groupOrd withinOrd pos τ
  set w_log := wQ.logOutput s!"tick {τ}"
  set active := popActive groups actTick groupOrd g₁ c₁ m
  set W_B := preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ m
  set e := stageEvent actTick groups gm cm
    ((chainAt groups gm cm).middleDelays.length + 1)
  set f₁ := stageEvent actTick groups g₁ c₁ (m + 1)
  set f₃ := stageEvent actTick groups g₂ c₂ (m + 1)
  set Aₘ := stageEvent actTick groups g₁ c₁ m
  set Dₘ := stageEvent actTick groups g₂ c₂ m
  have h_tgt₂ : stageTarget actTick groups g₂ c₂ m = τ :=
    (sameSpec_stageTarget groups actTick g₁ c₁ g₂ c₂ m h_act_eq h_spec).symm
  have h_tick_WB : W_B.tick = τ :=
    preStepWorld_tick_eq groups actTick groupOrd withinOrd pos g₁ c₁ m
  have h_tick_log : w_log.tick = τ := by
    dsimp [w_log, wQ]
    rw [gSimWorld_tick groups actTick groupOrd withinOrd pos τ]
  have h_gord_nd : groupOrd.Nodup := Nodup.of_perm h_ord List.nodup_range
  have h_within_nd : ∀ gi, gi < groups.length → (withinOrd gi).Nodup :=
    fun gi h_gi => Nodup.of_perm (h_within gi h_gi) List.nodup_range
  obtain ⟨h_ok_B, h_layout_B⟩ := preStepWorld_tickQueueOk groups actTick
    groupOrd withinOrd pos h_gord_nd h_within_nd g₁ c₁ m
  have h_nd_WB : W_B.events.Nodup := h_ok_B.1
  have h_nd_due_WB : (W_B.events.filter
      (fun ev => ev.targetTick == W_B.tick)).Nodup :=
    List.Nodup.filter (fun ev => ev.targetTick == W_B.tick) h_ok_B.1
  have h_stage_WB : StageMemAt groups actTick W_B W_B.tick :=
    StageMemAt_of_TickQueueOk groups actTick W_B _ h_ok_B
  have h_layout_log : NodeLayoutOk groups w_log := by
    dsimp [w_log, wQ]
    exact NodeLayoutOk_logOutput groups
      (gSimWorld groups actTick groupOrd withinOrd pos τ) s!"tick {τ}"
      (NodeLayoutOk_gSimWorld groups actTick groupOrd withinOrd pos τ)
  have h_nodup_log : (w_log.events.filter
      (fun ev => ev.targetTick == w_log.tick)).Nodup := by
    rw [World.logOutput_events, h_tick_log]
    exact List.Nodup.filter (fun ev => ev.targetTick == τ)
      (gSimWorld_events_Nodup groups actTick groupOrd withinOrd pos τ
        h_gord_nd h_within_nd)
  have h_stage_log : StageMemAt groups actTick w_log w_log.tick := by
    rw [h_tick_log]
    dsimp [w_log, wQ]
    exact StageMemAt_logOutput groups actTick
      (gSimWorld groups actTick groupOrd withinOrd pos τ) s!"tick {τ}" τ
      (StageMemAt_gSimWorld groups actTick groupOrd withinOrd pos τ)
  -- Aₘ left the burst: NoSpawnDue with f₁ present
  have hA_not_WB : Aₘ ∉ W_B.events := by
    intro hA_WB
    have h_nsd := h_ok_B.2.2
    dsimp [NoSpawnDue] at h_nsd
    exact (h_nsd g₁ c₁ m h_g₁ h_c₁ (by omega) h_tick_WB.symm hA_WB) h_sA_in
  -- Dₘ is queued pre-burst and survives the burst
  have hD_mem_log : Dₘ ∈ w_log.events := by
    rw [World.logOutput_events]
    dsimp [wQ, Dₘ]
    have h_mem := stageEvent_mem_gSimWorld groups actTick groupOrd
      withinOrd pos h_valid h_ord h_within g₂ c₂ h_g₂ h_c₂ m (by omega)
    rwa [h_tgt₂] at h_mem
  have hD_WB : Dₘ ∈ W_B.events := by
    by_contra hD_gone
    have h_f₃_B : f₃ ∈ W_B.events :=
      gSimBurst_spawn_mem groups τ (buildGroups groups).2 withinOrd pos
        w_log active.zipIdx Dₘ f₃ h_layout_log hD_mem_log
        (by dsimp [Dₘ, stageEvent]; rw [h_tgt₂, ← h_tick_log]) hD_gone
        (by
          intro hc
          dsimp [f₃, stageEvent] at hc
          rw [h_tick_log] at hc
          have hT : stageTarget actTick groups g₂ c₂ (m + 1) = T := by
            rw [← h_m₂]
            exact stageTarget_final_eq_T groups actTick T g₂ c₂ h_g₂ h_c₂
              h_uniform h_act
          have := stageTarget_lt_succ actTick groups g₂ c₂ m (by omega)
          omega)
        (by
          intro v h_v h_lay
          simpa [f₃, Dₘ, stageEvent] using
            stage_spawn groups actTick v g₂ c₂ m h_g₂ h_c₂ (by omega)
              (h_v.trans (h_tick_log.trans h_tgt₂.symm)) h_lay)
    exact h_sD_out h_f₃_B
  -- e and f₁ are not queued pre-burst
  have h_e_not_log : e ∉ w_log.events := by
    dsimp [e, w_log, wQ]
    exact stageEvent_succ_not_mem_gSimWorld groups actTick groupOrd
      withinOrd pos gm cm ((chainAt groups gm cm).middleDelays.length) τ
      h_gm h_cm (by omega) h_spawn_e
  have h_f₁_not_log : f₁ ∉ w_log.events := by
    dsimp [f₁, w_log, wQ]
    exact stageEvent_succ_not_mem_gSimWorld groups actTick groupOrd
      withinOrd pos g₁ c₁ m τ h_g₁ h_c₁ (by omega) rfl
  -- the post-drain queue is the stepUNT of the burst result
  have h_Q₁ : (gSimWorld groups actTick groupOrd withinOrd pos
      (τ + 1)).events = W_B.stepUntilNextTick.events :=
    gSimWorld_succ_events_eq_preStepWorld groups actTick groupOrd
      withinOrd pos g₁ c₁ m
  have h_nd_post : W_B.stepUntilNextTick.events.Nodup := by
    rw [← h_Q₁]
    exact gSimWorld_events_Nodup groups actTick groupOrd withinOrd pos
      (τ + 1) h_gord_nd h_within_nd
  have h_f₁_nd : f₁.targetTick ≠ W_B.tick := by
    dsimp [f₁, stageEvent]
    rw [h_tick_WB]
    intro hc
    have := stageTarget_lt_succ actTick groups g₁ c₁ m (by omega)
    omega
  have h_e_nd : e.targetTick ≠ W_B.tick := by
    dsimp [e, stageEvent]
    rw [h_tick_WB, ← h_spawn_e]
    intro hc
    have := stageTarget_lt_succ actTick groups gm cm
      ((chainAt groups gm cm).middleDelays.length) (by omega)
    omega
  have h_f₃_nd : f₃.targetTick ≠ W_B.tick := by
    dsimp [f₃, stageEvent]
    rw [h_tick_WB]
    intro hc
    have hT : stageTarget actTick groups g₂ c₂ (m + 1) = T := by
      rw [← h_m₂]
      exact stageTarget_final_eq_T groups actTick T g₂ c₂ h_g₂ h_c₂
        h_uniform h_act
    have := stageTarget_lt_succ actTick groups g₂ c₂ m (by omega)
    omega
  have hA_pri : Aₘ.priority = (-3 : Int) := by
    dsimp [Aₘ, stageEvent]
    exact stagePri_middle groups g₁ c₁ m h_m_ge (by omega)
  have hD_pri : Dₘ.priority = (-3 : Int) := by
    dsimp [Dₘ, stageEvent]
    exact stagePri_middle groups g₂ c₂ m h_m_ge (by omega)
  -- the parent of e, between Aₘ and Dₘ in the pre-burst due filter
  have h_case_data : ∃ (gi ci k : Nat), gi < groups.length ∧
      ci < (groupAt groups gi).length ∧
      k ≤ (chainAt groups gi ci).middleDelays.length ∧ 1 ≤ k ∧
      (stageEvent actTick groups gi ci k).targetTick = τ ∧
      e = stageEvent actTick groups gi ci (k + 1) ∧
      evBefore (w_log.events.filter
        (fun ev => ev.targetTick == w_log.tick)) Aₘ
        (stageEvent actTick groups gi ci k) ∧
      evBefore (w_log.events.filter
        (fun ev => ev.targetTick == w_log.tick))
        (stageEvent actTick groups gi ci k) Dₘ := by
    by_cases h_e_WB : e ∈ W_B.events
    · -- e is a burst spawn: trace it through the burst accumulator
      have h_b1_WB : evBefore W_B.events f₁ e :=
        evBefore_stepUNT_backward W_B f₁ e h_nd_WB h_nd_post h_sA_in
          h_e_WB h_f₁_nd h_e_nd h_ne_left (by rwa [h_Q₁] at h_b1)
      set pPri : ScheduledEvent → Bool :=
        fun ev => decide (ev.priority ≠ (0 : Int))
      set M := burstFuel' τ pos active.zipIdx
      have h_split_B : (W_B.events.filter
          (fun ev => ev.targetTick ≠ w_log.tick)).filter pPri =
          (w_log.events.filter
            (fun ev => ev.targetTick ≠ w_log.tick)).filter pPri ++
          (World.popSpawnAcc w_log M).filter pPri := by
        convert gSimBurst_filter_split' τ (buildGroups groups).2 withinOrd
          pos w_log active.zipIdx using 1
        dsimp [W_B, preStepWorld, popQueueWorld, popActive, w_log, wQ,
          active, τ]
      have h_e_pri : pPri e = true := by
        dsimp [pPri, e, stageEvent]
        rw [stagePri_last groups gm cm]
        simp
      have h_f₁_pri : pPri f₁ = true := by
        dsimp [pPri, f₁, stageEvent]
        rw [show m + 1 = (chainAt groups g₁ c₁).middleDelays.length + 1
          by omega, stagePri_last groups g₁ c₁]
        simp
      have h_e_acc : e ∈ World.popSpawnAcc w_log M := by
        have h_lhs : e ∈ (W_B.events.filter
            (fun ev => ev.targetTick ≠ w_log.tick)).filter pPri := by
          rw [List.mem_filter]
          refine ⟨?_, h_e_pri⟩
          rw [List.mem_filter]
          exact ⟨h_e_WB, by
            rw [decide_eq_true_eq]
            exact fun hc => h_e_nd (hc.trans (h_tick_log.trans h_tick_WB.symm))⟩
        rw [h_split_B, List.mem_append] at h_lhs
        rcases h_lhs with h_old | h_acc
        · exact absurd (List.mem_filter.mp (List.mem_filter.mp h_old).1).1
            h_e_not_log
        · exact (List.mem_filter.mp h_acc).1
      have h_f₁_acc : f₁ ∈ World.popSpawnAcc w_log M := by
        have h_lhs : f₁ ∈ (W_B.events.filter
            (fun ev => ev.targetTick ≠ w_log.tick)).filter pPri := by
          rw [List.mem_filter]
          refine ⟨?_, h_f₁_pri⟩
          rw [List.mem_filter]
          exact ⟨h_sA_in, by
            rw [decide_eq_true_eq]
            exact fun hc => h_f₁_nd (hc.trans (h_tick_log.trans h_tick_WB.symm))⟩
        rw [h_split_B, List.mem_append] at h_lhs
        rcases h_lhs with h_old | h_acc
        · exact absurd (List.mem_filter.mp (List.mem_filter.mp h_old).1).1
            h_f₁_not_log
        · exact (List.mem_filter.mp h_acc).1
      have h_single_L := pops_single_spawn' groups actTick w_log M
        (fun ev h_ev _ => h_stage_log ev h_ev)
      have h_distinct_L := pops_distinct_spawn' groups actTick w_log M
        (fun ev h_ev _ => h_stage_log ev h_ev)
      have h_uniqueA_L := pops_unique_spawn' groups actTick w_log M Aₘ f₁
        g₁ c₁ m h_g₁ h_c₁ (by omega) rfl (by dsimp [f₁])
        (fun ev h_ev _ => h_stage_log ev h_ev)
      have hA_pop : Aₘ ∈ World.popSeqFuel w_log M := by
        obtain ⟨evA, h_evA, vA, sA', h_vA, h_layA, h_spA, h_sA'⟩ :=
          mem_popSpawnAcc_singleton_spawn groups w_log M f₁ h_layout_log
            h_single_L h_f₁_acc
        rwa [← h_uniqueA_L evA h_evA vA h_vA h_layA sA' h_spA h_sA'.symm]
      have h_b_acc : evBefore (World.popSpawnAcc w_log M) f₁ e := by
        have h_f1 : evBefore (W_B.events.filter
            (fun ev => ev.targetTick ≠ w_log.tick)) f₁ e := by
          apply evBefore.filter (fun ev => ev.targetTick ≠ w_log.tick)
          · rw [decide_eq_true_eq]
            exact fun hc => h_f₁_nd (hc.trans (h_tick_log.trans h_tick_WB.symm))
          · rw [decide_eq_true_eq]
            exact fun hc => h_e_nd (hc.trans (h_tick_log.trans h_tick_WB.symm))
          · exact h_b1_WB
        have h_f2 : evBefore ((W_B.events.filter
            (fun ev => ev.targetTick ≠ w_log.tick)).filter pPri) f₁ e :=
          evBefore.filter pPri h_f₁_pri h_e_pri h_f1
        rw [h_split_B] at h_f2
        have h_f₁_not_old : f₁ ∉ (w_log.events.filter
            (fun ev => ev.targetTick ≠ w_log.tick)).filter pPri :=
          fun h_mem => h_f₁_not_log
            (List.mem_filter.mp (List.mem_filter.mp h_mem).1).1
        have h_acc_f := evBefore_append_left_absent' h_f₁_not_old h_f2
        exact evBefore.of_filter pPri h_acc_f
      obtain ⟨eP, h_eP_pop, h_AP, vP, h_vP_tick, h_vP_lay, h_eP_fire,
          h_eP_fresh⟩ :=
        popSpawnAcc_left_converse groups w_log M Aₘ f₁ e h_layout_log
          h_nodup_log hA_pop
          (by dsimp [Aₘ, stageEvent]; rw [h_tick_log])
          h_f₁_not_log
          (by
            dsimp [f₁, stageEvent]
            rw [h_tick_log]
            exact stageTarget_lt_succ actTick groups g₁ c₁ m (by omega))
          (by
            intro v h_v h_lay
            simpa [f₁, Aₘ, stageEvent] using
              stage_spawn groups actTick v g₁ c₁ m h_g₁ h_c₁ (by omega)
                (h_v.trans h_tick_log) h_lay)
          h_single_L h_uniqueA_L h_distinct_L h_e_not_log
          (Ne.symm h_ne_left) h_b_acc
      have h_eP_log : eP ∈ w_log.events :=
        World.mem_popSeqFuel_mem_events w_log M eP h_eP_pop
      obtain ⟨gi, ci, k, h_gi, h_ci, _, h_eP_eq, _, _⟩ :=
        h_stage_log eP h_eP_log
      have h_eP_due : eP.targetTick = w_log.tick :=
        World.mem_popSeqFuel_due w_log M eP h_eP_pop
      have h_k_mid : k ≤ (chainAt groups gi ci).middleDelays.length := by
        by_contra h_last
        have h_last' :
            k = (chainAt groups gi ci).middleDelays.length + 1 := by omega
        have h_nil : (vP.onScheduledTick eP.nodeId).events =
            vP.events := by
          rw [h_eP_eq, h_last']
          exact lastStage_spawn_nil groups actTick vP gi ci h_gi h_ci
            h_vP_lay
        rw [h_nil] at h_eP_fire
        exact h_eP_fresh h_eP_fire
      have h_k_tgt : (stageEvent actTick groups gi ci k).targetTick = τ := by
        have := congr_arg ScheduledEvent.targetTick h_eP_eq
        dsimp [stageEvent] at this
        dsimp [stageEvent]
        rw [← this, h_eP_due, h_tick_log]
      have h_fire_P : (vP.onScheduledTick eP.nodeId).events =
          vP.events ++ [stageEvent actTick groups gi ci (k + 1)] := by
        rw [h_eP_eq]
        exact stage_spawn groups actTick vP gi ci k h_gi h_ci h_k_mid
          (by
            rw [h_vP_tick, ← h_eP_due]
            have := congr_arg ScheduledEvent.targetTick h_eP_eq
            dsimp [stageEvent] at this
            exact this)
          h_vP_lay
      have h_e_eq' : e = stageEvent actTick groups gi ci (k + 1) := by
        rw [h_fire_P] at h_eP_fire
        rcases List.mem_append.mp h_eP_fire with h_mem | h_mem
        · exact absurd h_mem h_eP_fresh
        · simpa using h_mem
      have h_eP_not_WB : eP ∉ W_B.events := by
        intro h_eP_WB
        have h_nsd := h_ok_B.2.2
        dsimp [NoSpawnDue] at h_nsd
        have h_e_out : stageEvent actTick groups gi ci (k + 1) ∉
            W_B.events :=
          h_nsd gi ci k h_gi h_ci h_k_mid
            (by
              have := congr_arg ScheduledEvent.targetTick h_eP_eq
              dsimp [stageEvent] at this
              rw [← this, h_eP_due, h_tick_log, h_tick_WB.symm])
            (h_eP_eq ▸ h_eP_WB)
        apply h_e_out
        rw [← h_e_eq']
        exact h_e_WB
      have h_k_ne0 : k ≠ 0 := by
        intro h_k0
        have h_pri0 : eP.priority = (0 : Int) := by
          have := congr_arg ScheduledEvent.priority h_eP_eq
          dsimp [stageEvent] at this
          rw [this, h_k0]
          dsimp [stagePri]
        have h_contra := gSimBurst_not_pop_larger_pri τ
          (buildGroups groups).2 withinOrd pos w_log active.zipIdx Dₘ eP
          (by dsimp [Dₘ, stageEvent]; rw [h_tgt₂, ← h_tick_log])
          h_eP_due
          (by rw [hD_pri, h_pri0]; omega)
          h_eP_log hD_WB
        exact h_eP_not_WB h_contra
      have h_k_ge : 1 ≤ k := by omega
      have h_pri_P : eP.priority = (-3 : Int) := by
        have := congr_arg ScheduledEvent.priority h_eP_eq
        dsimp [stageEvent] at this
        rw [this]
        exact stagePri_middle groups gi ci k h_k_ge h_k_mid
      have h_log_AP : evBefore (w_log.events.filter
          (fun ev => ev.targetTick == w_log.tick)) Aₘ eP :=
        due_evBefore_of_popSeq_evBefore w_log M Aₘ eP hA_pop h_eP_pop
          (by dsimp [Aₘ, stageEvent]; rw [h_tick_log]) h_eP_due
          (by rw [hA_pri, h_pri_P]) h_nodup_log h_AP
      have h_log_PD : evBefore (w_log.events.filter
          (fun ev => ev.targetTick == w_log.tick)) eP Dₘ := by
        have hP_log : eP ∈ w_log.events.filter
            (fun ev => ev.targetTick == w_log.tick) := by
          rw [List.mem_filter]
          exact ⟨h_eP_log, by rw [h_eP_due]; simp⟩
        have hD_log : Dₘ ∈ w_log.events.filter
            (fun ev => ev.targetTick == w_log.tick) := by
          rw [List.mem_filter]
          refine ⟨hD_mem_log, ?_⟩
          dsimp [Dₘ, stageEvent]
          rw [h_tgt₂, ← h_tick_log]
          simp
        have h_PD_ne : eP ≠ Dₘ := by
          intro h_eq
          exact h_eP_not_WB (h_eq.symm ▸ hD_WB)
        obtain h_fwd | h_rev := evBefore.total_of_nodup h_nodup_log hP_log
          hD_log h_PD_ne
        · exact h_fwd
        · exfalso
          have h_P_WB : eP ∈ W_B.events :=
            gSimBurst_not_pop_later_samePri τ (buildGroups groups).2
              withinOrd pos w_log active.zipIdx Dₘ eP
              (by dsimp [Dₘ, stageEvent]; rw [h_tgt₂, ← h_tick_log])
              h_eP_due
              (by rw [hD_pri, h_pri_P])
              h_nodup_log h_rev hD_mem_log hD_WB
          exact h_eP_not_WB h_P_WB
      exact ⟨gi, ci, k, h_gi, h_ci, h_k_mid, h_k_ge, h_k_tgt, h_e_eq',
        (by rwa [h_eP_eq] at h_log_AP), (by rwa [h_eP_eq] at h_log_PD)⟩
    · -- e is a drain spawn: trace it through the drain accumulator
      set n := (W_B.events.filter
        (fun ev => ev.targetTick == W_B.tick)).length
      set spawns := World.popSpawnAcc W_B n
      set survivors := W_B.events.filter
        (fun ev => ev.targetTick ≠ W_B.tick)
      have h_split_drain : W_B.stepUntilNextTick.events =
          survivors ++ spawns := by
        dsimp [survivors, spawns]
        exact stepUNT_filter_split' W_B
      have h_b_spawns : evBefore spawns e f₃ := by
        have h_b2_step : evBefore W_B.stepUntilNextTick.events e f₃ := by
          rwa [h_Q₁] at h_b2
        rw [h_split_drain] at h_b2_step
        rcases evBefore_append_split_right' h_b2_step with h_e_s | h_b
        · dsimp [survivors] at h_e_s
          exact absurd h_e_s (fun h_mem => h_e_WB (List.mem_filter.mp h_mem).1)
        · exact h_b
      have h_single_B := pops_single_spawn' groups actTick W_B n
        (fun ev h_ev _ => h_stage_WB ev h_ev)
      have h_uniqueD_B := pops_unique_spawn' groups actTick W_B n Dₘ f₃
        g₂ c₂ m h_g₂ h_c₂ (by omega) rfl (by dsimp [f₃])
        (fun ev h_ev _ => h_stage_WB ev h_ev)
      have h_f₃_acc : f₃ ∈ spawns := evBefore.mem_right h_b_spawns
      have hD_pop : Dₘ ∈ World.popSeqFuel W_B n := by
        obtain ⟨evD, h_evD, vD, sD', h_vD, h_layD, h_spD, h_sD'⟩ :=
          mem_popSpawnAcc_singleton_spawn groups W_B n f₃ h_layout_B
            h_single_B h_f₃_acc
        rwa [← h_uniqueD_B evD h_evD vD h_vD h_layD sD' h_spD h_sD'.symm]
      obtain ⟨eP, h_eP_pop, h_PD_pop, vP, h_vP_tick, h_vP_lay, h_eP_fire,
          h_eP_fresh⟩ :=
        popSpawnAcc_right_converse groups W_B n Dₘ f₃ e h_layout_B
          h_nd_due_WB hD_pop
          (by dsimp [Dₘ, stageEvent]; rw [h_tgt₂, ← h_tick_WB])
          h_sD_out
          (by
            dsimp [f₃, stageEvent]
            rw [h_tick_WB, ← h_tgt₂]
            exact stageTarget_lt_succ actTick groups g₂ c₂ m (by omega))
          (by
            intro v h_v h_lay
            simpa [f₃, Dₘ, stageEvent] using
              stage_spawn groups actTick v g₂ c₂ m h_g₂ h_c₂ (by omega)
                (h_v.trans (h_tick_WB.trans h_tgt₂.symm)) h_lay)
          h_single_B h_uniqueD_B h_e_WB h_ne_right h_b_spawns
      have h_eP_WB : eP ∈ W_B.events :=
        World.mem_popSeqFuel_mem_events W_B n eP h_eP_pop
      have h_eP_due : eP.targetTick = W_B.tick :=
        World.mem_popSeqFuel_due W_B n eP h_eP_pop
      obtain ⟨gi, ci, k, h_gi, h_ci, _, h_eP_eq, _, _⟩ :=
        h_stage_WB eP h_eP_WB
      have h_k_mid : k ≤ (chainAt groups gi ci).middleDelays.length := by
        by_contra h_last
        have h_last' :
            k = (chainAt groups gi ci).middleDelays.length + 1 := by omega
        have h_nil : (vP.onScheduledTick eP.nodeId).events =
            vP.events := by
          rw [h_eP_eq, h_last']
          exact lastStage_spawn_nil groups actTick vP gi ci h_gi h_ci
            h_vP_lay
        rw [h_nil] at h_eP_fire
        exact h_eP_fresh h_eP_fire
      have h_k_ne0 : k ≠ 0 := by
        intro h_k0
        have h_pri0 : eP.priority = (0 : Int) := by
          have := congr_arg ScheduledEvent.priority h_eP_eq
          dsimp [stageEvent] at this
          rw [this, h_k0]
          dsimp [stagePri]
        have h_le := popSeqFuel_priority_mono W_B n eP Dₘ h_PD_pop
        rw [h_pri0, hD_pri] at h_le
        omega
      have h_k_ge : 1 ≤ k := by omega
      have h_pri_P : eP.priority = (-3 : Int) := by
        have := congr_arg ScheduledEvent.priority h_eP_eq
        dsimp [stageEvent] at this
        rw [this]
        exact stagePri_middle groups gi ci k h_k_ge h_k_mid
      have h_k_tgt : (stageEvent actTick groups gi ci k).targetTick = τ := by
        have := congr_arg ScheduledEvent.targetTick h_eP_eq
        dsimp [stageEvent] at this
        dsimp [stageEvent]
        rw [← this, h_eP_due, h_tick_WB]
      have h_fire_P : (vP.onScheduledTick eP.nodeId).events =
          vP.events ++ [stageEvent actTick groups gi ci (k + 1)] := by
        rw [h_eP_eq]
        exact stage_spawn groups actTick vP gi ci k h_gi h_ci h_k_mid
          (by
            rw [h_vP_tick, ← h_eP_due]
            have := congr_arg ScheduledEvent.targetTick h_eP_eq
            dsimp [stageEvent] at this
            exact this)
          h_vP_lay
      have h_e_eq' : e = stageEvent actTick groups gi ci (k + 1) := by
        rw [h_fire_P] at h_eP_fire
        rcases List.mem_append.mp h_eP_fire with h_mem | h_mem
        · exact absurd h_mem h_eP_fresh
        · simpa using h_mem
      have h_PD_WB : evBefore (W_B.events.filter
          (fun ev => ev.targetTick == W_B.tick)) eP Dₘ :=
        due_evBefore_of_popSeq_evBefore W_B n eP Dₘ h_eP_pop hD_pop
          h_eP_due
          (by dsimp [Dₘ, stageEvent]; rw [h_tgt₂, ← h_tick_WB])
          (by rw [h_pri_P, hD_pri]) h_nd_due_WB h_PD_pop
      have h_PD_log : evBefore (w_log.events.filter
          (fun ev => ev.targetTick == w_log.tick)) eP Dₘ := by
        apply evBefore_due_gSimBurst_back τ (buildGroups groups).2
          withinOrd pos w_log active.zipIdx eP Dₘ h_eP_WB hD_WB
        · rw [h_eP_due, h_tick_WB, ← h_tick_log]
        · dsimp [Dₘ, stageEvent]
          rw [h_tgt₂, ← h_tick_log]
        · exact h_nodup_log
        · convert h_PD_WB using 1
          congr 1
          ext ev
          rw [h_tick_log, h_tick_WB.symm]
      have h_eP_log : eP ∈ w_log.events :=
        mem_gSimBurst_due_back τ (buildGroups groups).2 withinOrd pos
          w_log active.zipIdx eP h_eP_WB (by
            rw [h_eP_due, h_tick_WB, ← h_tick_log])
      have h_AP_log : evBefore (w_log.events.filter
          (fun ev => ev.targetTick == w_log.tick)) Aₘ eP := by
        have hA_log : Aₘ ∈ w_log.events.filter
            (fun ev => ev.targetTick == w_log.tick) := by
          rw [List.mem_filter]
          refine ⟨?_, ?_⟩
          · rw [World.logOutput_events]
            dsimp [wQ, Aₘ]
            exact stageEvent_mem_gSimWorld groups actTick groupOrd
              withinOrd pos h_valid h_ord h_within g₁ c₁ h_g₁ h_c₁ m
              (by omega)
          · dsimp [Aₘ, stageEvent]
            rw [h_tick_log]
            dsimp [τ]
            simp
        have hP_log : eP ∈ w_log.events.filter
            (fun ev => ev.targetTick == w_log.tick) := by
          rw [List.mem_filter]
          exact ⟨h_eP_log, by rw [h_eP_due, h_tick_WB, ← h_tick_log]; simp⟩
        have h_AeP_ne : Aₘ ≠ eP := by
          intro h_eq
          exact hA_not_WB (h_eq ▸ h_eP_WB)
        obtain h_fwd | h_rev := evBefore.total_of_nodup h_nodup_log hA_log
          hP_log h_AeP_ne
        · exact h_fwd
        · exfalso
          obtain ⟨l₁, l₂, h_split, hA_l₂⟩ := h_rev
          have hA_WB := gSimBurst_samePri_later_survives τ
            (buildGroups groups).2 withinOrd pos w_log active.zipIdx eP Aₘ
            h_eP_log (List.mem_filter.mp hA_log).1
            (by rw [h_eP_due, h_tick_WB, ← h_tick_log])
            (by dsimp [Aₘ, stageEvent]; rw [h_tick_log])
            (by rw [h_pri_P, hA_pri])
            h_nodup_log ⟨l₁, l₂, h_split, hA_l₂⟩ h_eP_WB
          exact hA_not_WB hA_WB
      exact ⟨gi, ci, k, h_gi, h_ci, h_k_mid, h_k_ge, h_k_tgt, h_e_eq',
        (by rwa [h_eP_eq] at h_AP_log), (by rwa [h_eP_eq] at h_PD_log)⟩
  obtain ⟨gi, ci, k, h_gi, h_ci, h_k_mid, h_k_ge, h_k_tgt, h_e_eq',
      h_AP_log, h_PD_log⟩ := h_case_data
  -- identify the parent chain with (gm, cm)
  obtain ⟨h_g_eq, h_c_eq, h_k_eq⟩ := stageEvent_injective actTick groups
    gi ci (k + 1) gm cm ((chainAt groups gm cm).middleDelays.length + 1)
    h_gi h_ci h_gm h_cm (by omega) (by omega) (by
      rw [← h_e_eq'])
  -- classify the parent via the MiddleBlockOkLastMiddleStage invariant on the due filter
  have h_mb_due : MiddleBlockOk groups actTick T
      (w_log.events.filter (fun ev => ev.targetTick == w_log.tick))
      g₁ c₁ g₂ c₂ m := by
    have h_eq : w_log.events.filter
        (fun ev => ev.targetTick == w_log.tick) =
        wQ.events.filter (fun ev => ev.targetTick == τ) := by
      rw [World.logOutput_events, h_tick_log]
    rw [h_eq]
    exact MiddleBlockOk_filter groups actTick T wQ.events τ g₁ c₁ g₂ c₂ m
      h_mb_full
  have h_mb_P : MiddleBlock groups actTick T g₁ c₁ m
      (stageEvent actTick groups gi ci k) :=
    h_mb_due (stageEvent actTick groups gi ci k) h_AP_log h_PD_log
      (by
        dsimp [stageEvent]
        exact stagePri_middle groups gi ci k h_k_ge h_k_mid)
      h_k_tgt
  rcases h_mb_P with h_fin | ⟨g', c', h_g', h_c', h_P_eq', _, _, h_pref⟩
  · have := IsFinalEvent_priority groups actTick T
      (stageEvent actTick groups gi ci k) h_fin
    dsimp [stageEvent] at this
    have := stagePri_middle groups gi ci k h_k_ge h_k_mid
    omega
  · have h_m_le' : m ≤ (chainAt groups g' c').middleDelays.length := by
      have h_p : stagePri groups g' c' m = (-3 : Int) := by
        have := congr_arg ScheduledEvent.priority h_P_eq'
        dsimp [stageEvent] at this
        rw [stagePri_middle groups gi ci k h_k_ge h_k_mid] at this
        exact this.symm
      dsimp only [stagePri] at h_p
      split_ifs at h_p <;> omega
    obtain ⟨h_gi_g', h_ci_c', h_k_m⟩ := stageEvent_injective actTick groups
      gi ci k g' c' m h_gi h_ci h_g' h_c' (by omega) (by omega) h_P_eq'
    have h_mlen₂_m : (chainAt groups gm cm).middleDelays.length = m := by
      omega
    have h_g'_gm : g' = gm := h_gi_g'.symm.trans h_g_eq
    have h_c'_cm : c' = cm := h_ci_c'.symm.trans h_c_eq
    have h_pref_gc : prefixDelays groups gm cm m =
        prefixDelays groups g₁ c₁ m := by
      rw [h_g'_gm, h_c'_cm] at h_pref
      exact h_pref
    refine ⟨gm, cm, h_gm, h_cm, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · omega
    · dsimp [e]
      congr 1
      omega
    · have h_take_l : prefixDelays groups gm cm (m + 1) =
          prefixDelays groups gm cm m := by
        dsimp [prefixDelays]
        rw [take_all_of_length_le _ _ (by omega), take_all_of_length_le _ _ (by omega)]
      have h_take_r : prefixDelays groups g₁ c₁ (m + 1) =
          prefixDelays groups g₁ c₁ m := by
        dsimp [prefixDelays]
        rw [take_all_of_length_le _ _ (by omega), take_all_of_length_le _ _ (by omega)]
      rw [h_take_l, h_take_r]
      exact h_pref_gc
    · have h_T_l : stageTarget actTick groups gm cm (m + 1) = T := by
        rw [← h_mlen₂_m]
        exact stageTarget_final_eq_T groups actTick T gm cm h_gm h_cm
          h_uniform h_act
      have h_T_r : stageTarget actTick groups g₁ c₁ (m + 1) = T := by
        rw [← h_m₁]
        exact stageTarget_final_eq_T groups actTick T g₁ c₁ h_g₁ h_c₁
          h_uniform h_act
      rw [h_T_l, h_T_r]
    · have h_AP := h_AP_log
      rw [World.logOutput_events, h_tick_log] at h_AP
      rw [h_g_eq, h_c_eq, h_k_m] at h_AP
      convert h_AP using 1
      dsimp [popQueueWorld, wQ]
      congr 1
      ext ev
      rw [gSimWorld_tick groups actTick groupOrd withinOrd pos
        (stageTarget actTick groups g₁ c₁ m)]
    · have h_PD := h_PD_log
      rw [World.logOutput_events, h_tick_log] at h_PD
      rw [h_g_eq, h_c_eq, h_k_m] at h_PD
      convert h_PD using 1
      dsimp [popQueueWorld, wQ]
      congr 1
      ext ev
      rw [gSimWorld_tick groups actTick groupOrd withinOrd pos
        (stageTarget actTick groups g₁ c₁ m)]
