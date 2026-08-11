import BasicProofs.GroupClustering.ConverseSpawnFinal
import BasicProofs.GroupClustering.ConverseSpawn

set_option linter.unusedVariables false

open BasicRedstoneSim List

/-! # Group clustering — the unconditional converse spawn at the final stage

This file proves the converse spawn-origin fact for priority -1 events
at the final stage. The middle-stage converse spawn theorem
(`converse_spawn_gSimBurst` of ConverseSpawn) accepts events with priority
-3. At the final stage the spawned events carry priority -1.

Take the pop tick of stage `m`, the last middle stage of the two
reference chains. The two reference stage-`m` events spawn the two
reference stage-`(m + 1)` events. Every event that sits between the
two spawns in the post-burst queue, carries priority -1, and targets
the output tick is the stage-`(m + 1)` event of some chain. The
stage-`m` event of that chain sits between the two reference
stage-`m` events in the due filter.

## Scope

* `converse_spawn_gSimBurst_final` — the unconditional converse
  spawn-origin fact for priority -1 events at the final stage.
* `FinalBlockBetween_converse` — every `FinalBlockBetween` event in
  the post-burst queue satisfies `Pri1FinalOf`.
* `Pri1FinalOf_of_between` — the main clustering property at the
  final stage: every priority-(-1) event between the two
  stage-`(m + 1)` anchors that targets the output tick satisfies
  `Pri1FinalOf`.

## Method

The proof mirrors the structure of `converse_spawn_gSimBurst` of
ConverseSpawn. The burst queue is drained with `processNEvents`, split into
survivors and the spawn accumulator, and the event is traced back to
its unique parent pop with `popSpawnAcc_left_converse` and
`popSpawnAcc_right_converse` of ConverseSpawn. The parent pops lie between
the two reference pops, so `popSeqFuel_priority_mono` forces the
parent priority to -3. The stage-`m` middle-block invariant then
classifies the parent. -/


/-! ## List and `evBefore` helpers

Reproved here because the ConverseSpawn versions are private. -/

/-- In a split `l ++ r = p ++ s` with `p` at least as long as `l`, the
    prefix `p` starts with `l`. -/
private theorem append_prefix_of_length_le {α : Type} (l r p s : List α)
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
private theorem mem_left_of_short_prefix_split {α : Type} (l r p q : List α)
    (x : α) (h_eq : l ++ r = p ++ x :: q) (h_lt : p.length < l.length) :
    x ∈ l := by
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
private theorem evBefore_append_left_absent {l r : List ScheduledEvent}
    {x y : ScheduledEvent} (h_x : x ∉ l) (h : evBefore (l ++ r) x y) :
    evBefore r x y := by
  obtain ⟨p, q, h_eq, h_y⟩ := h
  have h_len : l.length ≤ p.length := by
    by_contra h_lt
    exact h_x (mem_left_of_short_prefix_split l r p q x h_eq (by omega))
  obtain ⟨p₁, _, h_r⟩ := append_prefix_of_length_le l r p (x :: q) h_eq h_len
  exact ⟨p₁, q, h_r, h_y⟩

/-- With `y` absent from `l`, the split of `evBefore (l ++ r) x y` starts
    in `l` or lies in `r`. -/
private theorem evBefore_append_split_right {l r : List ScheduledEvent}
    {x y : ScheduledEvent} (h : evBefore (l ++ r) x y) :
    x ∈ l ∨ evBefore r x y := by
  obtain ⟨p, q, h_eq, h_yq⟩ := h
  by_cases h_lt : p.length < l.length
  · exact Or.inl (mem_left_of_short_prefix_split l r p q x h_eq h_lt)
  · obtain ⟨p₁, _, h_r⟩ :=
      append_prefix_of_length_le l r p (x :: q) h_eq (by omega)
    exact Or.inr ⟨p₁, q, h_r, h_yq⟩

/-- An `evBefore` witness against itself places two copies of the
    event. -/
private theorem evBefore_self_two_split {l : List ScheduledEvent}
    {x : ScheduledEvent} (h : evBefore l x x) :
    ∃ l₁ l₂ l₃, l = l₁ ++ x :: (l₂ ++ x :: l₃) := by
  obtain ⟨p, q, h_eq, h_x⟩ := h
  obtain ⟨p₂, q₂, h_q⟩ := mem_split_append q x h_x
  refine ⟨p, p₂, q₂, ?_⟩
  rw [h_eq, h_q]

/-- `(l₁ ++ l₂).drop l₁.length = l₂`. -/
private theorem drop_append_self {α : Type} (l₁ l₂ : List α) :
    (l₁ ++ l₂).drop l₁.length = l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a l ih => simp [ih]

/-- Append cancellation on the left. -/
private theorem append_left_cancel' {α : Type} (l l₁ l₂ : List α)
    (h : l ++ l₁ = l ++ l₂) : l₁ = l₂ := by
  induction l generalizing l₁ l₂ with
  | nil => simpa using h
  | cons a l ih =>
    simp only [List.cons_append] at h
    exact ih l₁ l₂ (by simpa using congrArg List.tail h)

/-- A filter is empty when no member satisfies the predicate. -/
private theorem filter_empty_of_none {α : Type} (p : α → Bool) (l : List α)
    (h : ∀ x ∈ l, p x = false) : l.filter p = [] := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp [List.filter, h x (List.mem_cons.mpr (Or.inl rfl)),
      ih (fun y hy => h y (List.mem_cons.mpr (Or.inr hy)))]

/-- A Nat inequality decides the `==` comparison to false. -/
private theorem nat_beq_false_of_ne (a b : Nat) (h : a ≠ b) :
    (a == b) = false := by
  simp [h]


/-! ## Spawn-accumulator congruence

Reproved here because the ConverseSpawn versions are private. -/

/-- `onScheduledTick` preserves equality of the node lists. -/
private theorem onScheduledTick_nodes_of_nodes_eq (w₁ w₂ : World)
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
private theorem popSpawnAcc_of_no_due (w : World) (fuel : Nat)
    (h_no : ∀ ev ∈ w.events, ev.targetTick ≠ w.tick) :
    World.popSpawnAcc w fuel = [] := by
  induction fuel with
  | zero => dsimp [World.popSpawnAcc]
  | succ fuel ih =>
    dsimp only [World.popSpawnAcc]
    rw [World.popNextEvent_none_of_no_due w h_no]

/-- The spawn accumulator splits over a fuel sum. -/
private theorem popSpawnAcc_concat (w : World) (a b : Nat) :
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
      rw [popSpawnAcc_of_no_due w (a + b + 1) h_no]
      have h_acc : World.popSpawnAcc w (a + 1) = [] := by
        dsimp [World.popSpawnAcc]
        simp only [h_pop]
      have h_world : World.popSeqWorldFuel w (a + 1) = w := by
        dsimp [World.popSeqWorldFuel]
        simp only [h_pop]
      rw [h_acc, h_world, List.nil_append]
      exact (popSpawnAcc_of_no_due w b h_no).symm
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
private theorem popSpawnAcc_congr (w₁ w₂ : World)
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
      -- both pops append the same spawn list
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
        rw [h_new₁, h_new₂, drop_append_self, drop_append_self]
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
          apply filter_empty_of_none
          intro e h_e
          have h_gt := h_fut₁ e h_e
          exact nat_beq_false_of_ne e.targetTick w_pop₁.tick (by omega)
        have h_nil₂ :
            new₂.filter (fun e => e.targetTick == w_pop₂.tick) = [] := by
          apply filter_empty_of_none
          intro e h_e
          have h_gt := h_fut₂ e h_e
          exact nat_beq_false_of_ne e.targetTick w_pop₂.tick (by omega)
        rw [h_nil₁, h_nil₂, List.append_nil, List.append_nil]
        exact popNextEvent_filter_eq w₁ w₂ h_tick h_filter ev₀ w_pop₁
          w_pop₂ h_pop₁ h_pop₂
      have h_nodes_v : v₁.nodes = v₂.nodes :=
        onScheduledTick_nodes_of_nodes_eq w_pop₁ w_pop₂ ev₀.nodeId
          h_nodes_pop
      rw [ih v₁ v₂ h_tick_v h_filter_v h_nodes_v]

/-- Filter the post-burst queue to the non-due events of priority other
    than 0. The result is the old filtered queue plus the filtered spawn
    accumulator of the popped due events. The observer batches drop out
    of the filter. They all carry priority 0. -/
private theorem gSimBurst_filter_split (t : Nat)
    (obsAll : List (List Nat)) (withinOrd pos : Nat → List Nat)
    (w : World) (pairs : List (Nat × Nat)) :
    ∃ M,
      ((gSimBurst t obsAll withinOrd pos w pairs).events.filter
          (fun ev => ev.targetTick ≠ w.tick)).filter
        (fun ev => ev.priority ≠ (0 : Int)) =
        (w.events.filter (fun ev => ev.targetTick ≠ w.tick)).filter
          (fun ev => ev.priority ≠ (0 : Int)) ++
        (World.popSpawnAcc w M).filter
          (fun ev => ev.priority ≠ (0 : Int)) := by
  set pPri : ScheduledEvent → Bool :=
    fun ev => decide (ev.priority ≠ (0 : Int))
  induction pairs generalizing w with
  | nil =>
    refine ⟨0, ?_⟩
    dsimp [gSimBurst, World.popSpawnAcc]
    simp [pPri]
  | cons p ps ih =>
    rcases p with ⟨gi, k⟩
    dsimp only [gSimBurst, List.foldl_cons]
    set m := (pos t)[k]?.getD 0
    set ordered : List Nat := (withinOrd gi).foldl (fun acc ci =>
      match (obsAll[gi]?.getD [])[ci]? with
      | some oid => acc ++ [oid]
      | none => acc) []
    set Wp := processNEvents w m
    set W₁ := activateGroup Wp ordered
    obtain ⟨M', h_ih⟩ := ih W₁
    have h_tick_Wp : Wp.tick = w.tick := by
      dsimp [Wp]
      exact processNEvents_tick w m
    have h_tick_W₁ : W₁.tick = w.tick := by
      dsimp [W₁]
      rw [activateGroup_tick, h_tick_Wp]
    rw [h_tick_W₁] at h_ih
    -- the observer events appended by `activateGroup`
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
        apply filter_empty_of_none
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
    -- the accumulator does not see the appended observer events
    have h_acc : World.popSpawnAcc W₁ M' = World.popSpawnAcc Wp M' := by
      refine popSpawnAcc_congr W₁ Wp ?_ ?_ (activateGroup_nodes Wp ordered) M'
      · dsimp [W₁]
        exact activateGroup_tick Wp ordered
      · dsimp [W₁]
        rw [activateGroup_tick Wp ordered]
        exact activateGroup_due_filter Wp ordered
    refine ⟨m + M', ?_⟩
    change ((gSimBurst t obsAll withinOrd pos W₁ ps).events.filter
        (fun ev => ev.targetTick ≠ w.tick)).filter pPri =
      (w.events.filter (fun ev => ev.targetTick ≠ w.tick)).filter pPri ++
        (World.popSpawnAcc w (m + M')).filter pPri
    rw [h_ih, h_W₁_filter, h_acc, h_Wp_filter]
    rw [List.append_assoc, ← List.filter_append]
    congr 1
    rw [popSpawnAcc_concat w m M']
    have h_tail : World.popSpawnAcc Wp M' =
        World.popSpawnAcc (World.popSeqWorldFuel w m) M' := by
      congr 1
      dsimp [Wp]
      exact processNEvents_eq_popSeqWorldFuel w m
    rw [h_tail]


/-! ## The converse at the spawn accumulator -/

/-- The core of the final-stage converse spawn-origin fact. The event
    sits between the two spawned reference events in the spawn
    accumulator of `n` pops. The reference spawns force the reference
    pops into the pop sequence. The proof traces the event back to its
    parent pop. The parent pops lie between the two reference pops, so
    the priority monotonicity of the pop sequence forces the parent
    priority to -3. The stage-`m` middle-block invariant then
    classifies the parent. -/
private theorem converse_spawn_popSpawnAcc_final (groups : List GroupSpec)
    (actTick : Nat → Nat) (T : Nat) (w : World) (g₁ c₁ g₂ c₂ m n : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_layout : NodeLayoutOk groups w)
    (h_m_ge : 1 ≤ m)
    (h_m₁ : (chainAt groups g₁ c₁).middleDelays.length = m)
    (h_m₂ : (chainAt groups g₂ c₂).middleDelays.length = m)
    (h_due : w.tick = stageTarget actTick groups g₁ c₁ m)
    (h_tgt₂ : stageTarget actTick groups g₂ c₂ m =
        stageTarget actTick groups g₁ c₁ m)
    (h_nodup : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup)
    (h_mb : MiddleBlockOk groups actTick T
        (w.events.filter (fun e => e.targetTick == w.tick)) g₁ c₁ g₂ c₂ m)
    (h_stage : StageMemAt groups actTick w w.tick)
    (h_sA_absent : stageEvent actTick groups g₁ c₁ (m + 1) ∉ w.events)
    (h_sD_absent : stageEvent actTick groups g₂ c₂ (m + 1) ∉ w.events)
    (e : ScheduledEvent)
    (h_e_absent : e ∉ w.events)
    (h_b_left : evBefore (World.popSpawnAcc w n)
        (stageEvent actTick groups g₁ c₁ (m + 1)) e)
    (h_b_right : evBefore (World.popSpawnAcc w n) e
        (stageEvent actTick groups g₂ c₂ (m + 1))) :
    ∃ g c, g < groups.length ∧ c < (groupAt groups g).length ∧
      e = stageEvent actTick groups g c (m + 1) ∧
      (stageEvent actTick groups g c m).priority = (-3 : Int) ∧
      MiddleBlock groups actTick T g₁ c₁ m (stageEvent actTick groups g c m) ∧
      evBefore (w.events.filter (fun ev => ev.targetTick == w.tick))
        (stageEvent actTick groups g₁ c₁ m)
        (stageEvent actTick groups g c m) ∧
      evBefore (w.events.filter (fun ev => ev.targetTick == w.tick))
        (stageEvent actTick groups g c m)
        (stageEvent actTick groups g₂ c₂ m) := by
  set A := stageEvent actTick groups g₁ c₁ m
  set D := stageEvent actTick groups g₂ c₂ m
  set sA := stageEvent actTick groups g₁ c₁ (m + 1)
  set sD := stageEvent actTick groups g₂ c₂ (m + 1)
  set due := w.events.filter (fun ev => ev.targetTick == w.tick)
  -- basic facts about the two reference events
  have hA_due : A.targetTick = w.tick := by
    dsimp [A, stageEvent]
    exact h_due.symm
  have hD_due : D.targetTick = w.tick := by
    dsimp [D, stageEvent]
    rw [h_tgt₂, h_due]
  have hA_pri : A.priority = (-3 : Int) := by
    dsimp [A, stageEvent]
    exact stagePri_middle groups g₁ c₁ m h_m_ge (by omega)
  have hD_pri : D.priority = (-3 : Int) := by
    dsimp [D, stageEvent]
    exact stagePri_middle groups g₂ c₂ m h_m_ge (by omega)
  have h_sA_gt : sA.targetTick > w.tick := by
    dsimp [sA, stageEvent]
    rw [h_due]
    exact stageTarget_lt_succ actTick groups g₁ c₁ m (by omega)
  have h_sD_gt : sD.targetTick > w.tick := by
    dsimp [sD, stageEvent]
    rw [h_due, ← h_tgt₂]
    exact stageTarget_lt_succ actTick groups g₂ c₂ m (by omega)
  have h_spawnA : ∀ (v : World), v.tick = w.tick → NodeLayoutOk groups v →
      (v.onScheduledTick A.nodeId).events = v.events ++ [sA] := by
    intro v h_v h_lay
    simpa [A, sA, stageEvent] using
      stage_spawn groups actTick v g₁ c₁ m h_g₁ h_c₁ (by omega)
        (h_v.trans h_due) h_lay
  have h_spawnD : ∀ (v : World), v.tick = w.tick → NodeLayoutOk groups v →
      (v.onScheduledTick D.nodeId).events = v.events ++ [sD] := by
    intro v h_v h_lay
    simpa [D, sD, stageEvent] using
      stage_spawn groups actTick v g₂ c₂ m h_g₂ h_c₂ (by omega)
        ((h_v.trans h_due).trans h_tgt₂.symm) h_lay
  -- every pop spawns at most one event
  have h_single : ∀ ev ∈ World.popSeqFuel w n, ∀ (v : World),
      v.tick = w.tick → NodeLayoutOk groups v →
      ∃ s, (v.onScheduledTick ev.nodeId).events = v.events ++ [s] ∨
        (v.onScheduledTick ev.nodeId).events = v.events := by
    intro ev h_ev v h_v h_lay
    have h_ev_w : ev ∈ w.events :=
      World.mem_popSeqFuel_mem_events w n ev h_ev
    obtain ⟨gi₀, ci₀, k₀, h_gi₀, h_ci₀, h_k₀, h_ev_eq₀, _, _⟩ :=
      h_stage ev h_ev_w
    by_cases h_last :
        k₀ = (chainAt groups gi₀ ci₀).middleDelays.length + 1
    · refine ⟨ev, Or.inr ?_⟩
      rw [h_ev_eq₀, h_last]
      exact lastStage_spawn_nil groups actTick v gi₀ ci₀ h_gi₀ h_ci₀ h_lay
    · refine ⟨stageEvent actTick groups gi₀ ci₀ (k₀ + 1), Or.inl ?_⟩
      have h_mid : k₀ ≤ (chainAt groups gi₀ ci₀).middleDelays.length := by
        omega
      have h_ev_due : ev.targetTick = w.tick :=
        World.mem_popSeqFuel_due w n ev h_ev
      have h_tick : v.tick = stageTarget actTick groups gi₀ ci₀ k₀ := by
        rw [h_v, ← h_ev_due]
        have := congr_arg ScheduledEvent.targetTick h_ev_eq₀
        dsimp [stageEvent] at this
        exact this
      rw [h_ev_eq₀]
      exact stage_spawn groups actTick v gi₀ ci₀ k₀ h_gi₀ h_ci₀ h_mid
        h_tick h_lay
  -- only A spawns sA
  have h_uniqueA : ∀ ev ∈ World.popSeqFuel w n, ∀ (v : World),
      v.tick = w.tick → NodeLayoutOk groups v → ∀ s,
      (v.onScheduledTick ev.nodeId).events = v.events ++ [s] →
      s = sA → ev = A := by
    intro ev h_ev v h_v h_lay s h_sp h_s
    have h_ev_w : ev ∈ w.events :=
      World.mem_popSeqFuel_mem_events w n ev h_ev
    obtain ⟨gi₀, ci₀, k₀, h_gi₀, h_ci₀, h_k₀, h_ev_eq₀, _, _⟩ :=
      h_stage ev h_ev_w
    by_cases h_last :
        k₀ = (chainAt groups gi₀ ci₀).middleDelays.length + 1
    · have h_nil : (v.onScheduledTick ev.nodeId).events = v.events := by
        rw [h_ev_eq₀, h_last]
        exact lastStage_spawn_nil groups actTick v gi₀ ci₀ h_gi₀ h_ci₀
          h_lay
      rw [h_nil] at h_sp
      have h_len := congrArg List.length h_sp
      simp at h_len
    · have h_mid : k₀ ≤ (chainAt groups gi₀ ci₀).middleDelays.length := by
        omega
      have h_ev_due : ev.targetTick = w.tick :=
        World.mem_popSeqFuel_due w n ev h_ev
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
      have h_inj := append_left_cancel' v.events
        [stageEvent actTick groups gi₀ ci₀ (k₀ + 1)] [s] h_sp
      injection h_inj with h_one
      rw [h_s] at h_one
      obtain ⟨h_g_eq, h_c_eq, _⟩ :=
        stageEvent_injective actTick groups gi₀ ci₀ (k₀ + 1) g₁ c₁ (m + 1)
          h_gi₀ h_ci₀ h_g₁ h_c₁ (by omega) (by omega) h_one
      rw [h_ev_eq₀, h_g_eq, h_c_eq]
      dsimp [A]
      congr 1
      omega
  -- only D spawns sD
  have h_uniqueD : ∀ ev ∈ World.popSeqFuel w n, ∀ (v : World),
      v.tick = w.tick → NodeLayoutOk groups v → ∀ s,
      (v.onScheduledTick ev.nodeId).events = v.events ++ [s] →
      s = sD → ev = D := by
    intro ev h_ev v h_v h_lay s h_sp h_s
    have h_ev_w : ev ∈ w.events :=
      World.mem_popSeqFuel_mem_events w n ev h_ev
    obtain ⟨gi₀, ci₀, k₀, h_gi₀, h_ci₀, h_k₀, h_ev_eq₀, _, _⟩ :=
      h_stage ev h_ev_w
    by_cases h_last :
        k₀ = (chainAt groups gi₀ ci₀).middleDelays.length + 1
    · have h_nil : (v.onScheduledTick ev.nodeId).events = v.events := by
        rw [h_ev_eq₀, h_last]
        exact lastStage_spawn_nil groups actTick v gi₀ ci₀ h_gi₀ h_ci₀
          h_lay
      rw [h_nil] at h_sp
      have h_len := congrArg List.length h_sp
      simp at h_len
    · have h_mid : k₀ ≤ (chainAt groups gi₀ ci₀).middleDelays.length := by
        omega
      have h_ev_due : ev.targetTick = w.tick :=
        World.mem_popSeqFuel_due w n ev h_ev
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
      have h_inj := append_left_cancel' v.events
        [stageEvent actTick groups gi₀ ci₀ (k₀ + 1)] [s] h_sp
      injection h_inj with h_one
      rw [h_s] at h_one
      obtain ⟨h_g_eq, h_c_eq, _⟩ :=
        stageEvent_injective actTick groups gi₀ ci₀ (k₀ + 1) g₂ c₂ (m + 1)
          h_gi₀ h_ci₀ h_g₂ h_c₂ (by omega) (by omega) h_one
      rw [h_ev_eq₀, h_g_eq, h_c_eq]
      dsimp [D]
      congr 1
      omega
  -- distinct pops spawn distinct events
  have h_distinct : ∀ ev₁ ∈ World.popSeqFuel w n,
      ∀ ev₂ ∈ World.popSeqFuel w n, ev₁ ≠ ev₂ →
      ∀ (v₁ v₂ : World), v₁.tick = w.tick → v₂.tick = w.tick →
      NodeLayoutOk groups v₁ → NodeLayoutOk groups v₂ →
      ∀ s₁ s₂, (v₁.onScheduledTick ev₁.nodeId).events = v₁.events ++ [s₁] →
      (v₂.onScheduledTick ev₂.nodeId).events = v₂.events ++ [s₂] →
      s₁ ≠ s₂ := by
    intro ev₁ h₁ ev₂ h₂ h_ne v₁ v₂ h_v₁ h_v₂ h_l₁ h_l₂ s₁ s₂ h_sp₁ h_sp₂
        h_s_eq
    obtain ⟨gi₁, ci₁, k₁, h_gi₁, h_ci₁, h_k₁, h_ev₁, _, _⟩ :=
      h_stage ev₁ (World.mem_popSeqFuel_mem_events w n ev₁ h₁)
    obtain ⟨gi₂, ci₂, k₂, h_gi₂, h_ci₂, h_k₂, h_ev₂, _, _⟩ :=
      h_stage ev₂ (World.mem_popSeqFuel_mem_events w n ev₂ h₂)
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
    have h_inj₁ := append_left_cancel' v₁.events
      [stageEvent actTick groups gi₁ ci₁ (k₁ + 1)] [s₁] h_sp₁
    have h_inj₂ := append_left_cancel' v₂.events
      [stageEvent actTick groups gi₂ ci₂ (k₂ + 1)] [s₂] h_sp₂
    injection h_inj₁ with h_s₁
    injection h_inj₂ with h_s₂
    rw [← h_s₁, ← h_s₂] at h_s_eq
    obtain ⟨h_g, h_c, h_k⟩ := stageEvent_injective actTick groups gi₁ ci₁
      (k₁ + 1) gi₂ ci₂ (k₂ + 1) h_gi₁ h_ci₁ h_gi₂ h_ci₂ (by omega)
      (by omega) h_s_eq
    rw [h_ev₁, h_ev₂, h_g, h_c] at h_ne
    exact h_ne (by congr 1; omega)
  -- the reference spawns force the reference pops into the pop sequence
  have hA_pop : A ∈ World.popSeqFuel w n := by
    have h_sA_acc : sA ∈ World.popSpawnAcc w n := evBefore.mem_left h_b_left
    obtain ⟨ev, h_ev, v, s, h_v, h_lay, h_sp, h_s⟩ :=
      mem_popSpawnAcc_singleton_spawn groups w n sA h_layout h_single
        h_sA_acc
    have h_ev_A : ev = A :=
      h_uniqueA ev h_ev v h_v h_lay s h_sp h_s.symm
    rwa [← h_ev_A]
  have hD_pop : D ∈ World.popSeqFuel w n := by
    have h_sD_acc : sD ∈ World.popSpawnAcc w n :=
      evBefore.mem_right h_b_right
    obtain ⟨ev, h_ev, v, s, h_v, h_lay, h_sp, h_s⟩ :=
      mem_popSpawnAcc_singleton_spawn groups w n sD h_layout h_single
        h_sD_acc
    have h_ev_D : ev = D :=
      h_uniqueD ev h_ev v h_v h_lay s h_sp h_s.symm
    rwa [← h_ev_D]
  -- the accumulator is duplicate-free, and e differs from sA and sD
  have h_acc_nd : (World.popSpawnAcc w n).Nodup :=
    popSpawnAcc_nodup groups w n h_layout h_nodup h_single h_distinct
  have h_e_ne_sA : e ≠ sA := by
    intro h_eq
    rw [h_eq] at h_b_left
    obtain ⟨l₁, l₂, l₃, h_two⟩ := evBefore_self_two_split h_b_left
    exact nodup_cons_append_not_mem (h_two ▸ h_acc_nd)
      (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
  have h_e_ne_sD : e ≠ sD := by
    intro h_eq
    rw [h_eq] at h_b_right
    obtain ⟨l₁, l₂, l₃, h_two⟩ := evBefore_self_two_split h_b_right
    exact nodup_cons_append_not_mem (h_two ▸ h_acc_nd)
      (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
  -- trace e back to its parent pops on both sides
  obtain ⟨eL, h_eL_pop, h_AeL, vL, h_vL_tick, h_vL_lay, h_eL_fire,
      h_eL_fresh⟩ :=
    popSpawnAcc_left_converse groups w n A sA e h_layout h_nodup hA_pop
      hA_due h_sA_absent h_sA_gt h_spawnA h_single h_uniqueA h_distinct
      h_e_absent h_e_ne_sA h_b_left
  obtain ⟨eR, h_eR_pop, h_eRD, vR, h_vR_tick, h_vR_lay, h_eR_fire,
      h_eR_fresh⟩ :=
    popSpawnAcc_right_converse groups w n D sD e h_layout h_nodup hD_pop
      hD_due h_sD_absent h_sD_gt h_spawnD h_single h_uniqueD
      h_e_absent h_e_ne_sD h_b_right
  -- decode the right parent: it is a middle-stage event
  have h_eR_w : eR ∈ w.events :=
    World.mem_popSeqFuel_mem_events w n eR h_eR_pop
  obtain ⟨gi, ci, k, h_gi, h_ci, h_k_le, h_eR_eq, _, _⟩ :=
    h_stage eR h_eR_w
  have h_eR_due : eR.targetTick = w.tick :=
    World.mem_popSeqFuel_due w n eR h_eR_pop
  have h_k_mid : k ≤ (chainAt groups gi ci).middleDelays.length := by
    by_contra h_last
    have h_last' :
        k = (chainAt groups gi ci).middleDelays.length + 1 := by omega
    have h_nil : (vR.onScheduledTick eR.nodeId).events = vR.events := by
      rw [h_eR_eq, h_last']
      exact lastStage_spawn_nil groups actTick vR gi ci h_gi h_ci h_vR_lay
    rw [h_nil] at h_eR_fire
    exact h_eR_fresh h_eR_fire
  have h_tick_R : vR.tick = stageTarget actTick groups gi ci k := by
    rw [h_vR_tick, ← h_eR_due]
    have := congr_arg ScheduledEvent.targetTick h_eR_eq
    dsimp [stageEvent] at this
    exact this
  have h_fire_R : (vR.onScheduledTick eR.nodeId).events =
      vR.events ++ [stageEvent actTick groups gi ci (k + 1)] := by
    rw [h_eR_eq]
    exact stage_spawn groups actTick vR gi ci k h_gi h_ci h_k_mid h_tick_R
      h_vR_lay
  have h_e_eq : e = stageEvent actTick groups gi ci (k + 1) := by
    rw [h_fire_R] at h_eR_fire
    rcases List.mem_append.mp h_eR_fire with h_mem | h_mem
    · exact absurd h_mem h_eR_fresh
    · simpa using h_mem
  -- decode the left parent and identify it with the right parent
  have h_eL_w : eL ∈ w.events :=
    World.mem_popSeqFuel_mem_events w n eL h_eL_pop
  obtain ⟨gi', ci', k', h_gi', h_ci', h_k_le', h_eL_eq, _, _⟩ :=
    h_stage eL h_eL_w
  have h_parent_eq : eL = eR := by
    by_cases h_k'_last :
        k' = (chainAt groups gi' ci').middleDelays.length + 1
    · have h_nil : (vL.onScheduledTick eL.nodeId).events = vL.events := by
        rw [h_eL_eq, h_k'_last]
        exact lastStage_spawn_nil groups actTick vL gi' ci' h_gi' h_ci'
          h_vL_lay
      rw [h_nil] at h_eL_fire
      exact absurd h_eL_fire h_eL_fresh
    · have h_k'_mid : k' ≤ (chainAt groups gi' ci').middleDelays.length := by
        omega
      have h_eL_due : eL.targetTick = w.tick :=
        World.mem_popSeqFuel_due w n eL h_eL_pop
      have h_tick_L : vL.tick = stageTarget actTick groups gi' ci' k' := by
        rw [h_vL_tick, ← h_eL_due]
        have := congr_arg ScheduledEvent.targetTick h_eL_eq
        dsimp [stageEvent] at this
        exact this
      have h_fire_L : (vL.onScheduledTick eL.nodeId).events =
          vL.events ++ [stageEvent actTick groups gi' ci' (k' + 1)] := by
        rw [h_eL_eq]
        exact stage_spawn groups actTick vL gi' ci' k' h_gi' h_ci' h_k'_mid
          h_tick_L h_vL_lay
      have h_e_eq_L : e = stageEvent actTick groups gi' ci' (k' + 1) := by
        rw [h_fire_L] at h_eL_fire
        rcases List.mem_append.mp h_eL_fire with h_mem | h_mem
        · exact absurd h_mem h_eL_fresh
        · simpa using h_mem
      obtain ⟨h_g_eq, h_c_eq, _⟩ :=
        stageEvent_injective actTick groups gi' ci' (k' + 1) gi ci (k + 1)
          h_gi' h_ci' h_gi h_ci (by omega) (by omega)
          (h_e_eq_L.symm.trans h_e_eq)
      rw [h_eL_eq, h_eR_eq, h_g_eq, h_c_eq]
      congr 1
      omega
  have h_AeR : evBefore (World.popSeqFuel w n) A eR := by
    rwa [← h_parent_eq]
  -- the parent carries the middle priority
  have h_pri_eR : eR.priority = (-3 : Int) := by
    have h_le₁ : A.priority ≤ eR.priority :=
      popSeqFuel_priority_mono w n A eR h_AeR
    have h_le₂ : eR.priority ≤ D.priority :=
      popSeqFuel_priority_mono w n eR D h_eRD
    rw [hA_pri] at h_le₁
    rw [hD_pri] at h_le₂
    omega
  -- transfer the pop order to the due-filter order
  have h_due_AeR : evBefore due A eR :=
    due_evBefore_of_popSeq_evBefore w n A eR hA_pop h_eR_pop hA_due
      h_eR_due (by rw [hA_pri, h_pri_eR]) h_nodup h_AeR
  have h_due_eRD : evBefore due eR D :=
    due_evBefore_of_popSeq_evBefore w n eR D h_eR_pop hD_pop h_eR_due
      hD_due (by rw [h_pri_eR, hD_pri]) h_nodup h_eRD
  -- the stage-m middle-block invariant classifies the parent
  have h_mb_eR : MiddleBlock groups actTick T g₁ c₁ m eR :=
    h_mb eR h_due_AeR h_due_eRD h_pri_eR (h_eR_due.trans h_due)
  rcases h_mb_eR with h_fin | h_mid
  · exfalso
    exact IsFinalEvent_priority_ne_middle groups actTick T eR h_fin h_pri_eR
  · obtain ⟨g, c, h_g, h_c, h_ev_eq, h_mb_pri, h_mb_tgt, h_mb_pref⟩ := h_mid
    have h_mb_pri' : stagePri groups g c m = (-3 : Int) := by
      have h := congr_arg ScheduledEvent.priority h_ev_eq
      dsimp [stageEvent] at h
      rw [h_mb_pri] at h
      exact h.symm
    have h_m_bound : m ≤ (chainAt groups g c).middleDelays.length + 1 := by
      dsimp only [stagePri] at h_mb_pri'
      split_ifs at h_mb_pri' <;> omega
    obtain ⟨h_g_eq, h_c_eq, _⟩ :=
      stageEvent_injective actTick groups g c m gi ci k h_g h_c h_gi h_ci
        h_m_bound (by omega) (h_ev_eq.symm.trans h_eR_eq)
    refine ⟨g, c, h_g, h_c, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h_e_eq, h_g_eq, h_c_eq]
      congr 1
      omega
    · rw [← h_ev_eq]
      exact h_mb_pri
    · rw [← h_ev_eq]
      exact Or.inr ⟨g, c, h_g, h_c, h_ev_eq, h_mb_pri, h_mb_tgt, h_mb_pref⟩
    · rw [← h_ev_eq]
      exact h_due_AeR
    · rw [← h_ev_eq]
      exact h_due_eRD


/-! ## The m = 0 case

The converse spawn theorem above requires `1 ≤ m`: the two reference
stage-`m` events carry priority -3, and the priority squeeze between
their pops forces the parent of any intervening spawn to priority -3
as well, after which the middle-block invariant classifies it.

When `m = 0` the reference chains have no middle delays. Their
stage-`0` events are observer events carrying priority 0, and the
middle-block invariant does not apply at stage 0. The priority
squeeze still works: the pops between two priority-0 pops carry
priority 0, so the parent is a stage-`0` event of some chain. The
spawn is that chain's stage-`1` event; the spawn's priority -1
forces the witness chain to have no middle delays. -/

private theorem converse_spawn_popSpawnAcc_final_m0
    (groups : List GroupSpec)
    (actTick : Nat → Nat) (T : Nat) (w : World) (g₁ c₁ g₂ c₂ n : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_layout : NodeLayoutOk groups w)
    (h_m₁ : (chainAt groups g₁ c₁).middleDelays.length = 0)
    (h_m₂ : (chainAt groups g₂ c₂).middleDelays.length = 0)
    (h_due : w.tick = stageTarget actTick groups g₁ c₁ 0)
    (h_tgt₂ : stageTarget actTick groups g₂ c₂ 0 =
        stageTarget actTick groups g₁ c₁ 0)
    (h_nodup : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup)
    (h_stage : StageMemAt groups actTick w w.tick)
    (h_sA_absent : stageEvent actTick groups g₁ c₁ 1 ∉ w.events)
    (h_sD_absent : stageEvent actTick groups g₂ c₂ 1 ∉ w.events)
    (e : ScheduledEvent)
    (h_e_absent : e ∉ w.events)
    (h_pri : e.priority = (-1 : Int))
    (h_b_left : evBefore (World.popSpawnAcc w n)
        (stageEvent actTick groups g₁ c₁ 1) e)
    (h_b_right : evBefore (World.popSpawnAcc w n) e
        (stageEvent actTick groups g₂ c₂ 1)) :
    ∃ g c, g < groups.length ∧ c < (groupAt groups g).length ∧
      e = stageEvent actTick groups g c 1 ∧
      (chainAt groups g c).middleDelays.length = 0 ∧
      evBefore (w.events.filter (fun ev => ev.targetTick == w.tick))
        (stageEvent actTick groups g₁ c₁ 0)
        (stageEvent actTick groups g c 0) ∧
      evBefore (w.events.filter (fun ev => ev.targetTick == w.tick))
        (stageEvent actTick groups g c 0)
        (stageEvent actTick groups g₂ c₂ 0) := by
  set A := stageEvent actTick groups g₁ c₁ 0
  set D := stageEvent actTick groups g₂ c₂ 0
  set sA := stageEvent actTick groups g₁ c₁ 1
  set sD := stageEvent actTick groups g₂ c₂ 1
  set due := w.events.filter (fun ev => ev.targetTick == w.tick)
  -- basic facts about the two reference events
  have hA_due : A.targetTick = w.tick := by
    dsimp [A, stageEvent]
    exact h_due.symm
  have hD_due : D.targetTick = w.tick := by
    dsimp [D, stageEvent]
    rw [h_tgt₂, h_due]
  have hA_pri : A.priority = (0 : Int) := by
    dsimp [A, stageEvent, stagePri]
  have hD_pri : D.priority = (0 : Int) := by
    dsimp [D, stageEvent, stagePri]
  have h_sA_gt : sA.targetTick > w.tick := by
    dsimp [sA, stageEvent]
    rw [h_due]
    exact stageTarget_lt_succ actTick groups g₁ c₁ 0 (by omega)
  have h_sD_gt : sD.targetTick > w.tick := by
    dsimp [sD, stageEvent]
    rw [h_due, ← h_tgt₂]
    exact stageTarget_lt_succ actTick groups g₂ c₂ 0 (by omega)
  have h_spawnA : ∀ (v : World), v.tick = w.tick → NodeLayoutOk groups v →
      (v.onScheduledTick A.nodeId).events = v.events ++ [sA] := by
    intro v h_v h_lay
    simpa [A, sA, stageEvent] using
      stage_spawn groups actTick v g₁ c₁ 0 h_g₁ h_c₁ (by omega)
        (h_v.trans h_due) h_lay
  have h_spawnD : ∀ (v : World), v.tick = w.tick → NodeLayoutOk groups v →
      (v.onScheduledTick D.nodeId).events = v.events ++ [sD] := by
    intro v h_v h_lay
    simpa [D, sD, stageEvent] using
      stage_spawn groups actTick v g₂ c₂ 0 h_g₂ h_c₂ (by omega)
        ((h_v.trans h_due).trans h_tgt₂.symm) h_lay
  -- every pop spawns at most one event
  have h_single : ∀ ev ∈ World.popSeqFuel w n, ∀ (v : World),
      v.tick = w.tick → NodeLayoutOk groups v →
      ∃ s, (v.onScheduledTick ev.nodeId).events = v.events ++ [s] ∨
        (v.onScheduledTick ev.nodeId).events = v.events := by
    intro ev h_ev v h_v h_lay
    have h_ev_w : ev ∈ w.events :=
      World.mem_popSeqFuel_mem_events w n ev h_ev
    obtain ⟨gi₀, ci₀, k₀, h_gi₀, h_ci₀, h_k₀, h_ev_eq₀, _, _⟩ :=
      h_stage ev h_ev_w
    by_cases h_last :
        k₀ = (chainAt groups gi₀ ci₀).middleDelays.length + 1
    · refine ⟨ev, Or.inr ?_⟩
      rw [h_ev_eq₀, h_last]
      exact lastStage_spawn_nil groups actTick v gi₀ ci₀ h_gi₀ h_ci₀ h_lay
    · refine ⟨stageEvent actTick groups gi₀ ci₀ (k₀ + 1), Or.inl ?_⟩
      have h_mid : k₀ ≤ (chainAt groups gi₀ ci₀).middleDelays.length := by
        omega
      have h_ev_due : ev.targetTick = w.tick :=
        World.mem_popSeqFuel_due w n ev h_ev
      have h_tick : v.tick = stageTarget actTick groups gi₀ ci₀ k₀ := by
        rw [h_v, ← h_ev_due]
        have := congr_arg ScheduledEvent.targetTick h_ev_eq₀
        dsimp [stageEvent] at this
        exact this
      rw [h_ev_eq₀]
      exact stage_spawn groups actTick v gi₀ ci₀ k₀ h_gi₀ h_ci₀ h_mid
        h_tick h_lay
  -- only A spawns sA
  have h_uniqueA : ∀ ev ∈ World.popSeqFuel w n, ∀ (v : World),
      v.tick = w.tick → NodeLayoutOk groups v → ∀ s,
      (v.onScheduledTick ev.nodeId).events = v.events ++ [s] →
      s = sA → ev = A := by
    intro ev h_ev v h_v h_lay s h_sp h_s
    have h_ev_w : ev ∈ w.events :=
      World.mem_popSeqFuel_mem_events w n ev h_ev
    obtain ⟨gi₀, ci₀, k₀, h_gi₀, h_ci₀, h_k₀, h_ev_eq₀, _, _⟩ :=
      h_stage ev h_ev_w
    by_cases h_last :
        k₀ = (chainAt groups gi₀ ci₀).middleDelays.length + 1
    · have h_nil : (v.onScheduledTick ev.nodeId).events = v.events := by
        rw [h_ev_eq₀, h_last]
        exact lastStage_spawn_nil groups actTick v gi₀ ci₀ h_gi₀ h_ci₀
          h_lay
      rw [h_nil] at h_sp
      have h_len := congrArg List.length h_sp
      simp at h_len
    · have h_mid : k₀ ≤ (chainAt groups gi₀ ci₀).middleDelays.length := by
        omega
      have h_ev_due : ev.targetTick = w.tick :=
        World.mem_popSeqFuel_due w n ev h_ev
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
      have h_inj := append_left_cancel' v.events
        [stageEvent actTick groups gi₀ ci₀ (k₀ + 1)] [s] h_sp
      injection h_inj with h_one
      rw [h_s] at h_one
      obtain ⟨h_g_eq, h_c_eq, _⟩ :=
        stageEvent_injective actTick groups gi₀ ci₀ (k₀ + 1) g₁ c₁ 1
          h_gi₀ h_ci₀ h_g₁ h_c₁ (by omega) (by omega) h_one
      rw [h_ev_eq₀, h_g_eq, h_c_eq]
      dsimp [A]
      congr 1
      omega
  -- only D spawns sD
  have h_uniqueD : ∀ ev ∈ World.popSeqFuel w n, ∀ (v : World),
      v.tick = w.tick → NodeLayoutOk groups v → ∀ s,
      (v.onScheduledTick ev.nodeId).events = v.events ++ [s] →
      s = sD → ev = D := by
    intro ev h_ev v h_v h_lay s h_sp h_s
    have h_ev_w : ev ∈ w.events :=
      World.mem_popSeqFuel_mem_events w n ev h_ev
    obtain ⟨gi₀, ci₀, k₀, h_gi₀, h_ci₀, h_k₀, h_ev_eq₀, _, _⟩ :=
      h_stage ev h_ev_w
    by_cases h_last :
        k₀ = (chainAt groups gi₀ ci₀).middleDelays.length + 1
    · have h_nil : (v.onScheduledTick ev.nodeId).events = v.events := by
        rw [h_ev_eq₀, h_last]
        exact lastStage_spawn_nil groups actTick v gi₀ ci₀ h_gi₀ h_ci₀
          h_lay
      rw [h_nil] at h_sp
      have h_len := congrArg List.length h_sp
      simp at h_len
    · have h_mid : k₀ ≤ (chainAt groups gi₀ ci₀).middleDelays.length := by
        omega
      have h_ev_due : ev.targetTick = w.tick :=
        World.mem_popSeqFuel_due w n ev h_ev
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
      have h_inj := append_left_cancel' v.events
        [stageEvent actTick groups gi₀ ci₀ (k₀ + 1)] [s] h_sp
      injection h_inj with h_one
      rw [h_s] at h_one
      obtain ⟨h_g_eq, h_c_eq, _⟩ :=
        stageEvent_injective actTick groups gi₀ ci₀ (k₀ + 1) g₂ c₂ 1
          h_gi₀ h_ci₀ h_g₂ h_c₂ (by omega) (by omega) h_one
      rw [h_ev_eq₀, h_g_eq, h_c_eq]
      dsimp [D]
      congr 1
      omega
  -- distinct pops spawn distinct events
  have h_distinct : ∀ ev₁ ∈ World.popSeqFuel w n,
      ∀ ev₂ ∈ World.popSeqFuel w n, ev₁ ≠ ev₂ →
      ∀ (v₁ v₂ : World), v₁.tick = w.tick → v₂.tick = w.tick →
      NodeLayoutOk groups v₁ → NodeLayoutOk groups v₂ →
      ∀ s₁ s₂, (v₁.onScheduledTick ev₁.nodeId).events = v₁.events ++ [s₁] →
      (v₂.onScheduledTick ev₂.nodeId).events = v₂.events ++ [s₂] →
      s₁ ≠ s₂ := by
    intro ev₁ h₁ ev₂ h₂ h_ne v₁ v₂ h_v₁ h_v₂ h_l₁ h_l₂ s₁ s₂ h_sp₁ h_sp₂
        h_s_eq
    obtain ⟨gi₁, ci₁, k₁, h_gi₁, h_ci₁, h_k₁, h_ev₁, _, _⟩ :=
      h_stage ev₁ (World.mem_popSeqFuel_mem_events w n ev₁ h₁)
    obtain ⟨gi₂, ci₂, k₂, h_gi₂, h_ci₂, h_k₂, h_ev₂, _, _⟩ :=
      h_stage ev₂ (World.mem_popSeqFuel_mem_events w n ev₂ h₂)
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
    have h_inj₁ := append_left_cancel' v₁.events
      [stageEvent actTick groups gi₁ ci₁ (k₁ + 1)] [s₁] h_sp₁
    have h_inj₂ := append_left_cancel' v₂.events
      [stageEvent actTick groups gi₂ ci₂ (k₂ + 1)] [s₂] h_sp₂
    injection h_inj₁ with h_s₁
    injection h_inj₂ with h_s₂
    rw [← h_s₁, ← h_s₂] at h_s_eq
    obtain ⟨h_g, h_c, h_k⟩ := stageEvent_injective actTick groups gi₁ ci₁
      (k₁ + 1) gi₂ ci₂ (k₂ + 1) h_gi₁ h_ci₁ h_gi₂ h_ci₂ (by omega)
      (by omega) h_s_eq
    rw [h_ev₁, h_ev₂, h_g, h_c] at h_ne
    exact h_ne (by congr 1; omega)
  -- the reference spawns force the reference pops into the pop sequence
  have hA_pop : A ∈ World.popSeqFuel w n := by
    have h_sA_acc : sA ∈ World.popSpawnAcc w n := evBefore.mem_left h_b_left
    obtain ⟨ev, h_ev, v, s, h_v, h_lay, h_sp, h_s⟩ :=
      mem_popSpawnAcc_singleton_spawn groups w n sA h_layout h_single
        h_sA_acc
    have h_ev_A : ev = A :=
      h_uniqueA ev h_ev v h_v h_lay s h_sp h_s.symm
    rwa [← h_ev_A]
  have hD_pop : D ∈ World.popSeqFuel w n := by
    have h_sD_acc : sD ∈ World.popSpawnAcc w n :=
      evBefore.mem_right h_b_right
    obtain ⟨ev, h_ev, v, s, h_v, h_lay, h_sp, h_s⟩ :=
      mem_popSpawnAcc_singleton_spawn groups w n sD h_layout h_single
        h_sD_acc
    have h_ev_D : ev = D :=
      h_uniqueD ev h_ev v h_v h_lay s h_sp h_s.symm
    rwa [← h_ev_D]
  -- the accumulator is duplicate-free, and e differs from sA and sD
  have h_acc_nd : (World.popSpawnAcc w n).Nodup :=
    popSpawnAcc_nodup groups w n h_layout h_nodup h_single h_distinct
  have h_e_ne_sA : e ≠ sA := by
    intro h_eq
    rw [h_eq] at h_b_left
    obtain ⟨l₁, l₂, l₃, h_two⟩ := evBefore_self_two_split h_b_left
    exact nodup_cons_append_not_mem (h_two ▸ h_acc_nd)
      (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
  have h_e_ne_sD : e ≠ sD := by
    intro h_eq
    rw [h_eq] at h_b_right
    obtain ⟨l₁, l₂, l₃, h_two⟩ := evBefore_self_two_split h_b_right
    exact nodup_cons_append_not_mem (h_two ▸ h_acc_nd)
      (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
  -- trace e back to its parent pops on both sides
  obtain ⟨eL, h_eL_pop, h_AeL, vL, h_vL_tick, h_vL_lay, h_eL_fire,
      h_eL_fresh⟩ :=
    popSpawnAcc_left_converse groups w n A sA e h_layout h_nodup hA_pop
      hA_due h_sA_absent h_sA_gt h_spawnA h_single h_uniqueA h_distinct
      h_e_absent h_e_ne_sA h_b_left
  obtain ⟨eR, h_eR_pop, h_eRD, vR, h_vR_tick, h_vR_lay, h_eR_fire,
      h_eR_fresh⟩ :=
    popSpawnAcc_right_converse groups w n D sD e h_layout h_nodup hD_pop
      hD_due h_sD_absent h_sD_gt h_spawnD h_single h_uniqueD
      h_e_absent h_e_ne_sD h_b_right
  -- decode the right parent: it is a non-final stage event
  have h_eR_w : eR ∈ w.events :=
    World.mem_popSeqFuel_mem_events w n eR h_eR_pop
  obtain ⟨gi, ci, k, h_gi, h_ci, h_k_le, h_eR_eq, _, _⟩ :=
    h_stage eR h_eR_w
  have h_eR_due : eR.targetTick = w.tick :=
    World.mem_popSeqFuel_due w n eR h_eR_pop
  have h_k_mid : k ≤ (chainAt groups gi ci).middleDelays.length := by
    by_contra h_last
    have h_last' :
        k = (chainAt groups gi ci).middleDelays.length + 1 := by omega
    have h_nil : (vR.onScheduledTick eR.nodeId).events = vR.events := by
      rw [h_eR_eq, h_last']
      exact lastStage_spawn_nil groups actTick vR gi ci h_gi h_ci h_vR_lay
    rw [h_nil] at h_eR_fire
    exact h_eR_fresh h_eR_fire
  have h_tick_R : vR.tick = stageTarget actTick groups gi ci k := by
    rw [h_vR_tick, ← h_eR_due]
    have := congr_arg ScheduledEvent.targetTick h_eR_eq
    dsimp [stageEvent] at this
    exact this
  have h_fire_R : (vR.onScheduledTick eR.nodeId).events =
      vR.events ++ [stageEvent actTick groups gi ci (k + 1)] := by
    rw [h_eR_eq]
    exact stage_spawn groups actTick vR gi ci k h_gi h_ci h_k_mid h_tick_R
      h_vR_lay
  have h_e_eq : e = stageEvent actTick groups gi ci (k + 1) := by
    rw [h_fire_R] at h_eR_fire
    rcases List.mem_append.mp h_eR_fire with h_mem | h_mem
    · exact absurd h_mem h_eR_fresh
    · simpa using h_mem
  -- decode the left parent and identify it with the right parent
  have h_eL_w : eL ∈ w.events :=
    World.mem_popSeqFuel_mem_events w n eL h_eL_pop
  obtain ⟨gi', ci', k', h_gi', h_ci', h_k_le', h_eL_eq, _, _⟩ :=
    h_stage eL h_eL_w
  have h_parent_eq : eL = eR := by
    by_cases h_k'_last :
        k' = (chainAt groups gi' ci').middleDelays.length + 1
    · have h_nil : (vL.onScheduledTick eL.nodeId).events = vL.events := by
        rw [h_eL_eq, h_k'_last]
        exact lastStage_spawn_nil groups actTick vL gi' ci' h_gi' h_ci'
          h_vL_lay
      rw [h_nil] at h_eL_fire
      exact absurd h_eL_fire h_eL_fresh
    · have h_k'_mid : k' ≤ (chainAt groups gi' ci').middleDelays.length := by
        omega
      have h_eL_due : eL.targetTick = w.tick :=
        World.mem_popSeqFuel_due w n eL h_eL_pop
      have h_tick_L : vL.tick = stageTarget actTick groups gi' ci' k' := by
        rw [h_vL_tick, ← h_eL_due]
        have := congr_arg ScheduledEvent.targetTick h_eL_eq
        dsimp [stageEvent] at this
        exact this
      have h_fire_L : (vL.onScheduledTick eL.nodeId).events =
          vL.events ++ [stageEvent actTick groups gi' ci' (k' + 1)] := by
        rw [h_eL_eq]
        exact stage_spawn groups actTick vL gi' ci' k' h_gi' h_ci' h_k'_mid
          h_tick_L h_vL_lay
      have h_e_eq_L : e = stageEvent actTick groups gi' ci' (k' + 1) := by
        rw [h_fire_L] at h_eL_fire
        rcases List.mem_append.mp h_eL_fire with h_mem | h_mem
        · exact absurd h_mem h_eL_fresh
        · simpa using h_mem
      obtain ⟨h_g_eq, h_c_eq, _⟩ :=
        stageEvent_injective actTick groups gi' ci' (k' + 1) gi ci (k + 1)
          h_gi' h_ci' h_gi h_ci (by omega) (by omega)
          (h_e_eq_L.symm.trans h_e_eq)
      rw [h_eL_eq, h_eR_eq, h_g_eq, h_c_eq]
      congr 1
      omega
  have h_AeR : evBefore (World.popSeqFuel w n) A eR := by
    rwa [← h_parent_eq]
  -- the parent carries priority 0, squeezed between two priority-0 pops
  have h_pri_eR : eR.priority = (0 : Int) := by
    have h_le₁ : A.priority ≤ eR.priority :=
      popSeqFuel_priority_mono w n A eR h_AeR
    have h_le₂ : eR.priority ≤ D.priority :=
      popSeqFuel_priority_mono w n eR D h_eRD
    rw [hA_pri] at h_le₁
    rw [hD_pri] at h_le₂
    omega
  -- a stage event with priority 0 is a stage-0 event
  have h_k_zero : k = 0 := by
    have h := congr_arg ScheduledEvent.priority h_eR_eq
    dsimp [stageEvent, stagePri] at h
    rw [h_pri_eR] at h
    by_cases h_k0 : k = 0
    · exact h_k0
    · rw [if_neg h_k0] at h
      by_cases h_le : k ≤ (chainAt groups gi ci).middleDelays.length
      · rw [if_pos h_le] at h
        omega
      · rw [if_neg h_le] at h
        omega
  rw [h_k_zero] at h_e_eq
  -- the spawn carries priority -1, so the witness chain has no
  -- middle delays
  have h_len_zero : (chainAt groups gi ci).middleDelays.length = 0 := by
    have h_pri1 :
        (stageEvent actTick groups gi ci 1).priority = (-1 : Int) := by
      rw [← h_e_eq]
      exact h_pri
    dsimp [stageEvent, stagePri] at h_pri1
    by_cases h_le : 1 ≤ (chainAt groups gi ci).middleDelays.length
    · rw [if_pos h_le] at h_pri1
      omega
    · rw [if_neg h_le] at h_pri1
      omega
  -- transfer the pop order to the due-filter order
  have h_due_AeR : evBefore due A eR :=
    due_evBefore_of_popSeq_evBefore w n A eR hA_pop h_eR_pop hA_due
      h_eR_due (by rw [hA_pri, h_pri_eR]) h_nodup h_AeR
  have h_due_eRD : evBefore due eR D :=
    due_evBefore_of_popSeq_evBefore w n eR D h_eR_pop hD_pop h_eR_due
      hD_due (by rw [h_pri_eR, hD_pri]) h_nodup h_eRD
  rw [h_eR_eq, h_k_zero] at h_due_AeR h_due_eRD
  exact ⟨gi, ci, h_gi, h_ci, h_e_eq, h_len_zero, h_due_AeR, h_due_eRD⟩


/-! ## The main theorems -/

/-- The unconditional converse spawn-origin fact at the final stage.
    At the pop tick of stage `m`, the two reference stage-`m` events
    spawn the two reference stage-`(m + 1)` events. Take an event
    between the two spawns in the post-burst queue. It carries
    priority -1. It targets the output tick of the first chain. That
    event is the stage-`(m + 1)` event of some chain. The stage-`m`
    event of that chain sits between the two reference stage-`m`
    events in the due filter, carries priority -3, and lies in the
    stage-`m` middle block. -/
theorem converse_spawn_gSimBurst_final (groups : List GroupSpec)
    (actTick : Nat → Nat) (T : Nat) (t : Nat)
    (obsAll : List (List Nat)) (withinOrd pos : Nat → List Nat)
    (w : World) (pairs : List (Nat × Nat)) (g₁ c₁ g₂ c₂ m : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_layout : NodeLayoutOk groups w)
    (h_m_ge : 1 ≤ m)
    (h_m₁ : (chainAt groups g₁ c₁).middleDelays.length = m)
    (h_m₂ : (chainAt groups g₂ c₂).middleDelays.length = m)
    (h_due : w.tick = stageTarget actTick groups g₁ c₁ m)
    (h_tgt₂ : stageTarget actTick groups g₂ c₂ m =
        stageTarget actTick groups g₁ c₁ m)
    (hA_mem : stageEvent actTick groups g₁ c₁ m ∈ w.events)
    (hD_mem : stageEvent actTick groups g₂ c₂ m ∈ w.events)
    (h_nodup : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup)
    (hAD : evBefore (w.events.filter (fun e => e.targetTick == w.tick))
        (stageEvent actTick groups g₁ c₁ m)
        (stageEvent actTick groups g₂ c₂ m))
    (h_mb : MiddleBlockOk groups actTick T
        (w.events.filter (fun e => e.targetTick == w.tick)) g₁ c₁ g₂ c₂ m)
    (h_stage : StageMemAt groups actTick w w.tick)
    (h_sA_absent : stageEvent actTick groups g₁ c₁ (m + 1) ∉ w.events)
    (h_sD_absent : stageEvent actTick groups g₂ c₂ (m + 1) ∉ w.events)
    (e : ScheduledEvent)
    (h_e_absent : e ∉ w.events)
    (h_b1 : evBefore (gSimBurst t obsAll withinOrd pos w pairs).events
        (stageEvent actTick groups g₁ c₁ (m + 1)) e)
    (h_b2 : evBefore (gSimBurst t obsAll withinOrd pos w pairs).events e
        (stageEvent actTick groups g₂ c₂ (m + 1)))
    (h_pri : e.priority = (-1 : Int))
    (h_tgt : e.targetTick = T)
    (h_T : stageTarget actTick groups g₁ c₁ (m + 1) = T) :
    ∃ g c, g < groups.length ∧ c < (groupAt groups g).length ∧
      e = stageEvent actTick groups g c (m + 1) ∧
      (stageEvent actTick groups g c m).priority = (-3 : Int) ∧
      MiddleBlock groups actTick T g₁ c₁ m (stageEvent actTick groups g c m) ∧
      evBefore (w.events.filter (fun ev => ev.targetTick == w.tick))
        (stageEvent actTick groups g₁ c₁ m)
        (stageEvent actTick groups g c m) ∧
      evBefore (w.events.filter (fun ev => ev.targetTick == w.tick))
        (stageEvent actTick groups g c m)
        (stageEvent actTick groups g₂ c₂ m) := by
  set sA := stageEvent actTick groups g₁ c₁ (m + 1)
  set sD := stageEvent actTick groups g₂ c₂ (m + 1)
  set W_B := gSimBurst t obsAll withinOrd pos w pairs
  set pPri : ScheduledEvent → Bool :=
    fun ev => decide (ev.priority ≠ (0 : Int))
  -- sA, e, sD all miss the tick of w
  have h_sA_nd : sA.targetTick ≠ w.tick := by
    dsimp [sA, stageEvent]
    rw [h_due]
    exact (stageTarget_lt_succ actTick groups g₁ c₁ m (by omega)).ne'
  have h_e_nd : e.targetTick ≠ w.tick := by
    rw [h_tgt, ← h_T, h_due]
    exact (stageTarget_lt_succ actTick groups g₁ c₁ m (by omega)).ne'
  have h_sD_nd : sD.targetTick ≠ w.tick := by
    dsimp [sD, stageEvent]
    rw [h_due, ← h_tgt₂]
    exact (stageTarget_lt_succ actTick groups g₂ c₂ m (by omega)).ne'
  -- keep only the events that miss the tick of w
  have h_b1_f :
      evBefore (W_B.events.filter (fun ev => ev.targetTick ≠ w.tick))
        sA e :=
    evBefore.filter (fun ev => ev.targetTick ≠ w.tick)
      (by simp [h_sA_nd]) (by simp [h_e_nd]) h_b1
  have h_b2_f :
      evBefore (W_B.events.filter (fun ev => ev.targetTick ≠ w.tick))
        e sD :=
    evBefore.filter (fun ev => ev.targetTick ≠ w.tick)
      (by simp [h_e_nd]) (by simp [h_sD_nd]) h_b2
  -- sA, e, sD carry a priority other than 0
  have h_sA_ne₀ : sA.priority ≠ (0 : Int) := by
    dsimp [sA, stageEvent, stagePri]
    intro h_eq
    omega
  have h_sA_pri : decide (sA.priority ≠ (0 : Int)) = true := by
    simp [h_sA_ne₀]
  have h_sD_ne₀ : sD.priority ≠ (0 : Int) := by
    dsimp [sD, stageEvent, stagePri]
    intro h_eq
    omega
  have h_sD_pri : decide (sD.priority ≠ (0 : Int)) = true := by
    simp [h_sD_ne₀]
  have h_e_ne₀ : e.priority ≠ (0 : Int) := by
    rw [h_pri]
    intro h_eq
    omega
  have h_e_pri : decide (e.priority ≠ (0 : Int)) = true := by
    simp [h_e_ne₀]
  -- apply the burst split. The priority filter drops the observer
  -- batches.
  obtain ⟨M, h_split⟩ :=
    gSimBurst_filter_split t obsAll withinOrd pos w pairs
  have h_b1_ff : evBefore
      ((w.events.filter (fun ev => ev.targetTick ≠ w.tick)).filter pPri ++
        (World.popSpawnAcc w M).filter pPri) sA e := by
    have h := evBefore.filter pPri h_sA_pri h_e_pri h_b1_f
    rwa [h_split] at h
  have h_surv_sA :
      sA ∉ (w.events.filter (fun ev => ev.targetTick ≠ w.tick)).filter
        pPri :=
    fun h_mem =>
      h_sA_absent (List.mem_filter.mp (List.mem_filter.mp h_mem).1).1
  have h_b_left : evBefore (World.popSpawnAcc w M) sA e :=
    evBefore.of_filter pPri
      (evBefore_append_left_absent h_surv_sA h_b1_ff)
  have h_b_right : evBefore (World.popSpawnAcc w M) e sD := by
    have h_b2_ff : evBefore
        ((w.events.filter
            (fun ev => ev.targetTick ≠ w.tick)).filter pPri ++
          (World.popSpawnAcc w M).filter pPri) e sD := by
      have h := evBefore.filter pPri h_e_pri h_sD_pri h_b2_f
      rwa [h_split] at h
    have h_e_surv :
        e ∉ (w.events.filter (fun ev => ev.targetTick ≠ w.tick)).filter
          pPri :=
      fun h_mem =>
        h_e_absent (List.mem_filter.mp (List.mem_filter.mp h_mem).1).1
    rcases evBefore_append_split_right h_b2_ff with h_e_s | h_b
    · exact absurd h_e_s h_e_surv
    · exact evBefore.of_filter pPri h_b
  exact converse_spawn_popSpawnAcc_final groups actTick T w g₁ c₁ g₂ c₂ m M
    h_g₁ h_c₁ h_g₂ h_c₂ h_layout h_m_ge h_m₁ h_m₂ h_due h_tgt₂ h_nodup
    h_mb h_stage h_sA_absent h_sD_absent e h_e_absent h_b_left h_b_right

private theorem filter_eq_self_of_forall' {α : Type} (p : α → Bool)
    (l : List α) (h : ∀ x ∈ l, p x = true) : l.filter p = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have h_x := h x (List.mem_cons.mpr (Or.inl rfl))
    simp [List.filter, h_x, ih (fun y hy => h y (List.mem_cons.mpr (Or.inr hy)))]

/-- The unconditional converse spawn-origin fact at the final stage,
    for the drain phase (`stepUntilNextTick`). The reference stage-`m`
    events pop during the drain and spawn the reference stage-`(m + 1)`
    events; an event between the two spawns in the drained queue is the
    stage-`(m + 1)` event of a chain whose stage-`m` event lies between
    the two reference stage-`m` events. The drain is reduced to the
    spawn accumulator exactly as in `converse_spawn_stepUntilNextTick`,
    then classified by `converse_spawn_popSpawnAcc_final`. -/
theorem converse_spawn_stepUNT_final (groups : List GroupSpec)
    (actTick : Nat → Nat) (T : Nat) (w : World) (g₁ c₁ g₂ c₂ m : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_layout : NodeLayoutOk groups w)
    (h_m_ge : 1 ≤ m)
    (h_m₁ : (chainAt groups g₁ c₁).middleDelays.length = m)
    (h_m₂ : (chainAt groups g₂ c₂).middleDelays.length = m)
    (h_due : w.tick = stageTarget actTick groups g₁ c₁ m)
    (h_tgt₂ : stageTarget actTick groups g₂ c₂ m =
        stageTarget actTick groups g₁ c₁ m)
    (h_nodup : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup)
    (h_mb : MiddleBlockOk groups actTick T
        (w.events.filter (fun e => e.targetTick == w.tick)) g₁ c₁ g₂ c₂ m)
    (h_stage : StageMemAt groups actTick w w.tick)
    (h_sA_absent : stageEvent actTick groups g₁ c₁ (m + 1) ∉ w.events)
    (h_sD_absent : stageEvent actTick groups g₂ c₂ (m + 1) ∉ w.events)
    (e : ScheduledEvent)
    (h_e_absent : e ∉ w.events)
    (h_b1 : evBefore w.stepUntilNextTick.events
        (stageEvent actTick groups g₁ c₁ (m + 1)) e)
    (h_b2 : evBefore w.stepUntilNextTick.events e
        (stageEvent actTick groups g₂ c₂ (m + 1))) :
    ∃ g c, g < groups.length ∧ c < (groupAt groups g).length ∧
      e = stageEvent actTick groups g c (m + 1) ∧
      (stageEvent actTick groups g c m).priority = (-3 : Int) ∧
      MiddleBlock groups actTick T g₁ c₁ m (stageEvent actTick groups g c m) ∧
      evBefore (w.events.filter (fun ev => ev.targetTick == w.tick))
        (stageEvent actTick groups g₁ c₁ m)
        (stageEvent actTick groups g c m) ∧
      evBefore (w.events.filter (fun ev => ev.targetTick == w.tick))
        (stageEvent actTick groups g c m)
        (stageEvent actTick groups g₂ c₂ m) := by
  set sA := stageEvent actTick groups g₁ c₁ (m + 1)
  set sD := stageEvent actTick groups g₂ c₂ (m + 1)
  set due := w.events.filter (fun ev => ev.targetTick == w.tick)
  set n := due.length
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
  have h_surv_sA : sA ∉ w.events.filter (fun ev => ev.targetTick ≠ w.tick) :=
    fun h_mem => h_sA_absent (List.mem_filter.mp h_mem).1
  have h_b1' : evBefore
      (w.events.filter (fun ev => ev.targetTick ≠ w.tick) ++
        World.popSpawnAcc w n) sA e := by
    rwa [← h_split, ← h_post_events]
  have h_b_left : evBefore (World.popSpawnAcc w n) sA e :=
    evBefore_append_left_absent h_surv_sA h_b1'
  have h_surv_sD : sD ∉ w.events.filter (fun ev => ev.targetTick ≠ w.tick) :=
    fun h_mem => h_sD_absent (List.mem_filter.mp h_mem).1
  have h_b2' : evBefore
      (w.events.filter (fun ev => ev.targetTick ≠ w.tick) ++
        World.popSpawnAcc w n) e sD := by
    rwa [← h_split, ← h_post_events]
  have h_b_right : evBefore (World.popSpawnAcc w n) e sD := by
    rcases evBefore_append_split_right h_b2' with h_e_surv | h_b
    · exact absurd h_e_surv (fun h_mem =>
        h_e_absent (List.mem_filter.mp h_mem).1)
    · exact h_b
  exact converse_spawn_popSpawnAcc_final groups actTick T w g₁ c₁ g₂ c₂ m n
    h_g₁ h_c₁ h_g₂ h_c₂ h_layout h_m_ge h_m₁ h_m₂ h_due h_tgt₂ h_nodup
    h_mb h_stage h_sA_absent h_sD_absent e h_e_absent h_b_left h_b_right

/-- The unconditional converse at the final stage for the drain phase,
    packaged as `ConverseSpawnFinal`. The raw converse spawn data comes
    from `converse_spawn_stepUNT_final`; the assembly comes from
    `ConverseSpawnFinal_of_rawSpawn` of ConverseSpawnFinal. -/
theorem ConverseSpawnFinal_stepUNT_converse (groups : List GroupSpec)
    (actTick : Nat → Nat) (T : Nat) (w : World) (g₁ c₁ g₂ c₂ m : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_layout : NodeLayoutOk groups w)
    (h_m_ge : 1 ≤ m)
    (h_m₁ : (chainAt groups g₁ c₁).middleDelays.length = m)
    (h_m₂ : (chainAt groups g₂ c₂).middleDelays.length = m)
    (h_due : w.tick = stageTarget actTick groups g₁ c₁ m)
    (h_tgt₂ : stageTarget actTick groups g₂ c₂ m =
        stageTarget actTick groups g₁ c₁ m)
    (h_nodup : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup)
    (h_mb : MiddleBlockOk groups actTick T
        (w.events.filter (fun e => e.targetTick == w.tick)) g₁ c₁ g₂ c₂ m)
    (h_stage : StageMemAt groups actTick w w.tick)
    (h_sA_absent : stageEvent actTick groups g₁ c₁ (m + 1) ∉ w.events)
    (h_sD_absent : stageEvent actTick groups g₂ c₂ (m + 1) ∉ w.events)
    (h_T : stageTarget actTick groups g₁ c₁ (m + 1) = T)
    (e : ScheduledEvent)
    (h_e_absent : e ∉ w.events)
    (h_blk : FinalBlockBetween groups actTick T
        w.stepUntilNextTick.events g₁ c₁ g₂ c₂ m e) :
    ConverseSpawnFinal groups actTick w g₁ c₁ g₂ c₂ m e := by
  obtain ⟨g, c, h_g, h_c, h_e_eq, h_parent_pri, h_parent_mb, h_b1, h_b2⟩ :=
    converse_spawn_stepUNT_final groups actTick T w g₁ c₁ g₂ c₂ m
      h_g₁ h_c₁ h_g₂ h_c₂ h_layout h_m_ge h_m₁ h_m₂ h_due h_tgt₂
      h_nodup h_mb h_stage h_sA_absent h_sD_absent
      e h_e_absent h_blk.2.2.1 h_blk.2.2.2
  exact ConverseSpawnFinal_of_rawSpawn groups actTick w T
    w.stepUntilNextTick.events g₁ c₁ g₂ c₂ g c m e
    h_g₁ h_c₁ h_g h_c h_m₁ h_m_ge h_T h_blk
    h_e_eq h_parent_pri h_parent_mb h_b1 h_b2

/-- The conditional converse for `FinalBlockBetween` at the final
    stage. Every `FinalBlockBetween` event in the post-burst queue
    satisfies `Pri1FinalOf`. The raw converse spawn data comes from
    `converse_spawn_gSimBurst_final`. The assembly comes from
    `FinalBlockBetween_converse_of_rawSpawn` of ConverseSpawnFinal. -/
theorem FinalBlockBetween_converse (groups : List GroupSpec)
    (actTick : Nat → Nat) (T : Nat) (t : Nat)
    (obsAll : List (List Nat)) (withinOrd pos : Nat → List Nat)
    (w : World) (pairs : List (Nat × Nat)) (g₁ c₁ g₂ c₂ m : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_layout : NodeLayoutOk groups w)
    (h_m_ge : 1 ≤ m)
    (h_m₁ : (chainAt groups g₁ c₁).middleDelays.length = m)
    (h_m₂ : (chainAt groups g₂ c₂).middleDelays.length = m)
    (h_due : w.tick = stageTarget actTick groups g₁ c₁ m)
    (h_tgt₂ : stageTarget actTick groups g₂ c₂ m =
        stageTarget actTick groups g₁ c₁ m)
    (hA_mem : stageEvent actTick groups g₁ c₁ m ∈ w.events)
    (hD_mem : stageEvent actTick groups g₂ c₂ m ∈ w.events)
    (h_nodup : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup)
    (hAD : evBefore (w.events.filter (fun e => e.targetTick == w.tick))
        (stageEvent actTick groups g₁ c₁ m)
        (stageEvent actTick groups g₂ c₂ m))
    (h_mb : MiddleBlockOk groups actTick T
        (w.events.filter (fun e => e.targetTick == w.tick)) g₁ c₁ g₂ c₂ m)
    (h_stage : StageMemAt groups actTick w w.tick)
    (h_sA_absent : stageEvent actTick groups g₁ c₁ (m + 1) ∉ w.events)
    (h_sD_absent : stageEvent actTick groups g₂ c₂ (m + 1) ∉ w.events)
    (h_T : stageTarget actTick groups g₁ c₁ (m + 1) = T)
    (e : ScheduledEvent)
    (h_e_absent : e ∉ w.events)
    (h_blk : FinalBlockBetween groups actTick T
        (gSimBurst t obsAll withinOrd pos w pairs).events
        g₁ c₁ g₂ c₂ m e) :
    Pri1FinalOf groups actTick g₁ c₁ m e := by
  obtain ⟨g, c, h_g, h_c, h_e_eq, h_parent_pri, h_parent_mb, _, _⟩ :=
    converse_spawn_gSimBurst_final groups actTick T t obsAll withinOrd pos
      w pairs g₁ c₁ g₂ c₂ m
      h_g₁ h_c₁ h_g₂ h_c₂ h_layout h_m_ge h_m₁ h_m₂ h_due h_tgt₂
      hA_mem hD_mem h_nodup hAD h_mb h_stage h_sA_absent h_sD_absent
      e h_e_absent h_blk.2.2.1 h_blk.2.2.2 h_blk.1 h_blk.2.1 h_T
  exact FinalBlockBetween_converse_of_rawSpawn groups actTick T
    (gSimBurst t obsAll withinOrd pos w pairs).events w
    g₁ c₁ g₂ c₂ g c m e
    h_g₁ h_c₁ h_g h_c h_m₁ h_m_ge h_T h_blk
    h_e_eq h_parent_pri h_parent_mb

/-- The main clustering property at the final stage. Every event that
    sits between the two reference stage-`(m + 1)` anchors in the
    post-burst queue, carries priority -1, and targets the output
    tick satisfies `Pri1FinalOf`. The event matches the full spec of
    chain `(g₁, c₁)` at the last stage. -/
theorem Pri1FinalOf_of_between (groups : List GroupSpec)
    (actTick : Nat → Nat) (T : Nat) (t : Nat)
    (obsAll : List (List Nat)) (withinOrd pos : Nat → List Nat)
    (w : World) (pairs : List (Nat × Nat)) (g₁ c₁ g₂ c₂ m : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_layout : NodeLayoutOk groups w)
    (h_m_ge : 1 ≤ m)
    (h_m₁ : (chainAt groups g₁ c₁).middleDelays.length = m)
    (h_m₂ : (chainAt groups g₂ c₂).middleDelays.length = m)
    (h_due : w.tick = stageTarget actTick groups g₁ c₁ m)
    (h_tgt₂ : stageTarget actTick groups g₂ c₂ m =
        stageTarget actTick groups g₁ c₁ m)
    (hA_mem : stageEvent actTick groups g₁ c₁ m ∈ w.events)
    (hD_mem : stageEvent actTick groups g₂ c₂ m ∈ w.events)
    (h_nodup : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup)
    (hAD : evBefore (w.events.filter (fun e => e.targetTick == w.tick))
        (stageEvent actTick groups g₁ c₁ m)
        (stageEvent actTick groups g₂ c₂ m))
    (h_mb : MiddleBlockOk groups actTick T
        (w.events.filter (fun e => e.targetTick == w.tick)) g₁ c₁ g₂ c₂ m)
    (h_stage : StageMemAt groups actTick w w.tick)
    (h_sA_absent : stageEvent actTick groups g₁ c₁ (m + 1) ∉ w.events)
    (h_sD_absent : stageEvent actTick groups g₂ c₂ (m + 1) ∉ w.events)
    (h_T : stageTarget actTick groups g₁ c₁ (m + 1) = T)
    (e : ScheduledEvent)
    (h_e_absent : e ∉ w.events)
    (h_pri : e.priority = (-1 : Int))
    (h_tgt : e.targetTick = T)
    (h_b1 : evBefore (gSimBurst t obsAll withinOrd pos w pairs).events
        (stageEvent actTick groups g₁ c₁ (m + 1)) e)
    (h_b2 : evBefore (gSimBurst t obsAll withinOrd pos w pairs).events e
        (stageEvent actTick groups g₂ c₂ (m + 1))) :
    Pri1FinalOf groups actTick g₁ c₁ m e := by
  exact FinalBlockBetween_converse groups actTick T t obsAll withinOrd pos
    w pairs g₁ c₁ g₂ c₂ m
    h_g₁ h_c₁ h_g₂ h_c₂ h_layout h_m_ge h_m₁ h_m₂ h_due h_tgt₂
    hA_mem hD_mem h_nodup hAD h_mb h_stage h_sA_absent h_sD_absent
    h_T e h_e_absent ⟨h_pri, h_tgt, h_b1, h_b2⟩

/-- The unconditional converse spawn-origin fact at the final stage,
    for reference chains with no middle delays (`m = 0`). The two
    reference stage-`0` events are observer events carrying priority
    0. Any event between their stage-`1` spawns in the post-burst
    queue that carries priority -1 and targets the output tick is the
    stage-`1` event of some chain with no middle delays, whose
    stage-`0` event sits between the two reference stage-`0` events
    in the due filter. The conclusion is the `m = 0` instance of
    `ConverseSpawnFinal`. -/
theorem converse_spawn_gSimBurst_final_m0 (groups : List GroupSpec)
    (actTick : Nat → Nat) (T : Nat) (t : Nat)
    (obsAll : List (List Nat)) (withinOrd pos : Nat → List Nat)
    (w : World) (pairs : List (Nat × Nat)) (g₁ c₁ g₂ c₂ : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_layout : NodeLayoutOk groups w)
    (h_m₁ : (chainAt groups g₁ c₁).middleDelays.length = 0)
    (h_m₂ : (chainAt groups g₂ c₂).middleDelays.length = 0)
    (h_due : w.tick = stageTarget actTick groups g₁ c₁ 0)
    (h_tgt₂ : stageTarget actTick groups g₂ c₂ 0 =
        stageTarget actTick groups g₁ c₁ 0)
    (hA_mem : stageEvent actTick groups g₁ c₁ 0 ∈ w.events)
    (hD_mem : stageEvent actTick groups g₂ c₂ 0 ∈ w.events)
    (h_nodup : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup)
    (hAD : evBefore (w.events.filter (fun e => e.targetTick == w.tick))
        (stageEvent actTick groups g₁ c₁ 0)
        (stageEvent actTick groups g₂ c₂ 0))
    (h_stage : StageMemAt groups actTick w w.tick)
    (h_sA_absent : stageEvent actTick groups g₁ c₁ 1 ∉ w.events)
    (h_sD_absent : stageEvent actTick groups g₂ c₂ 1 ∉ w.events)
    (e : ScheduledEvent)
    (h_e_absent : e ∉ w.events)
    (h_b1 : evBefore (gSimBurst t obsAll withinOrd pos w pairs).events
        (stageEvent actTick groups g₁ c₁ 1) e)
    (h_b2 : evBefore (gSimBurst t obsAll withinOrd pos w pairs).events e
        (stageEvent actTick groups g₂ c₂ 1))
    (h_pri : e.priority = (-1 : Int))
    (h_tgt : e.targetTick = T)
    (h_T : stageTarget actTick groups g₁ c₁ 1 = T) :
    ConverseSpawnFinal groups actTick w g₁ c₁ g₂ c₂ 0 e := by
  set sA := stageEvent actTick groups g₁ c₁ 1
  set sD := stageEvent actTick groups g₂ c₂ 1
  set W_B := gSimBurst t obsAll withinOrd pos w pairs
  set pPri : ScheduledEvent → Bool :=
    fun ev => decide (ev.priority ≠ (0 : Int))
  -- sA, e, sD all miss the tick of w
  have h_sA_nd : sA.targetTick ≠ w.tick := by
    dsimp [sA, stageEvent]
    rw [h_due]
    exact (stageTarget_lt_succ actTick groups g₁ c₁ 0 (by omega)).ne'
  have h_e_nd : e.targetTick ≠ w.tick := by
    rw [h_tgt, ← h_T, h_due]
    exact (stageTarget_lt_succ actTick groups g₁ c₁ 0 (by omega)).ne'
  have h_sD_nd : sD.targetTick ≠ w.tick := by
    dsimp [sD, stageEvent]
    rw [h_due, ← h_tgt₂]
    exact (stageTarget_lt_succ actTick groups g₂ c₂ 0 (by omega)).ne'
  -- keep only the events that miss the tick of w
  have h_b1_f :
      evBefore (W_B.events.filter (fun ev => ev.targetTick ≠ w.tick))
        sA e :=
    evBefore.filter (fun ev => ev.targetTick ≠ w.tick)
      (by simp [h_sA_nd]) (by simp [h_e_nd]) h_b1
  have h_b2_f :
      evBefore (W_B.events.filter (fun ev => ev.targetTick ≠ w.tick))
        e sD :=
    evBefore.filter (fun ev => ev.targetTick ≠ w.tick)
      (by simp [h_e_nd]) (by simp [h_sD_nd]) h_b2
  -- sA, e, sD carry a priority other than 0
  have h_sA_ne₀ : sA.priority ≠ (0 : Int) := by
    dsimp [sA, stageEvent, stagePri]
    intro h_eq
    omega
  have h_sA_pri : decide (sA.priority ≠ (0 : Int)) = true := by
    simp [h_sA_ne₀]
  have h_sD_ne₀ : sD.priority ≠ (0 : Int) := by
    dsimp [sD, stageEvent, stagePri]
    intro h_eq
    omega
  have h_sD_pri : decide (sD.priority ≠ (0 : Int)) = true := by
    simp [h_sD_ne₀]
  have h_e_ne₀ : e.priority ≠ (0 : Int) := by
    rw [h_pri]
    intro h_eq
    omega
  have h_e_pri : decide (e.priority ≠ (0 : Int)) = true := by
    simp [h_e_ne₀]
  -- apply the burst split. The priority filter drops the observer
  -- batches.
  obtain ⟨M, h_split⟩ :=
    gSimBurst_filter_split t obsAll withinOrd pos w pairs
  have h_b1_ff : evBefore
      ((w.events.filter (fun ev => ev.targetTick ≠ w.tick)).filter pPri ++
        (World.popSpawnAcc w M).filter pPri) sA e := by
    have h := evBefore.filter pPri h_sA_pri h_e_pri h_b1_f
    rwa [h_split] at h
  have h_surv_sA :
      sA ∉ (w.events.filter (fun ev => ev.targetTick ≠ w.tick)).filter
        pPri :=
    fun h_mem =>
      h_sA_absent (List.mem_filter.mp (List.mem_filter.mp h_mem).1).1
  have h_b_left : evBefore (World.popSpawnAcc w M) sA e :=
    evBefore.of_filter pPri
      (evBefore_append_left_absent h_surv_sA h_b1_ff)
  have h_b_right : evBefore (World.popSpawnAcc w M) e sD := by
    have h_b2_ff : evBefore
        ((w.events.filter
            (fun ev => ev.targetTick ≠ w.tick)).filter pPri ++
          (World.popSpawnAcc w M).filter pPri) e sD := by
      have h := evBefore.filter pPri h_e_pri h_sD_pri h_b2_f
      rwa [h_split] at h
    have h_e_surv :
        e ∉ (w.events.filter (fun ev => ev.targetTick ≠ w.tick)).filter
          pPri :=
      fun h_mem =>
        h_e_absent (List.mem_filter.mp (List.mem_filter.mp h_mem).1).1
    rcases evBefore_append_split_right h_b2_ff with h_e_s | h_b
    · exact absurd h_e_s h_e_surv
    · exact evBefore.of_filter pPri h_b
  obtain ⟨g, c, h_g, h_c, h_e_eq, h_len0, h_b1_due, h_b2_due⟩ :=
    converse_spawn_popSpawnAcc_final_m0 groups actTick T w g₁ c₁ g₂ c₂ M
      h_g₁ h_c₁ h_g₂ h_c₂ h_layout h_m₁ h_m₂ h_due h_tgt₂ h_nodup
      h_stage h_sA_absent h_sD_absent e h_e_absent h_pri
      h_b_left h_b_right
  -- assemble ConverseSpawnFinal at m = 0
  have h_nil_gc : (chainAt groups g c).middleDelays = [] := by
    cases h_md : (chainAt groups g c).middleDelays with
    | nil => rfl
    | cons d ds =>
      have h_len : (d :: ds).length = 0 := h_md ▸ h_len0
      simp at h_len
  have h_nil_ref : (chainAt groups g₁ c₁).middleDelays = [] := by
    cases h_md : (chainAt groups g₁ c₁).middleDelays with
    | nil => rfl
    | cons d ds =>
      have h_len : (d :: ds).length = 0 := h_md ▸ h_m₁
      simp at h_len
  refine ⟨g, c, h_g, h_c, ?_, h_e_eq, ?_, ?_, h_b1_due, h_b2_due⟩
  · rw [h_len0, h_m₁]
  · dsimp [prefixDelays]
    rw [h_nil_gc, h_nil_ref]
  · have h_tgt_w : stageTarget actTick groups g c 1 = T := by
      have := congr_arg ScheduledEvent.targetTick h_e_eq
      dsimp [stageEvent] at this
      rw [← this, h_tgt]
    rw [h_tgt_w, h_T]

/-- The converse for `FinalBlockBetween` at the final stage, packaged
    as `ConverseSpawnFinal`. This keeps the stage-`m` betweenness of
    the witness parent, which `FinalBlockBetween_converse` (returning
    `Pri1FinalOf`) drops. The clustering argument needs the kept
    betweenness to pin down the activation tick, and with it the last
    delay (see `chainSpec_eq_of_ConverseSpawnFinal` of ConverseSpawnFinal). -/
theorem ConverseSpawnFinal_converse (groups : List GroupSpec)
    (actTick : Nat → Nat) (T : Nat) (t : Nat)
    (obsAll : List (List Nat)) (withinOrd pos : Nat → List Nat)
    (w : World) (pairs : List (Nat × Nat)) (g₁ c₁ g₂ c₂ m : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_layout : NodeLayoutOk groups w)
    (h_m_ge : 1 ≤ m)
    (h_m₁ : (chainAt groups g₁ c₁).middleDelays.length = m)
    (h_m₂ : (chainAt groups g₂ c₂).middleDelays.length = m)
    (h_due : w.tick = stageTarget actTick groups g₁ c₁ m)
    (h_tgt₂ : stageTarget actTick groups g₂ c₂ m =
        stageTarget actTick groups g₁ c₁ m)
    (hA_mem : stageEvent actTick groups g₁ c₁ m ∈ w.events)
    (hD_mem : stageEvent actTick groups g₂ c₂ m ∈ w.events)
    (h_nodup : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup)
    (hAD : evBefore (w.events.filter (fun e => e.targetTick == w.tick))
        (stageEvent actTick groups g₁ c₁ m)
        (stageEvent actTick groups g₂ c₂ m))
    (h_mb : MiddleBlockOk groups actTick T
        (w.events.filter (fun e => e.targetTick == w.tick)) g₁ c₁ g₂ c₂ m)
    (h_stage : StageMemAt groups actTick w w.tick)
    (h_sA_absent : stageEvent actTick groups g₁ c₁ (m + 1) ∉ w.events)
    (h_sD_absent : stageEvent actTick groups g₂ c₂ (m + 1) ∉ w.events)
    (h_T : stageTarget actTick groups g₁ c₁ (m + 1) = T)
    (e : ScheduledEvent)
    (h_e_absent : e ∉ w.events)
    (h_blk : FinalBlockBetween groups actTick T
        (gSimBurst t obsAll withinOrd pos w pairs).events
        g₁ c₁ g₂ c₂ m e) :
    ConverseSpawnFinal groups actTick w g₁ c₁ g₂ c₂ m e := by
  obtain ⟨g, c, h_g, h_c, h_e_eq, h_parent_pri, h_parent_mb, h_b1, h_b2⟩ :=
    converse_spawn_gSimBurst_final groups actTick T t obsAll withinOrd pos
      w pairs g₁ c₁ g₂ c₂ m
      h_g₁ h_c₁ h_g₂ h_c₂ h_layout h_m_ge h_m₁ h_m₂ h_due h_tgt₂
      hA_mem hD_mem h_nodup hAD h_mb h_stage h_sA_absent h_sD_absent
      e h_e_absent h_blk.2.2.1 h_blk.2.2.2 h_blk.1 h_blk.2.1 h_T
  exact ConverseSpawnFinal_of_rawSpawn groups actTick w T
    (gSimBurst t obsAll withinOrd pos w pairs).events
    g₁ c₁ g₂ c₂ g c m e
    h_g₁ h_c₁ h_g h_c h_m₁ h_m_ge h_T h_blk
    h_e_eq h_parent_pri h_parent_mb h_b1 h_b2
