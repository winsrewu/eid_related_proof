import BasicProofs.GroupClustering.FinalConverseDrainPhase
import BasicProofs.GroupClustering.FinalConverseBurstPhase
import BasicProofs.GroupClustering.FinalConverseMixedPhase
import BasicProofs.GroupClustering.MiddleBlockOkLastMiddleStage
import BasicProofs.GroupClustering.FinalStageAssemblySetup
import BasicProofs.GroupClustering.ConverseStage0
import BasicProofs.GroupClustering.FinalsBundle
import BasicProofs.GroupClustering.LogShape
import BasicProofs.GroupClustering.FinalPopIndex
import BasicProofs.GroupClustering.MiddleFinalSpawnTick
import BasicProofs.GroupClustering.BackwardTransport
import BasicProofs.GroupClustering.ActivationListOrder
import BasicProofs.GroupClustering.Stage0BaseOrder
import BasicProofs.GroupClustering.ConverseSpawnFinal
import BasicProofs.GroupClustering.CrossPriorityPopDiscipline
import BasicProofs.GroupClustering.SuccessorMembershipRange
import BasicProofs.GroupClustering.PreStepWorldFacts
import BasicProofs.GroupClustering.QSideOrderNoSurvival

set_option linter.unusedVariables false

open BasicRedstoneSim List

/-! # Group clustering — capstone assembly

Assembles `group_output_clustering` from the phase lemmas
(FinalConverseDrainPhase–FinalConverseMixedPhase), the m = 0 converses
(ConverseFinalUnconditional/ConverseStage0), the backward transport
(BackwardTransport / FinalsBackwardTransportI–III / MiddleFinalSpawnTick),
and the MiddleBlockOk invariant (MiddleBlockOkLastMiddleStage).

The reference pair orientation is resolved here: the stage-0 base
order comes from the Stage0BaseOrder cross-group base (burst order) or the
same-group withinOrd base below; the wrong orientation contradicts
the observed final-event betweenness via the QSideOrderNoSurvival induction at the
final stage.
-/

/-- A chain-index bound forces the group index in range (reproven;
    private in OutputBetweennessBridge). -/
private theorem gi_lt_of_ci_lt_groupAt (groups : List GroupSpec)
    (gi ci : Nat) (h : ci < (groupAt groups gi).length) :
    gi < groups.length := by
  by_contra h_ge
  have h_none : groups[gi]? = none :=
    List.getElem?_eq_none (Nat.le_of_not_lt h_ge)
  dsimp [groupAt] at h
  rw [h_none] at h
  dsimp at h
  omega

/-- The tick-`(t + 1)` queue is the result of the `gSimBody` call at
    tick `t` (reproven; private in Stage0BaseOrder). -/
private theorem gSimWorld_succ_events_eq_body (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (t : Nat) :
    (gSimWorld groups actTick groupOrd withinOrd pos (t + 1)).events =
    (gSimBody actTick (buildGroups groups).2 groupOrd withinOrd pos
      (gSimWorld groups actTick groupOrd withinOrd pos t) t).events := by
  dsimp [gSimWorld, gSimFoldl]
  simp only [List.range_succ, List.foldl_append, List.foldl_cons,
    List.foldl_nil]

/-- Two distinct members of a Nodup list stand in exactly one split
    order. -/
private theorem list_order_total {α : Type} (l : List α)
    (h_nd : l.Nodup) (a b : α) (h_a : a ∈ l) (h_b : b ∈ l)
    (h_ne : a ≠ b) :
    (∃ pre mid post, l = pre ++ a :: mid ++ b :: post) ∨
    (∃ pre mid post, l = pre ++ b :: mid ++ a :: post) := by
  obtain ⟨pre, post, h_split⟩ := split_at_mem l a h_a
  by_cases h_b_pre : b ∈ pre
  · obtain ⟨preB, postB, h_splitB⟩ := split_at_mem pre b h_b_pre
    right
    refine ⟨preB, postB, post, ?_⟩
    rw [h_splitB] at h_split
    exact h_split
  · left
    have h_b_post : b ∈ post := by
      have h_mem : b ∈ pre ++ a :: post := by
        rwa [← h_split]
      rw [List.mem_append, List.mem_cons] at h_mem
      obtain h_pre | h_mid := h_mem
      · exfalso; exact h_b_pre h_pre
      · cases h_mid with
        | inl h_eq => exfalso; exact h_ne h_eq.symm
        | inr h_post => exact h_post
    obtain ⟨mid, postB, h_splitB⟩ := split_at_mem post b h_b_post
    refine ⟨pre, mid, postB, ?_⟩
    rw [h_splitB] at h_split
    simpa [List.cons_append] using h_split

/-- A split of a list gives a split of its zipIdx at the pair of the
    element `a`. -/
private theorem zipIdx_split_of_split_one {α : Type} (preA postA : List α)
    (a : α) : ∃ preP postP,
    (preA ++ a :: postA).zipIdx = preP ++ (a, preA.length) :: postP := by
  refine ⟨preA.zipIdx, postA.zipIdx (preA.length + 1), ?_⟩
  rw [List.zipIdx_append, List.zipIdx_cons]
  simp only [Nat.zero_add]

/-- A filter that keeps every element of a list is the identity
    (reproven; private in FinalConverseDrainPhase). -/
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
private theorem stepUNT_filter_split (w : World) :
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
    in SideHypothesisDischarge/79/81). -/
private theorem NodeLayoutOk_gSimWorld (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (t : Nat) :
    NodeLayoutOk groups
      (gSimWorld groups actTick groupOrd withinOrd pos t) := by
  dsimp [gSimWorld]
  exact NodeLayoutOk_gSimFoldl groups actTick (buildGroups groups).2 groupOrd
    withinOrd pos (buildGroups groups).1 t (NodeLayoutOk_buildGroups groups)

/-- The stage-0 base order for two chains of the SAME group: the
    withinOrd split order, carried to the stage-0 pop queue. -/
theorem sameSpec_stage_evBefore_base_sameGroup (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat)
    (h_ord : List.Perm groupOrd (List.range groups.length))
    (g₁ c₁ c₂ : Nat)
    (h_g₁ : g₁ < groups.length)
    (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_c₂ : c₂ < (groupAt groups g₁).length)
    (h_ord_split : ∃ pre mid post,
        withinOrd g₁ = pre ++ c₁ :: mid ++ c₂ :: post) :
    evBefore
      ((popQueueWorld groups actTick groupOrd withinOrd pos
        g₁ c₁ 0).events)
      (stageEvent actTick groups g₁ c₁ 0)
      (stageEvent actTick groups g₁ c₂ 0) := by
  set t₀ : Nat := actTick g₁
  set W₀ : World := gSimWorld groups actTick groupOrd withinOrd pos t₀
  have h_tick_W₀ : W₀.tick = t₀ := by
    change (gSimFoldl actTick (buildGroups groups).2 groupOrd withinOrd pos
      (buildGroups groups).1 t₀).tick = t₀
    rw [gSimFoldl_tick, buildGroups_tick]
    omega
  -- g₁ activates at t₀, so the activation list is nonempty with g₁ in it
  have h_g₁_active : g₁ ∈ groupOrd.filter (fun gi =>
      decide (gi < (buildGroups groups).2.length) && (actTick gi == t₀)) := by
    have h_len : groupOrd.length = groups.length := by
      have h := List.Perm.length_eq h_ord
      rw [List.length_range] at h
      exact h
    have h_mem : g₁ ∈ groupOrd :=
      (Perm.mem_range_iff h_ord h_len g₁).mpr h_g₁
    rw [List.mem_filter]
    refine ⟨h_mem, ?_⟩
    rw [Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · rw [decide_eq_true_eq, buildGroups_snd_length]
      exact h_g₁
    · dsimp [t₀]
      simp
  -- the order at the tick-start queue of tick t₀ + 1
  have h_order_succ : evBefore
      ((gSimWorld groups actTick groupOrd withinOrd pos (t₀ + 1)).events)
      (stageEvent actTick groups g₁ c₁ 0)
      (stageEvent actTick groups g₁ c₂ 0) := by
    rw [gSimWorld_succ_events_eq_body groups actTick groupOrd withinOrd pos
      t₀]
    change evBefore
      ((gSimBody actTick (buildGroups groups).2 groupOrd withinOrd pos W₀
          t₀).events)
      (stageEvent actTick groups g₁ c₁ 0)
      (stageEvent actTick groups g₁ c₂ 0)
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
      -- split active_b.zipIdx at the step of g₁
      obtain ⟨preA, postA, h_active_split⟩ :
          ∃ preA postA, active_b = preA ++ g₁ :: postA := by
        exact split_at_mem active_b g₁ (by
          dsimp [active_b, t₀]
          exact h_g₁_active)
      obtain ⟨preP, postP, h_zip_split⟩ :
          ∃ preP postP, active_b.zipIdx =
              preP ++ (g₁, preA.length) :: postP := by
        obtain ⟨preP, postP, h_z⟩ := zipIdx_split_of_split_one preA postA g₁
        rw [← h_active_split] at h_z
        exact ⟨preP, postP, h_z⟩
      have h_burst_split :
          gSimBurst t₀ (buildGroups groups).2 withinOrd pos W₁
            (preP ++ (g₁, preA.length) :: postP) =
            gSimBurst t₀ (buildGroups groups).2 withinOrd pos
              (gSimBurst t₀ (buildGroups groups).2 withinOrd pos W₁ preP)
              ((g₁, preA.length) :: postP) := by
        simp only [gSimBurst, List.foldl_append]
      set W_pre : World := gSimBurst t₀ (buildGroups groups).2 withinOrd pos
        W₁ preP
      set mFuel : Nat := (pos t₀)[preA.length]?.getD 0
      set Wproc : World := processNEvents W_pre mFuel
      set ordered₁ : List Nat := (withinOrd g₁).foldl (fun acc ci =>
        match (((buildGroups groups).2)[g₁]?.getD [])[ci]? with
        | some oid => acc ++ [oid]
        | none => acc) []
      set W_b : World := activateGroup Wproc ordered₁
      -- tick bookkeeping
      have h_tick_Wpre : W_pre.tick = t₀ := by
        dsimp [W_pre]
        rw [gSimBurst_tick, h_tick_W₁]
      have h_tick_Wproc : Wproc.tick = t₀ := by
        dsimp [Wproc]
        rw [processNEvents_tick, h_tick_Wpre]
      have h_tick_Wb : W_b.tick = t₀ := by
        dsimp [W_b]
        rw [activateGroup_tick, h_tick_Wproc]
      -- the order right after the activateGroup step of g₁
      have h_order_Wb : evBefore W_b.events
          (stageEvent actTick groups g₁ c₁ 0)
          (stageEvent actTick groups g₁ c₂ 0) := by
        dsimp [W_b]
        exact activateGroup_stage0_order actTick groups withinOrd Wproc
          g₁ c₁ c₂ h_g₁ h_c₁ h_c₂ h_tick_Wproc h_ord_split
      -- the remaining burst steps keep the order: both events target t₀ + 2
      have h_carry_B : evBefore W_B.events
          (stageEvent actTick groups g₁ c₁ 0)
          (stageEvent actTick groups g₁ c₂ 0) := by
        dsimp [W_B]
        rw [h_zip_split, h_burst_split, gSimBurst, List.foldl_cons]
        apply evBefore_gSimBurst_of_notDue t₀ (buildGroups groups).2
          withinOrd pos W_b postP
        · dsimp [stageEvent]
          rw [stageTarget_zero_eq, h_tick_Wb]
          omega
        · dsimp [stageEvent]
          rw [stageTarget_zero_eq, h_tick_Wb]
          omega
        · exact h_order_Wb
      -- both events target t₀ + 2, so the drain step keeps the order
      have h_tick_WB : W_B.tick = t₀ := by
        dsimp [W_B]
        rw [gSimBurst_tick, h_tick_W₁]
      have h_ev₁ : stageEvent actTick groups g₁ c₁ 0 ∈ W_B.events :=
        evBefore.mem_left h_carry_B
      have h_ev₂ : stageEvent actTick groups g₁ c₂ 0 ∈ W_B.events :=
        evBefore.mem_right h_carry_B
      have h_nd₁ : (stageEvent actTick groups g₁ c₁ 0).targetTick ≠
          W_B.tick := by
        dsimp [stageEvent]
        rw [stageTarget_zero_eq, h_tick_WB]
        omega
      have h_nd₂ : (stageEvent actTick groups g₁ c₂ 0).targetTick ≠
          W_B.tick := by
        dsimp [stageEvent]
        rw [stageTarget_zero_eq, h_tick_WB]
        omega
      exact World.stepUntilNextTick_notDue_order W_B _ _ h_ev₁ h_ev₂
        h_nd₁ h_nd₂ h_carry_B
  -- transport from tick t₀ + 1 to the pop tick t₀ + 2
  dsimp [popQueueWorld]
  rw [stageTarget_zero_eq]
  apply evBefore_gSimWorld_const groups actTick groupOrd withinOrd pos
    (t₀ + 1) (t₀ + 2) (stageEvent actTick groups g₁ c₁ 0)
    (stageEvent actTick groups g₁ c₂ 0) (by omega) h_order_succ
  · show t₀ + 2 ≤ (stageEvent actTick groups g₁ c₁ 0).targetTick
    rw [show (stageEvent actTick groups g₁ c₁ 0).targetTick = t₀ + 2 from by
      dsimp [stageEvent, t₀]
      rw [stageTarget_zero_eq]]
  · show t₀ + 2 ≤ (stageEvent actTick groups g₁ c₂ 0).targetTick
    rw [show (stageEvent actTick groups g₁ c₂ 0).targetTick = t₀ + 2 from by
      dsimp [stageEvent, t₀]
      rw [stageTarget_zero_eq]]

/-! ## Pop-machinery helpers for the m = 0 mixed phase

Reproven from FinalConverseMixedPhase (private there). -/

/-- `(l₁ ++ l₂).drop l₁.length = l₂` (reproven; private in FinalConverseMixedPhase). -/
private theorem drop_append_self' {α : Type} (l₁ l₂ : List α) :
    (l₁ ++ l₂).drop l₁.length = l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a l ih => simp [ih]

/-- Append cancellation on the left (reproven; private in FinalConverseMixedPhase). -/
private theorem append_left_cancel'' {α : Type} (l l₁ l₂ : List α)
    (h : l ++ l₁ = l ++ l₂) : l₁ = l₂ := by
  induction l generalizing l₁ l₂ with
  | nil => simpa using h
  | cons a l ih =>
    simp only [List.cons_append] at h
    exact ih l₁ l₂ (by simpa using congrArg List.tail h)

/-- In a split `l ++ r = p ++ s` with `p` at least as long as `l`, the
    prefix `p` starts with `l` (reproven; private in FinalConverseMixedPhase). -/
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

/-- In `l ++ r = p ++ x :: q` with a short `p`, `x` lies in `l`
    (reproven; private in FinalConverseMixedPhase). -/
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
    already holds in `r` (reproven; private in FinalConverseMixedPhase). -/
private theorem evBefore_append_left_absent' {l r : List ScheduledEvent}
    {x y : ScheduledEvent} (h_x : x ∉ l) (h : evBefore (l ++ r) x y) :
    evBefore r x y := by
  obtain ⟨p, q, h_eq, h_y⟩ := h
  have h_len : l.length ≤ p.length := by
    by_contra h_lt
    exact h_x (mem_left_of_short_prefix_split' l r p q x h_eq (by omega))
  obtain ⟨p₁, _, h_r⟩ := append_prefix_of_length_le' l r p (x :: q) h_eq h_len
  exact ⟨p₁, q, h_r, h_y⟩

/-- A filter is empty when no member satisfies the predicate
    (reproven; private in FinalConverseMixedPhase). -/
private theorem filter_empty_of_none' {α : Type} (p : α → Bool)
    (l : List α) (h : ∀ x ∈ l, p x = false) : l.filter p = [] := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp [List.filter, h x (List.mem_cons.mpr (Or.inl rfl)),
      ih (fun y hy => h y (List.mem_cons.mpr (Or.inr hy)))]

/-- A Nat inequality decides the `==` comparison to false (reproven;
    private in FinalConverseMixedPhase). -/
private theorem nat_beq_false_of_ne' (a b : Nat) (h : a ≠ b) :
    (a == b) = false := by
  simp [h]

/-- Equal node lists give equal node lists after one
    `onScheduledTick`. Only signal levels change (reproven; private in
    FinalConverseMixedPhase). -/
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

/-- With no due events the spawn accumulator is empty (reproven;
    private in FinalConverseMixedPhase). -/
private theorem popSpawnAcc_of_no_due' (w : World) (fuel : Nat)
    (h_no : ∀ ev ∈ w.events, ev.targetTick ≠ w.tick) :
    World.popSpawnAcc w fuel = [] := by
  induction fuel with
  | zero => dsimp [World.popSpawnAcc]
  | succ fuel ih =>
    dsimp only [World.popSpawnAcc]
    rw [World.popNextEvent_none_of_no_due w h_no]

/-- The spawn accumulator splits over a fuel sum (reproven; private in
    FinalConverseMixedPhase). -/
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
    the due filter. Two such worlds accumulate the same spawns
    (reproven; private in FinalConverseMixedPhase). -/
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

/-- Total pop fuel spent by the `processNEvents` phases of a burst
    (reproven; private in FinalConverseMixedPhase). -/
private def burstFuel' (t : Nat) (pos : Nat → List Nat) :
    List (Nat × Nat) → Nat
  | [] => 0
  | (_, k) :: ps => (pos t)[k]?.getD 0 + burstFuel' t pos ps

/-- The non-due, non-zero-priority part of the burst result: the old
    filtered queue plus the filtered spawn accumulator of the popped
    due events. The observer batches drop out of the filter
    (reproven; private in FinalConverseMixedPhase). -/
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

/-- Every popped event spawns at most one event (reproven; private in
    FinalConverseMixedPhase). -/
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

/-- Only the reference stage event spawns its reference successor
    (reproven; private in FinalConverseMixedPhase). -/
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

/-- Distinct pops spawn distinct events (reproven; private in
    FinalConverseMixedPhase). -/
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

/-- Equal middle delays and equal last delay give equal `ChainSpec`
    (reproven; private in ConverseSpawnFinal). -/
private theorem ChainSpec_eq' (a b : ChainSpec)
    (h_md : a.middleDelays = b.middleDelays)
    (h_ld : a.lastDelay = b.lastDelay) : a = b := by
  cases a
  cases b
  dsimp at h_md h_ld ⊢
  simp [h_md, h_ld]

/-- The witness chain of `ConverseSpawnFinal` has the same `ChainSpec`
    as the reference chain, with the middle-delay length exposed
    (variant of ConverseSpawnFinal `chainSpec_eq_of_ConverseSpawnFinal`). -/
private theorem chainSpec_eq' (groups : List GroupSpec)
    (actTick : Nat → Nat) (w : World)
    (g₁ c₁ g₂ c₂ m : Nat) (e : ScheduledEvent)
    (h_m : (chainAt groups g₁ c₁).middleDelays.length = m)
    (h_cs : ConverseSpawnFinal groups actTick w g₁ c₁ g₂ c₂ m e) :
    ∃ g c, g < groups.length ∧ c < (groupAt groups g).length ∧
      (chainAt groups g c).middleDelays.length = m ∧
      e = stageEvent actTick groups g c (m + 1) ∧
      chainAt groups g c = chainAt groups g₁ c₁ := by
  rcases ConverseSpawnFinal_stageTarget_middle groups actTick w
      g₁ c₁ g₂ c₂ m e h_cs with
    ⟨g, c, h_g, h_c, h_len, h_ev, h_pref, h_tgt_succ, h_tgt_mid⟩
  have h_gc_m : (chainAt groups g c).middleDelays.length = m :=
    h_len.trans h_m
  have h_md : (chainAt groups g c).middleDelays =
      (chainAt groups g₁ c₁).middleDelays :=
    prefixDelays_final_eq_middleDelays_eq groups g c g₁ c₁ m
      h_gc_m h_m h_pref
  have h_cum : stageCumDelay (chainAt groups g c) m =
      stageCumDelay (chainAt groups g₁ c₁) m := by
    rw [stageCumDelay_of_le_middle (chainAt groups g c) m (by omega),
      stageCumDelay_of_le_middle (chainAt groups g₁ c₁) m (by omega),
      h_md]
  have h_act : actTick g = actTick g₁ := by
    dsimp [stageTarget] at h_tgt_mid
    rw [h_cum] at h_tgt_mid
    omega
  have h_cumA : stageCumDelay (chainAt groups g c) (m + 1) =
      stageCumDelay (chainAt groups g c) m +
        ((chainAt groups g c).lastDelay : Nat) := by
    rw [show m + 1 = (chainAt groups g c).middleDelays.length + 1 by
        omega,
      show m = (chainAt groups g c).middleDelays.length by omega]
    exact stageCumDelay_succ_last (chainAt groups g c)
  have h_cumB : stageCumDelay (chainAt groups g₁ c₁) (m + 1) =
      stageCumDelay (chainAt groups g₁ c₁) m +
        ((chainAt groups g₁ c₁).lastDelay : Nat) := by
    rw [show m + 1 =
        (chainAt groups g₁ c₁).middleDelays.length + 1 by omega,
      show m = (chainAt groups g₁ c₁).middleDelays.length by omega]
    exact stageCumDelay_succ_last (chainAt groups g₁ c₁)
  have h_last_nat : ((chainAt groups g c).lastDelay : Nat) =
      ((chainAt groups g₁ c₁).lastDelay : Nat) := by
    dsimp [stageTarget] at h_tgt_succ
    rw [h_cumA, h_cumB, h_cum, h_act] at h_tgt_succ
    omega
  refine ⟨g, c, h_g, h_c, h_gc_m, h_ev, ?_⟩
  exact ChainSpec_eq' (chainAt groups g c)
    (chainAt groups g₁ c₁) h_md (Subtype.ext h_last_nat)

/-- The tail after a given element is determined by the split in a
    duplicate-free list. -/
private theorem tail_split_unique_of_nodup {α : Type} {l : List α}
    (h_nd : l.Nodup) (y : α) {p₁ q₁ p₂ q₂ : List α}
    (h₁ : l = p₁ ++ y :: q₁) (h₂ : l = p₂ ++ y :: q₂) : q₁ = q₂ := by
  revert l h_nd h₁ h₂
  induction p₁ generalizing p₂ q₂ with
  | nil =>
    intro l h_nd h₁ h₂
    subst h₁
    cases h_nd with
    | cons h_y_nd _ =>
      cases p₂ with
      | nil =>
        injection h₂
      | cons b p₂' =>
        simp only [List.cons_append] at h₂
        injection h₂ with _ h_rest
        have h_y_q₁ : y ∈ q₁ := by
          rw [h_rest]
          apply List.mem_append_right p₂'
          exact List.mem_cons.mpr (Or.inl rfl)
        exfalso
        exact h_y_nd y h_y_q₁ rfl
  | cons c p₁ ih =>
    intro l h_nd h₁ h₂
    subst h₁
    cases h_nd with
    | cons h_c_nd h_nd_l =>
      cases p₂ with
      | nil =>
        simp only [List.nil_append] at h₂
        injection h₂ with h_cy _
        have h_y_mem : y ∈ p₁ ++ y :: q₁ := by
          apply List.mem_append_right p₁
          exact List.mem_cons.mpr (Or.inl rfl)
        exfalso
        exact h_c_nd y h_y_mem h_cy
      | cons d p₂' =>
        simp only [List.cons_append] at h₂
        injection h₂ with _ h_rest
        exact ih (l := p₁ ++ y :: q₁) (h_nd := h_nd_l) (h₁ := rfl)
          (h₂ := h_rest)

/-- Betweenness is transitive on duplicate-free lists. -/
private theorem evBefore_trans' {l : List ScheduledEvent}
    (h_nd : l.Nodup) {x y z : ScheduledEvent}
    (h_xy : evBefore l x y) (h_yz : evBefore l y z) : evBefore l x z := by
  obtain ⟨p, q, h_eq, h_yq⟩ := h_xy
  obtain ⟨a, b, h_q⟩ := split_at_mem q y h_yq
  obtain ⟨p₂, q₂, h_eq₂, h_zq₂⟩ := h_yz
  have h_l_split : l = (p ++ x :: a) ++ y :: b := by
    rw [h_eq, h_q]
    simp only [List.append_assoc, List.cons_append]
  have h_q_eq : b = q₂ :=
    tail_split_unique_of_nodup h_nd y h_l_split h_eq₂
  refine ⟨p, a ++ y :: b, ?_, ?_⟩
  · rw [h_eq, h_q]
  · rw [h_q_eq]
    apply List.mem_append_right a
    exact List.mem_cons.mpr (Or.inr h_zq₂)

/-- The clustering capstone core. -/
theorem group_output_clustering_core (groups : List GroupSpec)
    (h_valid : ∀ gi (c : ChainSpec), gi < groups.length →
        c ∈ groupAt groups gi →
        (∀ d ∈ c.middleDelays, ValidDelay d) ∧ ValidDelay c.lastDelay)
    (h_uniform : ∀ gi (c₁ c₂ : ChainSpec), gi < groups.length →
        c₁ ∈ groupAt groups gi → c₂ ∈ groupAt groups gi →
        chainDelay c₁ = chainDelay c₂)
    (T : Nat)
    (actTick : Nat → Nat)
    (h_act : ∀ gi, gi < groups.length → groupAt groups gi ≠ [] →
        actTick gi + groupDelay (groupAt groups gi) = T)
    (groupOrd : List Nat)
    (h_ord : List.Perm groupOrd (List.range groups.length))
    (withinOrd : Nat → List Nat)
    (h_within : ∀ gi, gi < groups.length →
        List.Perm (withinOrd gi) (List.range (groupAt groups gi).length))
    (pos : Nat → List Nat) :
    let log := groupSimulate T groups actTick groupOrd withinOrd pos
    ∀ gi₁ ci₁ gi₂ ci₂ gi₃ ci₃ p₁ p₂ p₃,
      ci₁ < (groupAt groups gi₁).length →
      ci₂ < (groupAt groups gi₂).length →
      ci₃ < (groupAt groups gi₃).length →
      outputPos log gi₁ ci₁ = some p₁ →
      outputPos log gi₂ ci₂ = some p₂ →
      outputPos log gi₃ ci₃ = some p₃ →
      p₁ < p₂ → p₂ < p₃ →
      chainAt groups gi₁ ci₁ = chainAt groups gi₃ ci₃ →
      chainAt groups gi₂ ci₂ = chainAt groups gi₁ ci₁ := by
  intro log gi₁ ci₁ gi₂ ci₂ gi₃ ci₃ p₁ p₂ p₃ h_c₁ h_c₂ h_c₃ h_p₁ h_p₂
    h_p₃ h₁₂ h₂₃ h_spec₁₃
  -- the bounds force the group indices in range
  have h_g₁ : gi₁ < groups.length :=
    gi_lt_of_ci_lt_groupAt groups gi₁ ci₁ h_c₁
  have h_g₂ : gi₂ < groups.length :=
    gi_lt_of_ci_lt_groupAt groups gi₂ ci₂ h_c₂
  have h_g₃ : gi₃ < groups.length :=
    gi_lt_of_ci_lt_groupAt groups gi₃ ci₃ h_c₃
  -- nodup of the orders
  have h_gord_nd : groupOrd.Nodup := Nodup.of_perm h_ord List.nodup_range
  have h_within_nd : ∀ gi, gi < groups.length → (withinOrd gi).Nodup :=
    fun gi h_gi => Nodup.of_perm (h_within gi h_gi) List.nodup_range
  -- the finals bundle
  obtain ⟨blocks, finals, finalEventOf, chainOf, finalIdx, entryOf,
    h_shape, h_no_early, h_finals, h_nd, h_feq, h_block, h_match,
    h_chainOf_eq, h_eq_chainOf, h_pos⟩ :=
    groupSimulate_final_bundle T groups actTick groupOrd withinOrd pos
      h_valid h_uniform h_act h_ord h_within
  have h_shape_lb : log = logBlocks [] 0 blocks (T + 1) := by
    dsimp [log]
    exact h_shape.trans (logBlocks_zero_eq_foldl blocks (T + 1)).symm
  -- outputPos of every valid chain is T + 1 + its final-pop index
  have h_outPos : ∀ gi ci, gi < groups.length →
      ci < (groupAt groups gi).length →
      outputPos log gi ci = some (T + 1 + finalIdx gi ci) := by
    intro gi ci h_gi h_ci
    obtain ⟨pre, post, h_split, h_len⟩ := h_pos gi ci h_gi h_ci
    have h := outputPos_eq_finalPopIndex_discharged T groups actTick
      groupOrd withinOrd pos gi ci h_gi h_ci blocks h_shape_lb h_no_early
      finals h_nd chainOf finalEventOf entryOf h_block h_match
      h_chainOf_eq h_eq_chainOf pre post h_split
    rw [h_len] at h
    exact h
  have h_p₁_eq : p₁ = T + 1 + finalIdx gi₁ ci₁ := by
    have h := h_outPos gi₁ ci₁ h_g₁ h_c₁
    rw [h] at h_p₁
    exact Option.some_inj.mp h_p₁.symm
  have h_p₂_eq : p₂ = T + 1 + finalIdx gi₂ ci₂ := by
    have h := h_outPos gi₂ ci₂ h_g₂ h_c₂
    rw [h] at h_p₂
    exact Option.some_inj.mp h_p₂.symm
  have h_p₃_eq : p₃ = T + 1 + finalIdx gi₃ ci₃ := by
    have h := h_outPos gi₃ ci₃ h_g₃ h_c₃
    rw [h] at h_p₃
    exact Option.some_inj.mp h_p₃.symm
  have h_idx₁₂ : finalIdx gi₁ ci₁ < finalIdx gi₂ ci₂ := by
    rw [h_p₁_eq, h_p₂_eq] at h₁₂
    omega
  have h_idx₂₃ : finalIdx gi₂ ci₂ < finalIdx gi₃ ci₃ := by
    rw [h_p₂_eq, h_p₃_eq] at h₂₃
    omega
  -- index order is evBefore order of the final events
  have h_ev₁₂ : evBefore finals (finalEventOf gi₁ ci₁)
      (finalEventOf gi₂ ci₂) :=
    (chain_entries_are_final_pops finals h_nd finalEventOf finalIdx
      gi₁ ci₁ gi₂ ci₂ (h_pos gi₁ ci₁ h_g₁ h_c₁)
      (h_pos gi₂ ci₂ h_g₂ h_c₂)).mp h_idx₁₂
  have h_ev₂₃ : evBefore finals (finalEventOf gi₂ ci₂)
      (finalEventOf gi₃ ci₃) :=
    (chain_entries_are_final_pops finals h_nd finalEventOf finalIdx
      gi₂ ci₂ gi₃ ci₃ (h_pos gi₂ ci₂ h_g₂ h_c₂)
      (h_pos gi₃ ci₃ h_g₃ h_c₃)).mp h_idx₂₃
  -- the three final events and the reference middle length
  set f₁ := stageEvent actTick groups gi₁ ci₁
    ((chainAt groups gi₁ ci₁).middleDelays.length + 1)
  set e := stageEvent actTick groups gi₂ ci₂
    ((chainAt groups gi₂ ci₂).middleDelays.length + 1)
  set f₃ := stageEvent actTick groups gi₃ ci₃
    ((chainAt groups gi₃ ci₃).middleDelays.length + 1)
  set m := (chainAt groups gi₁ ci₁).middleDelays.length
  -- betweenness in the tick-T due filter
  have h_due₁₂ : evBefore
      ((gSimWorld groups actTick groupOrd withinOrd pos T).events.filter
        (fun ev => ev.targetTick == T)) f₁ e := by
    have h := h_ev₁₂
    rw [h_finals] at h
    rw [show finalEventOf gi₁ ci₁ = f₁ from by
      dsimp [f₁]; exact (h_feq gi₁ ci₁).symm] at h
    rw [show finalEventOf gi₂ ci₂ = e from by
      dsimp [e]; exact (h_feq gi₂ ci₂).symm] at h
    exact h
  have h_due₂₃ : evBefore
      ((gSimWorld groups actTick groupOrd withinOrd pos T).events.filter
        (fun ev => ev.targetTick == T)) e f₃ := by
    have h := h_ev₂₃
    rw [h_finals] at h
    rw [show finalEventOf gi₂ ci₂ = e from by
      dsimp [e]; exact (h_feq gi₂ ci₂).symm] at h
    rw [show finalEventOf gi₃ ci₃ = f₃ from by
      dsimp [f₃]; exact (h_feq gi₃ ci₃).symm] at h
    exact h
  have h_nd_due :
      ((gSimWorld groups actTick groupOrd withinOrd pos T).events.filter
        (fun ev => ev.targetTick == T)).Nodup := by
    rwa [← h_finals]
  have h_ne_left : f₁ ≠ e := evBefore.ne_of_nodup h_nd_due h_due₁₂
  have h_ne_right : e ≠ f₃ := evBefore.ne_of_nodup h_nd_due h_due₂₃
  -- the activation ticks of the two reference groups coincide
  have h_g₁_ne : groupAt groups gi₁ ≠ [] := by
    intro h_empty
    rw [h_empty] at h_c₁
    cases h_c₁
  have h_g₃_ne : groupAt groups gi₃ ≠ [] := by
    intro h_empty
    rw [h_empty] at h_c₃
    cases h_c₃
  have h_delay₁ : groupDelay (groupAt groups gi₁) =
      chainDelay (chainAt groups gi₁ ci₁) := by
    cases h_decomp : groupAt groups gi₁ with
    | nil => contradiction
    | cons c_head cs =>
      have h_head_mem : c_head ∈ groupAt groups gi₁ := by
        rw [h_decomp]
        simp
      have h_spec_mem : chainAt groups gi₁ ci₁ ∈ groupAt groups gi₁ :=
        chainAt_mem groups gi₁ ci₁ h_c₁
      dsimp [groupDelay]
      exact h_uniform gi₁ c_head (chainAt groups gi₁ ci₁) h_g₁ h_head_mem
        h_spec_mem
  have h_delay₃ : groupDelay (groupAt groups gi₃) =
      chainDelay (chainAt groups gi₃ ci₃) := by
    cases h_decomp : groupAt groups gi₃ with
    | nil => contradiction
    | cons c_head cs =>
      have h_head_mem : c_head ∈ groupAt groups gi₃ := by
        rw [h_decomp]
        simp
      have h_spec_mem : chainAt groups gi₃ ci₃ ∈ groupAt groups gi₃ :=
        chainAt_mem groups gi₃ ci₃ h_c₃
      dsimp [groupDelay]
      exact h_uniform gi₃ c_head (chainAt groups gi₃ ci₃) h_g₃ h_head_mem
        h_spec_mem
  have h_act_eq : actTick gi₁ = actTick gi₃ := by
    have h_a := h_act gi₁ h_g₁ h_g₁_ne
    have h_b := h_act gi₃ h_g₃ h_g₃_ne
    rw [h_delay₁] at h_a
    rw [h_delay₃, ← h_spec₁₃] at h_b
    omega
  have h_m₃ : (chainAt groups gi₃ ci₃).middleDelays.length = m := by
    dsimp [m]
    rw [← h_spec₁₃]
  -- the m-indexed forms of the right-hand facts
  have h_due₂₃_m : evBefore
      ((gSimWorld groups actTick groupOrd withinOrd pos T).events.filter
        (fun ev => ev.targetTick == T)) e
      (stageEvent actTick groups gi₃ ci₃ (m + 1)) := by
    rw [show m + 1 = (chainAt groups gi₃ ci₃).middleDelays.length + 1
      from by rw [← h_m₃]]
    exact h_due₂₃
  have h_ne_right_m : e ≠ stageEvent actTick groups gi₃ ci₃ (m + 1) := by
    rw [show m + 1 = (chainAt groups gi₃ ci₃).middleDelays.length + 1
      from by rw [← h_m₃]]
    exact h_ne_right
  -- the middle final's parent pop tick equals the reference stage-m tick
  have h_spawn_e : stageTarget actTick groups gi₂ ci₂
      ((chainAt groups gi₂ ci₂).middleDelays.length) =
      stageTarget actTick groups gi₁ ci₁ m :=
    final_spawnTick_eq_of_dueBetween groups actTick groupOrd withinOrd pos
      T h_valid h_uniform h_act h_ord h_within gi₁ ci₁ gi₂ ci₂ gi₃ ci₃ m
      h_g₁ h_c₁ h_g₂ h_c₂ h_g₃ h_c₃ (by dsimp [m]) h_m₃
      (by
        intro h_lt
        have h_eq := (sameSpec_stageTarget groups actTick gi₁ ci₁ gi₃ ci₃
          m h_act_eq h_spec₁₃).symm
        omega)
      h_due₁₂ h_due₂₃_m
  -- withinOrd membership of the reference chains
  have h_c₁_in : ci₁ ∈ withinOrd gi₁ :=
    (List.Perm.mem_iff (h_within gi₁ h_g₁) (a := ci₁)).mpr
      (List.mem_range.mpr h_c₁)
  have h_c₃_in : ci₃ ∈ withinOrd gi₃ :=
    (List.Perm.mem_iff (h_within gi₃ h_g₃) (a := ci₃)).mpr
      (List.mem_range.mpr h_c₃)
  -- the stage-0 base order, oriented by the observed final order
  have h_base₀ : evBefore
      ((popQueueWorld groups actTick groupOrd withinOrd pos
        gi₁ ci₁ 0).events)
      (stageEvent actTick groups gi₁ ci₁ 0)
      (stageEvent actTick groups gi₃ ci₃ 0) := by
    by_cases h_same : gi₁ = gi₃
    · subst h_same
      have h_ci_ne : ci₁ ≠ ci₃ := by
        intro h_eq
        subst h_eq
        injection h_p₁.symm.trans h_p₃ with h_eq_p
        omega
      obtain h_dir | h_dir := list_order_total (withinOrd gi₁)
        (h_within_nd gi₁ h_g₁) ci₁ ci₃ h_c₁_in h_c₃_in h_ci_ne
      · exact sameSpec_stage_evBefore_base_sameGroup groups actTick
          groupOrd withinOrd pos h_ord gi₁ ci₁ ci₃ h_g₁ h_c₁ h_c₃ h_dir
      · exfalso
        have h_base_R := sameSpec_stage_evBefore_base_sameGroup groups
          actTick groupOrd withinOrd pos h_ord gi₁ ci₃ ci₁ h_g₁ h_c₃
          h_c₁ h_dir
        have h_ind_R : evBefore
            ((popQueueWorld groups actTick groupOrd withinOrd pos
              gi₁ ci₃
              ((chainAt groups gi₁ ci₃).middleDelays.length + 1)).events)
            (stageEvent actTick groups gi₁ ci₃
              ((chainAt groups gi₁ ci₃).middleDelays.length + 1))
            (stageEvent actTick groups gi₁ ci₁
              ((chainAt groups gi₁ ci₃).middleDelays.length + 1)) :=
          sameSpec_stage_evBefore_ind_self groups actTick groupOrd
            withinOrd pos gi₁ ci₃ gi₁ ci₁
            ((chainAt groups gi₁ ci₃).middleDelays.length + 1) h_g₁ h_c₃
            h_g₁ h_c₁ h_spec₁₃.symm h_act_eq.symm (by omega) h_base_R
            (fun k _ => NodeLayoutOk_gSimWorld groups actTick groupOrd
              withinOrd pos (stageTarget actTick groups gi₁ ci₃ k))
            (fun k hk => sameSpec_h_nodup_discharge groups actTick
              groupOrd withinOrd pos gi₁ ci₃ h_gord_nd h_within_nd k
              (by omega))
        dsimp [popQueueWorld] at h_ind_R
        have h_T_R : stageTarget actTick groups gi₁ ci₃
            ((chainAt groups gi₁ ci₃).middleDelays.length + 1) = T :=
          stageTarget_final_eq_T groups actTick T gi₁ ci₃ h_g₁ h_c₃
            h_uniform h_act
        rw [h_T_R] at h_ind_R
        have h_conv : stageEvent actTick groups gi₁ ci₁
            ((chainAt groups gi₁ ci₃).middleDelays.length + 1) = f₁ := by
          dsimp [f₁]
          rw [show (chainAt groups gi₁ ci₃).middleDelays.length + 1 =
              (chainAt groups gi₁ ci₁).middleDelays.length + 1 from by
            dsimp [m] at h_m₃
            omega]
        rw [h_conv] at h_ind_R
        have h_fwd : evBefore
            ((gSimWorld groups actTick groupOrd withinOrd pos T).events)
            f₁ f₃ :=
          evBefore_trans' (gSimWorld_events_Nodup groups actTick groupOrd
            withinOrd pos T h_gord_nd h_within_nd)
            (evBefore.of_filter (fun ev => ev.targetTick == T) h_due₁₂)
            (evBefore.of_filter (fun ev => ev.targetTick == T) h_due₂₃)
        exact evBefore.asymm (gSimWorld_events_Nodup groups actTick
          groupOrd withinOrd pos T h_gord_nd h_within_nd) h_fwd h_ind_R
    · have h_disj := burst_order_total groups actTick groupOrd gi₁ gi₃
        (actTick gi₁) h_ord h_g₁ h_g₃ h_same rfl h_act_eq.symm
      cases h_disj with
      | inl h_burst =>
        exact sameSpec_stage_evBefore_base groups actTick groupOrd
          withinOrd pos gi₁ ci₁ gi₃ ci₃ h_g₁ h_c₁ h_g₃ h_c₃ h_c₁_in
          h_c₃_in h_act_eq h_burst
      | inr h_burst_R =>
        exfalso
        have h_eq_pred : (fun gi =>
            decide (gi < (buildGroups groups).2.length) &&
            (actTick gi == actTick gi₁)) = (fun gi =>
            decide (gi < (buildGroups groups).2.length) &&
            (actTick gi == actTick gi₃)) := by
          ext gi
          simp [h_act_eq]
        rw [h_eq_pred] at h_burst_R
        have h_base_R := sameSpec_stage_evBefore_base groups actTick
          groupOrd withinOrd pos gi₃ ci₃ gi₁ ci₁ h_g₃ h_c₃ h_g₁ h_c₁
          h_c₃_in h_c₁_in h_act_eq.symm h_burst_R
        have h_ind_R : evBefore
            ((popQueueWorld groups actTick groupOrd withinOrd pos
              gi₃ ci₃
              ((chainAt groups gi₃ ci₃).middleDelays.length + 1)).events)
            (stageEvent actTick groups gi₃ ci₃
              ((chainAt groups gi₃ ci₃).middleDelays.length + 1))
            (stageEvent actTick groups gi₁ ci₁
              ((chainAt groups gi₃ ci₃).middleDelays.length + 1)) :=
          sameSpec_stage_evBefore_ind_self groups actTick groupOrd
            withinOrd pos gi₃ ci₃ gi₁ ci₁
            ((chainAt groups gi₃ ci₃).middleDelays.length + 1) h_g₃ h_c₃
            h_g₁ h_c₁ h_spec₁₃.symm h_act_eq.symm (by omega) h_base_R
            (fun k _ => NodeLayoutOk_gSimWorld groups actTick groupOrd
              withinOrd pos (stageTarget actTick groups gi₃ ci₃ k))
            (fun k hk => sameSpec_h_nodup_discharge groups actTick
              groupOrd withinOrd pos gi₃ ci₃ h_gord_nd h_within_nd k
              (by omega))
        dsimp [popQueueWorld] at h_ind_R
        have h_T_R : stageTarget actTick groups gi₃ ci₃
            ((chainAt groups gi₃ ci₃).middleDelays.length + 1) = T :=
          stageTarget_final_eq_T groups actTick T gi₃ ci₃ h_g₃ h_c₃
            h_uniform h_act
        rw [h_T_R] at h_ind_R
        have h_conv : stageEvent actTick groups gi₁ ci₁
            ((chainAt groups gi₃ ci₃).middleDelays.length + 1) = f₁ := by
          dsimp [f₁]
          rw [show (chainAt groups gi₃ ci₃).middleDelays.length + 1 =
              (chainAt groups gi₁ ci₁).middleDelays.length + 1 from by
            dsimp [m] at h_m₃
            omega]
        rw [h_conv] at h_ind_R
        have h_fwd : evBefore
            ((gSimWorld groups actTick groupOrd withinOrd pos T).events)
            f₁ f₃ :=
          evBefore_trans' (gSimWorld_events_Nodup groups actTick groupOrd
            withinOrd pos T h_gord_nd h_within_nd)
            (evBefore.of_filter (fun ev => ev.targetTick == T) h_due₁₂)
            (evBefore.of_filter (fun ev => ev.targetTick == T) h_due₂₃)
        exact evBefore.asymm (gSimWorld_events_Nodup groups actTick
          groupOrd withinOrd pos T h_gord_nd h_within_nd) h_fwd h_ind_R
  -- case split on the number of middle delays
  by_cases h_m0 : m = 0
  · -- Case m = 0: the reference stage-0 events are priority-0 observers
    dsimp [m] at h_m0
    have h_m₃₀ : (chainAt groups gi₃ ci₃).middleDelays.length = 0 := by
      rwa [← h_spec₁₃]
    have h_spawn_e₀ : stageTarget actTick groups gi₂ ci₂
        ((chainAt groups gi₂ ci₂).middleDelays.length) =
        stageTarget actTick groups gi₁ ci₁ 0 := by
      dsimp [m] at h_spawn_e
      rwa [h_m0] at h_spawn_e
    set τ₀ := stageTarget actTick groups gi₁ ci₁ 0
    set wQ₀ := popQueueWorld groups actTick groupOrd withinOrd pos
      gi₁ ci₁ 0
    set w_log₀ : World := wQ₀.logOutput s!"tick {τ₀}"
    set W_B₀ := preStepWorld groups actTick groupOrd withinOrd pos
      gi₁ ci₁ 0
    have h_tick_Q₀ : wQ₀.tick = τ₀ := by
      dsimp [wQ₀, popQueueWorld, τ₀]
      rw [gSimWorld_tick]
    have h_tick_log₀ : w_log₀.tick = τ₀ := by
      dsimp [w_log₀]
      rw [h_tick_Q₀]
    have h_tgt₂₀ : stageTarget actTick groups gi₃ ci₃ 0 = τ₀ := by
      dsimp [τ₀]
      exact (sameSpec_stageTarget groups actTick gi₁ ci₁ gi₃ ci₃ 0
        h_act_eq h_spec₁₃).symm
    -- the right-hand facts in the stageEvent-1 form
    have h_due₁₂₀ : evBefore
        ((gSimWorld groups actTick groupOrd withinOrd pos T).events.filter
          (fun ev => ev.targetTick == T))
        (stageEvent actTick groups gi₁ ci₁ 1) e := by
      have h := h_due₁₂
      dsimp [f₁] at h
      rw [h_m0] at h
      exact h
    have h_due₂₃₀ : evBefore
        ((gSimWorld groups actTick groupOrd withinOrd pos T).events.filter
          (fun ev => ev.targetTick == T)) e
        (stageEvent actTick groups gi₃ ci₃ 1) := by
      convert h_due₂₃ using 1
      dsimp [f₃]
      rw [h_m₃₀]
    have h_ne_right₀ : e ≠ stageEvent actTick groups gi₃ ci₃ 1 := by
      convert h_ne_right using 1
      dsimp [f₃]
      rw [h_m₃₀]
    have h_ne_left₀ : stageEvent actTick groups gi₁ ci₁ 1 ≠ e := by
      have h := h_ne_left
      dsimp [f₁] at h
      rw [h_m0] at h
      exact h
    -- layout, nodup, StageMemAt at the two worlds
    have h_layout_log₀ : NodeLayoutOk groups w_log₀ := by
      dsimp [w_log₀, wQ₀, popQueueWorld]
      exact NodeLayoutOk_logOutput groups
        (gSimWorld groups actTick groupOrd withinOrd pos
          (stageTarget actTick groups gi₁ ci₁ 0)) s!"tick {τ₀}"
        (NodeLayoutOk_gSimWorld groups actTick groupOrd withinOrd pos
          (stageTarget actTick groups gi₁ ci₁ 0))
    obtain ⟨h_ok_B₀, h_layout_B₀⟩ := preStepWorld_tickQueueOk groups actTick
      groupOrd withinOrd pos h_gord_nd h_within_nd gi₁ ci₁ 0
    have h_nd_WB₀ : W_B₀.events.Nodup := h_ok_B₀.1
    have h_stage_WB₀ : StageMemAt groups actTick W_B₀ W_B₀.tick :=
      StageMemAt_of_TickQueueOk groups actTick W_B₀ _ h_ok_B₀
    have h_nd_due_WB₀ : (W_B₀.events.filter
        (fun ev => ev.targetTick == W_B₀.tick)).Nodup :=
      List.Nodup.filter (fun ev => ev.targetTick == W_B₀.tick) h_ok_B₀.1
    have h_stage_log₀ : StageMemAt groups actTick w_log₀ w_log₀.tick := by
      rw [h_tick_log₀]
      dsimp [w_log₀, wQ₀, popQueueWorld]
      exact StageMemAt_logOutput groups actTick
        (gSimWorld groups actTick groupOrd withinOrd pos
          (stageTarget actTick groups gi₁ ci₁ 0)) s!"tick {τ₀}"
        (stageTarget actTick groups gi₁ ci₁ 0)
        (StageMemAt_gSimWorld groups actTick groupOrd withinOrd pos
          (stageTarget actTick groups gi₁ ci₁ 0))
    have h_nd_due_log₀ : (w_log₀.events.filter
        (fun ev => ev.targetTick == w_log₀.tick)).Nodup := by
      rw [World.logOutput_events, h_tick_log₀]
      exact List.Nodup.filter (fun ev => ev.targetTick ==
        stageTarget actTick groups gi₁ ci₁ 0)
        (gSimWorld_events_Nodup groups actTick groupOrd withinOrd pos
          (stageTarget actTick groups gi₁ ci₁ 0) h_gord_nd h_within_nd)
    -- the stage-0 order in the pre-burst due filter
    have hAD₀ : evBefore (w_log₀.events.filter
        (fun ev => ev.targetTick == w_log₀.tick))
        (stageEvent actTick groups gi₁ ci₁ 0)
        (stageEvent actTick groups gi₃ ci₃ 0) := by
      have h := h_base₀
      rw [World.logOutput_events, h_tick_log₀]
      apply evBefore.filter (fun ev => ev.targetTick ==
        stageTarget actTick groups gi₁ ci₁ 0)
      · dsimp [stageEvent]
        simp
      · dsimp [stageEvent]
        rw [h_tgt₂₀]
        dsimp [τ₀]
        simp
      · exact h
    -- membership and absence at the pre-burst queue
    have hA₀_mem : stageEvent actTick groups gi₁ ci₁ 0 ∈ w_log₀.events := by
      rw [World.logOutput_events]
      dsimp [wQ₀, popQueueWorld]
      exact stageEvent_mem_gSimWorld groups actTick groupOrd withinOrd pos
        h_valid h_ord h_within gi₁ ci₁ h_g₁ h_c₁ 0 (by omega)
    have hD₀_mem : stageEvent actTick groups gi₃ ci₃ 0 ∈ w_log₀.events := by
      rw [World.logOutput_events]
      dsimp [wQ₀, popQueueWorld]
      have h_mem := stageEvent_mem_gSimWorld groups actTick groupOrd
        withinOrd pos h_valid h_ord h_within gi₃ ci₃ h_g₃ h_c₃ 0 (by omega)
      rwa [h_tgt₂₀] at h_mem
    have h_sA₀_absent : stageEvent actTick groups gi₁ ci₁ 1 ∉
        w_log₀.events := by
      rw [World.logOutput_events]
      dsimp [wQ₀, popQueueWorld]
      exact stageEvent_succ_not_mem_gSimWorld groups actTick groupOrd
        withinOrd pos gi₁ ci₁ 0 (stageTarget actTick groups gi₁ ci₁ 0)
        h_g₁ h_c₁ (by omega) rfl
    have h_sD₀_absent : stageEvent actTick groups gi₃ ci₃ 1 ∉
        w_log₀.events := by
      rw [World.logOutput_events]
      dsimp [wQ₀, popQueueWorld]
      exact stageEvent_succ_not_mem_gSimWorld groups actTick groupOrd
        withinOrd pos gi₃ ci₃ 0 (stageTarget actTick groups gi₁ ci₁ 0)
        h_g₃ h_c₃ (by omega) h_tgt₂₀
    have h_e_absent_log₀ : e ∉ w_log₀.events := by
      rw [World.logOutput_events]
      dsimp [wQ₀, popQueueWorld]
      exact stageEvent_succ_not_mem_gSimWorld groups actTick groupOrd
        withinOrd pos gi₂ ci₂
        ((chainAt groups gi₂ ci₂).middleDelays.length)
        (stageTarget actTick groups gi₁ ci₁ 0) h_g₂ h_c₂ (by omega)
        h_spawn_e₀
    -- the betweenness transported to the post-burst drain queue
    obtain ⟨h_b1_s, h_b2_s⟩ := evBefore_final_stepUNT_of_dueFilter groups
      actTick groupOrd withinOrd pos T h_valid h_uniform h_act h_ord
      h_within gi₁ ci₁ gi₂ ci₂ gi₃ ci₃ 0 h_g₁ h_c₁ h_g₂ h_c₂ h_g₃ h_c₃
      h_m0 h_m₃₀ (le_of_eq h_spawn_e₀) (le_of_eq h_tgt₂₀) h_ne_left₀
      h_ne_right₀ h_due₁₂₀ h_due₂₃₀
    have h_nd_post₀ : W_B₀.stepUntilNextTick.events.Nodup := by
      rw [show W_B₀.stepUntilNextTick.events =
          (gSimWorld groups actTick groupOrd withinOrd pos
            (τ₀ + 1)).events from
        (gSimWorld_succ_events_eq_preStepWorld groups actTick groupOrd
          withinOrd pos gi₁ ci₁ 0).symm]
      exact gSimWorld_events_Nodup groups actTick groupOrd withinOrd pos
        (τ₀ + 1) h_gord_nd h_within_nd
    have h_e_tgt_T : e.targetTick = T := by
      dsimp [e, stageEvent]
      exact stageTarget_final_eq_T groups actTick T gi₂ ci₂ h_g₂ h_c₂
        h_uniform h_act
    have h_f₃_tgt_T : f₃.targetTick = T := by
      dsimp [f₃, stageEvent]
      exact stageTarget_final_eq_T groups actTick T gi₃ ci₃ h_g₃ h_c₃
        h_uniform h_act
    have h_τ₀_lt_T : τ₀ < T := by
      dsimp [τ₀]
      exact stageTarget_lt_T_of_middleLen groups actTick T gi₁ ci₁ 0 h_g₁
        h_c₁ h_uniform h_act h_m0
    have h_tick_WB₀ : W_B₀.tick = τ₀ :=
      preStepWorld_tick_eq groups actTick groupOrd withinOrd pos gi₁ ci₁ 0
    -- phase split on the two reference finals
    by_cases h₁₀ : f₁ ∈ W_B₀.events
    · have h₁₀' : stageEvent actTick groups gi₁ ci₁ 1 ∈ W_B₀.events := by
        dsimp [f₁] at h₁₀
        rw [h_m0] at h₁₀
        exact h₁₀
      by_cases h₃₀ : f₃ ∈ W_B₀.events
      · -- BURST phase at m = 0
        have h₃₀' : stageEvent actTick groups gi₃ ci₃ 1 ∈ W_B₀.events := by
          dsimp [f₃] at h₃₀
          rw [h_m₃₀] at h₃₀
          exact h₃₀
        have h_mem_e₀ : e ∈ W_B₀.events := by
          have h_f₃_surv : f₃ ∈ W_B₀.events.filter
              (fun ev => ev.targetTick ≠ W_B₀.tick) := by
            rw [List.mem_filter]
            refine ⟨h₃₀, ?_⟩
            rw [decide_eq_true_eq]
            intro h_eq
            rw [h_f₃_tgt_T, h_tick_WB₀] at h_eq
            omega
          by_contra h_e_out
          have h_e_step : e ∈ W_B₀.stepUntilNextTick.events := by
            have h_mem := stageEvent_succ_mem_range_complete groups actTick
              groupOrd withinOrd pos h_valid h_ord h_within gi₂ ci₂
              ((chainAt groups gi₂ ci₂).middleDelays.length) h_g₂ h_c₂
              (by omega) (τ₀ + 1) (by omega) (by
                rw [stageTarget_final_eq_T groups actTick T gi₂ ci₂ h_g₂
                  h_c₂ h_uniform h_act]
                omega)
            exact gSimWorld_succ_events_eq_preStepWorld groups actTick
              groupOrd withinOrd pos gi₁ ci₁ 0 ▸ h_mem
          have h_split := stepUNT_filter_split W_B₀
          rw [h_split] at h_e_step
          rcases List.mem_append.mp h_e_step with h_surv | h_acc
          · exact h_e_out (List.mem_filter.mp h_surv).1
          · have h_f₃_e : evBefore W_B₀.stepUntilNextTick.events f₃ e := by
              rw [h_split]
              apply evBefore.of_mem_append h_f₃_surv h_acc
            dsimp [f₃] at h_f₃_e
            rw [h_m₃₀] at h_f₃_e
            exact (evBefore.asymm h_nd_post₀ h_b2_s h_f₃_e).elim
        obtain ⟨h_b1_B, h_b2_B⟩ := evBefore_final_preStep_of_dueFilter
          groups actTick groupOrd withinOrd pos T h_valid h_uniform h_act
          h_ord h_within gi₁ ci₁ gi₂ ci₂ gi₃ ci₃ 0 h_g₁ h_c₁ h_g₂ h_c₂
          h_g₃ h_c₃ h_m0 h_m₃₀ (le_of_eq h_spawn_e₀) (le_of_eq h_tgt₂₀)
          h_ne_left₀ h_ne_right₀ h_due₁₂₀ h_due₂₃₀ h₁₀' h_mem_e₀ h₃₀'
          h_nd_WB₀
        have h_T₁₀ : stageTarget actTick groups gi₁ ci₁ 1 = T := by
          have h := stageTarget_final_eq_T groups actTick T gi₁ ci₁ h_g₁
            h_c₁ h_uniform h_act
          rw [h_m0] at h
          exact h
        have h_e_pri : e.priority = (-1 : Int) := by
          dsimp [e, stageEvent]
          rw [stagePri_last groups gi₂ ci₂]
        have h_cs := converse_spawn_gSimBurst_final_m0 groups actTick T τ₀
          (buildGroups groups).2 withinOrd pos w_log₀
          ((popActive groups actTick groupOrd gi₁ ci₁ 0).zipIdx)
          gi₁ ci₁ gi₃ ci₃ h_g₁ h_c₁ h_g₃ h_c₃ h_layout_log₀ h_m0 h_m₃₀
          h_tick_log₀ h_tgt₂₀ hA₀_mem hD₀_mem h_nd_due_log₀ hAD₀
          h_stage_log₀ h_sA₀_absent h_sD₀_absent e h_e_absent_log₀
          h_b1_B h_b2_B h_e_pri h_e_tgt_T h_T₁₀
        obtain ⟨g, c, h_g, h_c, h_len, h_ev, h_chain⟩ :=
          chainSpec_eq' groups actTick w_log₀ gi₁ ci₁ gi₃ ci₃ 0 e h_m0
            h_cs
        obtain ⟨h_g_eq, h_c_eq, _⟩ := stageEvent_injective actTick groups
          g c 1 gi₂ ci₂ ((chainAt groups gi₂ ci₂).middleDelays.length + 1)
          h_g h_c h_g₂ h_c₂ (by omega) (by omega) h_ev.symm
        rw [h_g_eq, h_c_eq] at h_chain
        exact h_chain
      · -- MIXED phase at m = 0: A₀ burst-popped, D₀ drained
        have h_T₁₀ : stageTarget actTick groups gi₁ ci₁ 1 = T := by
          have h := stageTarget_final_eq_T groups actTick T gi₁ ci₁ h_g₁
            h_c₁ h_uniform h_act
          rw [h_m0] at h
          exact h
        have hA₀_gone : stageEvent actTick groups gi₁ ci₁ 0 ∉
            W_B₀.events := by
          intro hA_WB
          have h_nsd := h_ok_B₀.2.2
          dsimp [NoSpawnDue] at h_nsd
          exact (h_nsd gi₁ ci₁ 0 h_g₁ h_c₁ (by omega)
            ((preStepWorld_tick_eq groups actTick groupOrd withinOrd pos
              gi₁ ci₁ 0).symm) hA_WB) h₁₀'
        have h_f₁_nd₀ : (stageEvent actTick groups gi₁ ci₁ 1).targetTick ≠
            W_B₀.tick := by
          dsimp [stageEvent]
          rw [h_T₁₀, h_tick_WB₀]
          omega
        have h_e_nd₀ : e.targetTick ≠ W_B₀.tick := by
          rw [h_e_tgt_T, h_tick_WB₀]
          omega
        by_cases h_e_B : e ∈ W_B₀.events
        · -- e was spawned during the burst: trace its parent pop
          have h_b1_WB : evBefore W_B₀.events
              (stageEvent actTick groups gi₁ ci₁ 1) e :=
            evBefore_stepUNT_backward W_B₀
              (stageEvent actTick groups gi₁ ci₁ 1) e h_nd_WB₀ h_nd_post₀
              h₁₀' h_e_B h_f₁_nd₀ h_e_nd₀ h_ne_left₀ h_b1_s
          set pPri : ScheduledEvent → Bool :=
            fun ev => decide (ev.priority ≠ (0 : Int))
          set M := burstFuel' τ₀ pos
            ((popActive groups actTick groupOrd gi₁ ci₁ 0).zipIdx)
          have h_split_B : (W_B₀.events.filter
              (fun ev => ev.targetTick ≠ w_log₀.tick)).filter pPri =
              (w_log₀.events.filter
                (fun ev => ev.targetTick ≠ w_log₀.tick)).filter pPri ++
              (World.popSpawnAcc w_log₀ M).filter pPri := by
            dsimp [W_B₀, preStepWorld, popQueueWorld, popActive, w_log₀,
              wQ₀, τ₀]
            exact gSimBurst_filter_split' τ₀ (buildGroups groups).2
              withinOrd pos w_log₀
              ((popActive groups actTick groupOrd gi₁ ci₁ 0).zipIdx)
          have h_e_pri : pPri e = true := by
            dsimp [pPri, e, stageEvent]
            rw [stagePri_last groups gi₂ ci₂]
            simp
          have h_f₁_pri : pPri (stageEvent actTick groups gi₁ ci₁ 1) =
              true := by
            dsimp [pPri, stageEvent]
            rw [show (1 : Nat) =
              (chainAt groups gi₁ ci₁).middleDelays.length + 1 by omega]
            rw [stagePri_last groups gi₁ ci₁]
            simp
          have h_e_acc : e ∈ World.popSpawnAcc w_log₀ M := by
            have h_lhs : e ∈ (W_B₀.events.filter
                (fun ev => ev.targetTick ≠ w_log₀.tick)).filter pPri := by
              rw [List.mem_filter]
              refine ⟨?_, h_e_pri⟩
              rw [List.mem_filter]
              refine ⟨h_e_B, ?_⟩
              rw [decide_eq_true_eq]
              intro h_eq
              rw [h_e_tgt_T, h_tick_log₀] at h_eq
              omega
            rw [h_split_B, List.mem_append] at h_lhs
            rcases h_lhs with h_old | h_acc
            · exact absurd (List.mem_filter.mp
                (List.mem_filter.mp h_old).1).1 h_e_absent_log₀
            · exact (List.mem_filter.mp h_acc).1
          have h_f₁_acc : stageEvent actTick groups gi₁ ci₁ 1 ∈
              World.popSpawnAcc w_log₀ M := by
            have h_lhs : stageEvent actTick groups gi₁ ci₁ 1 ∈
                (W_B₀.events.filter
                  (fun ev => ev.targetTick ≠ w_log₀.tick)).filter pPri :=
              by
              rw [List.mem_filter]
              refine ⟨?_, h_f₁_pri⟩
              rw [List.mem_filter]
              refine ⟨h₁₀', ?_⟩
              rw [decide_eq_true_eq]
              intro h_eq
              dsimp [stageEvent] at h_eq
              rw [h_T₁₀, h_tick_log₀] at h_eq
              omega
            rw [h_split_B, List.mem_append] at h_lhs
            rcases h_lhs with h_old | h_acc
            · exact absurd (List.mem_filter.mp
                (List.mem_filter.mp h_old).1).1 h_sA₀_absent
            · exact (List.mem_filter.mp h_acc).1
          have h_single_L := pops_single_spawn' groups actTick w_log₀ M
            (fun ev h_ev _ => h_stage_log₀ ev h_ev)
          have h_distinct_L := pops_distinct_spawn' groups actTick w_log₀ M
            (fun ev h_ev _ => h_stage_log₀ ev h_ev)
          have h_uniqueA_L := pops_unique_spawn' groups actTick w_log₀ M
            (stageEvent actTick groups gi₁ ci₁ 0)
            (stageEvent actTick groups gi₁ ci₁ 1) gi₁ ci₁ 0 h_g₁ h_c₁
            (by omega) rfl rfl
            (fun ev h_ev _ => h_stage_log₀ ev h_ev)
          have hA₀_pop : stageEvent actTick groups gi₁ ci₁ 0 ∈
              World.popSeqFuel w_log₀ M := by
            obtain ⟨evA, h_evA, vA, sA', h_vA, h_layA, h_spA, h_sA'⟩ :=
              mem_popSpawnAcc_singleton_spawn groups w_log₀ M
                (stageEvent actTick groups gi₁ ci₁ 1) h_layout_log₀
                h_single_L h_f₁_acc
            rwa [← h_uniqueA_L evA h_evA vA h_vA h_layA sA' h_spA
              h_sA'.symm]
          have h_b_acc : evBefore (World.popSpawnAcc w_log₀ M)
              (stageEvent actTick groups gi₁ ci₁ 1) e := by
            have h_f1 : evBefore (W_B₀.events.filter
                (fun ev => ev.targetTick ≠ w_log₀.tick))
                (stageEvent actTick groups gi₁ ci₁ 1) e := by
              apply evBefore.filter (fun ev => ev.targetTick ≠ w_log₀.tick)
              · rw [decide_eq_true_eq]
                dsimp [stageEvent]
                rw [h_T₁₀, h_tick_log₀]
                omega
              · rw [decide_eq_true_eq]
                rw [h_e_tgt_T, h_tick_log₀]
                omega
              · exact h_b1_WB
            have h_f2 : evBefore ((W_B₀.events.filter
                (fun ev => ev.targetTick ≠ w_log₀.tick)).filter pPri)
                (stageEvent actTick groups gi₁ ci₁ 1) e :=
              evBefore.filter pPri h_f₁_pri h_e_pri h_f1
            rw [h_split_B] at h_f2
            have h_f₁_not_old : stageEvent actTick groups gi₁ ci₁ 1 ∉
                (w_log₀.events.filter
                  (fun ev => ev.targetTick ≠ w_log₀.tick)).filter pPri :=
              fun h_mem => h_sA₀_absent
                ((List.mem_filter.mp (List.mem_filter.mp h_mem).1).1)
            have h_acc_f := evBefore_append_left_absent' h_f₁_not_old h_f2
            exact evBefore.of_filter pPri h_acc_f
          obtain ⟨eP, h_eP_pop, h_AP, vP, h_vP_tick, h_vP_lay, h_eP_fire,
              h_eP_fresh⟩ :=
            popSpawnAcc_left_converse groups w_log₀ M
              (stageEvent actTick groups gi₁ ci₁ 0)
              (stageEvent actTick groups gi₁ ci₁ 1) e h_layout_log₀
              h_nd_due_log₀ hA₀_pop
              (by dsimp [stageEvent]; rw [h_tick_log₀])
              h_sA₀_absent
              (by
                dsimp [stageEvent]
                rw [h_T₁₀, h_tick_log₀]
                omega)
              (by
                intro v h_v h_lay
                simpa [stageEvent] using
                  stage_spawn groups actTick v gi₁ ci₁ 0 h_g₁ h_c₁
                    (by omega) (h_v.trans h_tick_log₀) h_lay)
              h_single_L h_uniqueA_L h_distinct_L h_e_absent_log₀
              h_ne_left₀.symm h_b_acc
          have h_eP_log : eP ∈ w_log₀.events :=
            World.mem_popSeqFuel_mem_events w_log₀ M eP h_eP_pop
          have h_eP_due : eP.targetTick = w_log₀.tick :=
            World.mem_popSeqFuel_due w_log₀ M eP h_eP_pop
          obtain ⟨gi, ci, k, h_gi, h_ci, h_k_le, h_eP_eq, _, _⟩ :=
            h_stage_log₀ eP h_eP_log
          have h_eP_pri : eP.priority = (0 : Int) := by
            have h_ge : (0 : Int) ≤ eP.priority := by
              have h_mono := popSeqFuel_priority_mono w_log₀ M
                (stageEvent actTick groups gi₁ ci₁ 0) eP h_AP
              have hA_pri :
                  (stageEvent actTick groups gi₁ ci₁ 0).priority =
                    (0 : Int) := by
                dsimp [stageEvent, stagePri]
              rwa [hA_pri] at h_mono
            rw [h_eP_eq] at h_ge ⊢
            dsimp [stageEvent, stagePri] at h_ge ⊢
            split_ifs at h_ge ⊢ <;> omega
          have h_k0 : k = 0 := by
            have := congr_arg ScheduledEvent.priority h_eP_eq
            dsimp [stageEvent, stagePri] at this
            rw [h_eP_pri] at this
            split_ifs at this; omega
          have h_fire_P : (vP.onScheduledTick eP.nodeId).events =
              vP.events ++ [stageEvent actTick groups gi ci 1] := by
            rw [h_eP_eq, h_k0]
            exact stage_spawn groups actTick vP gi ci 0 h_gi h_ci
              (by omega) (by
                rw [h_vP_tick, ← h_eP_due]
                have := congr_arg ScheduledEvent.targetTick h_eP_eq
                dsimp [stageEvent] at this
                rw [h_k0] at this
                exact this) h_vP_lay
          have h_e_eq_gc1 : e = stageEvent actTick groups gi ci 1 := by
            rw [h_fire_P] at h_eP_fire
            rcases List.mem_append.mp h_eP_fire with h_old | h_new
            · exact absurd h_old h_eP_fresh
            · simpa using h_new
          have h_act_gc : actTick gi = actTick gi₁ := by
            have h_tgt0 : stageTarget actTick groups gi ci 0 =
                stageTarget actTick groups gi₁ ci₁ 0 := by
              have := congr_arg ScheduledEvent.targetTick h_eP_eq
              dsimp [stageEvent] at this
              rw [h_k0] at this
              rw [← this, h_eP_due, h_tick_log₀]
            rw [stageTarget_zero_eq, stageTarget_zero_eq] at h_tgt0
            omega
          have h_mlen_gc0 : (chainAt groups gi ci).middleDelays.length =
              0 := by
            have h_e_pri : e.priority = (-1 : Int) := by
              dsimp [e, stageEvent]
              rw [stagePri_last groups gi₂ ci₂]
            rw [h_e_eq_gc1] at h_e_pri
            dsimp [stageEvent, stagePri] at h_e_pri
            split_ifs at h_e_pri <;> omega
          have h_ld : (chainAt groups gi ci).lastDelay =
              (chainAt groups gi₁ ci₁).lastDelay := by
            have h_tgt_gc1 : stageTarget actTick groups gi ci 1 = T := by
              have := congr_arg ScheduledEvent.targetTick h_e_eq_gc1.symm
              dsimp [stageEvent] at this
              rwa [this]
            have h_eq_tgt : stageTarget actTick groups gi ci 1 =
                stageTarget actTick groups gi₁ ci₁ 1 := by
              rw [h_tgt_gc1, h_T₁₀]
            dsimp [stageTarget] at h_eq_tgt
            rw [h_act_gc] at h_eq_tgt
            rw [show stageCumDelay (chainAt groups gi ci) 1 =
                stageCumDelay (chainAt groups gi ci) 0 +
                  ((chainAt groups gi ci).lastDelay : Nat) from by
                rw [show 1 = (chainAt groups gi ci).middleDelays.length + 1
                    by omega,
                  show 0 = (chainAt groups gi ci).middleDelays.length by
                    omega]
                exact stageCumDelay_succ_last (chainAt groups gi ci),
              show stageCumDelay (chainAt groups gi₁ ci₁) 1 =
                stageCumDelay (chainAt groups gi₁ ci₁) 0 +
                  ((chainAt groups gi₁ ci₁).lastDelay : Nat) from by
                rw [show 1 =
                    (chainAt groups gi₁ ci₁).middleDelays.length + 1 by
                    omega,
                  show 0 = (chainAt groups gi₁ ci₁).middleDelays.length by
                    omega]
                exact stageCumDelay_succ_last (chainAt groups gi₁ ci₁),
              stageCumDelay_of_le_middle (chainAt groups gi ci) 0
                (by omega),
              stageCumDelay_of_le_middle (chainAt groups gi₁ ci₁) 0
                (by omega)] at h_eq_tgt
            simp [List.take] at h_eq_tgt
            have h_ld_val : (↑(chainAt groups gi ci).lastDelay : Nat) =
                (↑(chainAt groups gi₁ ci₁).lastDelay : Nat) := by omega
            exact Subtype.ext h_ld_val
          have h_chain_gc : chainAt groups gi ci =
              chainAt groups gi₁ ci₁ :=
            ChainSpec_eq' (chainAt groups gi ci)
              (chainAt groups gi₁ ci₁)
              (by
                have h_md_gc : (chainAt groups gi ci).middleDelays = [] :=
                  List.length_eq_zero_iff.mp h_mlen_gc0
                have h_md_ref :
                    (chainAt groups gi₁ ci₁).middleDelays = [] :=
                  List.length_eq_zero_iff.mp h_m0
                rw [h_md_gc, h_md_ref]) h_ld
          obtain ⟨h_g_eq, h_c_eq, _⟩ := stageEvent_injective actTick
            groups gi ci 1 gi₂ ci₂
            ((chainAt groups gi₂ ci₂).middleDelays.length + 1) h_gi h_ci
            h_g₂ h_c₂ (by omega) (by omega) h_e_eq_gc1.symm
          rw [h_g_eq, h_c_eq] at h_chain_gc
          exact h_chain_gc
        · -- e was spawned during the drain: classify the drain parent
          set n₀ := (W_B₀.events.filter
            (fun ev => ev.targetTick == W_B₀.tick)).length
          have h_e_step : e ∈ W_B₀.stepUntilNextTick.events := by
            have h_mem := stageEvent_succ_mem_range_complete groups actTick
              groupOrd withinOrd pos h_valid h_ord h_within gi₂ ci₂
              ((chainAt groups gi₂ ci₂).middleDelays.length) h_g₂ h_c₂
              (by omega) (τ₀ + 1) (by omega) (by
                rw [stageTarget_final_eq_T groups actTick T gi₂ ci₂ h_g₂
                  h_c₂ h_uniform h_act]
                omega)
            exact gSimWorld_succ_events_eq_preStepWorld groups actTick
              groupOrd withinOrd pos gi₁ ci₁ 0 ▸ h_mem
          have h_e_acc : e ∈ World.popSpawnAcc W_B₀ n₀ := by
            rw [stepUNT_filter_split W_B₀] at h_e_step
            rcases List.mem_append.mp h_e_step with h_surv | h_acc
            · exact absurd (List.mem_filter.mp h_surv).1 h_e_B
            · exact h_acc
          have h_single_B := pops_single_spawn' groups actTick W_B₀ n₀
            (fun ev h_ev _ => h_stage_WB₀ ev h_ev)
          obtain ⟨Q, hQ_pop, vQ, sQ, h_vQ, h_layQ, h_spQ, h_sQ⟩ :=
            mem_popSpawnAcc_singleton_spawn groups W_B₀ n₀ e h_layout_B₀
              h_single_B h_e_acc
          have hQ_mem : Q ∈ W_B₀.events :=
            World.mem_popSeqFuel_mem_events W_B₀ n₀ Q hQ_pop
          have hQ_due : Q.targetTick = W_B₀.tick :=
            World.mem_popSeqFuel_due W_B₀ n₀ Q hQ_pop
          have hQ_log : Q ∈ w_log₀.events :=
            mem_gSimBurst_due_back τ₀ (buildGroups groups).2 withinOrd pos
              w_log₀ ((popActive groups actTick groupOrd gi₁ ci₁ 0).zipIdx)
              Q hQ_mem (by
                rw [hQ_due, h_tick_WB₀]
                exact h_tick_log₀.symm)
          have hQ_pri_nonneg : (0 : Int) ≤ Q.priority := by
            by_contra h_lt
            have hA₀_surv := gSimBurst_not_pop_larger_pri τ₀
              (buildGroups groups).2 withinOrd pos w_log₀
              ((popActive groups actTick groupOrd gi₁ ci₁ 0).zipIdx)
              Q (stageEvent actTick groups gi₁ ci₁ 0)
              (by
                rw [hQ_due, h_tick_WB₀]
                exact h_tick_log₀.symm)
              (by dsimp [stageEvent]; rw [h_tick_log₀])
              (by
                have hA_pri :
                    (stageEvent actTick groups gi₁ ci₁ 0).priority =
                      (0 : Int) := by
                  dsimp [stageEvent, stagePri]
                rw [hA_pri]
                omega)
              hA₀_mem hQ_mem
            exact hA₀_gone hA₀_surv
          obtain ⟨gi, ci, k, h_gi, h_ci, h_k_le, hQ_eq, _⟩ :=
            h_ok_B₀.2.1 Q hQ_mem
          have hQ_pri : Q.priority = (0 : Int) := by
            rw [hQ_eq] at hQ_pri_nonneg ⊢
            dsimp [stageEvent, stagePri] at hQ_pri_nonneg ⊢
            split_ifs at hQ_pri_nonneg ⊢ <;> omega
          have h_k0 : k = 0 := by
            have := congr_arg ScheduledEvent.priority hQ_eq
            dsimp [stageEvent, stagePri] at this
            rw [hQ_pri] at this
            split_ifs at this; omega
          have h_fire_Q : (vQ.onScheduledTick Q.nodeId).events =
              vQ.events ++ [stageEvent actTick groups gi ci 1] := by
            rw [hQ_eq, h_k0]
            exact stage_spawn groups actTick vQ gi ci 0 h_gi h_ci
              (by omega) (by
                rw [h_vQ, ← hQ_due]
                have := congr_arg ScheduledEvent.targetTick hQ_eq
                dsimp [stageEvent] at this
                rw [h_k0] at this
                exact this) h_layQ
          have h_e_eq_gc1 : e = stageEvent actTick groups gi ci 1 := by
            have h_cancel := append_left_cancel'' vQ.events [sQ]
              [stageEvent actTick groups gi ci 1]
              (h_spQ.symm.trans h_fire_Q)
            injection h_cancel with h_sQ_eq
            rw [h_sQ, h_sQ_eq]
          have h_act_gc : actTick gi = actTick gi₁ := by
            have h_tgt0 : stageTarget actTick groups gi ci 0 =
                stageTarget actTick groups gi₁ ci₁ 0 := by
              have := congr_arg ScheduledEvent.targetTick hQ_eq
              dsimp [stageEvent] at this
              rw [h_k0] at this
              rw [← this, hQ_due, h_tick_WB₀]
            rw [stageTarget_zero_eq, stageTarget_zero_eq] at h_tgt0
            omega
          have h_mlen_gc0 : (chainAt groups gi ci).middleDelays.length =
              0 := by
            have h_e_pri : e.priority = (-1 : Int) := by
              dsimp [e, stageEvent]
              rw [stagePri_last groups gi₂ ci₂]
            rw [h_e_eq_gc1] at h_e_pri
            dsimp [stageEvent, stagePri] at h_e_pri
            split_ifs at h_e_pri <;> omega
          have h_ld : (chainAt groups gi ci).lastDelay =
              (chainAt groups gi₁ ci₁).lastDelay := by
            have h_tgt_gc1 : stageTarget actTick groups gi ci 1 = T := by
              have := congr_arg ScheduledEvent.targetTick h_e_eq_gc1.symm
              dsimp [stageEvent] at this
              rwa [this]
            have h_eq_tgt : stageTarget actTick groups gi ci 1 =
                stageTarget actTick groups gi₁ ci₁ 1 := by
              rw [h_tgt_gc1, h_T₁₀]
            dsimp [stageTarget] at h_eq_tgt
            rw [h_act_gc] at h_eq_tgt
            rw [show stageCumDelay (chainAt groups gi ci) 1 =
                stageCumDelay (chainAt groups gi ci) 0 +
                  ((chainAt groups gi ci).lastDelay : Nat) from by
                rw [show 1 = (chainAt groups gi ci).middleDelays.length + 1
                    by omega,
                  show 0 = (chainAt groups gi ci).middleDelays.length by
                    omega]
                exact stageCumDelay_succ_last (chainAt groups gi ci),
              show stageCumDelay (chainAt groups gi₁ ci₁) 1 =
                stageCumDelay (chainAt groups gi₁ ci₁) 0 +
                  ((chainAt groups gi₁ ci₁).lastDelay : Nat) from by
                rw [show 1 =
                    (chainAt groups gi₁ ci₁).middleDelays.length + 1 by
                    omega,
                  show 0 = (chainAt groups gi₁ ci₁).middleDelays.length by
                    omega]
                exact stageCumDelay_succ_last (chainAt groups gi₁ ci₁),
              stageCumDelay_of_le_middle (chainAt groups gi ci) 0
                (by omega),
              stageCumDelay_of_le_middle (chainAt groups gi₁ ci₁) 0
                (by omega)] at h_eq_tgt
            simp [List.take] at h_eq_tgt
            have h_ld_val : (↑(chainAt groups gi ci).lastDelay : Nat) =
                (↑(chainAt groups gi₁ ci₁).lastDelay : Nat) := by omega
            exact Subtype.ext h_ld_val
          have h_chain_gc : chainAt groups gi ci =
              chainAt groups gi₁ ci₁ :=
            ChainSpec_eq' (chainAt groups gi ci)
              (chainAt groups gi₁ ci₁)
              (by
                have h_md_gc : (chainAt groups gi ci).middleDelays = [] :=
                  List.length_eq_zero_iff.mp h_mlen_gc0
                have h_md_ref :
                    (chainAt groups gi₁ ci₁).middleDelays = [] :=
                  List.length_eq_zero_iff.mp h_m0
                rw [h_md_gc, h_md_ref]) h_ld
          obtain ⟨h_g_eq, h_c_eq, _⟩ := stageEvent_injective actTick
            groups gi ci 1 gi₂ ci₂
            ((chainAt groups gi₂ ci₂).middleDelays.length + 1) h_gi h_ci
            h_g₂ h_c₂ (by omega) (by omega) h_e_eq_gc1.symm
          rw [h_g_eq, h_c_eq] at h_chain_gc
          exact h_chain_gc
    · -- the drain-side phases at m = 0
      by_cases h₃₀ : f₃ ∈ W_B₀.events
      · -- impossible: A₀ survives but D₀ is burst-popped (SamePriorityPopOrder)
        exfalso
        have h₃₀' : stageEvent actTick groups gi₃ ci₃ 1 ∈ W_B₀.events := by
          dsimp [f₃] at h₃₀
          rwa [h_m₃₀] at h₃₀
        have hA₀_WB : stageEvent actTick groups gi₁ ci₁ 0 ∈ W_B₀.events :=
          by
          by_contra hA_gone
          have h_f₁_B : stageEvent actTick groups gi₁ ci₁ 1 ∈
              W_B₀.events :=
            gSimBurst_spawn_mem groups τ₀ (buildGroups groups).2 withinOrd
              pos w_log₀
              ((popActive groups actTick groupOrd gi₁ ci₁ 0).zipIdx)
              (stageEvent actTick groups gi₁ ci₁ 0)
              (stageEvent actTick groups gi₁ ci₁ 1) h_layout_log₀ hA₀_mem
              (by dsimp [stageEvent]; rw [h_tick_log₀]) hA_gone
              (by
                dsimp [stageEvent]
                rw [h_tick_log₀]
                exact (stageTarget_lt_succ actTick groups gi₁ ci₁ 0
                  (by omega)).ne')
              (by
                intro v h_v h_lay
                simpa [stageEvent] using
                  stage_spawn groups actTick v gi₁ ci₁ 0 h_g₁ h_c₁
                    (by omega) (h_v.trans h_tick_log₀) h_lay)
          have h := h₁₀
          dsimp [f₁] at h
          rw [h_m0] at h
          exact h h_f₁_B
        have hD₀_not_WB : stageEvent actTick groups gi₃ ci₃ 0 ∉
            W_B₀.events := by
          intro hD_WB
          have h_nsd := h_ok_B₀.2.2
          dsimp [NoSpawnDue] at h_nsd
          have h_f₃_out : stageEvent actTick groups gi₃ ci₃ 1 ∉
              W_B₀.events :=
            h_nsd gi₃ ci₃ 0 h_g₃ h_c₃ (by omega)
              (h_tgt₂₀.trans h_tick_WB₀.symm) hD_WB
          exact h_f₃_out h₃₀'
        have h_pri_le : (stageEvent actTick groups gi₁ ci₁ 0).priority ≤
            (stageEvent actTick groups gi₃ ci₃ 0).priority := by
          dsimp [stageEvent, stagePri]
          omega
        have hD₀_WB := gSimBurst_samePri_later_survives τ₀
          (buildGroups groups).2 withinOrd pos w_log₀
          ((popActive groups actTick groupOrd gi₁ ci₁ 0).zipIdx)
          (stageEvent actTick groups gi₁ ci₁ 0)
          (stageEvent actTick groups gi₃ ci₃ 0) hA₀_mem hD₀_mem
          (by dsimp [stageEvent]; rw [h_tick_log₀])
          (by dsimp [stageEvent]; rw [h_tgt₂₀, h_tick_log₀])
          h_pri_le h_nd_due_log₀ hAD₀ hA₀_WB
        exact hD₀_not_WB hD₀_WB
      · -- BOTH-DRAIN phase at m = 0
        have h_sA_out : stageEvent actTick groups gi₁ ci₁ 1 ∉
            W_B₀.events := by
          have h := h₁₀
          dsimp [f₁] at h
          rwa [h_m0] at h
        have h_sD_out : stageEvent actTick groups gi₃ ci₃ 1 ∉
            W_B₀.events := by
          have h := h₃₀
          dsimp [f₃] at h
          rwa [h_m₃₀] at h
        have h_e_absent_B₀ : e ∉ W_B₀.events := by
          intro h_e_in
          have h_split := stepUNT_filter_split W_B₀
          have h_e_step : e ∈ W_B₀.stepUntilNextTick.events := by
            have h_mem := stageEvent_succ_mem_range_complete groups actTick
              groupOrd withinOrd pos h_valid h_ord h_within gi₂ ci₂
              ((chainAt groups gi₂ ci₂).middleDelays.length) h_g₂ h_c₂
              (by omega) (τ₀ + 1) (by omega) (by
                rw [stageTarget_final_eq_T groups actTick T gi₂ ci₂ h_g₂
                  h_c₂ h_uniform h_act]
                omega)
            exact gSimWorld_succ_events_eq_preStepWorld groups actTick
              groupOrd withinOrd pos gi₁ ci₁ 0 ▸ h_mem
          have h_f₁_step : stageEvent actTick groups gi₁ ci₁ 1 ∈
              W_B₀.stepUntilNextTick.events :=
            evBefore.mem_left h_b1_s
          rw [h_split] at h_e_step h_f₁_step
          rcases List.mem_append.mp h_e_step with h_e_surv | h_e_acc
          · have h_f₁_acc : stageEvent actTick groups gi₁ ci₁ 1 ∈
                World.popSpawnAcc W_B₀
                  ((W_B₀.events.filter
                    (fun ev => ev.targetTick == W_B₀.tick)).length) := by
              rcases List.mem_append.mp h_f₁_step with h_surv | h_acc
              · exact absurd (List.mem_filter.mp h_surv).1 h_sA_out
              · exact h_acc
            have h_e_f₁ : evBefore W_B₀.stepUntilNextTick.events e
                (stageEvent actTick groups gi₁ ci₁ 1) := by
              rw [h_split]
              apply evBefore.of_mem_append h_e_surv h_f₁_acc
            exact (evBefore.asymm h_nd_post₀ h_b1_s h_e_f₁).elim
          · have h_nd_split : (W_B₀.events.filter
                (fun ev => ev.targetTick ≠ W_B₀.tick) ++
                World.popSpawnAcc W_B₀
                  ((W_B₀.events.filter
                    (fun ev => ev.targetTick == W_B₀.tick)).length)).Nodup
              := by
              rwa [← h_split]
            have h_e_surv' : e ∈ W_B₀.events.filter
                (fun ev => ev.targetTick ≠ W_B₀.tick) := by
              rw [List.mem_filter]
              refine ⟨h_e_in, ?_⟩
              rw [decide_eq_true_eq]
              intro h_eq
              rw [h_e_tgt_T, h_tick_WB₀] at h_eq
              omega
            rw [List.nodup_append] at h_nd_split
            exact h_nd_split.2.2 e h_e_surv' e h_e_acc rfl
        obtain ⟨g, c, h_g, h_c, h_ev_gc, hP_left, hP_right⟩ :=
          converse_spawn_stepUNT_stage0 groups actTick W_B₀ gi₁ ci₁ gi₃
            ci₃ h_g₁ h_c₁ h_g₃ h_c₃ h_layout_B₀
            (preStepWorld_tick_eq groups actTick groupOrd withinOrd pos
              gi₁ ci₁ 0) h_tgt₂₀ h_nd_due_WB₀ h_stage_WB₀ h_sA_out
            h_sD_out e h_e_absent_B₀ h_b1_s h_b2_s
        have h_gc_mlen₀ : (chainAt groups g c).middleDelays.length = 0 :=
          by
          have h_e_pri : e.priority = (-1 : Int) := by
            dsimp [e, stageEvent]
            rw [stagePri_last groups gi₂ ci₂]
          have := congr_arg ScheduledEvent.priority h_ev_gc
          dsimp [stageEvent] at this
          rw [h_e_pri] at this
          dsimp [stagePri] at this
          split_ifs at this <;> omega
        have h_act_g : actTick g = actTick gi₁ := by
          have h_tgt0 : stageTarget actTick groups g c 0 =
              stageTarget actTick groups gi₁ ci₁ 0 := by
            have h_mem := evBefore.mem_right hP_left
            rw [List.mem_filter] at h_mem
            have h_due := h_mem.2
            dsimp [stageEvent] at h_due
            have h_due_eq : stageTarget actTick groups g c 0 = W_B₀.tick := by
              simpa [Nat.beq_eq] using h_due
            rw [h_due_eq, h_tick_WB₀]
          rw [stageTarget_zero_eq, stageTarget_zero_eq] at h_tgt0
          omega
        have h_ld : (chainAt groups g c).lastDelay =
            (chainAt groups gi₁ ci₁).lastDelay := by
          have h_tgt_gc1 : stageTarget actTick groups g c 1 = T := by
            have := congr_arg ScheduledEvent.targetTick h_ev_gc.symm
            dsimp [stageEvent] at this
            rwa [this]
          have h_T₁₀ : stageTarget actTick groups gi₁ ci₁ 1 = T := by
            have h := stageTarget_final_eq_T groups actTick T gi₁ ci₁
              h_g₁ h_c₁ h_uniform h_act
            rw [h_m0] at h
            exact h
          have h_eq_tgt : stageTarget actTick groups g c 1 =
              stageTarget actTick groups gi₁ ci₁ 1 := by
            rw [h_tgt_gc1, h_T₁₀]
          dsimp [stageTarget] at h_eq_tgt
          rw [h_act_g] at h_eq_tgt
          rw [show stageCumDelay (chainAt groups g c) 1 =
              stageCumDelay (chainAt groups g c) 0 +
                ((chainAt groups g c).lastDelay : Nat) from by
              rw [show 1 = (chainAt groups g c).middleDelays.length + 1
                  by omega,
                show 0 = (chainAt groups g c).middleDelays.length by
                  omega]
              exact stageCumDelay_succ_last (chainAt groups g c),
            show stageCumDelay (chainAt groups gi₁ ci₁) 1 =
              stageCumDelay (chainAt groups gi₁ ci₁) 0 +
                ((chainAt groups gi₁ ci₁).lastDelay : Nat) from by
              rw [show 1 = (chainAt groups gi₁ ci₁).middleDelays.length + 1
                  by omega,
                show 0 = (chainAt groups gi₁ ci₁).middleDelays.length by
                  omega]
              exact stageCumDelay_succ_last (chainAt groups gi₁ ci₁),
            stageCumDelay_of_le_middle (chainAt groups g c) 0 (by omega),
            stageCumDelay_of_le_middle (chainAt groups gi₁ ci₁) 0
              (by omega)] at h_eq_tgt
          simp [List.take] at h_eq_tgt
          have h_ld_val : (↑(chainAt groups g c).lastDelay : Nat) =
              (↑(chainAt groups gi₁ ci₁).lastDelay : Nat) := by omega
          exact Subtype.ext h_ld_val
        have h_chain_gc : chainAt groups g c = chainAt groups gi₁ ci₁ :=
          ChainSpec_eq' (chainAt groups g c) (chainAt groups gi₁ ci₁)
            (by
              have h_md_gc : (chainAt groups g c).middleDelays = [] :=
                List.length_eq_zero_iff.mp h_gc_mlen₀
              have h_md_ref : (chainAt groups gi₁ ci₁).middleDelays = [] :=
                List.length_eq_zero_iff.mp h_m0
              rw [h_md_gc, h_md_ref]) h_ld
        obtain ⟨h_g_eq, h_c_eq, _⟩ := stageEvent_injective actTick groups
          g c 1 gi₂ ci₂ ((chainAt groups gi₂ ci₂).middleDelays.length + 1)
          h_g h_c h_g₂ h_c₂ (by omega) (by omega) h_ev_gc.symm
        rw [h_g_eq, h_c_eq] at h_chain_gc
        exact h_chain_gc
  · -- Case m ≥ 1: the phase lemmas of the final converse
    have h_m_ge : 1 ≤ m := Nat.pos_of_ne_zero h_m0
    set τ := stageTarget actTick groups gi₁ ci₁ m
    set W_B := preStepWorld groups actTick groupOrd withinOrd pos
      gi₁ ci₁ m
    set wQ := popQueueWorld groups actTick groupOrd withinOrd pos
      gi₁ ci₁ m
    set w_log : World := wQ.logOutput s!"tick {τ}"
    have h_tick_wQ : wQ.tick = τ := by
      dsimp [wQ, popQueueWorld, τ]
      rw [gSimWorld_tick]
    have h_tick_log : w_log.tick = τ := by
      dsimp [w_log]
      rw [h_tick_wQ]
    have h_tgt₂ₘ : stageTarget actTick groups gi₃ ci₃ m = τ := by
      dsimp [τ]
      exact (sameSpec_stageTarget groups actTick gi₁ ci₁ gi₃ ci₃ m
        h_act_eq h_spec₁₃).symm
    have h_e_tgt_T : e.targetTick = T := by
      dsimp [e, stageEvent]
      exact stageTarget_final_eq_T groups actTick T gi₂ ci₂ h_g₂ h_c₂
        h_uniform h_act
    -- MiddleBlockOk at stage m on the tick-start queue
    have h_mb_full := MiddleBlockOk_sameSpec_stage_m groups actTick
      groupOrd withinOrd pos h_valid h_ord h_within T gi₁ ci₁ gi₃ ci₃
      h_g₁ h_c₁ h_g₃ h_c₃ h_spec₁₃ h_act_eq h_base₀ m (by dsimp [m])
      h_m_ge
    -- the betweenness transported to the drain queue at τ
    obtain ⟨h_b1_s, h_b2_s⟩ := evBefore_final_stepUNT_of_dueFilter groups
      actTick groupOrd withinOrd pos T h_valid h_uniform h_act h_ord
      h_within gi₁ ci₁ gi₂ ci₂ gi₃ ci₃ m h_g₁ h_c₁ h_g₂ h_c₂ h_g₃ h_c₃
      (by dsimp [m]) h_m₃ (le_of_eq h_spawn_e) (le_of_eq h_tgt₂ₘ)
      h_ne_left h_ne_right_m h_due₁₂ h_due₂₃_m
    have h_nd_WB : W_B.events.Nodup :=
      (preStepWorld_tickQueueOk groups actTick groupOrd withinOrd pos
        h_gord_nd h_within_nd gi₁ ci₁ m).1.1
    have h_nd_post : W_B.stepUntilNextTick.events.Nodup := by
      rw [show W_B.stepUntilNextTick.events =
          (gSimWorld groups actTick groupOrd withinOrd pos
            (τ + 1)).events from
        (gSimWorld_succ_events_eq_preStepWorld groups actTick groupOrd
          withinOrd pos gi₁ ci₁ m).symm]
      exact gSimWorld_events_Nodup groups actTick groupOrd withinOrd pos
        (τ + 1) h_gord_nd h_within_nd
    have h_τ_lt_T : τ < T := by
      dsimp [τ]
      exact stageTarget_lt_T_of_middleLen groups actTick T gi₁ ci₁ m h_g₁
        h_c₁ h_uniform h_act (by dsimp [m])
    have h_f₁_nd : f₁.targetTick ≠ W_B.tick := by
      dsimp [f₁, stageEvent]
      rw [stageTarget_final_eq_T groups actTick T gi₁ ci₁ h_g₁ h_c₁
        h_uniform h_act]
      intro h_eq
      have := preStepWorld_tick_eq groups actTick groupOrd withinOrd pos
        gi₁ ci₁ m
      rw [this] at h_eq
      omega
    have h_e_nd : e.targetTick ≠ W_B.tick := by
      rw [h_e_tgt_T]
      intro h_eq
      have := preStepWorld_tick_eq groups actTick groupOrd withinOrd pos
        gi₁ ci₁ m
      rw [this] at h_eq
      omega
    -- phase split on the two reference finals
    by_cases h₁ : f₁ ∈ W_B.events
    · by_cases h₃ : f₃ ∈ W_B.events
      · -- BURST phase at m ≥ 1
        have h₃_conv : stageEvent actTick groups gi₃ ci₃ (m + 1) ∈
            W_B.events := by
          have h := h₃
          dsimp [f₃] at h
          rwa [h_m₃] at h
        have h_mem_e : e ∈ W_B.events := by
          have h_f₃_surv : f₃ ∈ W_B.events.filter
              (fun ev => ev.targetTick ≠ W_B.tick) := by
            rw [List.mem_filter]
            refine ⟨h₃, ?_⟩
            rw [decide_eq_true_eq]
            intro h_eq
            dsimp [f₃, stageEvent] at h_eq
            rw [stageTarget_final_eq_T groups actTick T gi₃ ci₃ h_g₃
              h_c₃ h_uniform h_act] at h_eq
            have := preStepWorld_tick_eq groups actTick groupOrd withinOrd
              pos gi₁ ci₁ m
            rw [this] at h_eq
            omega
          by_contra h_e_out
          have h_e_step : e ∈ W_B.stepUntilNextTick.events := by
            have h_mem := stageEvent_succ_mem_range_complete groups actTick
              groupOrd withinOrd pos h_valid h_ord h_within gi₂ ci₂
              ((chainAt groups gi₂ ci₂).middleDelays.length) h_g₂ h_c₂
              (by omega) (τ + 1) (by omega) (by
                rw [stageTarget_final_eq_T groups actTick T gi₂ ci₂ h_g₂
                  h_c₂ h_uniform h_act]
                omega)
            exact gSimWorld_succ_events_eq_preStepWorld groups actTick
              groupOrd withinOrd pos gi₁ ci₁ m ▸ h_mem
          have h_split := stepUNT_filter_split W_B
          rw [h_split] at h_e_step
          rcases List.mem_append.mp h_e_step with h_surv | h_acc
          · exact h_e_out (List.mem_filter.mp h_surv).1
          · have h_f₃_e : evBefore W_B.stepUntilNextTick.events f₃ e := by
              rw [h_split]
              apply evBefore.of_mem_append h_f₃_surv h_acc
            dsimp [f₃] at h_f₃_e
            rw [h_m₃] at h_f₃_e
            exact (evBefore.asymm h_nd_post h_b2_s h_f₃_e).elim
        have h_cs := burstPhase_ConverseSpawnFinal groups actTick groupOrd
          withinOrd pos h_valid h_uniform T h_act h_ord h_within gi₁ ci₁
          gi₂ ci₂ gi₃ ci₃ m h_g₁ h_c₁ h_g₂ h_c₂ h_g₃ h_c₃ h_spec₁₃
          h_act_eq h_base₀ (by dsimp [m]) h_m₃ h_m_ge h_mb_full h₁
          h_mem_e h₃_conv h_spawn_e h_ne_left h_ne_right_m h_due₁₂
          h_due₂₃_m
        obtain ⟨g, c, h_g, h_c, h_len, h_ev, h_chain⟩ :=
          chainSpec_eq' groups actTick
            ((popQueueWorld groups actTick groupOrd withinOrd pos
              gi₁ ci₁ m).logOutput s!"tick {τ}") gi₁ ci₁ gi₃ ci₃ m e
            (by dsimp [m]) h_cs
        obtain ⟨h_g_eq, h_c_eq, _⟩ := stageEvent_injective actTick groups
          g c (m + 1) gi₂ ci₂
          ((chainAt groups gi₂ ci₂).middleDelays.length + 1) h_g h_c h_g₂
          h_c₂ (by omega) (by omega) h_ev.symm
        rw [h_g_eq, h_c_eq] at h_chain
        exact h_chain
      · -- MIXED phase at m ≥ 1
        have h₃_out : stageEvent actTick groups gi₃ ci₃ (m + 1) ∉
            W_B.events := by
          have h := h₃
          dsimp [f₃] at h
          rwa [h_m₃] at h
        have h_b1_g : evBefore
            ((gSimWorld groups actTick groupOrd withinOrd pos
              (τ + 1)).events) f₁ e := by
          have h := h_b1_s
          rw [← gSimWorld_succ_events_eq_preStepWorld groups actTick
            groupOrd withinOrd pos gi₁ ci₁ m] at h
          exact h
        have h_b2_g : evBefore
            ((gSimWorld groups actTick groupOrd withinOrd pos
              (τ + 1)).events)
            (stageEvent actTick groups gi₂ ci₂
              ((chainAt groups gi₂ ci₂).middleDelays.length + 1))
            (stageEvent actTick groups gi₃ ci₃ (m + 1)) := by
          have h := h_b2_s
          rw [← gSimWorld_succ_events_eq_preStepWorld groups actTick
            groupOrd withinOrd pos gi₁ ci₁ m] at h
          exact h
        have h_cs := mixedPhase_ConverseSpawnFinal groups actTick groupOrd
          withinOrd pos h_valid h_uniform T h_act h_ord h_within gi₁ ci₁
          gi₂ ci₂ gi₃ ci₃ m h_g₁ h_c₁ h_g₂ h_c₂ h_g₃ h_c₃ h_spec₁₃
          h_act_eq (by dsimp [m]) h_m₃ h_m_ge h_mb_full h₁ h₃_out
          h_spawn_e h_ne_left h_ne_right_m h_b1_g h_b2_g
        obtain ⟨g, c, h_g, h_c, h_len, h_ev, h_chain⟩ :=
          chainSpec_eq' groups actTick
            (popQueueWorld groups actTick groupOrd withinOrd pos
              gi₁ ci₁ m) gi₁ ci₁ gi₃ ci₃ m e (by dsimp [m]) h_cs
        obtain ⟨h_g_eq, h_c_eq, _⟩ := stageEvent_injective actTick groups
          g c (m + 1) gi₂ ci₂
          ((chainAt groups gi₂ ci₂).middleDelays.length + 1) h_g h_c h_g₂
          h_c₂ (by omega) (by omega) h_ev.symm
        rw [h_g_eq, h_c_eq] at h_chain
        exact h_chain
    · by_cases h₃ : f₃ ∈ W_B.events
      · -- impossible: Aₘ survives but Dₘ is burst-popped (SamePriorityPopOrder)
        exfalso
        have hAₘ_WB : stageEvent actTick groups gi₁ ci₁ m ∈ W_B.events :=
          by
          by_contra hA_gone
          have h_f₁_B : f₁ ∈ W_B.events := by
            have h := gSimBurst_spawn_mem groups τ (buildGroups groups).2
              withinOrd pos w_log
              ((popActive groups actTick groupOrd gi₁ ci₁ m).zipIdx)
              (stageEvent actTick groups gi₁ ci₁ m)
              (stageEvent actTick groups gi₁ ci₁ (m + 1))
              (by
                dsimp [w_log, wQ, popQueueWorld]
                exact NodeLayoutOk_logOutput groups
                  (gSimWorld groups actTick groupOrd withinOrd pos τ)
                  s!"tick {τ}"
                  (NodeLayoutOk_gSimWorld groups actTick groupOrd
                    withinOrd pos τ))
              (by
                rw [World.logOutput_events]
                dsimp [wQ, popQueueWorld, τ]
                exact stageEvent_mem_gSimWorld groups actTick groupOrd
                  withinOrd pos h_valid h_ord h_within gi₁ ci₁ h_g₁ h_c₁
                  m (by omega))
              (by dsimp [stageEvent]; rw [h_tick_log]) hA_gone
              (by
                dsimp [stageEvent]
                rw [h_tick_log]
                exact (stageTarget_lt_succ actTick groups gi₁ ci₁ m
                  (by omega)).ne')
              (by
                intro v h_v h_lay
                simpa [stageEvent] using
                  stage_spawn groups actTick v gi₁ ci₁ m h_g₁ h_c₁
                    (by omega) (h_v.trans h_tick_log) h_lay)
            exact h
          exact absurd h_f₁_B h₁
        have hDₘ_not_WB : stageEvent actTick groups gi₃ ci₃ m ∉
            W_B.events := by
          intro hD_WB
          have h_nsd := (preStepWorld_tickQueueOk groups actTick groupOrd
            withinOrd pos h_gord_nd h_within_nd gi₁ ci₁ m).1.2.2
          have h_f₃_out : stageEvent actTick groups gi₃ ci₃ (m + 1) ∉
              W_B.events :=
            h_nsd gi₃ ci₃ m h_g₃ h_c₃ (by omega)
              (h_tgt₂ₘ.trans (preStepWorld_tick_eq groups actTick groupOrd
                withinOrd pos gi₁ ci₁ m).symm) hD_WB
          have h := h₃
          dsimp [f₃] at h
          rw [h_m₃] at h
          exact h_f₃_out h
        -- Aₘ before Dₘ in the pre-burst due filter (QSideOrderNoSurvival induction)
        have hADₘ : evBefore (w_log.events.filter
            (fun ev => ev.targetTick == w_log.tick))
            (stageEvent actTick groups gi₁ ci₁ m)
            (stageEvent actTick groups gi₃ ci₃ m) := by
          have h_ind : evBefore
              ((popQueueWorld groups actTick groupOrd withinOrd pos
                gi₁ ci₁ m).events)
              (stageEvent actTick groups gi₁ ci₁ m)
              (stageEvent actTick groups gi₃ ci₃ m) :=
            sameSpec_stage_evBefore_ind_self groups actTick groupOrd
              withinOrd pos gi₁ ci₁ gi₃ ci₃ m h_g₁ h_c₁ h_g₃ h_c₃
              h_spec₁₃ h_act_eq (by omega) h_base₀
              (fun k _ => NodeLayoutOk_gSimWorld groups actTick groupOrd
                withinOrd pos (stageTarget actTick groups gi₁ ci₁ k))
              (fun k hk => sameSpec_h_nodup_discharge groups actTick
                groupOrd withinOrd pos gi₁ ci₁ h_gord_nd h_within_nd k
                (by omega))
          rw [World.logOutput_events, h_tick_log]
          apply evBefore.filter (fun ev => ev.targetTick == τ)
          · dsimp [stageEvent]
            simpa using (show stageTarget actTick groups gi₁ ci₁ m = τ
              from rfl)
          · dsimp [stageEvent]
            rw [h_tgt₂ₘ]
            simp
          · dsimp [wQ, popQueueWorld] at h_ind
            exact h_ind
        have h_pri_le : (stageEvent actTick groups gi₁ ci₁ m).priority ≤
            (stageEvent actTick groups gi₃ ci₃ m).priority := by
          dsimp [stageEvent]
          rw [sameSpec_stagePri groups gi₁ ci₁ gi₃ ci₃ m h_spec₁₃]
        have hAₘ_mem_log : stageEvent actTick groups gi₁ ci₁ m ∈
            w_log.events := by
          rw [World.logOutput_events]
          dsimp [wQ, popQueueWorld, τ]
          exact stageEvent_mem_gSimWorld groups actTick groupOrd withinOrd
            pos h_valid h_ord h_within gi₁ ci₁ h_g₁ h_c₁ m (by omega)
        have hDₘ_mem_log : stageEvent actTick groups gi₃ ci₃ m ∈
            w_log.events := by
          rw [World.logOutput_events]
          dsimp [wQ, popQueueWorld, τ]
          have h_mem := stageEvent_mem_gSimWorld groups actTick groupOrd
            withinOrd pos h_valid h_ord h_within gi₃ ci₃ h_g₃ h_c₃ m
            (by omega)
          rwa [h_tgt₂ₘ] at h_mem
        have h_nd_due_log : (w_log.events.filter
            (fun ev => ev.targetTick == w_log.tick)).Nodup := by
          rw [World.logOutput_events, h_tick_log]
          exact List.Nodup.filter (fun ev => ev.targetTick == τ)
            (gSimWorld_events_Nodup groups actTick groupOrd withinOrd pos
              τ h_gord_nd h_within_nd)
        have hDₘ_WB := gSimBurst_samePri_later_survives τ
          (buildGroups groups).2 withinOrd pos w_log
          ((popActive groups actTick groupOrd gi₁ ci₁ m).zipIdx)
          (stageEvent actTick groups gi₁ ci₁ m)
          (stageEvent actTick groups gi₃ ci₃ m) hAₘ_mem_log hDₘ_mem_log
          (by dsimp [stageEvent]; rw [h_tick_log])
          (by dsimp [stageEvent]; rw [h_tgt₂ₘ, h_tick_log])
          h_pri_le h_nd_due_log hADₘ hAₘ_WB
        exact hDₘ_not_WB hDₘ_WB
      · -- DRAIN phase at m ≥ 1
        have h_sD_out : stageEvent actTick groups gi₃ ci₃ (m + 1) ∉
            W_B.events := by
          have h := h₃
          dsimp [f₃] at h
          rwa [h_m₃] at h
        have h_cs := drainPhase_ConverseSpawnFinal groups actTick groupOrd
          withinOrd pos h_valid h_uniform T h_act h_ord h_within gi₁ ci₁
          gi₂ ci₂ gi₃ ci₃ m h_g₁ h_c₁ h_g₂ h_c₂ h_g₃ h_c₃ h_spec₁₃
          h_act_eq (by dsimp [m]) h_m₃ h_m_ge h_mb_full h₁ h_sD_out
          (le_of_eq h_spawn_e) h_ne_left h_ne_right_m h_due₁₂ h_due₂₃_m
        obtain ⟨g, c, h_g, h_c, h_len, h_ev, h_chain⟩ :=
          chainSpec_eq' groups actTick W_B gi₁ ci₁ gi₃ ci₃ m e
            (by dsimp [m]) h_cs
        obtain ⟨h_g_eq, h_c_eq, _⟩ := stageEvent_injective actTick groups
          g c (m + 1) gi₂ ci₂
          ((chainAt groups gi₂ ci₂).middleDelays.length + 1) h_g h_c h_g₂
          h_c₂ (by omega) (by omega) h_ev.symm
        rw [h_g_eq, h_c_eq] at h_chain
        exact h_chain
