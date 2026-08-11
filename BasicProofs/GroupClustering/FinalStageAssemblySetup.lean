import BasicProofs.GroupClustering.QSideOrder
import BasicProofs.GroupClustering.NodupChain
import BasicProofs.GroupClustering.PreStepWorldFacts
import BasicProofs.GroupClustering.StageInductionSideFacts
import BasicProofs.GroupClustering.PopSeqFuel
import BasicProofs.GroupClustering.LockstepComposition

open BasicRedstoneSim List

/-! # Group clustering — assembly setup for the final stage

Shared discharges for the phase lemmas
(FinalConverseDrainPhase–FinalConverseMixedPhase):

* `preStepWorld_tickQueueOk` — the post-burst queue at the stage-`j`
  pop tick satisfies `TickQueueOk` and `NodeLayoutOk` (the SideHypothesisDischarge
  `nd_burst` discharge, exposed);
* `StageMemAt_of_TickQueueOk` / `StageMemAt_preStepWorld` — the queue
  membership invariant for the stepUNT converse (ConverseFinalUnconditional);
* `evBefore_due_gSimBurst_back` — due-filter betweenness among burst
  survivors already held in the tick-start queue;
* `MiddleBlockOk_filter` / `MiddleBlockOk_preStepWorld` — restrict or
  lift the MiddleBlockOk invariant between the tick-start queue and
  the post-burst due filter.
-/

/-- `NodeLayoutOk` holds at every tick-start queue. -/
private theorem NodeLayoutOk_gSimWorld (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (t : Nat) :
    NodeLayoutOk groups
      (gSimWorld groups actTick groupOrd withinOrd pos t) := by
  dsimp [gSimWorld]
  exact NodeLayoutOk_gSimFoldl groups actTick (buildGroups groups).2 groupOrd
    withinOrd pos (buildGroups groups).1 t (NodeLayoutOk_buildGroups groups)

/-- `zipIdx` followed by the first projection is the identity
    (reproven; private in NodupChain). -/
private theorem map_fst_zipIdx' {α : Type} (l : List α) :
    (l.zipIdx.map Prod.fst : List α) = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.zipIdx]

/-- The post-burst queue at the stage-`j` pop tick satisfies
    `TickQueueOk` (with the activated groups accumulated) and keeps
    `NodeLayoutOk`. Discharged from nodup of `groupOrd`/`withinOrd`
    alone. -/
theorem preStepWorld_tickQueueOk (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat)
    (h_gord_nd : groupOrd.Nodup)
    (h_within_nd : ∀ gi, gi < groups.length → (withinOrd gi).Nodup)
    (g₁ c₁ j : Nat) :
    TickQueueOk groups actTick
      (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ j)
      (popActive groups actTick groupOrd g₁ c₁ j) ∧
    NodeLayoutOk groups
      (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ j) := by
  dsimp [preStepWorld, popQueueWorld, popActive]
  set wQ := gSimWorld groups actTick groupOrd withinOrd pos
    (stageTarget actTick groups g₁ c₁ j)
  set wQ_log := wQ.logOutput s!"tick {stageTarget actTick groups g₁ c₁ j}"
  set activeQ := groupOrd.filter (fun gi =>
    decide (gi < (buildGroups groups).2.length) &&
    (actTick gi == stageTarget actTick groups g₁ c₁ j))
  have h_tick_w : wQ.tick = stageTarget actTick groups g₁ c₁ j :=
    gSimWorld_tick groups actTick groupOrd withinOrd pos
      (stageTarget actTick groups g₁ c₁ j)
  have h_ev_log : wQ_log.events = wQ.events := by
    rw [World.logOutput_events]
  have h_tick_log : wQ_log.tick = wQ.tick := by dsimp [wQ_log]
  have h_ok_log : TickQueueOk groups actTick wQ_log [] := by
    dsimp [TickQueueOk, NoSpawnDue]
    rw [h_ev_log, h_tick_log]
    refine ⟨?_, ?_, ?_⟩
    · exact gSimWorld_events_Nodup groups actTick groupOrd withinOrd pos
        (stageTarget actTick groups g₁ c₁ j) h_gord_nd h_within_nd
    · intro ev h_ev
      obtain ⟨gi, ci, k, h_gi, h_ci, h_k, h_ev_eq, h_win⟩ :=
        gSimWorld_events_stageWindow groups actTick groupOrd withinOrd pos
          (stageTarget actTick groups g₁ c₁ j) ev h_ev
      refine ⟨gi, ci, k, h_gi, h_ci, h_k, h_ev_eq,
        Or.inl (by rw [h_tick_w]; exact h_win)⟩
    · intro gi ci k h_gi h_ci h_km h_tgt _
      exact stageEvent_succ_not_mem_gSimWorld groups actTick groupOrd
        withinOrd pos gi ci k (stageTarget actTick groups g₁ c₁ j)
        h_gi h_ci h_km (h_tgt.trans h_tick_w)
  have h_nd_gis : ([] ++ activeQ.zipIdx.map Prod.fst).Nodup := by
    rw [List.nil_append, map_fst_zipIdx']
    exact List.Nodup.filter (fun gi =>
      decide (gi < (buildGroups groups).2.length) &&
      (actTick gi == stageTarget actTick groups g₁ c₁ j)) h_gord_nd
  have h_active_char : ∀ gi k, (gi, k) ∈ activeQ.zipIdx →
      gi < groups.length ∧ actTick gi = wQ.tick := by
    intro gi k h_mem
    have h_zip := List.mem_zipIdx h_mem
    obtain ⟨_, h_k_lt, h_gi_eq⟩ := h_zip
    have h_k_lt' : k < activeQ.length := by simpa using h_k_lt
    have h_gi_mem : gi ∈ activeQ := by
      have h_gi_eq' : gi = activeQ[k] := by simpa using h_gi_eq
      rw [h_gi_eq']
      exact List.getElem_mem h_k_lt'
    dsimp [activeQ] at h_gi_mem
    rw [List.mem_filter] at h_gi_mem
    obtain ⟨_, h_cond⟩ := h_gi_mem
    rw [Bool.and_eq_true] at h_cond
    obtain ⟨h_dec, h_beq⟩ := h_cond
    have h_gi_lt : gi < (buildGroups groups).2.length :=
      of_decide_eq_true h_dec
    have h_act_eq' : actTick gi = wQ.tick := by
      rw [h_tick_w]
      simpa [Nat.beq_eq] using h_beq
    exact ⟨by rwa [buildGroups_snd_length] at h_gi_lt, h_act_eq'⟩
  obtain ⟨h_ok_B, h_layout_B⟩ := gSimBurst_tickQueueOk groups actTick wQ.tick
    withinOrd pos wQ_log activeQ.zipIdx [] h_tick_log
    (NodeLayoutOk_logOutput groups wQ _
      (NodeLayoutOk_gSimWorld groups actTick groupOrd withinOrd pos
        (stageTarget actTick groups g₁ c₁ j)))
    h_ok_log h_nd_gis h_active_char h_within_nd
  have h_S : [] ++ activeQ.zipIdx.map Prod.fst = activeQ := by
    rw [List.nil_append, map_fst_zipIdx']
  rw [h_S] at h_ok_B
  rw [h_tick_w] at h_ok_B h_layout_B
  exact ⟨h_ok_B, h_layout_B⟩

/-- `TickQueueOk` implies the loose queue-membership invariant
    `StageMemAt` at the world's own tick. -/
theorem StageMemAt_of_TickQueueOk (groups : List GroupSpec)
    (actTick : Nat → Nat) (w : World) (S : List Nat)
    (h_ok : TickQueueOk groups actTick w S) :
    StageMemAt groups actTick w w.tick := by
  intro ev h_ev
  obtain ⟨gi, ci, j, h_gi, h_ci, h_j, h_ev_eq, h_disj⟩ := h_ok.2.1 ev h_ev
  refine ⟨gi, ci, j, h_gi, h_ci, h_j, h_ev_eq, ?_, ?_⟩
  · rcases h_disj with h_win | ⟨h_j0, h_act, _⟩ | ⟨h_j_ge, h_prev⟩
    · dsimp [stageWindow] at h_win
      by_cases h_j0 : j = 0 <;> simp [h_j0] at h_win ⊢ <;> omega
    · subst h_j0
      simp
      omega
    · have h_ne0 : ¬j = 0 := by omega
      simp [h_ne0]
      omega
  · rcases h_disj with h_win | ⟨h_j0, _, _⟩ | ⟨h_j_ge, h_prev⟩
    · dsimp [stageWindow] at h_win
      exact h_win.2
    · subst h_j0
      dsimp [stageTarget]
      rw [stageCumDelay_zero]
      omega
    · have h_lt := stageTarget_lt_succ actTick groups gi ci (j - 1)
        (by omega)
      rw [Nat.sub_add_cancel h_j_ge] at h_lt
      omega

/-- The post-burst queue satisfies `StageMemAt` at its own tick. -/
theorem StageMemAt_preStepWorld (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat)
    (h_gord_nd : groupOrd.Nodup)
    (h_within_nd : ∀ gi, gi < groups.length → (withinOrd gi).Nodup)
    (g₁ c₁ j : Nat) :
    StageMemAt groups actTick
      (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ j)
      ((preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ j).tick) :=
  StageMemAt_of_TickQueueOk groups actTick _ _
    (preStepWorld_tickQueueOk groups actTick groupOrd withinOrd pos
      h_gord_nd h_within_nd g₁ c₁ j).1

/-- Membership in an eraseIdx result implies membership in the
    original list. -/
private theorem mem_of_mem_eraseIdx' {α : Type} (l : List α)
    (i : Nat) (h_i : i < l.length) (a : α)
    (h_mem : a ∈ l.eraseIdx i) : a ∈ l := by
  revert i h_i a h_mem
  induction l with
  | nil => intro i h_i a h_a; cases h_i
  | cons x l' ih =>
    intro i h_i a h_a
    cases i with
    | zero =>
      change a ∈ l' at h_a
      exact List.mem_cons.mpr (Or.inr h_a)
    | succ i' =>
      change a ∈ x :: l'.eraseIdx i' at h_a
      rw [List.mem_cons] at h_a
      rcases h_a with h_ax | h_a
      · exact List.mem_cons.mpr (Or.inl h_ax)
      · exact List.mem_cons.mpr (Or.inr
          (ih i' (Nat.lt_of_succ_lt_succ h_i) a h_a))

/-- Reinserting an element distinct from both endpoints cannot destroy
    a betweenness. -/
private theorem evBefore_of_eraseIdx_of_ne (l : List ScheduledEvent) :
    ∀ (i : Nat) (h_i : i < l.length) (x y : ScheduledEvent),
      l[i]'h_i ≠ x → l[i]'h_i ≠ y →
      evBefore (l.eraseIdx i) x y → evBefore l x y := by
  induction l with
  | nil => intro i h_i; cases h_i
  | cons a l' ih =>
    intro i h_i x y h_ne_x h_ne_y h_b
    cases i with
    | zero =>
      change evBefore l' x y at h_b
      exact evBefore.cons_extend h_b
    | succ i' =>
      have h_i' : i' < l'.length := Nat.lt_of_succ_lt_succ h_i
      change evBefore (a :: l'.eraseIdx i') x y at h_b
      rw [evBefore.cons_iff] at h_b
      rcases h_b with ⟨h_ax, h_y⟩ | h_b
      · subst h_ax
        refine ⟨[], l', rfl, ?_⟩
        exact mem_of_mem_eraseIdx' l' i' h_i' y h_y
      · exact evBefore.cons_extend
          (ih i' h_i' x y (by simpa using h_ne_x)
            (by simpa using h_ne_y) h_b)

/-- A due event occupying the erased position cannot belong to the
    due-filter of the erased list: it would occur twice in the
    duplicate-free due-filter of the original list. (Reproven; private
    in SamePriorityPopOrder.) -/
private theorem not_mem_eraseIdx_due (t : Nat) (l : List ScheduledEvent) :
    ∀ (i : Nat) (h_i : i < l.length) (A : ScheduledEvent),
      l[i]'h_i = A → A.targetTick = t →
      (l.filter (fun e => e.targetTick == t)).Nodup →
      A ∉ (l.eraseIdx i).filter (fun e => e.targetTick == t) := by
  induction l with
  | nil => intro i h_i; cases h_i
  | cons a l' ih =>
    intro i h_i A h_get hA_due h_nd
    cases i with
    | zero =>
      change a = A at h_get
      subst h_get
      simp only [List.eraseIdx]
      intro h_A
      have h_pa : (fun e => e.targetTick == t) a = true := by
        simpa using hA_due
      have h_filt : (a :: l').filter (fun e => e.targetTick == t) =
          a :: l'.filter (fun e => e.targetTick == t) := by
        simp only [List.filter, h_pa]
      rw [h_filt, List.nodup_cons] at h_nd
      exact h_nd.1 h_A
    | succ i' =>
      have h_i' : i' < l'.length := Nat.lt_of_succ_lt_succ h_i
      have h_get' : l'[i']'h_i' = A := by
        simpa using h_get
      by_cases h_pa : (fun e => e.targetTick == t) a = true
      · have h_filt : (a :: l').filter (fun e => e.targetTick == t) =
            a :: l'.filter (fun e => e.targetTick == t) := by
          simp only [List.filter, h_pa]
        rw [h_filt, List.nodup_cons] at h_nd
        have h_nd' : (l'.filter (fun e => e.targetTick == t)).Nodup :=
          h_nd.2
        have h_a_not : a ∉ l'.filter (fun e => e.targetTick == t) :=
          h_nd.1
        simp only [List.eraseIdx]
        intro h_A
        have h_A' : A = a ∨ A ∈
            (l'.eraseIdx i').filter (fun e => e.targetTick == t) := by
          simpa only [List.filter, h_pa, List.mem_cons] using h_A
        rcases h_A' with h_Aa | h_A'
        · have h_a_l' : a ∈ l' := by
            rw [← h_Aa, ← h_get']
            exact List.getElem_mem h_i'
          have h_a_filt : a ∈ l'.filter (fun e => e.targetTick == t) := by
            rw [List.mem_filter]
            exact ⟨h_a_l', by rw [← h_Aa]; simpa using hA_due⟩
          exact h_a_not h_a_filt
        · exact ih i' h_i' A h_get' hA_due h_nd' h_A'
      · have h_filt : (a :: l').filter (fun e => e.targetTick == t) =
            l'.filter (fun e => e.targetTick == t) := by
          simp only [List.filter, h_pa]
        rw [h_filt] at h_nd
        simp only [List.eraseIdx, List.filter, h_pa]
        exact ih i' h_i' A h_get' hA_due h_nd

/-- `processNEvents` keeps the due filter Nodup. -/
private theorem due_Nodup_processNEvents (w : World) (n : Nat)
    (h_nd : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup) :
    ((processNEvents w n).events.filter
      (fun e => e.targetTick == (processNEvents w n).tick)).Nodup := by
  induction n generalizing w with
  | zero =>
    simp [processNEvents]
    exact h_nd
  | succ n ih =>
    dsimp only [processNEvents]
    cases h_step : w.step with
    | none => exact h_nd
    | some w' =>
      dsimp [World.step] at h_step
      cases h_pop : w.popNextEvent with
      | none =>
        simp only [h_pop] at h_step
        cases h_step
      | some p =>
        rcases p with ⟨ev₀, w_pop⟩
        simp only [h_pop] at h_step
        injection h_step with h_w'
        obtain ⟨idx, h_idx, h_erase, h_tick_ev, _, h_get_idx⟩ :=
          World.popNextEvent_eraseIdx w ev₀ w_pop h_pop
        set due := w.events.filter (fun e => e.targetTick == w.tick)
        have h_due_ev₀ : (fun e => e.targetTick == w.tick)
            (w.events[idx]'h_idx) = true := by
          simp [h_get_idx, h_tick_ev]
        obtain ⟨j, hj, h_filter_erase, h_get_due⟩ :=
          filter_eraseIdx_getElem (fun e => e.targetTick == w.tick)
            w.events idx h_idx h_due_ev₀
        obtain ⟨new₀, h_app_new, h_fut_new⟩ :=
          World.onScheduledTick_appends_future w_pop ev₀.nodeId
        have h_due_w' : w'.events.filter
            (fun e => e.targetTick == w'.tick) = due.eraseIdx j := by
          rw [← h_w', World.onScheduledTick_tick,
            World.popNextEvent_tick w ev₀ w_pop h_pop, h_app_new,
            List.filter_append]
          have h_new_nil : new₀.filter
              (fun e => e.targetTick == w.tick) = [] := by
            apply List.filter_eq_nil_iff.mpr
            intro e h_e
            have h_gt := h_fut_new e h_e
            rw [World.popNextEvent_tick w ev₀ w_pop h_pop] at h_gt
            simp
            omega
          rw [h_new_nil, List.append_nil, h_erase, h_filter_erase]
        exact ih (w := w') (by rw [h_due_w']; exact nodup_eraseIdx due j h_nd)

/-- Betweenness in the due filter of a `processNEvents` result, among
    events still due at the input tick, already held in the input's
    due filter: pops erase only due events distinct from the
    endpoints. -/
private theorem evBefore_due_processNEvents_back (w : World) (n : Nat)
    (x y : ScheduledEvent)
    (h_x : x ∈ (processNEvents w n).events)
    (h_y : y ∈ (processNEvents w n).events)
    (h_xt : x.targetTick = w.tick) (h_yt : y.targetTick = w.tick)
    (h_nodup : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup)
    (h_b : evBefore ((processNEvents w n).events.filter
        (fun e => e.targetTick == w.tick)) x y) :
    evBefore (w.events.filter (fun e => e.targetTick == w.tick)) x y := by
  induction n generalizing w with
  | zero =>
    simp [processNEvents] at h_b
    exact h_b
  | succ n ih =>
    dsimp only [processNEvents] at h_x h_y h_b ⊢
    cases h_step : w.step with
    | none => simpa [h_step] using h_b
    | some w' =>
      simp only [h_step] at h_x h_y h_b ⊢
      dsimp [World.step] at h_step
      cases h_pop : w.popNextEvent with
      | none =>
        simp only [h_pop] at h_step
        cases h_step
      | some p =>
        rcases p with ⟨ev₀, w_pop⟩
        simp only [h_pop] at h_step
        injection h_step with h_w'
        have h_tick_pop : w_pop.tick = w.tick :=
          World.popNextEvent_tick w ev₀ w_pop h_pop
        have h_tick_w' : w'.tick = w.tick := by
          rw [← h_w', World.onScheduledTick_tick, h_tick_pop]
        have h_x_w' : x ∈ w'.events :=
          mem_processNEvents_due_back w' n x h_x (by rw [h_xt, h_tick_w'])
        have h_y_w' : y ∈ w'.events :=
          mem_processNEvents_due_back w' n y h_y (by rw [h_yt, h_tick_w'])
        obtain ⟨new₀, h_app_new, h_fut_new⟩ :=
          World.onScheduledTick_appends_future w_pop ev₀.nodeId
        have h_x_pop : x ∈ w_pop.events := by
          rw [← h_w', h_app_new, List.mem_append] at h_x_w'
          rcases h_x_w' with h | h_new
          · exact h
          · have h_gt := h_fut_new x h_new
            rw [h_tick_pop, h_xt] at h_gt
            omega
        have h_y_pop : y ∈ w_pop.events := by
          rw [← h_w', h_app_new, List.mem_append] at h_y_w'
          rcases h_y_w' with h | h_new
          · exact h
          · have h_gt := h_fut_new y h_new
            rw [h_tick_pop, h_yt] at h_gt
            omega
        obtain ⟨idx, h_idx, h_erase, h_tick_ev, _, h_get_idx⟩ :=
          World.popNextEvent_eraseIdx w ev₀ w_pop h_pop
        set due := w.events.filter (fun e => e.targetTick == w.tick)
        have h_due_ev₀ : (fun e => e.targetTick == w.tick)
            (w.events[idx]'h_idx) = true := by
          simp [h_get_idx, h_tick_ev]
        obtain ⟨j, hj, h_filter_erase, h_get_due⟩ :=
          filter_eraseIdx_getElem (fun e => e.targetTick == w.tick)
            w.events idx h_idx h_due_ev₀
        have h_get_due_ev₀ : due[j]'hj = ev₀ := h_get_due.trans h_get_idx
        have h_due_w' : w'.events.filter
            (fun e => e.targetTick == w'.tick) = due.eraseIdx j := by
          rw [← h_w', World.onScheduledTick_tick, h_tick_pop, h_app_new,
            List.filter_append]
          have h_new_nil : new₀.filter
              (fun e => e.targetTick == w.tick) = [] := by
            apply List.filter_eq_nil_iff.mpr
            intro e h_e
            have h_gt := h_fut_new e h_e
            rw [h_tick_pop] at h_gt
            simp
            omega
          rw [h_new_nil, List.append_nil, h_erase, h_filter_erase]
        have h_ev_ne_x : ev₀ ≠ x := by
          intro h_eq
          have h_x_due' : x ∈ due.eraseIdx j := by
            rw [← h_filter_erase, List.mem_filter]
            refine ⟨?_, ?_⟩
            · rwa [← h_erase]
            · simpa using h_xt
          have h_not : ev₀ ∉ due.eraseIdx j := by
            rw [← h_filter_erase]
            exact not_mem_eraseIdx_due w.tick w.events idx h_idx ev₀
              h_get_idx h_tick_ev h_nodup
          exact h_not (by rwa [← h_eq] at h_x_due')
        have h_ev_ne_y : ev₀ ≠ y := by
          intro h_eq
          have h_y_due' : y ∈ due.eraseIdx j := by
            rw [← h_filter_erase, List.mem_filter]
            refine ⟨?_, ?_⟩
            · rwa [← h_erase]
            · simpa using h_yt
          have h_not : ev₀ ∉ due.eraseIdx j := by
            rw [← h_filter_erase]
            exact not_mem_eraseIdx_due w.tick w.events idx h_idx ev₀
              h_get_idx h_tick_ev h_nodup
          exact h_not (by rwa [← h_eq] at h_y_due')
        have h_nd_w' : (w'.events.filter
            (fun e => e.targetTick == w'.tick)).Nodup := by
          rw [h_due_w']
          exact nodup_eraseIdx due j h_nodup
        have h_b_erase : evBefore (due.eraseIdx j) x y := by
          have h_b_w' : evBefore (w'.events.filter
              (fun e => e.targetTick == w'.tick)) x y :=
            ih (w := w') (h_x := h_x) (h_y := h_y)
              (h_xt := by rw [h_xt, h_tick_w'])
              (h_yt := by rw [h_yt, h_tick_w'])
              (h_nodup := h_nd_w')
              (h_b := by simpa [h_tick_w'] using h_b)
          rwa [h_due_w'] at h_b_w'
        exact evBefore_of_eraseIdx_of_ne due j hj x y
          (fun hc => h_ev_ne_x (h_get_due_ev₀.symm.trans hc))
          (fun hc => h_ev_ne_y (h_get_due_ev₀.symm.trans hc))
          h_b_erase

/-- Betweenness in the due filter of a burst result, among events
    still due at the input tick, already held in the input's due
    filter. `activateGroup` segments append strictly future events,
    and `processNEvents` pops erase only due events distinct from the
    endpoints. -/
theorem evBefore_due_gSimBurst_back (t : Nat) (obsAll : List (List Nat))
    (withinOrd pos : Nat → List Nat) (w : World) (pairs : List (Nat × Nat))
    (x y : ScheduledEvent)
    (h_x : x ∈ (gSimBurst t obsAll withinOrd pos w pairs).events)
    (h_y : y ∈ (gSimBurst t obsAll withinOrd pos w pairs).events)
    (h_xt : x.targetTick = w.tick) (h_yt : y.targetTick = w.tick)
    (h_nodup : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup)
    (h_b : evBefore ((gSimBurst t obsAll withinOrd pos w pairs).events.filter
        (fun e => e.targetTick == w.tick)) x y) :
    evBefore (w.events.filter (fun e => e.targetTick == w.tick)) x y := by
  induction pairs generalizing w with
  | nil =>
    simp [gSimBurst] at h_b
    exact h_b
  | cons p ps ih =>
    simp only [gSimBurst, List.foldl_cons] at h_x h_y h_b ⊢
    rcases p with ⟨gi, k⟩
    set m := (pos t)[k]?.getD 0
    set ordered : List Nat := (withinOrd gi).foldl (fun acc ci =>
      match (obsAll[gi]?.getD [])[ci]? with
      | some oid => acc ++ [oid]
      | none => acc) []
    set Wproc := processNEvents w m
    set W₁ := activateGroup Wproc ordered
    have h_tick_W₁ : W₁.tick = w.tick := by
      dsimp [W₁, Wproc]
      rw [activateGroup_tick, processNEvents_tick]
    have h_nd_W₁ : (W₁.events.filter
        (fun e => e.targetTick == W₁.tick)).Nodup := by
      have h_due_eq : W₁.events.filter
          (fun e => e.targetTick == W₁.tick) =
          Wproc.events.filter (fun e => e.targetTick == Wproc.tick) := by
        dsimp only [W₁]
        obtain ⟨new₁, h_app₁, h_fut₁⟩ := activateGroup_events_append
          Wproc ordered
        rw [h_app₁, activateGroup_tick, List.filter_append]
        have h_nil : new₁.filter
            (fun e => e.targetTick == Wproc.tick) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro e h_e
          have h_gt := h_fut₁ e h_e
          simp
          omega
        rw [h_nil, List.append_nil]
      rw [h_due_eq]
      exact due_Nodup_processNEvents w m h_nodup
    have h_x_tail : x ∈ (gSimBurst t obsAll withinOrd pos W₁ ps).events := by
      convert h_x using 1
      simp only [gSimBurst, W₁, Wproc, ordered, m]
      congr 1
    have h_y_tail : y ∈ (gSimBurst t obsAll withinOrd pos W₁ ps).events := by
      convert h_y using 1
      simp only [gSimBurst, W₁, Wproc, ordered, m]
      congr 1
    have h_b_tail : evBefore ((gSimBurst t obsAll withinOrd pos W₁
        ps).events.filter (fun e => e.targetTick == W₁.tick)) x y := by
      convert h_b using 1
      simp only [gSimBurst, W₁, Wproc, ordered, m]
      congr 1
      · funext e
        rw [h_tick_W₁]
    have h_b_W₁ : evBefore (W₁.events.filter
        (fun e => e.targetTick == W₁.tick)) x y :=
      ih (w := W₁) (h_x := h_x_tail) (h_y := h_y_tail)
        (h_xt := by rw [h_xt, h_tick_W₁])
        (h_yt := by rw [h_yt, h_tick_W₁])
        (h_nodup := h_nd_W₁)
        (h_b := h_b_tail)
    -- back through the activateGroup append (due filter unchanged)
    have h_due_W₁ : W₁.events.filter (fun e => e.targetTick == W₁.tick) =
        Wproc.events.filter (fun e => e.targetTick == Wproc.tick) := by
      dsimp only [W₁]
      obtain ⟨new₁, h_app₁, h_fut₁⟩ := activateGroup_events_append
        Wproc ordered
      rw [h_app₁, activateGroup_tick, List.filter_append]
      have h_nil : new₁.filter
          (fun e => e.targetTick == Wproc.tick) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro e h_e
        have h_gt := h_fut₁ e h_e
        simp
        omega
      rw [h_nil, List.append_nil]
    rw [h_due_W₁] at h_b_W₁
    -- back to Wproc membership: x, y are due, so not activateGroup spawns
    have h_x_W₁ : x ∈ W₁.events :=
      mem_gSimBurst_due_back t obsAll withinOrd pos W₁ ps x h_x_tail (by
        rw [h_xt, h_tick_W₁])
    have h_y_W₁ : y ∈ W₁.events :=
      mem_gSimBurst_due_back t obsAll withinOrd pos W₁ ps y h_y_tail (by
        rw [h_yt, h_tick_W₁])
    have h_x_proc : x ∈ Wproc.events := by
      dsimp [W₁] at h_x_W₁
      rw [activateGroup_events_map, List.mem_append] at h_x_W₁
      rcases h_x_W₁ with h | h_obs
      · exact h
      · rcases List.mem_map.mp h_obs with ⟨nid, _, h_ev_eq⟩
        have h_tgt : x.targetTick = Wproc.tick + 2 := by
          rw [← h_ev_eq]
        have h_tick_proc : Wproc.tick = w.tick := by
          dsimp [Wproc]
          exact processNEvents_tick w m
        rw [h_tick_proc, h_xt] at h_tgt
        omega
    have h_y_proc : y ∈ Wproc.events := by
      dsimp [W₁] at h_y_W₁
      rw [activateGroup_events_map, List.mem_append] at h_y_W₁
      rcases h_y_W₁ with h | h_obs
      · exact h
      · rcases List.mem_map.mp h_obs with ⟨nid, _, h_ev_eq⟩
        have h_tgt : y.targetTick = Wproc.tick + 2 := by
          rw [← h_ev_eq]
        have h_tick_proc : Wproc.tick = w.tick := by
          dsimp [Wproc]
          exact processNEvents_tick w m
        rw [h_tick_proc, h_yt] at h_tgt
        omega
    exact evBefore_due_processNEvents_back w m x y h_x_proc h_y_proc
      h_xt h_yt h_nodup
      (by simpa [Wproc, processNEvents_tick] using h_b_W₁)

/-- The endpoints of a betweenness are both members of the list. -/
private theorem evBefore_mem_both {l : List ScheduledEvent}
    {x y : ScheduledEvent} (h : evBefore l x y) : x ∈ l ∧ y ∈ l := by
  obtain ⟨p, q, h_eq, h_y⟩ := h
  refine ⟨?_, ?_⟩
  · rw [h_eq]
    exact List.mem_append_right p (List.mem_cons.mpr (Or.inl rfl))
  · rw [h_eq]
    exact List.mem_append_right p (List.mem_cons.mpr (Or.inr h_y))

/-- `MiddleBlockOk` restricts to a due-style filter of the queue. -/
theorem MiddleBlockOk_filter (groups : List GroupSpec)
    (actTick : Nat → Nat) (T : Nat) (queue : List ScheduledEvent)
    (t : Nat) (g₁ c₁ g₂ c₂ j : Nat)
    (h_mb : MiddleBlockOk groups actTick T queue g₁ c₁ g₂ c₂ j) :
    MiddleBlockOk groups actTick T
      (queue.filter (fun e => e.targetTick == t)) g₁ c₁ g₂ c₂ j := by
  intro e h_b1 h_b2 h_pri h_tgt
  exact h_mb e (evBefore.of_filter _ h_b1) (evBefore.of_filter _ h_b2)
    h_pri h_tgt

/-- `MiddleBlockOk` at the full tick-start queue lifts to the
    post-burst due filter: betweenness among burst survivors there
    already held at the tick-start queue. -/
theorem MiddleBlockOk_preStepWorld (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (T : Nat)
    (g₁ c₁ g₂ c₂ m : Nat)
    (h_mb : MiddleBlockOk groups actTick T
        ((gSimWorld groups actTick groupOrd withinOrd pos
          (stageTarget actTick groups g₁ c₁ m)).events) g₁ c₁ g₂ c₂ m)
    (h_gord_nd : groupOrd.Nodup)
    (h_within_nd : ∀ gi, gi < groups.length → (withinOrd gi).Nodup) :
    MiddleBlockOk groups actTick T
      ((preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ m).events.filter
        (fun ev => ev.targetTick ==
          (preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ m).tick))
      g₁ c₁ g₂ c₂ m := by
  set τ := stageTarget actTick groups g₁ c₁ m
  set wQ := gSimWorld groups actTick groupOrd withinOrd pos τ
  set wQ_log := wQ.logOutput s!"tick {τ}"
  set W_B := preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ m
  set pairs := (popActive groups actTick groupOrd g₁ c₁ m).zipIdx
  have h_tick_log : wQ_log.tick = τ := by
    dsimp [wQ_log, wQ]
    rw [gSimWorld_tick groups actTick groupOrd withinOrd pos τ]
  have h_W_B : W_B = gSimBurst τ (buildGroups groups).2 withinOrd pos
      wQ_log pairs := by
    dsimp [W_B, preStepWorld, popQueueWorld, popActive, wQ_log, wQ, pairs, τ]
  have h_nd_log : (wQ_log.events.filter
      (fun ev => ev.targetTick == wQ_log.tick)).Nodup := by
    rw [World.logOutput_events, h_tick_log]
    exact List.Nodup.filter (fun ev => ev.targetTick == τ)
      (gSimWorld_events_Nodup groups actTick groupOrd withinOrd pos τ
        h_gord_nd h_within_nd)
  intro e h_b1 h_b2 h_pri h_tgt
  apply h_mb e
  · -- Aₘ before e: lift from the post-burst due filter
    apply evBefore.of_filter (fun ev => ev.targetTick == τ)
    obtain ⟨hA_filt, h_e_filt⟩ := evBefore_mem_both h_b1
    have hA_B : stageEvent actTick groups g₁ c₁ m ∈
        (gSimBurst τ (buildGroups groups).2 withinOrd pos wQ_log
          pairs).events := by
      have h_mem := (List.mem_filter.mp hA_filt).1
      dsimp [W_B, preStepWorld, popQueueWorld, popActive, wQ_log, wQ,
        pairs, τ] at h_mem
      exact h_mem
    have h_e_B : e ∈ (gSimBurst τ (buildGroups groups).2 withinOrd pos
        wQ_log pairs).events := by
      have h_mem := (List.mem_filter.mp h_e_filt).1
      dsimp [W_B, preStepWorld, popQueueWorld, popActive, wQ_log, wQ,
        pairs, τ] at h_mem
      exact h_mem
    have hA_tgt : (stageEvent actTick groups g₁ c₁ m).targetTick =
        wQ_log.tick := by
      have h_t := (List.mem_filter.mp hA_filt).2
      have h_eq : (stageEvent actTick groups g₁ c₁ m).targetTick =
          W_B.tick := by simpa [Nat.beq_eq] using h_t
      rw [h_eq]
      dsimp [W_B]
      rw [preStepWorld_tick_eq groups actTick groupOrd withinOrd pos
        g₁ c₁ m, h_tick_log]
    have h_e_tgt : e.targetTick = wQ_log.tick := by
      have h_t := (List.mem_filter.mp h_e_filt).2
      have h_eq : e.targetTick = W_B.tick := by
        simpa [Nat.beq_eq] using h_t
      rw [h_eq]
      dsimp [W_B]
      rw [preStepWorld_tick_eq groups actTick groupOrd withinOrd pos
        g₁ c₁ m, h_tick_log]
    have h_b1' : evBefore ((gSimBurst τ (buildGroups groups).2 withinOrd
        pos wQ_log pairs).events.filter
        (fun ev => ev.targetTick == wQ_log.tick))
        (stageEvent actTick groups g₁ c₁ m) e := by
      dsimp [W_B, preStepWorld, popQueueWorld, popActive, wQ_log, wQ,
        pairs, τ] at h_b1
      rw [gSimBurst_tick] at h_b1
      exact h_b1
    have h_lift := evBefore_due_gSimBurst_back τ (buildGroups groups).2
      withinOrd pos wQ_log pairs (stageEvent actTick groups g₁ c₁ m) e
      hA_B h_e_B hA_tgt h_e_tgt h_nd_log h_b1'
    rw [World.logOutput_events, h_tick_log] at h_lift
    exact h_lift
  · -- e before Dₘ: lift from the post-burst due filter
    apply evBefore.of_filter (fun ev => ev.targetTick == τ)
    obtain ⟨h_e_filt, hD_filt⟩ := evBefore_mem_both h_b2
    have h_e_B : e ∈ (gSimBurst τ (buildGroups groups).2 withinOrd pos
        wQ_log pairs).events := by
      have h_mem := (List.mem_filter.mp h_e_filt).1
      dsimp [W_B, preStepWorld, popQueueWorld, popActive, wQ_log, wQ,
        pairs, τ] at h_mem
      exact h_mem
    have hD_B : stageEvent actTick groups g₂ c₂ m ∈
        (gSimBurst τ (buildGroups groups).2 withinOrd pos wQ_log
          pairs).events := by
      have h_mem := (List.mem_filter.mp hD_filt).1
      dsimp [W_B, preStepWorld, popQueueWorld, popActive, wQ_log, wQ,
        pairs, τ] at h_mem
      exact h_mem
    have h_e_tgt : e.targetTick = wQ_log.tick := by
      have h_t := (List.mem_filter.mp h_e_filt).2
      have h_eq : e.targetTick = W_B.tick := by
        simpa [Nat.beq_eq] using h_t
      rw [h_eq]
      dsimp [W_B]
      rw [preStepWorld_tick_eq groups actTick groupOrd withinOrd pos
        g₁ c₁ m, h_tick_log]
    have hD_tgt : (stageEvent actTick groups g₂ c₂ m).targetTick =
        wQ_log.tick := by
      have h_t := (List.mem_filter.mp hD_filt).2
      have h_eq : (stageEvent actTick groups g₂ c₂ m).targetTick =
          W_B.tick := by simpa [Nat.beq_eq] using h_t
      rw [h_eq]
      dsimp [W_B]
      rw [preStepWorld_tick_eq groups actTick groupOrd withinOrd pos
        g₁ c₁ m, h_tick_log]
    have h_b2' : evBefore ((gSimBurst τ (buildGroups groups).2 withinOrd
        pos wQ_log pairs).events.filter
        (fun ev => ev.targetTick == wQ_log.tick))
        e (stageEvent actTick groups g₂ c₂ m) := by
      dsimp [W_B, preStepWorld, popQueueWorld, popActive, wQ_log, wQ,
        pairs, τ] at h_b2
      rw [gSimBurst_tick] at h_b2
      exact h_b2
    have h_lift := evBefore_due_gSimBurst_back τ (buildGroups groups).2
      withinOrd pos wQ_log pairs e (stageEvent actTick groups g₂ c₂ m)
      h_e_B hD_B h_e_tgt hD_tgt h_nd_log h_b2'
    rw [World.logOutput_events, h_tick_log] at h_lift
    exact h_lift
  · exact h_pri
  · exact h_tgt
