import BasicProofs.PrefixChain.Part16


open BasicRedstoneSim

/-- Convergence at ticks t₂, t₂+1, t₂+2 when an event exists at tick t₂:
    the outer two simBody steps agree for insertion positions `pos` and `pos'`. -/
theorem pos_indep_conv3_tail (c1 c2 : ChainSpec) (t1 t2 pos pos' : Nat)
    (h1_middle : ∀ d ∈ c1.middleDelays, ValidDelay d)
    (h1_last : ValidDelay c1.lastDelay)
    (h2_middle : ∀ d ∈ c2.middleDelays, ValidDelay d)
    (h2_last : ValidDelay c2.lastDelay) :
    let in1 := (buildChain World.empty "A" c1).1
    let in2 := (buildChain (buildChain World.empty "A" c1).2 "B" c2).1
    let w_t₂ := (List.range t2).foldl (simBody t1 t2 pos' in1 in2)
        (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
    let w₁_pos := simBody t1 t2 pos in1 in2 w_t₂ 0
    let w₁_pos' := simBody t1 t2 pos' in1 in2 w_t₂ 0
    (h_events : ∃ ev ∈ w_t₂.events, ev.targetTick = t2) →
    (h_t1_lt_t2 : t1 < t2) →
    (h_t₂_tick : w_t₂.tick = t2) →
    (h_delay_w : ∀ nid nd, w_t₂.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2) →
    (h_wt2_nodeId_lt : ∀ ev ∈ w_t₂.events, ev.nodeId < in2) →
    (h_wt2_nodeId_ne_in1 : ∀ ev ∈ w_t₂.events, ev.nodeId ≠ in1) →
    (h_nodes_eq : w₁_pos.nodes = w₁_pos'.nodes) →
    (h_log_eq : w₁_pos.outputLog = w₁_pos'.outputLog) →
    (h_nextId_eq : w₁_pos.nextId = w₁_pos'.nextId) →
    (h_perm : List.Perm w₁_pos.events w₁_pos'.events) →
    (h_no_at_t2p1 : ∀ ev ∈ w₁_pos.events, ev.targetTick ≠ t2 + 1) →
    (h_no_at_t2p1' : ∀ ev ∈ w₁_pos'.events, ev.targetTick ≠ t2 + 1) →
    simBody t1 t2 pos' in1 in2 (simBody t1 t2 pos' in1 in2 w₁_pos 1) 2 =
      simBody t1 t2 pos' in1 in2 (simBody t1 t2 pos' in1 in2 w₁_pos' 1) 2 := by
      intro in1 in2 w_t₂ w₁_pos w₁_pos' h_events h_t1_lt_t2 h_t₂_tick h_delay_w h_wt2_nodeId_lt h_wt2_nodeId_ne_in1 h_nodes_eq h_log_eq h_nextId_eq h_perm h_no_at_t2p1 h_no_at_t2p1'
      have h_tick₁_pos : w₁_pos.tick = t2 + 1 := by dsimp [w₁_pos]; rw [simBody_tick, h_t₂_tick]
      have h_tick₁_pos' : w₁_pos'.tick = t2 + 1 := by dsimp [w₁_pos']; rw [simBody_tick, h_t₂_tick]
      have h_iter1_pos : simBody t1 t2 pos' in1 in2 w₁_pos 1 =
          (w₁_pos.logOutput s!"tick {w₁_pos.tick}").stepUntilNextTick := by
        dsimp (config := { zeta := true }) [simBody]
        split_ifs <;> simp [World.setInput_tick, World.logOutput_tick] at * <;> try omega
      have h_iter1_pos' : simBody t1 t2 pos' in1 in2 w₁_pos' 1 =
          (w₁_pos'.logOutput s!"tick {w₁_pos'.tick}").stepUntilNextTick := by
        dsimp (config := { zeta := true }) [simBody]
        split_ifs <;> simp [World.setInput_tick, World.logOutput_tick] at * <;> try omega
      rw [h_iter1_pos, h_iter1_pos']
      dsimp (config := { zeta := true }) [simBody]
      split_ifs <;> simp [World.setInput_tick, World.logOutput_tick, World.tick_stepUntilNextTick] at * <;> try omega
      -- Concrete event-form re-derivation for the convergence step (mirrors h_perm setup)
      obtain ⟨ev_s, h_ev_s_mem, h_ev_s_tick⟩ := h_events
      have h_wt2_singleton₂ : w_t₂.events = [ev_s] := by
        have h_len : w_t₂.events.length = 1 := by
          have h_len_le : w_t₂.events.length ≤ 1 := by
            dsimp [w_t₂, in1, in2]
            exact (simFoldl_events_length_le_one c1 c2 t1 t2 pos' h_t1_lt_t2).1
          have h_pos : 0 < w_t₂.events.length := by
            by_contra hz
            have h_empty : w_t₂.events = [] := List.length_eq_zero_iff.mp (by omega)
            exact List.not_mem_nil (a := ev_s) (by rwa [← h_empty])
          omega
        have h_gen : ∀ (l : List ScheduledEvent) (x : ScheduledEvent),
            l.length = 1 → x ∈ l → l = [x] := by
          intro l x h_l_len h_x_mem
          cases l with
          | nil => simp at h_l_len
          | cons a tl =>
            have h_tl : tl = [] := by
              have h_app : (a :: tl).length = tl.length + 1 := rfl
              rw [h_app] at h_l_len
              exact List.length_eq_zero_iff.mp (by omega)
            have h_a : a = x := by
              rw [h_tl] at h_x_mem
              simp at h_x_mem
              exact h_x_mem.symm
            rw [h_tl, h_a]
        exact h_gen w_t₂.events ev_s h_len h_ev_s_mem
      set w_log₂ := w_t₂.logOutput s!"tick {t2}"
      set W_proc₂ := ({ w_log₂ with events := [] }).onScheduledTick ev_s.nodeId
      set o₂ : ScheduledEvent := { targetTick := t2 + 2, priority := 0, nodeId := in2 + 1 }
      have h_wlog2_events : w_log₂.events = [ev_s] := by
        dsimp [w_log₂]; exact h_wt2_singleton₂
      have h_wlog2_tick : w_log₂.tick = t2 := by
        dsimp [w_log₂]; exact h_t₂_tick
      have h_evs_ne_in2₂ : ev_s.nodeId ≠ in2 := by
        have := h_wt2_nodeId_lt ev_s h_ev_s_mem; omega
      -- Observer structure of in2 in w_t₂
      obtain ⟨h_in2_st₂, h_obs_st₂⟩ := w_t2_in2_observer_struct c1 c2 t1 t2 pos' h_t1_lt_t2
      obtain ⟨nd_in2₂, h_gn_in2₂, h_out_in2₂⟩ := h_in2_st₂
      obtain ⟨nd_obs₂, h_gn_obs₂, h_kind_obs₂⟩ := h_obs_st₂
      -- setInput in2 on w_log₂ appends [o₂]
      have h_setlog2 : (w_log₂.setInput in2 15).events = w_log₂.events ++ [o₂] := by
        have := setInput_append_observer w_log₂ in2 (in2 + 1)
          ⟨nd_in2₂, by dsimp [w_log₂]; rw [World.logOutput_getNode]; exact h_gn_in2₂, h_out_in2₂⟩
          ⟨nd_obs₂, by dsimp [w_log₂]; rw [World.logOutput_getNode]; exact h_gn_obs₂, h_kind_obs₂⟩
          (by omega)
        rw [h_wlog2_tick] at this
        dsimp [o₂]
        exact this
      -- W_proc₂ : world after processing ev_s once
      have h_step_log2 : w_log₂.step = some W_proc₂ := by
        dsimp [World.step, W_proc₂]
        rw [popNextEvent_singleton w_log₂ ev_s h_wlog2_events
          (by rw [h_wlog2_tick]; exact h_ev_s_tick)]
      have h_Wproc2_tick : W_proc₂.tick = t2 := by
        dsimp [W_proc₂]; rw [World.onScheduledTick_tick]; dsimp; rw [h_wlog2_tick]
      have h_delay_empty2 : ∀ nid nd, ({ w_log₂ with events := [] } : World).getNode nid = some nd →
          ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
        intro nid nd h_nd d p h_kind
        change w_log₂.getNode nid = some nd at h_nd
        dsimp [w_log₂] at h_nd
        rw [World.logOutput_getNode] at h_nd
        exact h_delay_w nid nd h_nd d p h_kind
      have h_tick_base2 : ({ w_log₂ with events := [] } : World).tick = t2 := by
        change w_log₂.tick = t2
        exact h_wlog2_tick
      -- processNEvents w_log₂ p = W_proc₂ for p ≥ 1
      have h_proc2 : ∀ p, p ≠ 0 → processNEvents w_log₂ p = W_proc₂ := by
        intro p hp_ne0
        have h_no : ∀ ev ∈ W_proc₂.events, ev.targetTick ≠ W_proc₂.tick := by
          dsimp [W_proc₂]
          obtain ⟨new_ev, h_app, h_fut⟩ :=
            World.onScheduledTick_events_append ({ w_log₂ with events := [] } : World) ev_s.nodeId h_delay_empty2
          rw [h_tick_base2] at h_fut
          intro ev h_ev
          have h_ev_new : ev ∈ new_ev := by
            have h_base : ({ w_log₂ with events := [] } : World).events = [] := rfl
            have : W_proc₂.events = [] ++ new_ev := by
              change (({ w_log₂ with events := [] } : World).onScheduledTick ev_s.nodeId).events = _
              rw [h_app, h_base]
            rwa [this, List.nil_append] at h_ev
          have h_gt := h_fut ev h_ev_new
          intro h_eq
          rw [h_eq, h_Wproc2_tick] at h_gt
          omega
        cases p with
        | zero => exfalso; apply hp_ne0; rfl
        | succ n =>
          dsimp [processNEvents]
          rw [h_step_log2]
          exact processNEvents_eq_of_no_events W_proc₂ n h_no
      -- setInput in2 on W_proc₂ appends [o₂]
      have h_Wproc_in2₂ : W_proc₂.getNode in2 = w_log₂.getNode in2 := by
        dsimp [W_proc₂]
        rw [World.onScheduledTick_getNode_ne _ ev_s.nodeId in2 (Ne.symm h_evs_ne_in2₂)]
        rfl
      have h_Wproc_obs₂ : W_proc₂.getNode (in2 + 1) = w_log₂.getNode (in2 + 1) := by
        dsimp [W_proc₂]
        have h_ne_obs : in2 + 1 ≠ ev_s.nodeId := by
          have := h_wt2_nodeId_lt ev_s h_ev_s_mem
          omega
        rw [World.onScheduledTick_getNode_ne _ ev_s.nodeId (in2 + 1) h_ne_obs]
        rfl
      have h_setW2 : (W_proc₂.setInput in2 15).events = W_proc₂.events ++ [o₂] := by
        have := setInput_append_observer W_proc₂ in2 (in2 + 1)
          ⟨nd_in2₂, by rw [h_Wproc_in2₂]; dsimp [w_log₂]; rw [World.logOutput_getNode]; exact h_gn_in2₂, h_out_in2₂⟩
          ⟨nd_obs₂, by rw [h_Wproc_obs₂]; dsimp [w_log₂]; rw [World.logOutput_getNode]; exact h_gn_obs₂, h_kind_obs₂⟩
          (by omega)
        rw [h_Wproc2_tick] at this
        dsimp [o₂]
        exact this
      -- W_proc₂.events has no events at tick t2
      have h_Wproc2_no : ∀ ev ∈ W_proc₂.events, ev.targetTick ≠ t2 := by
        dsimp [W_proc₂]
        obtain ⟨new_ev, h_app, h_fut⟩ :=
          World.onScheduledTick_events_append ({ w_log₂ with events := [] } : World) ev_s.nodeId h_delay_empty2
        rw [h_tick_base2] at h_fut
        intro ev h_ev
        have h_ev_new : ev ∈ new_ev := by
          have h_base : ({ w_log₂ with events := [] } : World).events = [] := rfl
          have : W_proc₂.events = [] ++ new_ev := by
            change (({ w_log₂ with events := [] } : World).onScheduledTick ev_s.nodeId).events = _
            rw [h_app, h_base]
          rwa [this, List.nil_append] at h_ev
        have h_gt := h_fut ev h_ev_new
        intro h_eq; omega
      set BW₂ := W_proc₂.setInput in2 15
      have h_BW2_tick : BW₂.tick = t2 := by dsimp [BW₂]; rw [World.setInput_tick, h_Wproc2_tick]
      have h_BW2_events : BW₂.events = W_proc₂.events ++ [o₂] := by dsimp [BW₂]; exact h_setW2
      have h_BW2_no : ∀ ev ∈ BW₂.events, ev.targetTick ≠ BW₂.tick := by
        intro ev h_ev
        rw [h_BW2_tick]
        dsimp [BW₂] at h_ev
        rw [h_setW2] at h_ev
        simp [List.mem_append] at h_ev
        rcases h_ev with h_ev | h_ev
        · exact h_Wproc2_no ev h_ev
        · subst h_ev; dsimp [o₂]; omega
      have h_BW2_sunt : BW₂.stepUntilNextTick.events = BW₂.events :=
        stepUntilNextTick_events_eq_of_no_events BW₂ h_BW2_no
      -- pos = 0 concrete form: (w_log₂.setInput in2 15).stepUntilNextTick.events = [o₂] ++ W_proc₂.events
      set B0₂ := w_log₂.setInput in2 15
      have h_B02_events : B0₂.events = [ev_s] ++ [o₂] := by
        dsimp [B0₂]; rw [h_setlog2, h_wlog2_events]; simp
      have h_B02_tick : B0₂.tick = t2 := by dsimp [B0₂]; rw [World.setInput_tick, h_wlog2_tick]
      have h_pop_B02 : B0₂.popNextEvent = some (ev_s, { B0₂ with events := [o₂] }) := by
        unfold World.popNextEvent
        rw [h_B02_events, h_B02_tick]
        dsimp (config := { zeta := true })
        have h_zip : (List.range 2).zip [ev_s, o₂] = [(0, ev_s), (1, o₂)] := by
          have h_range : List.range 2 = [0, 1] := by decide
          rw [h_range]
          simp
        have h_filter : ([(0, ev_s), (1, o₂)]).filter (fun x => x.2.targetTick == t2) =
            [(0, ev_s)] := by
          simp [o₂, h_ev_s_tick]
        rw [h_zip, h_filter]
        simp [o₂]
      set B0_pop₂ := { B0₂ with events := [o₂] }
      set C_proc₂ := B0_pop₂.onScheduledTick ev_s.nodeId
      have h_congr2 : ∃ new, W_proc₂.events = ({ w_log₂ with events := [] } : World).events ++ new ∧
          C_proc₂.events = B0_pop₂.events ++ new := by
        dsimp [W_proc₂, C_proc₂]
        apply onScheduledTick_events_congr ({ w_log₂ with events := [] }) B0_pop₂ ev_s.nodeId
        · dsimp [B0_pop₂, B0₂]
          simp [World.setInput_tick, h_wlog2_tick]
        · change w_log₂.getNode ev_s.nodeId = (w_log₂.setInput in2 15).getNode ev_s.nodeId
          exact (setInput_getNode_ne' w_log₂ in2 ev_s.nodeId h_evs_ne_in2₂).symm
        · intro nid
          change (w_log₂.getNode nid).map (·.kind) = ((w_log₂.setInput in2 15).getNode nid).map (·.kind)
          exact (setInput_map_kind w_log₂ in2 15 nid).symm
      obtain ⟨new_ev₂, h_Wproc_app2, h_Cproc_app2⟩ := h_congr2
      have h_base_empty2 : ({ w_log₂ with events := [] } : World).events = [] := rfl
      have h_Wproc_eq2 : W_proc₂.events = new_ev₂ := by
        rw [h_Wproc_app2, h_base_empty2, List.nil_append]
      have h_B0pop_events2 : B0_pop₂.events = [o₂] := rfl
      have h_Cproc_eq2 : C_proc₂.events = [o₂] ++ new_ev₂ := by
        rw [h_Cproc_app2, h_B0pop_events2]
      have h_B0_step2 : B0₂.step = some C_proc₂ := by
        dsimp [World.step, C_proc₂, B0_pop₂]
        rw [h_pop_B02]
      have h_Cproc2_tick : C_proc₂.tick = t2 := by
        dsimp [C_proc₂]
        rw [World.onScheduledTick_tick]
        dsimp [B0_pop₂, B0₂]
        rw [World.setInput_tick, h_wlog2_tick]
      have h_Cproc2_no : ∀ ev ∈ C_proc₂.events, ev.targetTick ≠ C_proc₂.tick := by
        intro ev h_ev
        rw [h_Cproc_eq2] at h_ev
        rw [h_Cproc2_tick]
        simp [] at h_ev
        rcases h_ev with h_ev | h_ev
        · subst h_ev; dsimp [o₂]; omega
        · exact h_Wproc2_no ev (h_Wproc_eq2.symm ▸ h_ev)
      have h_C2_events : B0₂.stepUntilNextTick.events = [o₂] ++ W_proc₂.events := by
        have h_sunt : B0₂.stepUntilNextTick = C_proc₂.stepUntilNextTick := by
          rw [World.stepUntilNextTick, h_B0_step2]
        rw [h_sunt, stepUntilNextTick_events_eq_of_no_events C_proc₂ h_Cproc2_no,
            h_Cproc_eq2, ← h_Wproc_eq2]
      -- Concrete event forms for w₁_pos / w₁_pos' by cases on pos / pos'
      have h_w1_eq : w₁_pos = ((processNEvents w_log₂ pos).setInput in2 15).stepUntilNextTick := by
        dsimp (config := { zeta := true }) [w₁_pos, simBody, w_log₂]
        split_ifs <;>
          (try { exfalso; simp [World.logOutput_tick, h_t₂_tick] at * <;> omega }) ;
          (try { congr 1; congr 1; simp [h_t₂_tick] })
      have h_w1'_eq : w₁_pos' = ((processNEvents w_log₂ pos').setInput in2 15).stepUntilNextTick := by
        dsimp (config := { zeta := true }) [w₁_pos', simBody, w_log₂]
        split_ifs <;>
          (try { exfalso; simp [World.logOutput_tick, h_t₂_tick] at * <;> omega }) ;
          (try { congr 1; congr 1; simp [h_t₂_tick] })
      have h_filter_pos : w₁_pos.events.filter (fun e => e.targetTick ≠ t2 + 2) =
          W_proc₂.events.filter (fun e => e.targetTick ≠ t2 + 2) := by
        rw [h_w1_eq]
        by_cases hp : pos = 0
        · subst hp
          have h_p0 : processNEvents w_log₂ 0 = w_log₂ := rfl
          rw [h_p0]
          have h_ev : ((w_log₂.setInput in2 15).stepUntilNextTick).events = [o₂] ++ W_proc₂.events := by
            change B0₂.stepUntilNextTick.events = _
            exact h_C2_events
          rw [h_ev]
          simp [o₂]
        · have h_ev : ((W_proc₂.setInput in2 15).stepUntilNextTick).events =
              W_proc₂.events ++ [o₂] := by
            change BW₂.stepUntilNextTick.events = _
            rw [h_BW2_sunt, h_BW2_events]
          rw [h_proc2 pos hp, h_ev]
          simp [o₂, List.filter_append]
      have h_filter_pos' : w₁_pos'.events.filter (fun e => e.targetTick ≠ t2 + 2) =
          W_proc₂.events.filter (fun e => e.targetTick ≠ t2 + 2) := by
        rw [h_w1'_eq]
        by_cases hp : pos' = 0
        · subst hp
          have h_p0 : processNEvents w_log₂ 0 = w_log₂ := rfl
          rw [h_p0]
          have h_ev : ((w_log₂.setInput in2 15).stepUntilNextTick).events = [o₂] ++ W_proc₂.events := by
            change B0₂.stepUntilNextTick.events = _
            exact h_C2_events
          rw [h_ev]
          simp [o₂]
        · have h_ev : ((W_proc₂.setInput in2 15).stepUntilNextTick).events =
              W_proc₂.events ++ [o₂] := by
            change BW₂.stepUntilNextTick.events = _
            rw [h_BW2_sunt, h_BW2_events]
          rw [h_proc2 pos' hp, h_ev]
          simp [o₂, List.filter_append]
      have h_future : w₁_pos.events.filter (fun e => e.targetTick ≠ t2 + 2) =
          w₁_pos'.events.filter (fun e => e.targetTick ≠ t2 + 2) := by
        rw [h_filter_pos, h_filter_pos']
      -- Reduce iterations 1,2 (ticks t2+1, t2+2 both ≠ t1, t2) to logOutput + stepUntilNextTick.
      -- Iteration 1 has no events at t2+1, so it just advances the tick to t2+2.
      have h_log1_tick : (w₁_pos.logOutput s!"tick {t2+1}").tick = t2 + 1 := by
        rw [World.logOutput_tick, h_tick₁_pos]
      have h_log1_no : ∀ ev ∈ (w₁_pos.logOutput s!"tick {t2+1}").events,
          ev.targetTick ≠ (w₁_pos.logOutput s!"tick {t2+1}").tick := by
        intro ev h_ev
        rw [h_log1_tick]
        simpa [World.logOutput_events] using h_no_at_t2p1 ev h_ev
      set M := w₁_pos.logOutput s!"tick {t2+1}"
      set M' := w₁_pos'.logOutput s!"tick {t2+1}"
      have h_M_step : M.stepUntilNextTick = { M with tick := t2 + 2 } := by
        rw [stepUntilNextTick_no_events M h_log1_no, h_log1_tick]
      have h_log1'_tick : (w₁_pos'.logOutput s!"tick {t2+1}").tick = t2 + 1 := by
        rw [World.logOutput_tick, h_tick₁_pos']
      have h_log1'_no : ∀ ev ∈ (w₁_pos'.logOutput s!"tick {t2+1}").events,
          ev.targetTick ≠ (w₁_pos'.logOutput s!"tick {t2+1}").tick := by
        intro ev h_ev
        rw [h_log1'_tick]
        simpa [World.logOutput_events] using h_no_at_t2p1' ev h_ev
      have h_M'_step : M'.stepUntilNextTick = { M' with tick := t2 + 2 } := by
        rw [stepUntilNextTick_no_events M' h_log1'_no, h_log1'_tick]
      -- The goal is definitionally (logOutput + stepUntilNextTick) ∘ (logOutput + stepUntilNextTick).
      -- Rewrite ticks to t2+1 / t2+2, collapse iteration 1 (no events at t2+1) via h_M_step.
      rw [h_tick₁_pos, h_tick₁_pos']
      change (M.stepUntilNextTick.logOutput s!"tick {t2+2}").stepUntilNextTick =
          (M'.stepUntilNextTick.logOutput s!"tick {t2+2}").stepUntilNextTick
      rw [h_M_step, h_M'_step]
      set W := ({ M with tick := t2 + 2 }).logOutput s!"tick {t2+2}"
      set W' := ({ M' with tick := t2 + 2 }).logOutput s!"tick {t2+2}"
      -- Invariant bundle: repeater priorities < 100 (lifted from buildChain to w_t₂ to w₁_pos)
      set w₀ := (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
      have h_np₀ : ∀ nid nd, w₀.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 100 := by
        dsimp [w₀]
        have h_c1 : ∀ nid nd, (buildChain World.empty "A" c1).2.getNode nid = some nd →
            ∀ d p, nd.kind = .repeater d p → p < 100 :=
          buildChain_repeater_priority_lt_100 World.empty "A" c1
            (fun nid nd h => by simp [World.empty, World.getNode] at h)
            (fun p hp => by simp [World.empty] at hp)
        have h_ids : ∀ p ∈ (buildChain World.empty "A" c1).2.nodes,
            p.1 < (buildChain World.empty "A" c1).2.nextId :=
          buildChain_ids_lt_nextId World.empty "A" c1 (fun p hp => by simp [World.empty] at hp)
        exact buildChain_repeater_priority_lt_100 (buildChain World.empty "A" c1).2 "B" c2 h_c1 h_ids
      have h_np_wt2 : ∀ nid nd, w_t₂.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 100 := by
        intro nid nd h_nd d p h_kind
        dsimp [w_t₂] at h_nd
        obtain ⟨nd₀, h_nd₀, h_kind_eq⟩ := simFoldl_kind_preserved w₀ t1 t2 pos' in1 in2 t2 nid nd h_nd
        exact h_np₀ nid nd₀ h_nd₀ d p (h_kind_eq.symm.trans h_kind)
      have h_np0_neg : ∀ nid nd, w₀.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 0 := by
        dsimp [w₀]
        have h_c1n : ∀ nid nd, (buildChain World.empty "A" c1).2.getNode nid = some nd →
            ∀ d p, nd.kind = .repeater d p → p < 0 :=
          buildChain_repeater_priority_neg World.empty "A" c1
            (fun nid nd h => by simp [World.empty, World.getNode] at h)
            (fun p hp => by simp [World.empty] at hp)
        have h_idsn : ∀ p ∈ (buildChain World.empty "A" c1).2.nodes,
            p.1 < (buildChain World.empty "A" c1).2.nextId :=
          buildChain_ids_lt_nextId World.empty "A" c1 (fun p hp => by simp [World.empty] at hp)
        exact buildChain_repeater_priority_neg (buildChain World.empty "A" c1).2 "B" c2 h_c1n h_idsn
      have h_np_wt2_neg : ∀ nid nd, w_t₂.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 0 := by
        intro nid nd h_nd d p h_kind
        dsimp [w_t₂] at h_nd
        obtain ⟨nd₀, h_nd₀, h_kind_eq⟩ := simFoldl_kind_preserved w₀ t1 t2 pos' in1 in2 t2 nid nd h_nd
        exact h_np0_neg nid nd₀ h_nd₀ d p (h_kind_eq.symm.trans h_kind)
      have h_pri_wt2 : ∀ ev ∈ w_t₂.events, ev.priority < 100 := by
        dsimp [w_t₂, w₀]
        apply simFoldl_events_pri (buildChain (buildChain World.empty "A" c1).2 "B" c2).2 t1 t2 pos' in1 in2 t2
        · intro ev h_ev
          have h_ev_empty : (buildChain (buildChain World.empty "A" c1).2 "B" c2).2.events = [] := by
            have h_addNode_ev : ∀ (w : World) (nd : NodeData), (w.addNode nd).2.events = w.events := by
              intro w nd; dsimp [World.addNode]
            have h_repFoldl_ev : ∀ (d : PNat) (acc : List Nat × World),
                (repFoldlStep acc d).2.events = acc.2.events := by
              intro d acc; dsimp [repFoldlStep]; rw [h_addNode_ev]
            have h_foldl_ev : ∀ (ds : List PNat) (acc : List Nat × World),
                (ds.foldl repFoldlStep acc).2.events = acc.2.events := by
              intro ds acc; induction ds generalizing acc with
              | nil => rfl
              | cons d rest ih => simp [List.foldl_cons, h_repFoldl_ev, ih]
            have h_buildChainPre_ev : ∀ (w : World) (name : String) (c : ChainSpec),
                (buildChainPre w name c).2.1.events = w.events := by
              intro w name c
              dsimp [buildChainPre]
              rw [h_addNode_ev, h_addNode_ev, h_foldl_ev, h_addNode_ev, h_addNode_ev]
            have h_buildChain_ev : ∀ (w : World) (name : String) (c : ChainSpec),
                (buildChain w name c).2.events = w.events := by
              intro w name c
              dsimp [buildChain]
              rw [connectChain_events, h_buildChainPre_ev]
            rw [h_buildChain_ev, h_buildChain_ev]
            rfl
          rw [h_ev_empty] at h_ev; cases h_ev
        · exact h_np₀
        · intro nid nd h_nd d p h_kind
          have h_c1d : ∀ nid nd, (buildChain World.empty "A" c1).2.getNode nid = some nd →
              ∀ d p, nd.kind = .repeater d p → d ≥ 2 :=
            buildChain_repeater_delay_ge2 World.empty "A" c1
              (fun d hd => ValidDelay.ge2 (h1_middle d hd)) (ValidDelay.ge2 h1_last)
              (fun nid nd h => by simp [World.empty, World.getNode] at h)
              (fun p hp => by simp [World.empty] at hp)
          have h_idsd : ∀ p ∈ (buildChain World.empty "A" c1).2.nodes,
              p.1 < (buildChain World.empty "A" c1).2.nextId :=
            buildChain_ids_lt_nextId World.empty "A" c1 (fun p hp => by simp [World.empty] at hp)
          exact buildChain_repeater_delay_ge2 (buildChain World.empty "A" c1).2 "B" c2
            (fun d hd => ValidDelay.ge2 (h2_middle d hd)) (ValidDelay.ge2 h2_last) h_c1d h_idsd
            nid nd h_nd d p h_kind
      -- Lift to w₁_pos (simBody preserves kinds and event priorities)
      have h_delay_w1 : ∀ nid nd, w₁_pos.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
        intro nid nd h_nd d p h_kind
        obtain ⟨nd₀, h_nd₀, h_kind_eq⟩ := simBody_kind_preserved t1 t2 pos in1 in2 w_t₂ 0 nid nd h_nd
        exact h_delay_w nid nd₀ h_nd₀ d p (h_kind_eq.symm.trans h_kind)
      have h_np_w1 : ∀ nid nd, w₁_pos.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → p < 100 := by
        intro nid nd h_nd d p h_kind
        obtain ⟨nd₀, h_nd₀, h_kind_eq⟩ := simBody_kind_preserved t1 t2 pos in1 in2 w_t₂ 0 nid nd h_nd
        exact h_np_wt2 nid nd₀ h_nd₀ d p (h_kind_eq.symm.trans h_kind)
      have h_pri_w1 : ∀ ev ∈ w₁_pos.events, ev.priority < 100 :=
        simBody_events_pri t1 t2 pos in1 in2 w_t₂ 0 h_pri_wt2 h_np_wt2 h_delay_w
      change W.stepUntilNextTick = W'.stepUntilNextTick
      -- Projections of W / W' back to w₁_pos / w₁_pos'
      have h_W_nodes : W.nodes = w₁_pos.nodes := rfl
      have h_W'_nodes : W'.nodes = w₁_pos'.nodes := rfl
      have h_W_tick : W.tick = t2 + 2 := rfl
      have h_W'_tick : W'.tick = t2 + 2 := rfl
      have h_W_events : W.events = w₁_pos.events := rfl
      have h_W'_events : W'.events = w₁_pos'.events := rfl
      have h_W_nextId : W.nextId = w₁_pos.nextId := rfl
      have h_W'_nextId : W'.nextId = w₁_pos'.nextId := rfl
      have h_W_log : W.outputLog =
          w₁_pos.outputLog ++ [s!"tick {t2+1}", s!"tick {t2+2}"] := by
        dsimp [W, M, World.logOutput]; simp [List.append_assoc]
      have h_W'_log : W'.outputLog =
          w₁_pos'.outputLog ++ [s!"tick {t2+1}", s!"tick {t2+2}"] := by
        dsimp [W', M', World.logOutput]; simp [List.append_assoc]
      -- Membership: every event of w₁_pos is either o₂ or belongs to W_proc₂.events
      have h_w1_events_form : w₁_pos.events = [o₂] ++ W_proc₂.events ∨
          w₁_pos.events = W_proc₂.events ++ [o₂] := by
        by_cases hp : pos = 0
        · subst hp
          left
          rw [h_w1_eq]
          have h_p0 : processNEvents w_log₂ 0 = w_log₂ := rfl
          rw [h_p0]
          change B0₂.stepUntilNextTick.events = _
          exact h_C2_events
        · right
          rw [h_w1_eq]
          rw [h_proc2 pos hp]
          change BW₂.stepUntilNextTick.events = _
          rw [h_BW2_sunt, h_BW2_events]
      have h_mem_w1 : ∀ ev, ev ∈ w₁_pos.events → ev = o₂ ∨ ev ∈ W_proc₂.events := by
        intro ev h_ev
        rcases h_w1_events_form with h_form | h_form
        · rw [h_form] at h_ev
          simp at h_ev
          exact h_ev
        · rw [h_form] at h_ev
          simp at h_ev
          exact h_ev.elim Or.inr Or.inl
      -- W_proc₂ events at tick t2+2: none has priority 0 (o₂'s), and pairwise distinct priorities.
      have h_out_ev_s : ∀ nd, w_t₂.getNode ev_s.nodeId = some nd → nd.outputs.length ≤ 1 := by
        intro nd h_nd
        dsimp [w_t₂, in1, in2] at h_nd
        exact (simFoldl_events_length_le_one c1 c2 t1 t2 pos' h_t1_lt_t2).2 ev_s.nodeId nd h_nd
      have h_Wproc2_len : W_proc₂.events.length ≤ 1 := by
        dsimp [W_proc₂]
        have h_le := World.onScheduledTick_events_length_le
          ({ w_log₂ with events := [] } : World) ev_s.nodeId
        have h_elim : (({ w_log₂ with events := [] } : World).getNode ev_s.nodeId).elim 0
            (fun nd => nd.outputs.length) ≤ 1 := by
          cases h_gn : ({ w_log₂ with events := [] } : World).getNode ev_s.nodeId with
          | none => simp []
          | some nd =>
            simp []
            have h_gn_log : w_log₂.getNode ev_s.nodeId = some nd := by
              have : ({ w_log₂ with events := [] } : World).getNode ev_s.nodeId =
                  w_log₂.getNode ev_s.nodeId := by dsimp [World.getNode]
              rwa [this] at h_gn
            have h_nd_wt2 : w_t₂.getNode ev_s.nodeId = some nd := by
              have : w_log₂.getNode ev_s.nodeId = w_t₂.getNode ev_s.nodeId := by
                dsimp [w_log₂]; rw [World.logOutput_getNode]
              rwa [this] at h_gn_log
            exact h_out_ev_s nd h_nd_wt2
        simp at h_le
        omega
      have h_Wproc2_t2p2 :
          (∀ ev ∈ W_proc₂.events, ev.targetTick = t2 + 2 → ev.priority ≠ 0) ∧
          (∀ ev₁ ∈ W_proc₂.events, ∀ ev₂ ∈ W_proc₂.events,
            ev₁.targetTick = t2 + 2 → ev₂.targetTick = t2 + 2 → ev₁ ≠ ev₂ →
            ev₁.priority ≠ ev₂.priority) := by
        constructor
        · -- priority ≠ 0: new events from processing ev_s have negative priority
          intro ev h_ev _
          have h_out_prem : ∀ nd, ({ w_log₂ with events := [] } : World).getNode ev_s.nodeId = some nd →
              ∀ out_id ∈ nd.outputs, ∀ nd_out,
                ({ w_log₂ with events := [] } : World).getNode out_id = some nd_out →
                (∀ d p, nd_out.kind = .repeater d p → p < 0) ∧ nd_out.kind ≠ .observer := by
            intro nd h_nd out_id h_out_mem nd_out h_nd_out
            have h_gn_eq : ∀ x, ({ w_log₂ with events := [] } : World).getNode x =
                w_t₂.getNode x := by
              intro x
              have : ({ w_log₂ with events := [] } : World).getNode x = w_log₂.getNode x := by
                dsimp [World.getNode]
              rw [this]
              dsimp [w_log₂]
              rw [World.logOutput_getNode]
            rw [h_gn_eq] at h_nd h_nd_out
            constructor
            · exact h_np_wt2_neg out_id nd_out h_nd_out
            · exact w_t2_c1_outputs_not_observer c1 c2 t1 t2 pos' h_t1_lt_t2
                ev_s.nodeId (h_wt2_nodeId_lt ev_s h_ev_s_mem) (h_wt2_nodeId_ne_in1 ev_s h_ev_s_mem)
                nd h_nd out_id h_out_mem nd_out h_nd_out
          have h_neg : ev.priority < 0 :=
            World.onScheduledTick_new_events_neg ({ w_log₂ with events := [] } : World) ev_s.nodeId
              h_out_prem ev h_ev (by simp)
          omega
        · -- pairwise distinct priorities: W_proc₂.events.length ≤ 1, so no two distinct events
          intro ev₁ h_ev₁ ev₂ h_ev₂ h_t1' h_t2'' h_ne
          exfalso
          by_cases h0 : W_proc₂.events.length = 0
          · rw [List.length_eq_zero_iff.mp h0] at h_ev₁; cases h_ev₁
          · have h1 : W_proc₂.events.length = 1 := by omega
            have h_gen : ∀ (l : List ScheduledEvent) (x : ScheduledEvent),
                l.length = 1 → x ∈ l → l = [x] := by
              intro l x h_l_len h_x_mem
              cases l with
              | nil => simp at h_l_len
              | cons a tl =>
                have h_tl : tl = [] := by
                  have h_app : (a :: tl).length = tl.length + 1 := rfl
                  rw [h_app] at h_l_len
                  exact List.length_eq_zero_iff.mp (by omega)
                have h_a : a = x := by
                  rw [h_tl] at h_x_mem
                  simp at h_x_mem
                  exact h_x_mem.symm
                rw [h_tl, h_a]
            have h_single : W_proc₂.events = [ev₁] := h_gen W_proc₂.events ev₁ h1 h_ev₁
            rw [h_single] at h_ev₂
            simp at h_ev₂
            exact h_ne h_ev₂.symm
      apply stepUntilNextTick_perm_eq W W'
      · -- nodes
        rw [h_W_nodes, h_W'_nodes]; exact h_nodes_eq
      · -- tick
        rw [h_W_tick, h_W'_tick]
      · -- outputLog
        rw [h_W_log, h_W'_log, h_log_eq]
      · -- nextId
        rw [h_W_nextId, h_W'_nextId]; exact h_nextId_eq
      · -- perm
        rw [h_W_events, h_W'_events]; exact h_perm
      · -- future filter
        rw [h_W_events, h_W'_events, h_W_tick, h_W'_tick]; exact h_future
      · -- h_unique
        intro ev₁ h_ev₁ ev₂ h_ev₂ h_t1 h_t2' h_ne
        rw [h_W_events] at h_ev₁ h_ev₂
        rw [h_W_tick] at h_t1 h_t2'
        have h_m1 := h_mem_w1 ev₁ h_ev₁
        have h_m2 := h_mem_w1 ev₂ h_ev₂
        rcases h_m1 with rfl | h_ev1_W
        · rcases h_m2 with rfl | h_ev2_W
          · exact (h_ne rfl).elim
          · dsimp [o₂]
            exact Ne.symm (h_Wproc2_t2p2.1 ev₂ h_ev2_W h_t2')
        · rcases h_m2 with rfl | h_ev2_W
          · dsimp [o₂]
            exact h_Wproc2_t2p2.1 ev₁ h_ev1_W h_t1
          · exact h_Wproc2_t2p2.2 ev₁ h_ev1_W ev₂ h_ev2_W h_t1 h_t2' h_ne
      · -- h_pri
        intro ev h_ev
        rw [h_W_events] at h_ev
        exact h_pri_w1 ev h_ev
      · -- h_delay
        intro nid nd h_nd d p h_kind
        have h_nd_w1 : w₁_pos.getNode nid = some nd := by
          have : W.getNode nid = w₁_pos.getNode nid := by
            dsimp [World.getNode]; rw [h_W_nodes]
          rwa [this] at h_nd
        exact h_delay_w1 nid nd h_nd_w1 d p h_kind
      · -- h_new_pri
        intro nid nd h_nd d p h_kind
        have h_nd_w1 : w₁_pos.getNode nid = some nd := by
          have : W.getNode nid = w₁_pos.getNode nid := by
            dsimp [World.getNode]; rw [h_W_nodes]
          rwa [this] at h_nd
        exact h_np_w1 nid nd h_nd_w1 d p h_kind


/-- The simulation output is independent of the insertion position `pos`. -/
theorem simulateWithInsertion_pos_indep
    (c1 c2 : ChainSpec) (t1 t2 pos pos' : Nat)
    (h1_middle : ∀ d ∈ c1.middleDelays, ValidDelay d)
    (h1_last : ValidDelay c1.lastDelay)
    (h2_middle : ∀ d ∈ c2.middleDelays, ValidDelay d)
    (h2_last : ValidDelay c2.lastDelay)
    (h_same : t1 + c1.totalDelay = t2 + c2.totalDelay) :
    simulateWithInsertion c1 c2 t1 t2 pos = simulateWithInsertion c1 c2 t1 t2 pos' := by
  dsimp (config := { zeta := true }) [simulateWithInsertion]
  congr 1
  -- Goal: (range T).foldl (simBody ... pos ...) w₀ = (range T).foldl (simBody ... pos' ...) w₀
  -- w₀.tick = 0
  have h_w₀_tick : (buildChain (buildChain World.empty "A" c1).2 "B" c2).2.tick = 0 :=
    pos_indep_w0_tick c1 c2
  -- For ticks 0..t₂-1, bodies are identical
  have h_before : (List.range t2).foldl
      (simBody t1 t2 pos (buildChain World.empty "A" c1).1
        (buildChain (buildChain World.empty "A" c1).2 "B" c2).1)
      (buildChain (buildChain World.empty "A" c1).2 "B" c2).2 =
    (List.range t2).foldl
      (simBody t1 t2 pos' (buildChain World.empty "A" c1).1
        (buildChain (buildChain World.empty "A" c1).2 "B" c2).1)
      (buildChain (buildChain World.empty "A" c1).2 "B" c2).2 := by
    suffices h : ∀ k ≤ t2,
        (List.range k).foldl
          (simBody t1 t2 pos (buildChain World.empty "A" c1).1
            (buildChain (buildChain World.empty "A" c1).2 "B" c2).1)
          (buildChain (buildChain World.empty "A" c1).2 "B" c2).2 =
        (List.range k).foldl
          (simBody t1 t2 pos' (buildChain World.empty "A" c1).1
            (buildChain (buildChain World.empty "A" c1).2 "B" c2).1)
          (buildChain (buildChain World.empty "A" c1).2 "B" c2).2 by
      exact h t2 (le_refl t2)
    intro k hk
    induction k with
    | zero => rfl
    | succ k' ih =>
      have hk' : k' ≤ t2 := by omega
      rw [List.range_succ, List.foldl_append, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [ih hk']
      apply simBody_pos_indep
      rw [simFoldl_tick (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
        t1 t2 pos' (buildChain World.empty "A" c1).1
        (buildChain (buildChain World.empty "A" c1).2 "B" c2).1 k', h_w₀_tick]
      omega
  -- Split the foldl at t₂
  rw [foldl_split_simBody t1 t2 pos
      (buildChain World.empty "A" c1).1
      (buildChain (buildChain World.empty "A" c1).2 "B" c2).1
      (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
      t2 (max (t1 + c1.totalDelay) (t2 + c2.totalDelay) + 1) (by omega)]
  rw [foldl_split_simBody t1 t2 pos'
      (buildChain World.empty "A" c1).1
      (buildChain (buildChain World.empty "A" c1).2 "B" c2).1
      (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
      t2 (max (t1 + c1.totalDelay) (t2 + c2.totalDelay) + 1) (by omega)]
  rw [h_before]
  -- Remaining: (range (T-t₂)).foldl (simBody pos) w_t₂ = (range (T-t₂)).foldl (simBody pos') w_t₂
  set w_t₂ := (List.range t2).foldl
    (simBody t1 t2 pos' (buildChain World.empty "A" c1).1
      (buildChain (buildChain World.empty "A" c1).2 "B" c2).1)
    (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
  set in1 := (buildChain World.empty "A" c1).1
  set in2 := (buildChain (buildChain World.empty "A" c1).2 "B" c2).1
  set T := max (t1 + c1.totalDelay) (t2 + c2.totalDelay) + 1
  change (List.range (T - t2)).foldl (simBody t1 t2 pos in1 in2) w_t₂ =
    (List.range (T - t2)).foldl (simBody t1 t2 pos' in1 in2) w_t₂
  -- w_t₂.tick = t₂
  have h_t₂_tick : w_t₂.tick = t2 := pos_indep_wt2_tick c1 c2 t1 t2 pos'
  -- T - t₂ ≥ 5 (since c2.totalDelay ≥ 4)
  have h_T_ge : T - t2 ≥ 3 := by
    dsimp [T, ChainSpec.totalDelay]
    have := ValidDelay.ge2 h2_last
    omega
  -- Split at 3 iterations (ticks t₂, t₂+1, t₂+2)
  rw [foldl_split_simBody t1 t2 pos in1 in2 w_t₂ 3 (T - t2) (by omega)]
  rw [foldl_split_simBody t1 t2 pos' in1 in2 w_t₂ 3 (T - t2) (by omega)]
  -- Prove 3-iteration convergence: after processing ticks t₂, t₂+1, t₂+2, worlds are equal
  have h_conv_3 : (List.range 3).foldl (simBody t1 t2 pos in1 in2) w_t₂ =
      (List.range 3).foldl (simBody t1 t2 pos' in1 in2) w_t₂ := by
    simp only [List.range_succ, List.range_zero, List.foldl_cons, List.foldl_nil,
      List.nil_append, List.cons_append]
    -- Goal: simBody pos (simBody pos (simBody pos w_t₂ 0) 1) 2 = simBody pos' (simBody pos' (simBody pos' w_t₂ 0) 1) 2
    -- Iterations 1,2 have tick > t₂, so simBody is pos-independent
    set w₁_pos := simBody t1 t2 pos in1 in2 w_t₂ 0
    set w₁_pos' := simBody t1 t2 pos' in1 in2 w_t₂ 0
    have h_tick₁_pos : w₁_pos.tick = t2 + 1 := by dsimp [w₁_pos]; rw [simBody_tick, h_t₂_tick]
    have h_tick₁_pos' : w₁_pos'.tick = t2 + 1 := by dsimp [w₁_pos']; rw [simBody_tick, h_t₂_tick]
    -- Rewrite outer simBody (iteration 2) to use pos'
    have h_outer : simBody t1 t2 pos in1 in2 (simBody t1 t2 pos in1 in2 w₁_pos 1) 2 =
        simBody t1 t2 pos' in1 in2 (simBody t1 t2 pos in1 in2 w₁_pos 1) 2 := by
      apply simBody_pos_indep
      rw [simBody_tick, h_tick₁_pos]; omega
    -- Rewrite middle simBody (iteration 1) to use pos'
    have h_middle : simBody t1 t2 pos in1 in2 w₁_pos 1 =
        simBody t1 t2 pos' in1 in2 w₁_pos 1 := by
      apply simBody_pos_indep
      rw [h_tick₁_pos]; omega
    rw [h_outer]
    rw [h_middle]
    -- Goal: simBody pos' (simBody pos' w₁_pos 1) 2 = simBody pos' (simBody pos' w₁_pos' 1) 2
    -- w₁_pos and w₁_pos' differ by event swap at tick t₂+2 (different priorities).
    -- After simBody at tick t₂+1 (logOutput + stepUntilNextTick), swap preserved.
    -- After simBody at tick t₂+2, swap resolved (different priorities → same processing order).
    -- Key: prove w₁_pos = w₁_pos' by showing processNEvents + setInput + stepUntilNextTick
    -- is pos-independent when there are no events at tick t₂, or by convergence when there are.
    by_cases h_events : ∃ ev ∈ w_t₂.events, ev.targetTick = t2
    · -- Events exist at tick t₂: need convergence argument
      -- Prove w₁_pos = w₁_pos' by showing processNEvents + setInput in2 + stepUntilNextTick
      -- is pos-independent. Chain separation: events at tick t₂ target chain c1 nodes
      -- whose inputs are all < in2, so setInput in2 doesn't affect processing.
      have h_delay_w : ∀ nid nd, w_t₂.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2 :=
        pos_indep_wt2_delay c1 c2 t1 t2 pos' h1_middle h1_last h2_middle h2_last
      -- Chain separation + commutativity + fuel independence → w₁_pos = w₁_pos'
      -- w₁_pos = w₁_pos' is FALSE in general (event lists are permuted).
      -- Prove the 3-iteration convergence directly.
      -- Step 1: t₁ < t₂
      have h_t1_lt_t2 : t1 < t2 := pos_indep_t1_lt_t2 c1 c2 t1 t2 pos' h_events
      have h_in1_lt_in2 : in1 < in2 := pos_indep_in1_lt_in2 c1 c2
      have h_wt2_nodeId_lt : ∀ ev ∈ w_t₂.events, ev.nodeId < in2 :=
        pos_indep_wt2_nodeId_lt c1 c2 t1 t2 pos' h1_middle h1_last h2_middle h2_last h_in1_lt_in2
      have h_wt2_nodeId_ne_in1 : ∀ ev ∈ w_t₂.events, ev.nodeId ≠ in1 :=
        pos_indep_wt2_nodeId_ne_in1 c1 c2 t1 t2 pos' h1_middle h1_last h2_middle h2_last h_in1_lt_in2
      have h_nodes_eq : w₁_pos.nodes = w₁_pos'.nodes :=
        pos_indep_w1_nodes_eq c1 c2 t1 t2 pos pos' h1_middle h1_last h2_middle h2_last
        h_t1_lt_t2 h_t₂_tick h_delay_w h_wt2_nodeId_lt
      have h_log_eq : w₁_pos.outputLog = w₁_pos'.outputLog :=
        pos_indep_w1_log_eq c1 c2 t1 t2 pos pos' h1_middle h1_last h2_middle h2_last
        h_t1_lt_t2 h_t₂_tick h_delay_w h_wt2_nodeId_lt
      have h_nextId_eq : w₁_pos.nextId = w₁_pos'.nextId := by
        dsimp (config := { zeta := true }) [w₁_pos, w₁_pos', simBody]
        split_ifs <;> simp [World.setInput_tick, World.logOutput_tick, h_t₂_tick] at * <;> try omega
        rw [World.stepUntilNextTick_nextId, World.stepUntilNextTick_nextId,
            World.setInput_nextId, World.setInput_nextId,
            processNEvents_nextId, processNEvents_nextId]
      have h_perm : List.Perm w₁_pos.events w₁_pos'.events :=
        pos_indep_w1_perm c1 c2 t1 t2 pos pos' h1_middle h1_last h2_middle h2_last
        h_events h_t1_lt_t2 h_t₂_tick h_delay_w h_wt2_nodeId_lt
      obtain ⟨h_no_at_t2p1, h_no_at_t2p1'⟩ :=
        pos_indep_no_events_at_t2p1 c1 c2 t1 t2 pos pos' h1_middle h1_last h2_middle h2_last
        h_same h_t1_lt_t2 h_t₂_tick
      exact pos_indep_conv3_tail c1 c2 t1 t2 pos pos' h1_middle h1_last h2_middle h2_last
        h_events h_t1_lt_t2 h_t₂_tick h_delay_w h_wt2_nodeId_lt h_wt2_nodeId_ne_in1
        h_nodes_eq h_log_eq h_nextId_eq h_perm h_no_at_t2p1 h_no_at_t2p1'
    · -- No events at tick t₂: simBody is trivially pos-independent
      -- Key: processNEvents does nothing, stepUntilNextTick just advances tick
      -- setInput preserves "no events at tick" (new events have targetTick > tick)
      have h_no_log : ∀ ev ∈ (w_t₂.logOutput s!"tick {w_t₂.tick}").events,
          ev.targetTick ≠ (w_t₂.logOutput s!"tick {w_t₂.tick}").tick := by
        intro ev h_ev
        simp only [World.logOutput_events, World.logOutput_tick] at h_ev ⊢
        intro h_eq; rw [h_t₂_tick] at h_eq
        exact h_events ⟨ev, h_ev, h_eq⟩
      -- setInput preserves "no events at tick"
      have h_delay_w : ∀ nid nd, w_t₂.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
        intro nid nd h_nd d p h_kind
        -- w_t₂ is obtained from w₀ by simulation; simulation preserves kind
        -- So nd.kind = nd₀.kind where nd₀ is the node in w₀
        -- And w₀ is built by buildChain with ValidDelay delays
        dsimp [w_t₂] at h_nd
        obtain ⟨nd₀, h_nd₀, h_kind_eq⟩ := simFoldl_kind_preserved
          (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
          t1 t2 pos' in1 in2 t2 nid nd h_nd
        rw [h_kind_eq] at h_kind
        -- nd₀.kind = .repeater d p in the initial world
        -- The initial world is built by buildChain, so d comes from c1 or c2
        -- and ValidDelay gives d ≥ 2
        dsimp [buildChain, buildChainPre] at h_nd₀
        -- The node is either from c1's chain or c2's chain
        -- In both cases, the delay is from middleDelays or lastDelay, which are ValidDelay
        have h_all_delays : ∀ nid' nd', (buildChain (buildChain World.empty "A" c1).2 "B" c2).2.getNode nid' = some nd' →
            ∀ d' p', nd'.kind = .repeater d' p' → d' ≥ 2 := by
          -- First prove the property for the inner chain (c1)
          have h_c1 : ∀ nid nd, (buildChain World.empty "A" c1).2.getNode nid = some nd →
              ∀ d p, nd.kind = .repeater d p → d ≥ 2 :=
            buildChain_repeater_delay_ge2 World.empty "A" c1
              (fun d hd => ValidDelay.ge2 (h1_middle d hd))
              (ValidDelay.ge2 h1_last)
              (fun nid nd h => by simp [World.empty, World.getNode] at h)
              (fun p hp => by simp [World.empty] at hp)
          -- IDs invariant for (buildChain World.empty "A" c1).2
          have h_ids_c1 : ∀ p ∈ (buildChain World.empty "A" c1).2.nodes,
              p.1 < (buildChain World.empty "A" c1).2.nextId :=
            buildChain_ids_lt_nextId World.empty "A" c1
              (fun p hp => by simp [World.empty] at hp)
          -- Now apply for c2
          exact buildChain_repeater_delay_ge2 (buildChain World.empty "A" c1).2 "B" c2
            (fun d hd => ValidDelay.ge2 (h2_middle d hd))
            (ValidDelay.ge2 h2_last)
            h_c1 h_ids_c1
        exact h_all_delays nid nd₀ h_nd₀ d p h_kind
      have h_no_after_set (w : World) (id level : Nat)
          (h_no : ∀ ev ∈ w.events, ev.targetTick ≠ w.tick)
          (h_delay : ∀ nid nd, w.getNode nid = some nd → ∀ d p, nd.kind = .repeater d p → d ≥ 2) :
          ∀ ev ∈ (w.setInput id level).events, ev.targetTick ≠ (w.setInput id level).tick := by
        intro ev h_ev
        rw [World.setInput_tick]
        intro h_eq
        by_cases h_old : ev ∈ w.events
        · exact h_no ev h_old h_eq
        · have := setInput_events_future w id level h_delay ev h_ev h_old
          omega
      -- processNEvents does nothing when no events at tick
      have h_proc_log : ∀ n, processNEvents (w_t₂.logOutput s!"tick {w_t₂.tick}") n =
          w_t₂.logOutput s!"tick {w_t₂.tick}" :=
        fun n => processNEvents_eq_of_no_events _ n h_no_log
      -- logOutput preserves nodes, so the delay property transfers
      have h_delay_log : ∀ nid nd, (w_t₂.logOutput s!"tick {w_t₂.tick}").getNode nid = some nd →
          ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
        intro nid nd h d p h_kind
        apply h_delay_w nid nd _ d p h_kind
        dsimp [World.logOutput, World.getNode] at h ⊢
        exact h
      have h_no_log_set1 := h_no_after_set (w_t₂.logOutput _) in1 15 h_no_log h_delay_log
      have h_proc_log_set1 : ∀ n, processNEvents ((w_t₂.logOutput s!"tick {w_t₂.tick}").setInput in1 15) n =
          (w_t₂.logOutput s!"tick {w_t₂.tick}").setInput in1 15 :=
        fun n => processNEvents_eq_of_no_events _ n h_no_log_set1
      -- stepUntilNextTick just advances tick when no events
      have h_no_log_set2 := h_no_after_set (w_t₂.logOutput _) in2 15 h_no_log h_delay_log
      -- setInput preserves kinds, so the delay property transfers
      have h_delay_set1 : ∀ nid nd, ((w_t₂.logOutput s!"tick {w_t₂.tick}").setInput in1 15).getNode nid = some nd →
          ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
        intro nid nd h_get d p h_kind
        obtain ⟨nd₀, h_nd₀, h_kind_eq⟩ := World.setInput_kind_preserved (w_t₂.logOutput _) in1 15 nid nd h_get
        rw [h_kind_eq] at h_kind
        exact h_delay_log nid nd₀ h_nd₀ d p h_kind
      have h_no_log_set1_set2 := h_no_after_set ((w_t₂.logOutput _).setInput in1 15) in2 15 h_no_log_set1 h_delay_set1
      -- Now prove w₁_pos = w₁_pos'
      have h_eq₀ : w₁_pos = w₁_pos' := by
        dsimp [w₁_pos, w₁_pos', simBody]
        split_ifs
        · -- tick == t1, tick == t2: processNEvents with setInput in1
          rw [h_proc_log_set1 pos, h_proc_log_set1 pos']
        · -- tick == t1, tick ≠ t2: both sides identical
          rfl
        · -- tick ≠ t1, tick == t2: processNEvents without setInput in1
          rw [h_proc_log pos, h_proc_log pos']
        · -- tick ≠ t1, tick ≠ t2: both sides identical
          rfl
      rw [h_eq₀]
  rw [h_conv_3]
  -- Remaining: tick = t₂+3 > t₂, so foldl_simBody_pos_indep_from applies
  apply foldl_simBody_pos_indep_from
  rw [simFoldl_tick w_t₂ t1 t2 pos' in1 in2 3, h_t₂_tick]
  omega
