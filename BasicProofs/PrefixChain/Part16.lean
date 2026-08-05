import BasicProofs.PrefixChain.Part15


open BasicRedstoneSim

/-- After one simBody step at tick t₂, the event lists for insertion
    positions `pos` and `pos'` are permutations of each other. -/
theorem pos_indep_w1_perm (c1 c2 : ChainSpec) (t1 t2 pos pos' : Nat)
    (_ : ∀ d ∈ c1.middleDelays, ValidDelay d)
    (_ : ValidDelay c1.lastDelay)
    (_ : ∀ d ∈ c2.middleDelays, ValidDelay d)
    (_ : ValidDelay c2.lastDelay) :
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
    List.Perm w₁_pos.events w₁_pos'.events := by
        intro in1 in2 w_t₂ w₁_pos w₁_pos' h_events h_t1_lt_t2 h_t₂_tick h_delay_w h_wt2_nodeId_lt
        -- w_t₂.events is a singleton [ev_s] at tick t2
        obtain ⟨ev_s, h_ev_s_mem, h_ev_s_tick⟩ := h_events
        have h_wt2_len : w_t₂.events.length ≤ 1 := by
          dsimp [w_t₂, in1, in2]
          exact (simFoldl_events_length_le_one c1 c2 t1 t2 pos' h_t1_lt_t2).1
        have h_wt2_singleton : w_t₂.events = [ev_s] := by
          have h_len : w_t₂.events.length = 1 := by
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
        set w_log := w_t₂.logOutput s!"tick {t2}"
        set C := (w_log.setInput in2 15).stepUntilNextTick
        -- Show each simBody at tick t2 yields events permutable with C.events
        suffices h_all : ∀ p, List.Perm (simBody t1 t2 p in1 in2 w_t₂ 0).events C.events from by
          exact (h_all pos).trans (h_all pos').symm
        intro p
        -- Expand simBody at tick t2 (≠ t1)
        have h_body : simBody t1 t2 p in1 in2 w_t₂ 0 =
            ((processNEvents w_log p).setInput in2 15).stepUntilNextTick := by
          dsimp (config := { zeta := true }) [simBody, w_log]
          split_ifs <;>
            (try { exfalso; simp [World.logOutput_tick, h_t₂_tick] at * <;> omega }) ;
            (try { congr 1; congr 1; simp [h_t₂_tick] })
        rw [h_body]
        by_cases hp0 : p = 0
        · -- p = 0: processNEvents is identity
          subst hp0
          dsimp [C]
          simp [processNEvents]
        · -- p ≥ 1: processNEvents processes ev_s
          -- Facts about w_log
          have h_wlog_events : w_log.events = [ev_s] := by
            dsimp [w_log]; exact h_wt2_singleton
          have h_wlog_tick : w_log.tick = t2 := by
            dsimp [w_log]; exact h_t₂_tick
          -- ev_s targets a chain-A node, so its nodeId is below in2
          have h_evs_lt : ev_s.nodeId < in2 := h_wt2_nodeId_lt ev_s h_ev_s_mem
          have h_evs_ne_in2 : ev_s.nodeId ≠ in2 := by omega
          have h_evs_ne_obs : ev_s.nodeId ≠ in2 + 1 := by omega
          -- Observer structure of in2 in w_t₂
          obtain ⟨h_in2_st, h_obs_st⟩ := w_t2_in2_observer_struct c1 c2 t1 t2 pos' h_t1_lt_t2
          obtain ⟨nd_in2, h_gn_in2, h_out_in2⟩ := h_in2_st
          obtain ⟨nd_obs, h_gn_obs, h_kind_obs⟩ := h_obs_st
          -- The observer event added by setInput in2
          set o : ScheduledEvent := { targetTick := t2 + 2, priority := 0, nodeId := in2 + 1 }
          -- setInput in2 on w_log appends [o]
          have h_setlog : (w_log.setInput in2 15).events = w_log.events ++ [o] := by
            have := setInput_append_observer w_log in2 (in2 + 1)
              (by refine ⟨nd_in2, ?_, h_out_in2⟩; dsimp [w_log]; rw [World.logOutput_getNode]; exact h_gn_in2)
              (by refine ⟨nd_obs, ?_, h_kind_obs⟩; dsimp [w_log]; rw [World.logOutput_getNode]; exact h_gn_obs)
              (by omega)
            rw [h_wlog_tick] at this
            dsimp [o]
            exact this
          -- W_proc: world after processing ev_s once
          set W_proc := ({ w_log with events := [] }).onScheduledTick ev_s.nodeId
          have h_step_log : w_log.step = some W_proc := by
            dsimp [World.step, W_proc]
            rw [popNextEvent_singleton w_log ev_s h_wlog_events
              (by rw [h_wlog_tick]; exact h_ev_s_tick)]
          have h_Wproc_tick : W_proc.tick = t2 := by
            dsimp [W_proc]; rw [World.onScheduledTick_tick]; dsimp; rw [h_wlog_tick]
          -- delay condition transfers to {w_log with events := []}
          have h_delay_empty : ∀ nid nd, ({ w_log with events := [] } : World).getNode nid = some nd →
              ∀ d p, nd.kind = .repeater d p → d ≥ 2 := by
            intro nid nd h_nd d p h_kind
            change w_log.getNode nid = some nd at h_nd
            dsimp [w_log] at h_nd
            rw [World.logOutput_getNode] at h_nd
            exact h_delay_w nid nd h_nd d p h_kind
          have h_tick_base : ({ w_log with events := [] } : World).tick = t2 := by
            change w_log.tick = t2
            exact h_wlog_tick
          -- processNEvents w_log p = W_proc for p ≥ 1
          have h_proc : processNEvents w_log p = W_proc := by
            have h_no : ∀ ev ∈ W_proc.events, ev.targetTick ≠ W_proc.tick := by
              dsimp [W_proc]
              obtain ⟨new_ev, h_app, h_fut⟩ :=
                World.onScheduledTick_events_append ({ w_log with events := [] } : World) ev_s.nodeId h_delay_empty
              rw [h_tick_base] at h_fut
              intro ev h_ev
              have h_ev_new : ev ∈ new_ev := by
                have h_base : ({ w_log with events := [] } : World).events = [] := rfl
                have : W_proc.events = [] ++ new_ev := by
                  change (({ w_log with events := [] } : World).onScheduledTick ev_s.nodeId).events = _
                  rw [h_app, h_base]
                rwa [this, List.nil_append] at h_ev
              have h_gt := h_fut ev h_ev_new
              rw [h_Wproc_tick]
              intro h_eq; omega
            cases p with
            | zero => exfalso; apply hp0; rfl
            | succ n =>
              dsimp [processNEvents]
              rw [h_step_log]
              exact processNEvents_eq_of_no_events W_proc n h_no
          rw [h_proc]
          -- setInput in2 on W_proc appends [o]
          have h_Wproc_in2 : W_proc.getNode in2 = w_log.getNode in2 := by
            dsimp [W_proc]
            rw [World.onScheduledTick_getNode_ne _ ev_s.nodeId in2 (Ne.symm h_evs_ne_in2)]
            rfl
          have h_Wproc_obs : W_proc.getNode (in2 + 1) = w_log.getNode (in2 + 1) := by
            dsimp [W_proc]
            rw [World.onScheduledTick_getNode_ne _ ev_s.nodeId (in2 + 1) (Ne.symm h_evs_ne_obs)]
            rfl
          have h_setW : (W_proc.setInput in2 15).events = W_proc.events ++ [o] := by
            have := setInput_append_observer W_proc in2 (in2 + 1)
              (by refine ⟨nd_in2, ?_, h_out_in2⟩; rw [h_Wproc_in2]; dsimp [w_log]; rw [World.logOutput_getNode]; exact h_gn_in2)
              (by refine ⟨nd_obs, ?_, h_kind_obs⟩; rw [h_Wproc_obs]; dsimp [w_log]; rw [World.logOutput_getNode]; exact h_gn_obs)
              (by omega)
            rw [h_Wproc_tick] at this
            dsimp [o]
            exact this
          -- (W_proc.setInput in2 15) has no events at tick t2
          set BW := W_proc.setInput in2 15
          have h_BW_tick : BW.tick = t2 := by dsimp [BW]; rw [World.setInput_tick, h_Wproc_tick]
          have h_BW_no : ∀ ev ∈ BW.events, ev.targetTick ≠ BW.tick := by
            intro ev h_ev
            rw [h_BW_tick]
            dsimp [BW] at h_ev
            rw [h_setW] at h_ev
            have h_fut : ∀ ev ∈ W_proc.events, ev.targetTick > t2 := by
              dsimp [W_proc]
              obtain ⟨new_ev, h_app, h_fut⟩ :=
                World.onScheduledTick_events_append ({ w_log with events := [] } : World) ev_s.nodeId h_delay_empty
              rw [h_tick_base] at h_fut
              intro ev' h_ev'
              have h_ev_new : ev' ∈ new_ev := by
                have h_base : ({ w_log with events := [] } : World).events = [] := rfl
                have : W_proc.events = [] ++ new_ev := by
                  change (({ w_log with events := [] } : World).onScheduledTick ev_s.nodeId).events = _
                  rw [h_app, h_base]
                rwa [this, List.nil_append] at h_ev'
              exact h_fut ev' h_ev_new
            simp [List.mem_append] at h_ev
            rcases h_ev with h_ev | h_ev
            · have := h_fut ev h_ev; omega
            · subst h_ev; dsimp [o]; omega
          -- w₁_pos.events = W_proc.events ++ [o]
          have h_lhs : ((W_proc.setInput in2 15).stepUntilNextTick).events = W_proc.events ++ [o] := by
            change (BW.stepUntilNextTick).events = W_proc.events ++ [o]
            rw [stepUntilNextTick_events_eq_of_no_events BW h_BW_no]
            exact h_setW
          rw [h_lhs]
          -- Now compute C.events = [o] ++ W_proc.events
          set B0 := w_log.setInput in2 15
          have h_B0_events : B0.events = [ev_s] ++ [o] := by
            dsimp [B0]; rw [h_setlog, h_wlog_events]; simp
          have h_B0_tick : B0.tick = t2 := by dsimp [B0]; rw [World.setInput_tick, h_wlog_tick]
          -- popNextEvent B0 pops ev_s (the unique event at tick t2), leaving [o]
          have h_pop_B0 : B0.popNextEvent = some (ev_s, { B0 with events := [o] }) := by
            unfold World.popNextEvent
            rw [h_B0_events, h_B0_tick]
            dsimp (config := { zeta := true })
            have h_zip : (List.range 2).zip [ev_s, o] = [(0, ev_s), (1, o)] := by
              have h_range : List.range 2 = [0, 1] := by decide
              rw [h_range]
              simp
            have h_filter : ([(0, ev_s), (1, o)]).filter (fun x => x.2.targetTick == t2) =
                [(0, ev_s)] := by
              simp [o, h_ev_s_tick]
            rw [h_zip, h_filter]
            simp [o]
          set B0_pop := { B0 with events := [o] }
          set C_proc := B0_pop.onScheduledTick ev_s.nodeId
          -- C_proc.events = [o] ++ new_ev and W_proc.events = [] ++ new_ev
          have h_congr : ∃ new, W_proc.events = ({ w_log with events := [] } : World).events ++ new ∧
              C_proc.events = B0_pop.events ++ new := by
            dsimp [W_proc, C_proc]
            apply onScheduledTick_events_congr ({ w_log with events := [] }) B0_pop ev_s.nodeId
            · -- same tick
              dsimp [B0_pop, B0]
              simp [World.setInput_tick, h_wlog_tick]
            · -- same getNode ev_s.nodeId
              change w_log.getNode ev_s.nodeId = (w_log.setInput in2 15).getNode ev_s.nodeId
              exact (setInput_getNode_ne' w_log in2 ev_s.nodeId h_evs_ne_in2).symm
            · -- same kinds everywhere
              intro nid
              change (w_log.getNode nid).map (·.kind) = ((w_log.setInput in2 15).getNode nid).map (·.kind)
              exact (setInput_map_kind w_log in2 15 nid).symm
          obtain ⟨new_ev, h_Wproc_app, h_Cproc_app⟩ := h_congr
          have h_base_empty : ({ w_log with events := [] } : World).events = [] := rfl
          have h_Wproc_eq : W_proc.events = new_ev := by
            rw [h_Wproc_app, h_base_empty, List.nil_append]
          have h_B0pop_events : B0_pop.events = [o] := rfl
          have h_Cproc_eq : C_proc.events = [o] ++ new_ev := by
            rw [h_Cproc_app, h_B0pop_events]
          -- B0.step = some C_proc, so C = C_proc.stepUntilNextTick
          have h_B0_step : B0.step = some C_proc := by
            dsimp [World.step, C_proc, B0_pop]
            rw [h_pop_B0]
          have h_Cproc_tick : C_proc.tick = t2 := by
            dsimp [C_proc]
            rw [World.onScheduledTick_tick]
            dsimp [B0_pop, B0]
            rw [World.setInput_tick, h_wlog_tick]
          -- C_proc has no events at tick t2, so stepping only advances the tick
          have h_Cproc_no : ∀ ev ∈ C_proc.events, ev.targetTick ≠ C_proc.tick := by
            intro ev h_ev
            rw [h_Cproc_eq] at h_ev
            rw [h_Cproc_tick]
            simp [] at h_ev
            rcases h_ev with h_ev | h_ev
            · subst h_ev; dsimp [o]; omega
            · have h_ev_W : ev ∈ W_proc.events := by rwa [h_Wproc_eq]
              have h_mem_BW : ev ∈ BW.events := by
                dsimp [BW]
                rw [h_setW]
                exact List.mem_append.mpr (Or.inl h_ev_W)
              have := h_BW_no ev h_mem_BW
              rwa [h_BW_tick] at this
          -- C.events = C_proc.events = [o] ++ W_proc.events
          have h_C_events : C.events = C_proc.events := by
            have h_sunt : B0.stepUntilNextTick = C_proc.stepUntilNextTick := by
              rw [World.stepUntilNextTick, h_B0_step]
            dsimp [C]
            change (B0.stepUntilNextTick).events = C_proc.events
            rw [h_sunt]
            exact stepUntilNextTick_events_eq_of_no_events C_proc h_Cproc_no
          rw [h_C_events, h_Cproc_eq]
          rw [show new_ev = W_proc.events from h_Wproc_eq.symm]
          -- Goal: List.Perm (W_proc.events ++ [o]) ([o] ++ W_proc.events)
          exact List.perm_append_comm


/-- After one simBody step at tick t₂, no event targets tick `t₂ + 1`
    (parity argument). -/
theorem pos_indep_no_events_at_t2p1 (c1 c2 : ChainSpec) (t1 t2 pos pos' : Nat)
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
    (h_same : t1 + c1.totalDelay = t2 + c2.totalDelay) →
    (h_t1_lt_t2 : t1 < t2) →
    (h_t₂_tick : w_t₂.tick = t2) →
    (∀ ev ∈ w₁_pos.events, ev.targetTick ≠ t2 + 1) ∧
    (∀ ev ∈ w₁_pos'.events, ev.targetTick ≠ t2 + 1) := by
      intro in1 in2 w_t₂ w₁_pos w₁_pos' h_same h_t1_lt_t2 h_t₂_tick
      -- Parity helpers (shared between h_no_at_t2p1 and h_no_at_t2p1')
      have h_t1_t2_parity : t1 % 2 = t2 % 2 := by
        have h_c1_even : ChainSpec.totalDelay c1 % 2 = 0 := ChainSpec.totalDelay_even c1 h1_middle h1_last
        have h_c2_even : ChainSpec.totalDelay c2 % 2 = 0 := ChainSpec.totalDelay_even c2 h2_middle h2_last
        have := congrArg (· % 2) h_same
        rw [Nat.add_mod] at this
        rw [h_c1_even] at this
        conv at this => rhs; rw [Nat.add_mod]; rw [h_c2_even]
        simp at this; omega
      have h_even_w0 : ∀ nid nd, (buildChain (buildChain World.empty "A" c1).2 "B" c2).2.getNode nid = some nd →
          ∀ d pr, nd.kind = .repeater d pr → (d : Nat) % 2 = 0 := by
        have h_c1 : ∀ nid nd, (buildChain World.empty "A" c1).2.getNode nid = some nd →
            ∀ d p, nd.kind = .repeater d p → (d : Nat) % 2 = 0 :=
          buildChain_repeater_delay_even World.empty "A" c1
            (fun d hd => ValidDelay.even (h1_middle d hd)) (ValidDelay.even h1_last)
            (fun nid nd h => by simp [World.empty, World.getNode] at h)
            (fun p hp => by simp [World.empty] at hp)
        have h_ids : ∀ p ∈ (buildChain World.empty "A" c1).2.nodes,
            p.1 < (buildChain World.empty "A" c1).2.nextId :=
          buildChain_ids_lt_nextId World.empty "A" c1 (fun p hp => by simp [World.empty] at hp)
        exact buildChain_repeater_delay_even (buildChain World.empty "A" c1).2 "B" c2
          (fun d hd => ValidDelay.even (h2_middle d hd)) (ValidDelay.even h2_last) h_c1 h_ids
      have h_wt2_parity : ∀ ev ∈ w_t₂.events, ev.targetTick % 2 = t1 % 2 := by
        dsimp [w_t₂]
        apply simFoldl_parity _ t1 t2 pos' in1 in2 t2 (t1 % 2)
        · intro ev h_ev; have := w0_events_empty c1 c2; rw [this] at h_ev; cases h_ev
        · exact h_even_w0
        · intro k hk
          have h_tick := simFoldl_tick (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
            t1 t2 pos' in1 in2 k
          rw [w0_tick] at h_tick
          intro h_eq; omega
        · rfl
      have h_no_at_t2p1 : ∀ ev ∈ w₁_pos.events, ev.targetTick ≠ t2 + 1 := by
        -- Step 3: Events in w₁_pos have targetTick % 2 = t₂ % 2
        -- w₁_pos = simBody t1 t2 pos in1 in2 w_t₂ 0
        -- At tick t₂ (≠ t₁): logOutput + processNEvents pos + setInput in2 15 + stepUntilNextTick
        have h_w1_eq : w₁_pos =
            ((processNEvents (w_t₂.logOutput s!"tick {t2}") pos).setInput in2 15).stepUntilNextTick := by
          dsimp (config := { zeta := true }) [w₁_pos, simBody]
          split_ifs <;>
            (try { exfalso; simp [World.logOutput_tick, h_t₂_tick] at * <;> omega }) ;
            (try { congr 1; congr 1; simp [h_t₂_tick] })
        intro ev h_ev
        rw [h_w1_eq] at h_ev
        have h_parity_final : ev.targetTick % 2 = t2 % 2 := by
          apply stepUntilNextTick_parity _ (t2 % 2) _ _ ev h_ev
          · -- Events after setInput in2 15 have parity t₂ % 2
            intro ev' h_ev'
            by_cases h_old : ev' ∈ (processNEvents (w_t₂.logOutput s!"tick {t2}") pos).events
            · -- Old event from processNEvents
              have h_proc := processNEvents_parity (w_t₂.logOutput s!"tick {t2}") pos (t1 % 2)
                (fun ev'' h_ev'' => by
                  dsimp [World.logOutput] at h_ev''
                  exact h_wt2_parity ev'' h_ev'')
                (fun nid nd h_nd d pr h_kind => by
                  obtain ⟨nd₀, h₀, hk⟩ := World.logOutput_kind_preserved w_t₂ s!"tick {t2}" nid nd h_nd
                  rw [hk] at h_kind
                  dsimp [w_t₂] at h₀
                  obtain ⟨nd₁, h₁, hk₁⟩ := simFoldl_kind_preserved (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
                    t1 t2 pos' in1 in2 t2 nid nd₀ h₀
                  rw [hk₁] at h_kind
                  exact h_even_w0 nid nd₁ h₁ d pr h_kind)
                ev' h_old
              rwa [h_t1_t2_parity] at h_proc
            · -- New event from setInput in2 15
              have h_new := setInput_events_parity (processNEvents (w_t₂.logOutput s!"tick {t2}") pos) in2 15
                (fun nid nd h_nd d pr h_kind => by
                  obtain ⟨nd₀, h₀, hk⟩ := processNEvents_kind_preserved (w_t₂.logOutput s!"tick {t2}") pos nid nd h_nd
                  rw [hk] at h_kind
                  obtain ⟨nd₁, h₁, hk₁⟩ := World.logOutput_kind_preserved w_t₂ s!"tick {t2}" nid nd₀ h₀
                  rw [hk₁] at h_kind
                  dsimp [w_t₂] at h₁
                  obtain ⟨nd₂, h₂, hk₂⟩ := simFoldl_kind_preserved (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
                    t1 t2 pos' in1 in2 t2 nid nd₁ h₁
                  rw [hk₂] at h_kind
                  exact h_even_w0 nid nd₂ h₂ d pr h_kind)
                ev' h_ev' h_old
              have h_tick_proc : (processNEvents (w_t₂.logOutput s!"tick {t2}") pos).tick = t2 := by
                rw [processNEvents_tick, World.logOutput_tick, h_t₂_tick]
              have := h_new
              rw [h_tick_proc] at this
              exact this
          · -- Even delays after setInput in2 15
            intro nid nd h_nd d pr h_kind
            obtain ⟨nd₁, h₁, hk₁⟩ := World.setInput_kind_preserved (processNEvents (w_t₂.logOutput s!"tick {t2}") pos) in2 15 nid nd h_nd
            rw [hk₁] at h_kind
            obtain ⟨nd₂, h₂, hk₂⟩ := processNEvents_kind_preserved (w_t₂.logOutput s!"tick {t2}") pos nid nd₁ h₁
            rw [hk₂] at h_kind
            obtain ⟨nd₃, h₃, hk₃⟩ := World.logOutput_kind_preserved w_t₂ s!"tick {t2}" nid nd₂ h₂
            rw [hk₃] at h_kind
            dsimp [w_t₂] at h₃
            obtain ⟨nd₄, h₄, hk₄⟩ := simFoldl_kind_preserved (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
              t1 t2 pos' in1 in2 t2 nid nd₃ h₃
            rw [hk₄] at h_kind
            exact h_even_w0 nid nd₄ h₄ d pr h_kind
        intro h_eq
        have : (t2 + 1) % 2 = t2 % 2 := by rw [← h_eq]; exact h_parity_final
        omega
      have h_no_at_t2p1' : ∀ ev ∈ w₁_pos'.events, ev.targetTick ≠ t2 + 1 := by
        -- Same parity argument as h_no_at_t2p1 but with pos'
        have h_w1'_eq : w₁_pos' =
            ((processNEvents (w_t₂.logOutput s!"tick {t2}") pos').setInput in2 15).stepUntilNextTick := by
          dsimp (config := { zeta := true }) [w₁_pos', simBody]
          split_ifs <;>
            (try { exfalso; simp [World.logOutput_tick, h_t₂_tick] at * <;> omega }) ;
            (try { congr 1; congr 1; simp [h_t₂_tick] })
        intro ev h_ev
        rw [h_w1'_eq] at h_ev
        have h_parity_final : ev.targetTick % 2 = t2 % 2 := by
          apply stepUntilNextTick_parity _ (t2 % 2) _ _ ev h_ev
          · intro ev' h_ev'
            by_cases h_old : ev' ∈ (processNEvents (w_t₂.logOutput s!"tick {t2}") pos').events
            · have h_proc := processNEvents_parity (w_t₂.logOutput s!"tick {t2}") pos' (t1 % 2)
                (fun ev'' h_ev'' => by dsimp [World.logOutput] at h_ev''; exact h_wt2_parity ev'' h_ev'')
                (fun nid nd h_nd d pr h_kind => by
                  obtain ⟨nd₀, h₀, hk⟩ := World.logOutput_kind_preserved w_t₂ s!"tick {t2}" nid nd h_nd
                  rw [hk] at h_kind
                  dsimp [w_t₂] at h₀
                  obtain ⟨nd₁, h₁, hk₁⟩ := simFoldl_kind_preserved (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
                    t1 t2 pos' in1 in2 t2 nid nd₀ h₀
                  rw [hk₁] at h_kind
                  exact h_even_w0 nid nd₁ h₁ d pr h_kind)
                ev' h_old
              rwa [h_t1_t2_parity] at h_proc
            · have h_new := setInput_events_parity (processNEvents (w_t₂.logOutput s!"tick {t2}") pos') in2 15
                (fun nid nd h_nd d pr h_kind => by
                  obtain ⟨nd₀, h₀, hk⟩ := processNEvents_kind_preserved (w_t₂.logOutput s!"tick {t2}") pos' nid nd h_nd
                  rw [hk] at h_kind
                  obtain ⟨nd₁, h₁, hk₁⟩ := World.logOutput_kind_preserved w_t₂ s!"tick {t2}" nid nd₀ h₀
                  rw [hk₁] at h_kind
                  dsimp [w_t₂] at h₁
                  obtain ⟨nd₂, h₂, hk₂⟩ := simFoldl_kind_preserved (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
                    t1 t2 pos' in1 in2 t2 nid nd₁ h₁
                  rw [hk₂] at h_kind
                  exact h_even_w0 nid nd₂ h₂ d pr h_kind)
                ev' h_ev' h_old
              have h_tick_proc : (processNEvents (w_t₂.logOutput s!"tick {t2}") pos').tick = t2 := by
                rw [processNEvents_tick, World.logOutput_tick, h_t₂_tick]
              have := h_new; rw [h_tick_proc] at this; exact this
          · intro nid nd h_nd d pr h_kind
            obtain ⟨nd₁, h₁, hk₁⟩ := World.setInput_kind_preserved (processNEvents (w_t₂.logOutput s!"tick {t2}") pos') in2 15 nid nd h_nd
            rw [hk₁] at h_kind
            obtain ⟨nd₂, h₂, hk₂⟩ := processNEvents_kind_preserved (w_t₂.logOutput s!"tick {t2}") pos' nid nd₁ h₁
            rw [hk₂] at h_kind
            obtain ⟨nd₃, h₃, hk₃⟩ := World.logOutput_kind_preserved w_t₂ s!"tick {t2}" nid nd₂ h₂
            rw [hk₃] at h_kind
            dsimp [w_t₂] at h₃
            obtain ⟨nd₄, h₄, hk₄⟩ := simFoldl_kind_preserved (buildChain (buildChain World.empty "A" c1).2 "B" c2).2
              t1 t2 pos' in1 in2 t2 nid nd₃ h₃
            rw [hk₄] at h_kind
            exact h_even_w0 nid nd₄ h₄ d pr h_kind
        intro h_eq
        have : (t2 + 1) % 2 = t2 % 2 := by rw [← h_eq]; exact h_parity_final
        omega
      exact ⟨h_no_at_t2p1, h_no_at_t2p1'⟩

