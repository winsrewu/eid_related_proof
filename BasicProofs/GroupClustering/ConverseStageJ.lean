import BasicProofs.GroupClustering.ConverseStage0

set_option linter.unusedVariables false

open BasicRedstoneSim List

/-! # Group clustering — the stage-j converse spawn-origin fact

At the pop tick of a middle stage `j ≥ 1`, the two reference stage-`j`
events `A_j` and `D_j` (both priority `-3`) spawn the stage-`j + 1`
events `sA` and `sD`. This file proves the middle-stage generalization
of the stage-`0` converse spawn-origin fact of ConverseStage0: any event between
`sA` and `sD` in the spawn accumulator is the stage-`k + 1` event of
some chain at some middle stage `k` (with `1 ≤ k ≤ middleDelays.length`),
and that chain's stage-`k` event sits between `A_j` and `D_j` in the due
filter.

The priority squeeze between the two priority-`-3` reference pops forces
the parent to priority `-3`, and `stagePri = -3` holds only at middle
stages, so the parent is a middle-stage event. Which middle stage `k` it
is (in particular, whether `k = j`) is not decided here: that case split
belongs to the caller. -/

/-- `evBefore l x x` splits the list around two copies of `x`. -/
private theorem evBefore_self_two_split {l : List ScheduledEvent}
    {x : ScheduledEvent} (h : evBefore l x x) :
    ∃ l₁ l₂ l₃, l = l₁ ++ x :: (l₂ ++ x :: l₃) := by
  obtain ⟨p, q, h_eq, h_x⟩ := h
  obtain ⟨p₂, q₂, h_q⟩ := mem_split_append q x h_x
  refine ⟨p, p₂, q₂, ?_⟩
  rw [h_eq, h_q]

/-- Append cancellation on the left. -/
private theorem append_left_cancel' {α : Type} (l l₁ l₂ : List α)
    (h : l ++ l₁ = l ++ l₂) : l₁ = l₂ := by
  induction l generalizing l₁ l₂ with
  | nil => simpa using h
  | cons a l ih =>
    simp only [List.cons_append] at h
    exact ih l₁ l₂ (by simpa using congrArg List.tail h)

/-- At the pop tick of a middle stage `j ≥ 1`, two reference stage-`j`
    events `A_j` and `D_j` spawn `sA` and `sD`. An event between `sA`
    and `sD` in the spawn accumulator is the stage-`k + 1` event of some
    chain at some middle stage `k`, and that chain's stage-`k` event sits
    between `A_j` and `D_j` in the due filter. -/
theorem converse_spawn_popSpawnAcc_stagej (groups : List GroupSpec)
    (actTick : Nat → Nat) (w : World) (g₁ c₁ g₂ c₂ j n : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_j : 1 ≤ j)
    (h_j₁ : j + 1 ≤ (chainAt groups g₁ c₁).middleDelays.length)
    (h_j₂ : j + 1 ≤ (chainAt groups g₂ c₂).middleDelays.length)
    (h_layout : NodeLayoutOk groups w)
    (h_due : w.tick = stageTarget actTick groups g₁ c₁ j)
    (h_tgt₂ : stageTarget actTick groups g₂ c₂ j =
        stageTarget actTick groups g₁ c₁ j)
    (h_nodup : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup)
    (h_stage : StageMemAt groups actTick w w.tick)
    (h_sA_absent : stageEvent actTick groups g₁ c₁ (j + 1) ∉ w.events)
    (h_sD_absent : stageEvent actTick groups g₂ c₂ (j + 1) ∉ w.events)
    (e : ScheduledEvent)
    (h_e_absent : e ∉ w.events)
    (h_b_left : evBefore (World.popSpawnAcc w n)
        (stageEvent actTick groups g₁ c₁ (j + 1)) e)
    (h_b_right : evBefore (World.popSpawnAcc w n) e
        (stageEvent actTick groups g₂ c₂ (j + 1))) :
    ∃ g c k, g < groups.length ∧ c < (groupAt groups g).length ∧
      1 ≤ k ∧ k ≤ (chainAt groups g c).middleDelays.length ∧
      e = stageEvent actTick groups g c (k + 1) ∧
      evBefore (w.events.filter (fun ev => ev.targetTick == w.tick))
        (stageEvent actTick groups g₁ c₁ j)
        (stageEvent actTick groups g c k) ∧
      evBefore (w.events.filter (fun ev => ev.targetTick == w.tick))
        (stageEvent actTick groups g c k)
        (stageEvent actTick groups g₂ c₂ j) := by
  set A := stageEvent actTick groups g₁ c₁ j
  set D := stageEvent actTick groups g₂ c₂ j
  set sA := stageEvent actTick groups g₁ c₁ (j + 1)
  set sD := stageEvent actTick groups g₂ c₂ (j + 1)
  set due := w.events.filter (fun ev => ev.targetTick == w.tick)
  -- basic facts about the two reference stage-j events
  have hA_due : A.targetTick = w.tick := by
    dsimp [A, stageEvent]
    exact h_due.symm
  have hD_due : D.targetTick = w.tick := by
    dsimp [D, stageEvent]
    rw [h_tgt₂, h_due]
  have hA_pri : A.priority = (-3 : Int) := by
    dsimp [A, stageEvent]
    exact stagePri_middle groups g₁ c₁ j h_j (by omega)
  have hD_pri : D.priority = (-3 : Int) := by
    dsimp [D, stageEvent]
    exact stagePri_middle groups g₂ c₂ j h_j (by omega)
  have h_sA_gt : sA.targetTick > w.tick := by
    dsimp [sA, stageEvent]
    rw [h_due]
    exact stageTarget_lt_succ actTick groups g₁ c₁ j (by omega)
  have h_sD_gt : sD.targetTick > w.tick := by
    dsimp [sD, stageEvent]
    rw [h_due, ← h_tgt₂]
    exact stageTarget_lt_succ actTick groups g₂ c₂ j (by omega)
  have h_spawnA : ∀ (v : World), v.tick = w.tick → NodeLayoutOk groups v →
      (v.onScheduledTick A.nodeId).events = v.events ++ [sA] := by
    intro v h_v h_lay
    simpa [A, sA, stageEvent] using
      stage_spawn groups actTick v g₁ c₁ j h_g₁ h_c₁ (by omega)
        (h_v.trans h_due) h_lay
  have h_spawnD : ∀ (v : World), v.tick = w.tick → NodeLayoutOk groups v →
      (v.onScheduledTick D.nodeId).events = v.events ++ [sD] := by
    intro v h_v h_lay
    simpa [D, sD, stageEvent] using
      stage_spawn groups actTick v g₂ c₂ j h_g₂ h_c₂ (by omega)
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
      obtain ⟨h_g_eq, h_c_eq, h_k_eq⟩ :=
        stageEvent_injective actTick groups gi₀ ci₀ (k₀ + 1) g₁ c₁ (j + 1)
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
      obtain ⟨h_g_eq, h_c_eq, h_k_eq⟩ :=
        stageEvent_injective actTick groups gi₀ ci₀ (k₀ + 1) g₂ c₂ (j + 1)
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
      hD_due h_sD_absent h_sD_gt h_spawnD h_single h_uniqueD h_e_absent
      h_e_ne_sD h_b_right
  -- decode the right parent as a stage event
  have h_eR_w : eR ∈ w.events :=
    World.mem_popSeqFuel_mem_events w n eR h_eR_pop
  obtain ⟨gi, ci, k, h_gi, h_ci, h_k_le, h_eR_eq, _, _⟩ :=
    h_stage eR h_eR_w
  have h_eR_due : eR.targetTick = w.tick :=
    World.mem_popSeqFuel_due w n eR h_eR_pop
  -- identify the left and right parents
  have h_eL_w : eL ∈ w.events :=
    World.mem_popSeqFuel_mem_events w n eL h_eL_pop
  obtain ⟨gi', ci', k', h_gi', h_ci', h_k_le', h_eL_eq, _, _⟩ :=
    h_stage eL h_eL_w
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
      obtain ⟨h_g_eq, h_c_eq, h_k_eq⟩ :=
        stageEvent_injective actTick groups gi' ci' (k' + 1) gi ci (k + 1)
          h_gi' h_ci' h_gi h_ci (by omega) (by omega)
          (h_e_eq_L.symm.trans h_e_eq)
      rw [h_eL_eq, h_eR_eq, h_g_eq, h_c_eq]
      congr 1
      omega
  have h_AeR : evBefore (World.popSeqFuel w n) A eR := by
    rwa [← h_parent_eq]
  -- the parent sits between two priority-(-3) pops, so it has priority -3
  have h_pri_eR : eR.priority = (-3 : Int) := by
    have h_le₁ : A.priority ≤ eR.priority :=
      popSeqFuel_priority_mono w n A eR h_AeR
    have h_le₂ : eR.priority ≤ D.priority :=
      popSeqFuel_priority_mono w n eR D h_eRD
    rw [hA_pri] at h_le₁
    rw [hD_pri] at h_le₂
    omega
  -- priority -3 occurs only at middle stages, so the parent's stage k
  -- satisfies 1 ≤ k
  have h_k_ge : 1 ≤ k := by
    have h_p : stagePri groups gi ci k = (-3 : Int) := by
      have h := congr_arg ScheduledEvent.priority h_eR_eq.symm
      dsimp [stageEvent] at h
      rw [h_pri_eR] at h
      exact h
    dsimp only [stagePri] at h_p
    split_ifs at h_p
    all_goals omega
  -- transfer the pop order to the due-filter order
  have h_due_AeR : evBefore due A eR :=
    due_evBefore_of_popSeq_evBefore w n A eR hA_pop h_eR_pop hA_due
      h_eR_due (by rw [hA_pri, h_pri_eR]) h_nodup h_AeR
  have h_due_eRD : evBefore due eR D :=
    due_evBefore_of_popSeq_evBefore w n eR D h_eR_pop hD_pop h_eR_due
      hD_due (by rw [h_pri_eR, hD_pri]) h_nodup h_eRD
  refine ⟨gi, ci, k, h_gi, h_ci, h_k_ge, h_k_mid, h_e_eq, ?_, ?_⟩
  · -- the stage-k event of (gi, ci) sits after A in the due filter
    rwa [← h_eR_eq]
  · -- the stage-k event of (gi, ci) sits before D in the due filter
    rwa [← h_eR_eq]

/-! ## The stepUNT wrapper -/

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

/-- `filter` keeps a list unchanged when the predicate holds
    everywhere. -/
private theorem filter_eq_self_of_forall' {α : Type} (p : α → Bool)
    (l : List α) (h : ∀ x ∈ l, p x = true) : l.filter p = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have h_x := h x (List.mem_cons.mpr (Or.inl rfl))
    simp [List.filter, h_x, ih (fun y hy => h y (List.mem_cons.mpr (Or.inr hy)))]

/-- At the pop tick of a middle stage `j ≥ 1`, two reference stage-`j`
    events spawn `sA` and `sD` during the drain step. An event between
    `sA` and `sD` in the post-drain queue `w.stepUntilNextTick.events`
    is the stage-`k + 1` event of some chain at some middle stage `k`,
    and that chain's stage-`k` event sits between the two reference
    events in the due filter. Wraps `converse_spawn_popSpawnAcc_stagej`
    by splitting the post-drain queue into survivors and the spawn
    accumulator. -/
theorem converse_spawn_stepUNT_stagej (groups : List GroupSpec)
    (actTick : Nat → Nat) (w : World) (g₁ c₁ g₂ c₂ j : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_j : 1 ≤ j)
    (h_j₁ : j + 1 ≤ (chainAt groups g₁ c₁).middleDelays.length)
    (h_j₂ : j + 1 ≤ (chainAt groups g₂ c₂).middleDelays.length)
    (h_layout : NodeLayoutOk groups w)
    (h_due : w.tick = stageTarget actTick groups g₁ c₁ j)
    (h_tgt₂ : stageTarget actTick groups g₂ c₂ j =
        stageTarget actTick groups g₁ c₁ j)
    (h_nodup : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup)
    (h_stage : StageMemAt groups actTick w w.tick)
    (h_sA_absent : stageEvent actTick groups g₁ c₁ (j + 1) ∉ w.events)
    (h_sD_absent : stageEvent actTick groups g₂ c₂ (j + 1) ∉ w.events)
    (e : ScheduledEvent)
    (h_e_absent : e ∉ w.events)
    (h_b1 : evBefore w.stepUntilNextTick.events
        (stageEvent actTick groups g₁ c₁ (j + 1)) e)
    (h_b2 : evBefore w.stepUntilNextTick.events e
        (stageEvent actTick groups g₂ c₂ (j + 1))) :
    ∃ g c k, g < groups.length ∧ c < (groupAt groups g).length ∧
      1 ≤ k ∧ k ≤ (chainAt groups g c).middleDelays.length ∧
      e = stageEvent actTick groups g c (k + 1) ∧
      evBefore (w.events.filter (fun ev => ev.targetTick == w.tick))
        (stageEvent actTick groups g₁ c₁ j)
        (stageEvent actTick groups g c k) ∧
      evBefore (w.events.filter (fun ev => ev.targetTick == w.tick))
        (stageEvent actTick groups g c k)
        (stageEvent actTick groups g₂ c₂ j) := by
  set sA := stageEvent actTick groups g₁ c₁ (j + 1)
  set sD := stageEvent actTick groups g₂ c₂ (j + 1)
  set due := w.events.filter (fun ev => ev.targetTick == w.tick)
  -- drain the tick and split the next queue into survivors and spawns
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
  exact converse_spawn_popSpawnAcc_stagej groups actTick w g₁ c₁ g₂ c₂ j n
    h_g₁ h_c₁ h_g₂ h_c₂ h_j h_j₁ h_j₂ h_layout h_due h_tgt₂ h_nodup
    h_stage h_sA_absent h_sD_absent e h_e_absent h_b_left h_b_right
