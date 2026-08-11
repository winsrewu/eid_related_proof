import BasicProofs.GroupClustering.BurstCrossPrioritySpawnOrder
import BasicProofs.GroupClustering.SuccessorMembershipRange
import BasicProofs.GroupClustering.PreStepWorldFacts
import BasicProofs.GroupClustering.ForwardTransport
import BasicProofs.GroupClustering.NodupChain
import BasicProofs.GroupClustering.StageEventNodup
import BasicProofs.GroupClustering.ActivationListOrder

open BasicRedstoneSim List

/-! # Group clustering — the general stage-1 base case of `MiddleBlockOk`

The stage-`1` base case for arbitrary `pos`. An interloper `e` between
the two reference stage-`1` events `sA`, `sD` in the tick-`τ₁` queue,
with priority `-3` and target `τ₁`, is a stage event
`stageEvent g c j` whose parent popped at
`σ := stageTarget g c (j - 1) < τ₁`. A trichotomy on `σ` against the
stage-`0` pop tick `τ₀` rules out every shape except `j = 1` with
`σ = τ₀`, which is exactly the prefix class of the first reference
chain:

* `σ < τ₀`: `e` already sits in the tick-`τ₀` queue while `sA` is not
  even present there, so `e` precedes `sA` — contradicting the given
  `sA` before `e`;
* `σ > τ₀`: symmetric — `sD` sits in the tick-`σ` queue before `e`
  appears, contradicting `e` before `sD`;
* `σ = τ₀` with `j = 1`: the conclusion is arithmetic (the parent's
  due tick gives the activation tick, `e`'s target gives the first
  middle delay);
* `σ = τ₀` with `j ≥ 2`: the parent `P` carries priority `-3`, below
  the priority-`0` reference `A`; in every burst/drain fate
  combination the priority discipline of
  CrossPriorityPopDiscipline/BurstCrossPrioritySpawnOrder puts `e` before
  `sA`, again contradicting `sA` before `e`.

This supersedes Stage1BaseCase, whose `h_sA_absent` premise does not hold for
arbitrary `pos`. -/

/-! ## Private helper (reproven: the QSideOrder/41/55 versions are private) -/

/-- `NodeLayoutOk` holds at every tick-start world. -/
private theorem NodeLayoutOk_gSimWorld' (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (t : Nat) :
    NodeLayoutOk groups
      (gSimWorld groups actTick groupOrd withinOrd pos t) := by
  dsimp [gSimWorld]
  exact NodeLayoutOk_gSimFoldl groups actTick (buildGroups groups).2 groupOrd
    withinOrd pos (buildGroups groups).1 t (NodeLayoutOk_buildGroups groups)

/-! ## The base case -/

/-- The `MiddleBlockOk` base case at stage 1, valid for arbitrary
    `pos`. -/
theorem MiddleBlockOk_stage1_general (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat)
    (h_valid : ∀ gi (c : ChainSpec), gi < groups.length →
        c ∈ groupAt groups gi →
        (∀ d ∈ c.middleDelays, ValidDelay d) ∧ ValidDelay c.lastDelay)
    (h_ord : List.Perm groupOrd (List.range groups.length))
    (h_within : ∀ gi, gi < groups.length →
        List.Perm (withinOrd gi) (List.range (groupAt groups gi).length))
    (T : Nat) (g₁ c₁ g₂ c₂ : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_m₁ : 1 ≤ (chainAt groups g₁ c₁).middleDelays.length)
    (h_tgt0 : stageTarget actTick groups g₂ c₂ 0 =
        stageTarget actTick groups g₁ c₁ 0)
    (h_tgt1 : stageTarget actTick groups g₂ c₂ 1 =
        stageTarget actTick groups g₁ c₁ 1) :
    MiddleBlockOk groups actTick T
      (gSimWorld groups actTick groupOrd withinOrd pos
        (stageTarget actTick groups g₁ c₁ 1)).events g₁ c₁ g₂ c₂ 1 := by
  set τ₀ := stageTarget actTick groups g₁ c₁ 0
  set τ₁ := stageTarget actTick groups g₁ c₁ 1
  set sA := stageEvent actTick groups g₁ c₁ 1
  set sD := stageEvent actTick groups g₂ c₂ 1
  set Q₁ := (gSimWorld groups actTick groupOrd withinOrd pos τ₁).events
  have h_τ₀τ₁ : τ₀ < τ₁ :=
    stageTarget_lt_succ actTick groups g₁ c₁ 0 (Nat.zero_le _)
  -- nodup of the tick-τ₁ queue, for asymmetry contradictions
  have h_gord_nd : groupOrd.Nodup := Nodup.of_perm h_ord List.nodup_range
  have h_within_nd : ∀ gi, gi < groups.length → (withinOrd gi).Nodup :=
    fun gi h_gi => Nodup.of_perm (h_within gi h_gi) List.nodup_range
  have h_nd_Q₁ : Q₁.Nodup :=
    gSimWorld_events_Nodup groups actTick groupOrd withinOrd pos τ₁
      h_gord_nd h_within_nd
  intro e h_b1 h_b2 h_pri_e h_tgt_e
  -- characterize e via the stage-window property of the tick-start queue
  have h_e_mem : e ∈ Q₁ := evBefore.mem_left h_b2
  obtain ⟨g, c, j, h_g, h_c, _, h_e_eq, h_win⟩ :=
    gSimWorld_events_stageWindow groups actTick groupOrd withinOrd pos τ₁ e
      h_e_mem
  -- priority -3 forces a middle stage: 1 ≤ j ≤ middleDelays.length
  have h_j_mid : 1 ≤ j ∧ j ≤ (chainAt groups g c).middleDelays.length := by
    rw [h_e_eq] at h_pri_e
    dsimp [stageEvent, stagePri] at h_pri_e
    have h_j_ne0 : j ≠ 0 := by
      intro h_j0
      rw [h_j0] at h_pri_e
      dsimp at h_pri_e
      omega
    have h_j_le : j ≤ (chainAt groups g c).middleDelays.length := by
      by_contra h_gt
      have h_val : (if j = 0 then 0
          else if j ≤ (chainAt groups g c).middleDelays.length then (-3 : Int)
          else (-1 : Int)) = (-1 : Int) := by
        split_ifs <;> omega
      rw [h_val] at h_pri_e
      omega
    exact ⟨by omega, h_j_le⟩
  -- e's target equation as a stage-target equation
  have h_tgt_e' : stageTarget actTick groups g c j = τ₁ :=
    (by rw [h_e_eq]; rfl : e.targetTick =
      stageTarget actTick groups g c j).symm.trans h_tgt_e
  -- the parent's pop tick
  set σ := stageTarget actTick groups g c (j - 1)
  have h_σ_lt : σ < τ₁ := by
    dsimp [stageWindow] at h_win
    split_ifs at h_win with h_j0
    · omega
    · exact h_win.1
  by_cases h_σ_lt_τ₀ : σ < τ₀
  · -- Case 1: e is already queued at τ₀, where sA is absent
    have h_e_τ₀ : e ∈
        (gSimWorld groups actTick groupOrd withinOrd pos τ₀).events := by
      convert stageEvent_succ_mem_range_complete groups actTick groupOrd
        withinOrd pos h_valid h_ord h_within g c (j - 1) h_g h_c
        (by omega) τ₀ (by change σ + 1 ≤ τ₀; try omega) (by
          rw [Nat.sub_add_cancel (show 1 ≤ j by omega), h_tgt_e']
          omega) using 1
      · rw [h_e_eq, Nat.sub_add_cancel (show 1 ≤ j by omega)]
    have h_sA_not_τ₀ : sA ∉
        (gSimWorld groups actTick groupOrd withinOrd pos τ₀).events :=
      stageEvent_succ_not_mem_gSimWorld groups actTick groupOrd withinOrd
        pos g₁ c₁ 0 τ₀ h_g₁ h_c₁ (Nat.zero_le _) rfl
    have h_sA_τ₀1 : sA ∈
        (gSimWorld groups actTick groupOrd withinOrd pos (τ₀ + 1)).events :=
      stageEvent_succ_mem_range_complete groups actTick groupOrd withinOrd
        pos h_valid h_ord h_within g₁ c₁ 0 h_g₁ h_c₁ (Nat.zero_le _) (τ₀ + 1)
        (by change τ₀ + 1 ≤ τ₀ + 1; try omega) (by change τ₀ + 1 ≤ τ₁; try omega)
    have h_e_lt_sA : evBefore
        (gSimWorld groups actTick groupOrd withinOrd pos
          (τ₀ + 1)).events e sA :=
      evBefore_survivor_before_spawn groups actTick groupOrd withinOrd pos
        τ₀ h_valid e sA h_e_τ₀ (by rw [h_tgt_e]; try omega) h_sA_τ₀1 h_sA_not_τ₀
    have h_e_lt_sA_T : evBefore Q₁ e sA :=
      evBefore_gSimWorld_const groups actTick groupOrd withinOrd pos
        (τ₀ + 1) τ₁ e sA (by omega) h_e_lt_sA
        (by rw [h_tgt_e]; try omega) (by dsimp [sA, stageEvent]; try omega)
    exact (evBefore.asymm h_nd_Q₁ h_b1 h_e_lt_sA_T).elim
  · by_cases h_τ₀_lt_σ : τ₀ < σ
    · -- Case 2: sD is already queued at σ, before e appears
      have h_sD_σ : sD ∈
          (gSimWorld groups actTick groupOrd withinOrd pos σ).events :=
        stageEvent_succ_mem_range_complete groups actTick groupOrd withinOrd
          pos h_valid h_ord h_within g₂ c₂ 0 h_g₂ h_c₂ (Nat.zero_le _) σ
          (by rw [h_tgt0]; try omega) (by rw [h_tgt1]; try omega)
      have h_e_not_σ : e ∉
          (gSimWorld groups actTick groupOrd withinOrd pos σ).events := by
        convert stageEvent_succ_not_mem_gSimWorld groups actTick groupOrd
          withinOrd pos g c (j - 1) σ h_g h_c (by omega) rfl using 1
        · rw [h_e_eq, Nat.sub_add_cancel (show 1 ≤ j by omega)]
      have h_e_σ1 : e ∈
          (gSimWorld groups actTick groupOrd withinOrd pos
            (σ + 1)).events := by
        convert stageEvent_succ_mem_range_complete groups actTick groupOrd
          withinOrd pos h_valid h_ord h_within g c (j - 1) h_g h_c
          (by omega) (σ + 1) (by change σ + 1 ≤ σ + 1; try omega) (by
            rw [Nat.sub_add_cancel (show 1 ≤ j by omega), h_tgt_e']
            omega) using 1
        · rw [h_e_eq]
          congr 1
          omega
      have h_sD_lt_e : evBefore
          (gSimWorld groups actTick groupOrd withinOrd pos
            (σ + 1)).events sD e :=
        evBefore_survivor_before_spawn groups actTick groupOrd withinOrd pos
          σ h_valid sD e h_sD_σ (by
            dsimp [sD, stageEvent]
            rw [h_tgt1]
            omega) h_e_σ1 h_e_not_σ
      have h_sD_lt_e_T : evBefore Q₁ sD e :=
        evBefore_gSimWorld_const groups actTick groupOrd withinOrd pos
          (σ + 1) τ₁ sD e (by omega) h_sD_lt_e
          (by dsimp [sD, stageEvent]; rw [h_tgt1]; try omega)
          (by rw [h_tgt_e]; try omega)
      exact (evBefore.asymm h_nd_Q₁ h_b2 h_sD_lt_e_T).elim
    · -- Case 3: σ = τ₀
      have h_σ_eq : σ = τ₀ := by omega
      by_cases h_j1 : j = 1
      · -- the interloper is a stage-1 event whose parent popped at τ₀:
        -- the conclusion is arithmetic
        subst h_j1
        refine Or.inr ⟨g, c, h_g, h_c, h_e_eq, h_pri_e, h_tgt_e, ?_⟩
        exact prefixDelays_ext_of_targets_eq groups actTick g c g₁ c₁ 0
          (by omega) (by omega) rfl h_σ_eq h_tgt_e'
      · -- j ≥ 2: the parent P carries priority -3, below A's priority 0
        have h_j_ge2 : 2 ≤ j := by omega
        set P := stageEvent actTick groups g c (j - 1)
        set A := stageEvent actTick groups g₁ c₁ 0
        set W₁ : World :=
          (gSimWorld groups actTick groupOrd withinOrd pos τ₀).logOutput
            s!"tick {τ₀}"
        set active : List Nat := groupOrd.filter (fun gi =>
          decide (gi < (buildGroups groups).2.length) && (actTick gi == τ₀))
        set W_B : World := gSimBurst τ₀ (buildGroups groups).2 withinOrd pos
          W₁ (active.zipIdx)
        -- W_B is exactly preStepWorld g₁ c₁ 0
        have h_WB_eq : W_B =
            preStepWorld groups actTick groupOrd withinOrd pos g₁ c₁ 0 := by
          dsimp [W_B, W₁, active, preStepWorld, popQueueWorld, popActive]
        have h_tick_W₁ : W₁.tick = τ₀ := by
          dsimp [W₁]
          rw [gSimWorld_tick]
        have h_tick_WB : W_B.tick = τ₀ := by
          rw [h_WB_eq]
          exact preStepWorld_tick_eq groups actTick groupOrd withinOrd pos
            g₁ c₁ 0
        -- layout health
        have h_layout_W₁ : NodeLayoutOk groups W₁ :=
          NodeLayoutOk_logOutput groups
            (gSimWorld groups actTick groupOrd withinOrd pos τ₀)
            s!"tick {τ₀}"
            (NodeLayoutOk_gSimWorld' groups actTick groupOrd withinOrd pos
              τ₀)
        have h_layout_WB : NodeLayoutOk groups W_B :=
          NodeLayoutOk_gSimBurst groups τ₀ (buildGroups groups).2 withinOrd
            pos W₁ (active.zipIdx) h_layout_W₁
        -- facts about P
        have hP_pri : P.priority = (-3 : Int) := by
          dsimp [P, stageEvent, stagePri]
          split_ifs <;> omega
        have hP_tgt : P.targetTick = τ₀ := by
          dsimp [P, stageEvent]
          exact h_σ_eq
        have hP_τ₀ : P ∈
            (gSimWorld groups actTick groupOrd withinOrd pos τ₀).events := by
          dsimp only [P]
          convert stageEvent_mem_gSimWorld groups actTick groupOrd withinOrd
            pos h_valid h_ord h_within g c h_g h_c (j - 1) (by omega) using 1
          · change (gSimWorld groups actTick groupOrd withinOrd pos τ₀).events =
              (gSimWorld groups actTick groupOrd withinOrd pos σ).events
            rw [h_σ_eq]
        have hP_W₁ : P ∈ W₁.events := by
          simpa [W₁, World.logOutput_events] using hP_τ₀
        -- facts about A
        have hA_pri : A.priority = (0 : Int) := by
          dsimp [A, stageEvent, stagePri]
        have hA_tgt : A.targetTick = τ₀ := by
          dsimp [A, stageEvent]
        have hA_τ₀ : A ∈
            (gSimWorld groups actTick groupOrd withinOrd pos τ₀).events :=
          stageEvent_mem_gSimWorld groups actTick groupOrd withinOrd pos
            h_valid h_ord h_within g₁ c₁ h_g₁ h_c₁ 0 (Nat.zero_le _)
        have hA_W₁ : A ∈ W₁.events := by
          simpa [W₁, World.logOutput_events] using hA_τ₀
        have h_pri_PA : P.priority < A.priority := by
          rw [hP_pri, hA_pri]
          omega
        -- spawn equations, valid at every good-layout world of tick τ₀
        have h_spawnP : ∀ (v : World), v.tick = τ₀ →
            NodeLayoutOk groups v →
            (v.onScheduledTick P.nodeId).events = v.events ++ [e] := by
          intro v h_v h_lay
          have h_v_tick : v.tick = stageTarget actTick groups g c (j - 1) := by
            rw [h_v, ← h_σ_eq]
          have h_sp := stage_spawn groups actTick v g c (j - 1) h_g h_c
            (by omega) h_v_tick h_lay
          rw [Nat.sub_add_cancel (show 1 ≤ j by omega)] at h_sp
          rw [← h_e_eq] at h_sp
          simpa [P, stageEvent] using h_sp
        have h_spawnA : ∀ (v : World), v.tick = τ₀ →
            NodeLayoutOk groups v →
            (v.onScheduledTick A.nodeId).events = v.events ++ [sA] := by
          intro v h_v h_lay
          have h_sp := stage_spawn groups actTick v g₁ c₁ 0 h_g₁ h_c₁
            (Nat.zero_le _) (by rw [h_v]) h_lay
          simpa [A, sA, stageEvent] using h_sp
        -- short forms for the non-due side conditions
        have h_e_nd_WB : e.targetTick ≠ W_B.tick := by
          rw [h_tick_WB]
          rw [h_tgt_e]
          omega
        have h_sA_nd_WB : sA.targetTick ≠ W_B.tick := by
          rw [h_tick_WB]
          dsimp [sA, stageEvent]
          omega
        by_cases hA_B : A ∈ W_B.events
        · by_cases hP_B : P ∈ W_B.events
          · -- both survive the burst: drain spawn order
            have h_ord_drain : evBefore W_B.stepUntilNextTick.events e sA :=
              stepUNT_spawn_before_of_pri_lt groups W_B P A e sA h_layout_WB
                hP_B hA_B (by rw [hP_tgt, h_tick_WB])
                (by rw [hA_tgt, h_tick_WB]) h_pri_PA h_e_nd_WB h_sA_nd_WB
                (fun v h_v => h_spawnP v (h_v.trans h_tick_WB))
                (fun v h_v => h_spawnA v (h_v.trans h_tick_WB))
            have h_ord_T : evBefore Q₁ e sA := by
              have h_ord_τ₀1 : evBefore
                  (gSimWorld groups actTick groupOrd withinOrd pos
                    (τ₀ + 1)).events e sA := by
                rw [gSimWorld_succ_events_eq_preStepWorld groups actTick
                  groupOrd withinOrd pos g₁ c₁ 0, ← h_WB_eq]
                exact h_ord_drain
              exact evBefore_gSimWorld_const groups actTick groupOrd
                withinOrd pos (τ₀ + 1) τ₁ e sA (by omega) h_ord_τ₀1
                (by rw [h_tgt_e]; try omega)
                (by dsimp [sA, stageEvent]; try omega)
            exact (evBefore.asymm h_nd_Q₁ h_b1 h_ord_T).elim
          · -- P popped by the burst, A survives: e is a survivor of the
            -- drain and precedes the drain-spawn sA
            have h_e_WB : e ∈ W_B.events :=
              gSimBurst_spawn_mem groups τ₀ (buildGroups groups).2 withinOrd
                pos W₁ (active.zipIdx) P e h_layout_W₁ hP_W₁
                (by rw [hP_tgt, h_tick_W₁]) hP_B
                (by rw [h_tick_W₁]; rw [h_tgt_e]; try omega)
                (fun v h_v => h_spawnP v (h_v.trans h_tick_W₁))
            have h_ord_drain : evBefore W_B.stepUntilNextTick.events e sA :=
              World.presentNotDue_before_dueSpawn_layout groups W_B e A sA
                h_layout_WB h_e_WB h_e_nd_WB hA_B
                (by rw [hA_tgt, h_tick_WB]) h_sA_nd_WB
                (fun v h_v => h_spawnA v (h_v.trans h_tick_WB))
            have h_ord_T : evBefore Q₁ e sA := by
              have h_ord_τ₀1 : evBefore
                  (gSimWorld groups actTick groupOrd withinOrd pos
                    (τ₀ + 1)).events e sA := by
                rw [gSimWorld_succ_events_eq_preStepWorld groups actTick
                  groupOrd withinOrd pos g₁ c₁ 0, ← h_WB_eq]
                exact h_ord_drain
              exact evBefore_gSimWorld_const groups actTick groupOrd
                withinOrd pos (τ₀ + 1) τ₁ e sA (by omega) h_ord_τ₀1
                (by rw [h_tgt_e]; try omega)
                (by dsimp [sA, stageEvent]; try omega)
            exact (evBefore.asymm h_nd_Q₁ h_b1 h_ord_T).elim
        · -- A popped by the burst: by the cross-priority discipline
          -- (CrossPriorityPopDiscipline), P was popped too; the burst spawn order (BurstCrossPrioritySpawnOrder)
          -- puts e before sA
          have hP_B' : P ∉ W_B.events := by
            intro hP_B
            exact hA_B (gSimBurst_not_pop_larger_pri τ₀
              (buildGroups groups).2 withinOrd pos W₁ (active.zipIdx) P A
              (by rw [hP_tgt, h_tick_W₁]) (by rw [hA_tgt, h_tick_W₁])
              h_pri_PA hA_W₁ hP_B)
          have h_e_WB : e ∈ W_B.events :=
            gSimBurst_spawn_mem groups τ₀ (buildGroups groups).2 withinOrd
              pos W₁ (active.zipIdx) P e h_layout_W₁ hP_W₁
              (by rw [hP_tgt, h_tick_W₁]) hP_B'
              (by rw [h_tick_W₁]; rw [h_tgt_e]; try omega)
              (fun v h_v => h_spawnP v (h_v.trans h_tick_W₁))
          have h_sA_WB : sA ∈ W_B.events :=
            gSimBurst_spawn_mem groups τ₀ (buildGroups groups).2 withinOrd
              pos W₁ (active.zipIdx) A sA h_layout_W₁ hA_W₁
              (by rw [hA_tgt, h_tick_W₁]) hA_B
              (by rw [h_tick_W₁]; dsimp [sA, stageEvent]; try omega)
              (fun v h_v => h_spawnA v (h_v.trans h_tick_W₁))
          have h_ord_WB : evBefore W_B.events e sA :=
            gSimBurst_smaller_pri_spawn_before groups τ₀
              (buildGroups groups).2 withinOrd pos W₁ (active.zipIdx) P A
              e sA h_layout_W₁ hP_W₁ hA_W₁
              (by rw [hP_tgt, h_tick_W₁]) (by rw [hA_tgt, h_tick_W₁])
              h_pri_PA hP_B' hA_B
              (by rw [h_tick_W₁]; rw [h_tgt_e]; try omega)
              (by rw [h_tick_W₁]; dsimp [sA, stageEvent]; try omega)
              (fun v h_v => h_spawnP v (h_v.trans h_tick_W₁))
              (fun v h_v => h_spawnA v (h_v.trans h_tick_W₁))
          have h_ord_drain : evBefore W_B.stepUntilNextTick.events e sA :=
            evBefore_stepUNT_of_notDue W_B e sA h_e_WB h_sA_WB h_e_nd_WB
              h_sA_nd_WB h_ord_WB
          have h_ord_T : evBefore Q₁ e sA := by
            have h_ord_τ₀1 : evBefore
                (gSimWorld groups actTick groupOrd withinOrd pos
                  (τ₀ + 1)).events e sA := by
              rw [gSimWorld_succ_events_eq_preStepWorld groups actTick
                groupOrd withinOrd pos g₁ c₁ 0, ← h_WB_eq]
              exact h_ord_drain
            exact evBefore_gSimWorld_const groups actTick groupOrd withinOrd
              pos (τ₀ + 1) τ₁ e sA (by omega) h_ord_τ₀1
              (by rw [h_tgt_e]; try omega)
              (by dsimp [sA, stageEvent]; try omega)
          exact (evBefore.asymm h_nd_Q₁ h_b1 h_ord_T).elim
