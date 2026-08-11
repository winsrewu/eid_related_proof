import BasicProofs.GroupClustering.FinalsBundle
import BasicProofs.GroupClustering.ActivationListOrder
import BasicProofs.GroupClustering.QSideOrderNoSurvival

open BasicRedstoneSim List

/-! # Group clustering — order preservation core

The group-vs-group output order is spec-independent. The argument:

1. The bridge of LogShape turns `groupBeforeSpec` on the log into
   `evBefore` on the final events in the tick-`T` due filter (the
   bundle of FinalsBundle).
2. The order of the final events of two same-spec chains is the order
   of the two groups in the activation burst (QSideOrderNoSurvival).
3. If the observed spec orders group `ga` before group `gb`, the
   reverse burst order contradicts the asymmetry of `evBefore` on the
   duplicate-free finals list. Hence `ga` bursts before `gb`, and every
   other shared spec orders `ga` before `gb` by QSideOrderNoSurvival again.
-/

/-- Transport the burst order of two same-spec chains into the `evBefore`
    order of their final events in the tick-`T` due filter `finals`.
    `sameSpec_final_evBefore` orders the final-stage events in the
    tick-start queue `popQueueWorld`; both events carry the first chain's
    stage index, so the second index is reconciled via the shared spec
    (`h_spec`) before both are rewritten to `finalEventOf` (`h_feq`), and
    `evBefore.filter` moves to the due filter. -/
theorem evBefore_finals_of_burst (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (T : Nat)
    (h_uniform : ∀ gi (c₁ c₂ : ChainSpec), gi < groups.length →
        c₁ ∈ groupAt groups gi → c₂ ∈ groupAt groups gi →
        chainDelay c₁ = chainDelay c₂)
    (h_act : ∀ gi, gi < groups.length → groupAt groups gi ≠ [] →
        actTick gi + groupDelay (groupAt groups gi) = T)
    (finals : List ScheduledEvent)
    (h_finals : finals =
        (gSimWorld groups actTick groupOrd withinOrd pos T).events.filter
          (fun ev => ev.targetTick == T))
    (finalEventOf : Nat → Nat → ScheduledEvent)
    (h_feq : ∀ gi ci, stageEvent actTick groups gi ci
        ((chainAt groups gi ci).middleDelays.length + 1) =
      finalEventOf gi ci)
    (g₁ c₁ g₂ c₂ : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_spec : chainAt groups g₁ c₁ = chainAt groups g₂ c₂)
    (h_act_eq : actTick g₁ = actTick g₂)
    (h_c₁_in : c₁ ∈ withinOrd g₁) (h_c₂_in : c₂ ∈ withinOrd g₂)
    (h_burst : ∃ pre mid post,
        groupOrd.filter (fun gi =>
            decide (gi < (buildGroups groups).2.length) &&
            (actTick gi == actTick g₁)) =
        pre ++ g₁ :: mid ++ g₂ :: post)
    (h_gord_nd : groupOrd.Nodup)
    (h_within_nd : ∀ gi, gi < groups.length → (withinOrd gi).Nodup) :
    evBefore finals (finalEventOf g₁ c₁) (finalEventOf g₂ c₂) := by
  have h_ev_q := sameSpec_final_evBefore groups actTick groupOrd withinOrd
    pos g₁ c₁ g₂ c₂ h_g₁ h_c₁ h_g₂ h_c₂ h_spec h_act_eq h_c₁_in h_c₂_in
    h_burst h_gord_nd h_within_nd
  dsimp [popQueueWorld] at h_ev_q
  have h_tgt : stageTarget actTick groups g₁ c₁
      ((chainAt groups g₁ c₁).middleDelays.length + 1) = T :=
    stageTarget_final_eq_T groups actTick T g₁ c₁ h_g₁ h_c₁ h_uniform h_act
  rw [h_tgt] at h_ev_q
  -- both events currently carry `g₁ c₁`'s final-stage index; reconcile the
  -- second to `g₂ c₂`'s (equal specs), then rewrite both to `finalEventOf`
  have h_mlen : (chainAt groups g₁ c₁).middleDelays.length =
      (chainAt groups g₂ c₂).middleDelays.length := by
    rw [h_spec]
  rw [h_feq] at h_ev_q
  rw [h_mlen] at h_ev_q
  rw [h_feq] at h_ev_q
  rw [h_finals]
  apply evBefore.filter (fun ev => ev.targetTick == T)
  · rw [← h_feq]
    dsimp [stageEvent]
    rw [h_tgt]
    simp
  · rw [← h_feq]
    dsimp [stageEvent]
    rw [stageTarget_final_eq_T groups actTick T g₂ c₂ h_g₂ h_c₂ h_uniform
      h_act]
    simp
  · exact h_ev_q

/-- Order preservation for the group simulation. -/
theorem group_order_preservation_core (groups : List GroupSpec)
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
    ∀ ga gb sa sb,
      ga < groups.length → gb < groups.length → ga ≠ gb →
      (∃ ca, ca < (groupAt groups ga).length ∧ chainAt groups ga ca = sa) →
      (∃ cb, cb < (groupAt groups gb).length ∧ chainAt groups gb cb = sa) →
      groupBeforeSpec log groups ga gb sa →
      groupBeforeSpec log groups ga gb sb := by
  intro log ga gb sa sb h_ga h_gb h_ne h_sa_a h_sa_b h_before
  -- the finals bundle
  obtain ⟨blocks, finals, finalEventOf, chainOf, finalIdx, entryOf,
    h_shape, h_no_early, h_finals, h_nd, h_feq, h_block, h_match,
    h_chainOf_eq, h_eq_chainOf, h_pos⟩ :=
    groupSimulate_final_bundle T groups actTick groupOrd withinOrd pos
      h_valid h_uniform h_act h_ord h_within
  -- log shape in the logBlocks form that LogShape expects
  have h_shape_lb : log = logBlocks [] 0 blocks (T + 1) := by
    dsimp [log]
    exact h_shape.trans (logBlocks_zero_eq_foldl blocks (T + 1)).symm
  -- nodup of the orders, from the permutation hypotheses
  have h_gord_nd : groupOrd.Nodup :=
    Nodup.of_perm h_ord List.nodup_range
  have h_within_nd : ∀ gi, gi < groups.length → (withinOrd gi).Nodup :=
    fun gi h_gi => Nodup.of_perm (h_within gi h_gi) List.nodup_range
  -- the sa instances
  obtain ⟨ca₀, h_ca₀, h_sa_ca₀⟩ := h_sa_a
  obtain ⟨cb₀, h_cb₀, h_sa_cb₀⟩ := h_sa_b
  -- withinOrd membership of the sa instances
  have h_ca₀_in : ca₀ ∈ withinOrd ga :=
    (List.Perm.mem_iff (h_within ga h_ga) (a := ca₀)).mpr
      (List.mem_range.mpr h_ca₀)
  have h_cb₀_in : cb₀ ∈ withinOrd gb :=
    (List.Perm.mem_iff (h_within gb h_gb) (a := cb₀)).mpr
      (List.mem_range.mpr h_cb₀)
  -- both groups activate at the same tick: T - chainDelay sa
  have h_ga_ne : groupAt groups ga ≠ [] := by
    intro h_empty
    rw [h_empty] at h_ca₀
    cases h_ca₀
  have h_gb_ne : groupAt groups gb ≠ [] := by
    intro h_empty
    rw [h_empty] at h_cb₀
    cases h_cb₀
  have h_delay_a : groupDelay (groupAt groups ga) = chainDelay sa := by
    cases h_decomp : groupAt groups ga with
    | nil => contradiction
    | cons c_head cs =>
      have h_head_mem : c_head ∈ groupAt groups ga := by
        rw [h_decomp]
        simp
      have h_sa_mem : sa ∈ groupAt groups ga := by
        rw [← h_sa_ca₀]
        exact chainAt_mem groups ga ca₀ h_ca₀
      dsimp [groupDelay]
      exact h_uniform ga c_head sa h_ga h_head_mem h_sa_mem
  have h_delay_b : groupDelay (groupAt groups gb) = chainDelay sa := by
    cases h_decomp : groupAt groups gb with
    | nil => contradiction
    | cons c_head cs =>
      have h_head_mem : c_head ∈ groupAt groups gb := by
        rw [h_decomp]
        simp
      have h_sa_mem : sa ∈ groupAt groups gb := by
        rw [← h_sa_cb₀]
        exact chainAt_mem groups gb cb₀ h_cb₀
      dsimp [groupDelay]
      exact h_uniform gb c_head sa h_gb h_head_mem h_sa_mem
  have h_act_eq : actTick ga = actTick gb := by
    have h_a := h_act ga h_ga h_ga_ne
    have h_b := h_act gb h_gb h_gb_ne
    rw [h_delay_a] at h_a
    rw [h_delay_b] at h_b
    omega
  -- the bridge for spec sa: log order iff final-event order
  have h_bridge_sa :=
    (groupBeforeSpec_iff_evBefore_discharged T groups actTick groupOrd
      withinOrd pos ga gb sa h_ga h_gb blocks h_shape_lb h_no_early
      finals h_nd chainOf finalEventOf finalIdx entryOf h_block h_match
      h_chainOf_eq h_eq_chainOf h_pos).mp h_before
  have h_ev₀ : evBefore finals (finalEventOf ga ca₀)
      (finalEventOf gb cb₀) :=
    h_bridge_sa ca₀ cb₀ h_ca₀ h_cb₀ h_sa_ca₀ h_sa_cb₀
  -- the burst order of the two groups
  have h_burst_disj := burst_order_total groups actTick groupOrd ga gb
    (actTick ga) h_ord h_ga h_gb h_ne rfl h_act_eq.symm
  -- the `gb` before `ga` case contradicts the observed `sa` order, so
  -- `ga` bursts before `gb`
  have h_burst_ab : ∃ pre mid post,
      groupOrd.filter (fun gi =>
          decide (gi < (buildGroups groups).2.length) &&
          (actTick gi == actTick ga)) =
      pre ++ ga :: mid ++ gb :: post := by
    rcases h_burst_disj with h_ab | h_ba
    · exact h_ab
    · exfalso
      -- restate the split with the `actTick gb` filter predicate
      have h_ba' : ∃ pre mid post,
          groupOrd.filter (fun gi =>
              decide (gi < (buildGroups groups).2.length) &&
              (actTick gi == actTick gb)) =
          pre ++ gb :: mid ++ ga :: post := by
        obtain ⟨pre, mid, post, h_split⟩ := h_ba
        refine ⟨pre, mid, post, ?_⟩
        have hpred : (fun gi =>
            decide (gi < (buildGroups groups).2.length) &&
            (actTick gi == actTick gb)) =
            (fun gi =>
            decide (gi < (buildGroups groups).2.length) &&
            (actTick gi == actTick ga)) := by
          ext gi
          rw [← h_act_eq]
        rw [hpred]
        exact h_split
      have h_ev_rev : evBefore finals (finalEventOf gb cb₀)
          (finalEventOf ga ca₀) :=
        evBefore_finals_of_burst groups actTick groupOrd withinOrd pos T
          h_uniform h_act finals h_finals finalEventOf h_feq
          gb cb₀ ga ca₀ h_gb h_cb₀ h_ga h_ca₀
          (by rw [h_sa_cb₀, h_sa_ca₀]) h_act_eq.symm h_cb₀_in h_ca₀_in
          h_ba' h_gord_nd h_within_nd
      exact evBefore.asymm h_nd h_ev₀ h_ev_rev
  -- apply the bridge for spec `sb`: the burst order yields the
  -- final-event order for every `sb` instance
  refine (groupBeforeSpec_iff_evBefore_discharged T groups actTick
    groupOrd withinOrd pos ga gb sb h_ga h_gb blocks h_shape_lb
    h_no_early finals h_nd chainOf finalEventOf finalIdx entryOf h_block
    h_match h_chainOf_eq h_eq_chainOf h_pos).mpr
    (fun ca cb h_ca h_cb h_sb_ca h_sb_cb => ?_)
  have h_ca_in : ca ∈ withinOrd ga :=
    (List.Perm.mem_iff (h_within ga h_ga) (a := ca)).mpr
      (List.mem_range.mpr h_ca)
  have h_cb_in : cb ∈ withinOrd gb :=
    (List.Perm.mem_iff (h_within gb h_gb) (a := cb)).mpr
      (List.mem_range.mpr h_cb)
  exact evBefore_finals_of_burst groups actTick groupOrd withinOrd pos T
    h_uniform h_act finals h_finals finalEventOf h_feq
    ga ca gb cb h_ga h_ca h_gb h_cb
    (by rw [h_sb_ca, h_sb_cb]) h_act_eq h_ca_in h_cb_in
    h_burst_ab h_gord_nd h_within_nd
