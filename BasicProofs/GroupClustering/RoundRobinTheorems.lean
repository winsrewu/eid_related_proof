import BasicProofs.GroupClustering.ClusteringCore
import BasicProofs.GroupClustering.OrderPreservationCore
import BasicProofs.GroupClustering.RoundRobinSplit

open BasicRedstoneSim List

/-! # Group clustering — round-robin capstone corollaries

Applies the clustering and order-preservation cores to the singleton-split
system that DEFINES the round-robin simulation (`groupSimulateRR`). Each
bundle chain `(gi, ci)` becomes split group `rrFlatIndex groups gi ci`
holding the single chain `chainAt groups gi ci`, so the split chain index
is always `0` and `rrWithinOrd`/`rrPos` are trivial.
-/

/-- The split simulation is definitionally the round-robin simulation. -/
private theorem splitLog_eq_rr (T : Nat) (groups : List GroupSpec)
    (groupOrd : List Nat) :
    groupSimulate T (rrSplitGroups groups) (rrActTick T groups)
      (rrGroupOrd groups groupOrd) rrWithinOrd rrPos =
      groupSimulateRR T groups groupOrd := by
  rfl

/-- A bundle chain's split group has exactly one chain, so chain index
    `0` is in bounds. -/
private theorem split_chain0_inBounds (groups : List GroupSpec)
    (gi ci : Nat) (h_gi : gi < groups.length)
    (h_ci : ci < (groupAt groups gi).length) :
    0 < (groupAt (rrSplitGroups groups)
      (rrFlatIndex groups gi ci)).length := by
  rw [rrGroupAt_flat groups gi ci h_gi h_ci]
  simp

/-- **Round-robin clustering.** Identical-spec bundle-chain outputs are
    contiguous in the round-robin output order. -/
theorem group_rr_output_clustering
    (groups : List GroupSpec)
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
    (h_ord : List.Perm groupOrd (List.range groups.length)) :
    let log := groupSimulateRR T groups groupOrd
    ∀ g₁ c₁ g₂ c₂ g₃ c₃ p₁ p₂ p₃,
      g₁ < groups.length → g₂ < groups.length → g₃ < groups.length →
      c₁ < (groupAt groups g₁).length →
      c₂ < (groupAt groups g₂).length →
      c₃ < (groupAt groups g₃).length →
      outputPosRR log groups g₁ c₁ = some p₁ →
      outputPosRR log groups g₂ c₂ = some p₂ →
      outputPosRR log groups g₃ c₃ = some p₃ →
      p₁ < p₂ → p₂ < p₃ →
      chainAt groups g₁ c₁ = chainAt groups g₃ c₃ →
      chainAt groups g₂ c₂ = chainAt groups g₁ c₁ := by
  intro log g₁ c₁ g₂ c₂ g₃ c₃ p₁ p₂ p₃ hg₁ hg₂ hg₃ hc₁ hc₂ hc₃
    hp₁ hp₂ hp₃ h12 h23 hspec
  -- apply the clustering core to the singleton-split system
  have h_core := group_output_clustering_core (rrSplitGroups groups)
    (rrSplit_valid groups h_valid) (rrSplit_uniform groups) T
    (rrActTick T groups) (rrSplit_act groups h_uniform T actTick h_act)
    (rrGroupOrd groups groupOrd) (rrGroupOrd_perm groups groupOrd h_ord)
    rrWithinOrd (fun f hf => rrWithinOrd_perm groups f hf) rrPos
  -- instantiate at the three split groups, chain index 0
  have h_split := h_core
    (rrFlatIndex groups g₁ c₁) 0
    (rrFlatIndex groups g₂ c₂) 0
    (rrFlatIndex groups g₃ c₃) 0
    p₁ p₂ p₃
    (split_chain0_inBounds groups g₁ c₁ hg₁ hc₁)
    (split_chain0_inBounds groups g₂ c₂ hg₂ hc₂)
    (split_chain0_inBounds groups g₃ c₃ hg₃ hc₃)
  -- rewrite the outputPosRR hypotheses into the core's outputPos form
  dsimp [outputPosRR] at hp₁ hp₂ hp₃
  have h_split' := h_split hp₁ hp₂ hp₃ h12 h23
  -- transport the spec equality to split chains and back
  have h_spec₁₃ : chainAt (rrSplitGroups groups)
      (rrFlatIndex groups g₁ c₁) 0 =
      chainAt (rrSplitGroups groups) (rrFlatIndex groups g₃ c₃) 0 := by
    rw [rrChainAt_flat_self groups g₁ c₁ hg₁ hc₁,
      rrChainAt_flat_self groups g₃ c₃ hg₃ hc₃]
    exact hspec
  have h_concl := h_split' h_spec₁₃
  rw [rrChainAt_flat_self groups g₂ c₂ hg₂ hc₂,
    rrChainAt_flat_self groups g₁ c₁ hg₁ hc₁] at h_concl
  exact h_concl

/-- The round-robin activation order lifts into a split of the
    singleton-split activation burst: the filtered round-robin order
    places the first chain's singleton before the second's. -/
private theorem rrBefore_burst_split (groups : List GroupSpec)
    (groupOrd : List Nat) (T : Nat) (g₁ c₁ g₂ c₂ : Nat)
    (h_g₁ : g₁ < groups.length) (h_g₂ : g₂ < groups.length)
    (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_ord : List.Perm groupOrd (List.range groups.length))
    (h_d : chainDelay (chainAt groups g₁ c₁) =
        chainDelay (chainAt groups g₂ c₂))
    (h_before : rrBefore groupOrd g₁ c₁ g₂ c₂) :
    ∃ pre mid post,
      (rrGroupOrd groups groupOrd).filter (fun f =>
          decide (f < (buildGroups (rrSplitGroups groups)).2.length) &&
            (rrActTick T groups f ==
              rrActTick T groups (rrFlatIndex groups g₁ c₁))) =
        pre ++ rrFlatIndex groups g₁ c₁ :: mid ++
          rrFlatIndex groups g₂ c₂ :: post := by
  set f₁ := rrFlatIndex groups g₁ c₁
  set f₂ := rrFlatIndex groups g₂ c₂
  set p : Nat → Bool := fun f =>
    decide (f < (buildGroups (rrSplitGroups groups)).2.length) &&
      (rrActTick T groups f == rrActTick T groups f₁) with hp_def
  have h_f₁ : f₁ < (rrSplitGroups groups).length :=
    rrFlatIndex_lt groups g₁ c₁ h_g₁ h_c₁
  have h_f₂ : f₂ < (rrSplitGroups groups).length :=
    rrFlatIndex_lt groups g₂ c₂ h_g₂ h_c₂
  have h_p₁ : p f₁ = true := by
    rw [hp_def]
    dsimp only
    have h_dec : decide (f₁ < (buildGroups (rrSplitGroups groups)).2.length)
        = true := by
      rw [decide_eq_true_eq, buildGroups_snd_length]
      exact h_f₁
    rw [h_dec]
    simp
  have h_p₂ : p f₂ = true := by
    rw [hp_def]
    dsimp only
    rw [show decide (f₂ < (buildGroups (rrSplitGroups groups)).2.length) =
        true from by
      rw [decide_eq_true_eq, buildGroups_snd_length]
      exact h_f₂]
    rw [show (rrActTick T groups f₂ == rrActTick T groups f₁) = true from by
      dsimp [rrActTick, f₁, f₂]
      rw [rrChainAt_flat_self groups g₁ c₁ h_g₁ h_c₁,
        rrChainAt_flat_self groups g₂ c₂ h_g₂ h_c₂]
      simp [h_d]]
    rfl
  dsimp [rrBefore] at h_before
  have h_c₁_tot : c₁ < rrTotalChains groups := by
    have h := h_f₁
    rw [rrSplitGroups_length] at h
    dsimp [f₁, rrFlatIndex] at h
    omega
  cases h_before with
  | inl h_lt =>
    have h_c₂_tot : c₂ < rrTotalChains groups := by
      have h := h_f₂
      rw [rrSplitGroups_length] at h
      dsimp [f₂, rrFlatIndex] at h
      omega
    rw [rrGroupOrd_round_cons groups groupOrd c₁ h_c₁_tot,
      List.filter_append, List.filter_append]
    set preR := (List.range c₁).flatMap (rrRound groups groupOrd)
    set postR := ((List.range (rrTotalChains groups - c₁ - 1)).map
      (fun j => c₁ + 1 + j)).flatMap (rrRound groups groupOrd)
    have h_g₁_ord : g₁ ∈ groupOrd :=
      (List.Perm.mem_iff h_ord).mpr (List.mem_range.mpr h_g₁)
    have h_g₂_ord : g₂ ∈ groupOrd :=
      (List.Perm.mem_iff h_ord).mpr (List.mem_range.mpr h_g₂)
    have h_f₁_filter : f₁ ∈ (rrRound groups groupOrd c₁).filter p := by
      rw [List.mem_filter]
      refine ⟨?_, h_p₁⟩
      dsimp [f₁]
      exact rrRound_mem groups groupOrd g₁ c₁ h_g₁_ord h_c₁
    obtain ⟨m₁, m₂, h_mid₁⟩ := mem_split h_f₁_filter
    have h_f₂_post : f₂ ∈ postR := by
      dsimp [postR]
      rw [List.mem_flatMap]
      refine ⟨c₂, ?_, ?_⟩
      · rw [List.mem_map]
        refine ⟨c₂ - c₁ - 1, List.mem_range.mpr (by omega), ?_⟩
        omega
      · dsimp [f₂]
        exact rrRound_mem groups groupOrd g₂ c₂ h_g₂_ord h_c₂
    have h_f₂_filter : f₂ ∈ postR.filter p := by
      rw [List.mem_filter]
      exact ⟨h_f₂_post, h_p₂⟩
    obtain ⟨n₁, n₂, h_post₁⟩ := mem_split h_f₂_filter
    refine ⟨preR.filter p ++ m₁, m₂ ++ n₁, n₂, ?_⟩
    rw [h_mid₁, h_post₁]
    simp [List.append_assoc]
  | inr h_pair =>
    obtain ⟨h_eq_c, pre₀, mid₀, post₀, h_ord_split⟩ := h_pair
    have h_dec₁ : decide (c₁ < (groupAt groups g₁).length) = true := by
      rw [decide_eq_true_eq]
      exact h_c₁
    have h_dec₂ : decide (c₁ < (groupAt groups g₂).length) = true := by
      rw [decide_eq_true_eq, h_eq_c]
      exact h_c₂
    set roundFn : Nat → Option Nat := fun gi =>
      if decide (c₁ < (groupAt groups gi).length)
      then some (rrFlatIndex groups gi c₁) else none
    have h_fx : roundFn g₁ = some f₁ := by
      dsimp [roundFn, f₁]
      rw [h_dec₁]
      simp
    have h_fy : roundFn g₂ = some f₂ := by
      dsimp [roundFn, f₂]
      rw [h_dec₂, h_eq_c]
      simp
    obtain ⟨rpre, rmid, rpost, h_rsp⟩ :=
      filterMap_split_preserve roundFn pre₀ g₁ mid₀ g₂ post₀ f₁ f₂
        h_fx h_fy
    have h_round_split : rrRound groups groupOrd c₁ =
        rpre ++ f₁ :: rmid ++ f₂ :: rpost := by
      dsimp only [rrRound]
      rw [h_ord_split]
      exact h_rsp
    obtain ⟨bpre, bmid, bpost, h_bsp⟩ :=
      filter_split_preserve p rpre f₁ rmid f₂ rpost h_p₁ h_p₂
    rw [rrGroupOrd_round_cons groups groupOrd c₁ h_c₁_tot,
      List.filter_append, List.filter_append]
    set preR := (List.range c₁).flatMap (rrRound groups groupOrd)
    set postR := ((List.range (rrTotalChains groups - c₁ - 1)).map
      (fun j => c₁ + 1 + j)).flatMap (rrRound groups groupOrd)
    refine ⟨preR.filter p ++ bpre, bmid, bpost ++ postR.filter p, ?_⟩
    rw [h_round_split, h_bsp]
    simp [List.append_assoc]

/-- **Round-robin order preservation.** For two same-spec bundle chains,
    the output order in the round-robin simulation is exactly the
    round-robin activation order: round (chain index) first, then
    position in `groupOrd`. -/
theorem group_rr_order_preservation
    (groups : List GroupSpec)
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
    (h_ord : List.Perm groupOrd (List.range groups.length)) :
    let log := groupSimulateRR T groups groupOrd
    ∀ g₁ c₁ g₂ c₂ p₁ p₂,
      g₁ < groups.length → g₂ < groups.length →
      c₁ < (groupAt groups g₁).length →
      c₂ < (groupAt groups g₂).length →
      outputPosRR log groups g₁ c₁ = some p₁ →
      outputPosRR log groups g₂ c₂ = some p₂ →
      chainAt groups g₁ c₁ = chainAt groups g₂ c₂ →
      g₁ ≠ g₂ ∨ c₁ ≠ c₂ →
      (p₁ < p₂ ↔ rrBefore groupOrd g₁ c₁ g₂ c₂) := by
  intro log g₁ c₁ g₂ c₂ p₁ p₂ hg₁ hg₂ hc₁ hc₂ hp₁ hp₂ h_spec h_ne
  set f₁ := rrFlatIndex groups g₁ c₁
  set f₂ := rrFlatIndex groups g₂ c₂
  set s := chainAt (rrSplitGroups groups) f₁ 0
  dsimp [outputPosRR, f₁, f₂] at hp₁ hp₂
  -- the finals bundle of the split system
  obtain ⟨blocks, finals, finalEventOf, chainOf, finalIdx, entryOf,
      h_shape, h_no_early, h_finals, h_nd, h_feq, h_block, h_match,
      h_chainOf_eq, h_eq_chainOf, h_pos⟩ :=
    groupSimulate_final_bundle T (rrSplitGroups groups)
      (rrActTick T groups) (rrGroupOrd groups groupOrd) rrWithinOrd rrPos
      (rrSplit_valid groups h_valid) (rrSplit_uniform groups)
      (rrSplit_act groups h_uniform T actTick h_act)
      (rrGroupOrd_perm groups groupOrd h_ord)
      (fun f h_f => rrWithinOrd_perm groups f h_f)
  have h_shape_lb : groupSimulate T (rrSplitGroups groups)
      (rrActTick T groups) (rrGroupOrd groups groupOrd) rrWithinOrd rrPos =
      logBlocks [] 0 blocks (T + 1) :=
    h_shape.trans (logBlocks_zero_eq_foldl blocks (T + 1)).symm
  have h_f₁ : f₁ < (rrSplitGroups groups).length :=
    rrFlatIndex_lt groups g₁ c₁ hg₁ hc₁
  have h_f₂ : f₂ < (rrSplitGroups groups).length :=
    rrFlatIndex_lt groups g₂ c₂ hg₂ hc₂
  have h_len₁ : (groupAt (rrSplitGroups groups) f₁).length = 1 := by
    dsimp [f₁]
    rw [rrGroupAt_flat groups g₁ c₁ hg₁ hc₁]
    simp
  have h_len₂ : (groupAt (rrSplitGroups groups) f₂).length = 1 := by
    dsimp [f₂]
    rw [rrGroupAt_flat groups g₂ c₂ hg₂ hc₂]
    simp
  have h_c₁₀ : 0 < (groupAt (rrSplitGroups groups) f₁).length := by
    omega
  have h_c₂₀ : 0 < (groupAt (rrSplitGroups groups) f₂).length := by
    omega
  have h_spec_split : chainAt (rrSplitGroups groups) f₁ 0 =
      chainAt (rrSplitGroups groups) f₂ 0 := by
    dsimp [f₁, f₂]
    rw [rrChainAt_flat_self groups g₁ c₁ hg₁ hc₁,
      rrChainAt_flat_self groups g₂ c₂ hg₂ hc₂]
    exact h_spec
  have h_delay : chainDelay (chainAt groups g₁ c₁) =
      chainDelay (chainAt groups g₂ c₂) := by
    rw [h_spec]
  have h_act_eq : rrActTick T groups f₁ = rrActTick T groups f₂ := by
    dsimp [rrActTick, f₁, f₂]
    rw [rrChainAt_flat_self groups g₁ c₁ hg₁ hc₁,
      rrChainAt_flat_self groups g₂ c₂ hg₂ hc₂, h_delay]
  have h_c₁_in : 0 ∈ rrWithinOrd f₁ := by
    dsimp [rrWithinOrd]
    simp
  have h_c₂_in : 0 ∈ rrWithinOrd f₂ := by
    dsimp [rrWithinOrd]
    simp
  have h_gord_nd : (rrGroupOrd groups groupOrd).Nodup :=
    rrGroupOrd_nodup groups groupOrd h_ord
  have h_within_nd : ∀ f, f < (rrSplitGroups groups).length →
      (rrWithinOrd f).Nodup := by
    intro f _
    dsimp [rrWithinOrd]
    simp
  -- the log-order bridge for the split system
  have h_bridge := groupBeforeSpec_iff_evBefore_discharged T
    (rrSplitGroups groups) (rrActTick T groups)
    (rrGroupOrd groups groupOrd) rrWithinOrd rrPos f₁ f₂ s h_f₁ h_f₂
    blocks h_shape_lb h_no_early finals h_nd chainOf finalEventOf
    finalIdx entryOf h_block h_match h_chainOf_eq h_eq_chainOf h_pos
  have h_g₁_ord : g₁ ∈ groupOrd :=
    (List.Perm.mem_iff h_ord).mpr (List.mem_range.mpr hg₁)
  have h_g₂_ord : g₂ ∈ groupOrd :=
    (List.Perm.mem_iff h_ord).mpr (List.mem_range.mpr hg₂)
  constructor
  · -- output order implies round-robin order
    intro h_lt
    have h_gbs : groupBeforeSpec log (rrSplitGroups groups) f₁ f₂ s := by
      intro ca cb h_ca h_cb h_sa h_sb
      have h_ca₀ : ca = 0 := by omega
      have h_cb₀ : cb = 0 := by omega
      subst h_ca₀
      subst h_cb₀
      exact ⟨p₁, p₂, hp₁, hp₂, h_lt⟩
    have h_ev : evBefore finals (finalEventOf f₁ 0) (finalEventOf f₂ 0) :=
      h_bridge.mp h_gbs 0 0 h_c₁₀ h_c₂₀ rfl h_spec_split.symm
    obtain h_rr | h_rr := rrBefore_total groupOrd g₁ c₁ g₂ c₂
      h_g₁_ord h_g₂_ord h_ne
    · exact h_rr
    · exfalso
      have h_burst_rev := rrBefore_burst_split groups groupOrd T
        g₂ c₂ g₁ c₁ hg₂ hg₁ hc₂ hc₁ h_ord h_delay.symm h_rr
      have h_ev_rev : evBefore finals (finalEventOf f₂ 0)
          (finalEventOf f₁ 0) :=
        evBefore_finals_of_burst (rrSplitGroups groups)
          (rrActTick T groups) (rrGroupOrd groups groupOrd) rrWithinOrd
          rrPos T (rrSplit_uniform groups)
          (rrSplit_act groups h_uniform T actTick h_act)
          finals h_finals finalEventOf h_feq
          f₂ 0 f₁ 0 h_f₂ h_c₂₀ h_f₁ h_c₁₀
          h_spec_split.symm h_act_eq.symm h_c₂_in h_c₁_in
          h_burst_rev h_gord_nd h_within_nd
      exact evBefore.asymm h_nd h_ev h_ev_rev
  · -- round-robin order implies output order
    intro h_rr
    have h_burst := rrBefore_burst_split groups groupOrd T g₁ c₁ g₂ c₂
      hg₁ hg₂ hc₁ hc₂ h_ord h_delay h_rr
    have h_ev : evBefore finals (finalEventOf f₁ 0) (finalEventOf f₂ 0) :=
      evBefore_finals_of_burst (rrSplitGroups groups) (rrActTick T groups)
        (rrGroupOrd groups groupOrd) rrWithinOrd rrPos T
        (rrSplit_uniform groups)
        (rrSplit_act groups h_uniform T actTick h_act)
        finals h_finals finalEventOf h_feq
        f₁ 0 f₂ 0 h_f₁ h_c₁₀ h_f₂ h_c₂₀
        h_spec_split h_act_eq h_c₁_in h_c₂_in
        h_burst h_gord_nd h_within_nd
    have h_gbs : groupBeforeSpec log (rrSplitGroups groups) f₁ f₂ s :=
      h_bridge.mpr (fun ca cb h_ca h_cb h_sa h_sb => by
        have h_ca₀ : ca = 0 := by omega
        have h_cb₀ : cb = 0 := by omega
        subst h_ca₀
        subst h_cb₀
        exact h_ev)
    obtain ⟨p, q, h_p, h_q, h_pq⟩ := h_gbs 0 0 h_c₁₀ h_c₂₀ rfl
      h_spec_split.symm
    have h_p_eq : p = p₁ := Option.some_inj.mp (h_p.symm.trans hp₁)
    have h_q_eq : q = p₂ := Option.some_inj.mp (h_q.symm.trans hp₂)
    rw [h_p_eq, h_q_eq] at h_pq
    exact h_pq
