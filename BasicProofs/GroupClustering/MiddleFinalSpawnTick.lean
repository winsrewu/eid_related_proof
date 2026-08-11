import BasicProofs.GroupClustering.FinalsBackwardTransportIII

set_option linter.unusedVariables false

open BasicRedstoneSim List

/-! # Group clustering — the middle final's spawn tick is forced

The transport lemmas of FinalsBackwardTransportI–III carry the tick-`T` due-filter
betweenness of the three finals back to the reference stage-`m` pop
tick `τ := stageTarget actTick groups g₁ c₁ m`, under the side
condition that the middle final spawned no later than `τ` (premise
`h_spawn_e` of FinalsBackwardTransportII/III). This file DISCHARGES that side condition
by proving the middle final's spawn tick must EQUAL `τ`: both other
cases of the trichotomy contradict the due-filter betweenness.

## Case split over the spawn tick

Let `e` be the middle final (spawning at
`σ := stageTarget actTick groups gm cm (middleDelays.length)`) and let
the reference finals be `f₁ := stageEvent actTick groups g₁ c₁ (m + 1)`
(left) and `f₂ := stageEvent actTick groups g₂ c₂ (m + 1)` (right),
with the due-filter betweenness `f₁ < e` and `e < f₂` at `T`.

* `σ < τ` (`not_final_spawn_lt_of_dueBetween`): `e` is a survivor of
  tick `τ` (present since `σ + 1`, targeting `T > τ`), while `f₁` first
  appears at `τ + 1`. Survivors precede new spawns
  (`evBefore_survivor_before_spawn`, ForwardTransport), so `e < f₁` at `τ + 1`,
  persisting to `T` (`evBefore_gSimWorld_const`, OrderPreservationPremises) — contradicting
  `f₁ < e` at `T`.
* `σ > τ` (`not_final_spawn_gt_of_dueBetween`): with the right
  reference final already queued at `σ` (premise `h_f₂_first`: it
  spawns no later than `τ`), `f₂` is a survivor of tick `σ` while `e`
  first appears at `σ + 1`, so `f₂ < e` persists to `T` —
  contradicting `e < f₂` at `T`.

`final_spawnTick_eq_of_dueBetween` assembles the trichotomy. The
`σ > τ` branch needs the right-final availability conditionally
(`τ < σ → stageTarget actTick groups g₂ c₂ m + 1 ≤ σ`); assembly
discharges it from the equal ChainSpec of chains 1 and 3, which forces
the right spawn tick to `τ`. -/

/-- The middle final cannot have spawned strictly before the reference
    stage-`m` pop tick: as a survivor it would precede the left
    reference final's spawn, contradicting the due-filter betweenness
    at `T`. -/
theorem not_final_spawn_lt_of_dueBetween (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (T : Nat)
    (h_valid : ∀ gi (c : ChainSpec), gi < groups.length →
        c ∈ groupAt groups gi →
        (∀ d ∈ c.middleDelays, ValidDelay d) ∧ ValidDelay c.lastDelay)
    (h_uniform : ∀ gi (c₁ c₂ : ChainSpec), gi < groups.length →
        c₁ ∈ groupAt groups gi → c₂ ∈ groupAt groups gi →
        chainDelay c₁ = chainDelay c₂)
    (h_act : ∀ gi, gi < groups.length → groupAt groups gi ≠ [] →
        actTick gi + groupDelay (groupAt groups gi) = T)
    (h_ord : List.Perm groupOrd (List.range groups.length))
    (h_within : ∀ gi, gi < groups.length →
        List.Perm (withinOrd gi) (List.range (groupAt groups gi).length))
    (g₁ c₁ gm cm m : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_gm : gm < groups.length) (h_cm : cm < (groupAt groups gm).length)
    (h_m₁ : (chainAt groups g₁ c₁).middleDelays.length = m)
    (h_lt : stageTarget actTick groups gm cm
        ((chainAt groups gm cm).middleDelays.length) <
      stageTarget actTick groups g₁ c₁ m)
    (h_due : evBefore
        ((gSimWorld groups actTick groupOrd withinOrd pos T).events.filter
          (fun ev => ev.targetTick == T))
        (stageEvent actTick groups g₁ c₁ (m + 1))
        (stageEvent actTick groups gm cm
          ((chainAt groups gm cm).middleDelays.length + 1))) :
    False := by
  set τ := stageTarget actTick groups g₁ c₁ m
  set f₁ := stageEvent actTick groups g₁ c₁ (m + 1)
  set e := stageEvent actTick groups gm cm
    ((chainAt groups gm cm).middleDelays.length + 1)
  have h_τ_lt_T : τ < T :=
    stageTarget_lt_T_of_middleLen groups actTick T g₁ c₁ m h_g₁ h_c₁
      h_uniform h_act h_m₁
  -- e is a survivor of tick τ
  have h_e_τ : e ∈
      (gSimWorld groups actTick groupOrd withinOrd pos τ).events :=
    stageEvent_succ_mem_range_complete groups actTick groupOrd withinOrd
      pos h_valid h_ord h_within gm cm
      ((chainAt groups gm cm).middleDelays.length) h_gm h_cm (by omega) τ
      (Nat.succ_le_of_lt h_lt) (by
        rw [stageTarget_final_eq_T groups actTick T gm cm h_gm h_cm h_uniform h_act]
        exact Nat.le_of_lt h_τ_lt_T)
  have h_e_nd : e.targetTick ≠ τ := by
    dsimp [e, stageEvent]
    rw [stageTarget_final_eq_T groups actTick T gm cm h_gm h_cm h_uniform h_act]
    exact h_τ_lt_T.ne'
  -- f₁ first appears at τ + 1
  have h_f₁_next : f₁ ∈
      (gSimWorld groups actTick groupOrd withinOrd pos (τ + 1)).events :=
    stageEvent_succ_mem_range_complete groups actTick groupOrd withinOrd
      pos h_valid h_ord h_within g₁ c₁ m h_g₁ h_c₁ (by omega)
      (τ + 1) (by dsimp [τ]; omega)
      (Nat.succ_le_of_lt (stageTarget_lt_succ actTick groups g₁ c₁ m
        (by omega)))
  have h_f₁_not : f₁ ∉
      (gSimWorld groups actTick groupOrd withinOrd pos τ).events :=
    stageEvent_succ_not_mem_gSimWorld groups actTick groupOrd withinOrd
      pos g₁ c₁ m τ h_g₁ h_c₁ (by omega) rfl
  -- the survivor precedes the new spawn, and the order persists to T
  have h_e_f₁_T : evBefore
      (gSimWorld groups actTick groupOrd withinOrd pos T).events e f₁ :=
    evBefore_spawn_order groups actTick groupOrd withinOrd pos τ T
      h_valid e f₁ h_e_τ h_e_nd h_f₁_next h_f₁_not
      (Nat.succ_le_of_lt h_τ_lt_T)
      (by
        dsimp [e, stageEvent]
        rw [stageTarget_final_eq_T groups actTick T gm cm h_gm h_cm h_uniform h_act])
      (by
        dsimp [f₁, stageEvent]
        rw [show m + 1 = (chainAt groups g₁ c₁).middleDelays.length + 1 from by omega]
        rw [stageTarget_final_eq_T groups actTick T g₁ c₁ h_g₁ h_c₁ h_uniform h_act])
  -- but the due filter puts f₁ before e at T
  have h_f₁_e_T : evBefore
      (gSimWorld groups actTick groupOrd withinOrd pos T).events f₁ e :=
    evBefore.of_filter (fun ev => ev.targetTick == T) h_due
  have h_nd_T : (gSimWorld groups actTick groupOrd withinOrd pos T).events.Nodup :=
    gSimWorld_events_Nodup groups actTick groupOrd withinOrd pos T
      (Nodup.of_perm h_ord List.nodup_range)
      (fun gi h_gi => Nodup.of_perm (h_within gi h_gi) List.nodup_range)
  exact evBefore.asymm h_nd_T h_f₁_e_T h_e_f₁_T

/-- The middle final cannot have spawned strictly after the reference
    stage-`m` pop tick when the right reference final was already
    queued at its spawn tick: as a survivor, the right final would
    precede the middle final's spawn, contradicting the due-filter
    betweenness at `T`. -/
theorem not_final_spawn_gt_of_dueBetween (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (T : Nat)
    (h_valid : ∀ gi (c : ChainSpec), gi < groups.length →
        c ∈ groupAt groups gi →
        (∀ d ∈ c.middleDelays, ValidDelay d) ∧ ValidDelay c.lastDelay)
    (h_uniform : ∀ gi (c₁ c₂ : ChainSpec), gi < groups.length →
        c₁ ∈ groupAt groups gi → c₂ ∈ groupAt groups gi →
        chainDelay c₁ = chainDelay c₂)
    (h_act : ∀ gi, gi < groups.length → groupAt groups gi ≠ [] →
        actTick gi + groupDelay (groupAt groups gi) = T)
    (h_ord : List.Perm groupOrd (List.range groups.length))
    (h_within : ∀ gi, gi < groups.length →
        List.Perm (withinOrd gi) (List.range (groupAt groups gi).length))
    (g₁ c₁ gm cm g₂ c₂ m : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_gm : gm < groups.length) (h_cm : cm < (groupAt groups gm).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_m₂ : (chainAt groups g₂ c₂).middleDelays.length = m)
    (h_f₂_first : stageTarget actTick groups g₂ c₂ m + 1 ≤
        stageTarget actTick groups gm cm
          ((chainAt groups gm cm).middleDelays.length))
    (h_due : evBefore
        ((gSimWorld groups actTick groupOrd withinOrd pos T).events.filter
          (fun ev => ev.targetTick == T))
        (stageEvent actTick groups gm cm
          ((chainAt groups gm cm).middleDelays.length + 1))
        (stageEvent actTick groups g₂ c₂ (m + 1))) :
    False := by
  set σ := stageTarget actTick groups gm cm
    ((chainAt groups gm cm).middleDelays.length)
  set f₂ := stageEvent actTick groups g₂ c₂ (m + 1)
  set e := stageEvent actTick groups gm cm
    ((chainAt groups gm cm).middleDelays.length + 1)
  have h_σ_lt_T : σ < T := by
    dsimp [σ]
    rw [← stageTarget_final_eq_T groups actTick T gm cm h_gm h_cm h_uniform h_act]
    exact stageTarget_lt_succ actTick groups gm cm
      ((chainAt groups gm cm).middleDelays.length) (by omega)
  -- f₂ is a survivor of tick σ
  have h_f₂_σ : f₂ ∈
      (gSimWorld groups actTick groupOrd withinOrd pos σ).events :=
    stageEvent_succ_mem_range_complete groups actTick groupOrd withinOrd
      pos h_valid h_ord h_within g₂ c₂ m h_g₂ h_c₂ (by omega) σ
      h_f₂_first (by
        rw [show m + 1 = (chainAt groups g₂ c₂).middleDelays.length + 1 from by omega]
        rw [stageTarget_final_eq_T groups actTick T g₂ c₂ h_g₂ h_c₂ h_uniform h_act]
        exact Nat.le_of_lt h_σ_lt_T)
  have h_f₂_nd : f₂.targetTick ≠ σ := by
    dsimp [f₂, stageEvent]
    rw [show m + 1 = (chainAt groups g₂ c₂).middleDelays.length + 1 from by omega]
    rw [stageTarget_final_eq_T groups actTick T g₂ c₂ h_g₂ h_c₂ h_uniform h_act]
    exact h_σ_lt_T.ne'
  -- e first appears at σ + 1
  have h_e_next : e ∈
      (gSimWorld groups actTick groupOrd withinOrd pos (σ + 1)).events :=
    stageEvent_succ_mem_range_complete groups actTick groupOrd withinOrd
      pos h_valid h_ord h_within gm cm
      ((chainAt groups gm cm).middleDelays.length) h_gm h_cm (by omega)
      (σ + 1) (by dsimp [σ]; omega)
      (Nat.succ_le_of_lt (by
        dsimp [σ]
        exact stageTarget_lt_succ actTick groups gm cm
          ((chainAt groups gm cm).middleDelays.length) (by omega)))
  have h_e_not : e ∉
      (gSimWorld groups actTick groupOrd withinOrd pos σ).events :=
    stageEvent_succ_not_mem_gSimWorld groups actTick groupOrd withinOrd
      pos gm cm ((chainAt groups gm cm).middleDelays.length) σ h_gm h_cm
      (by omega) rfl
  -- the survivor precedes the new spawn, and the order persists to T
  have h_f₂_e_T : evBefore
      (gSimWorld groups actTick groupOrd withinOrd pos T).events f₂ e :=
    evBefore_spawn_order groups actTick groupOrd withinOrd pos σ T
      h_valid f₂ e h_f₂_σ h_f₂_nd h_e_next h_e_not
      (Nat.succ_le_of_lt h_σ_lt_T)
      (by
        dsimp [f₂, stageEvent]
        rw [show m + 1 = (chainAt groups g₂ c₂).middleDelays.length + 1 from by omega]
        rw [stageTarget_final_eq_T groups actTick T g₂ c₂ h_g₂ h_c₂ h_uniform h_act])
      (by
        dsimp [e, stageEvent]
        rw [stageTarget_final_eq_T groups actTick T gm cm h_gm h_cm h_uniform h_act])
  -- but the due filter puts e before f₂ at T
  have h_e_f₂_T : evBefore
      (gSimWorld groups actTick groupOrd withinOrd pos T).events e f₂ :=
    evBefore.of_filter (fun ev => ev.targetTick == T) h_due
  have h_nd_T : (gSimWorld groups actTick groupOrd withinOrd pos T).events.Nodup :=
    gSimWorld_events_Nodup groups actTick groupOrd withinOrd pos T
      (Nodup.of_perm h_ord List.nodup_range)
      (fun gi h_gi => Nodup.of_perm (h_within gi h_gi) List.nodup_range)
  exact evBefore.asymm h_nd_T h_e_f₂_T h_f₂_e_T

/-- The middle final's spawn tick equals the reference stage-`m` pop
    tick: spawning earlier contradicts the left betweenness, spawning
    later contradicts the right betweenness. The conditional premise
    supplies the right reference final's availability in the later
    branch; assembly discharges it from the equal ChainSpec of chains
    1 and 3 (which forces the right spawn tick to `τ`). -/
theorem final_spawnTick_eq_of_dueBetween (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (T : Nat)
    (h_valid : ∀ gi (c : ChainSpec), gi < groups.length →
        c ∈ groupAt groups gi →
        (∀ d ∈ c.middleDelays, ValidDelay d) ∧ ValidDelay c.lastDelay)
    (h_uniform : ∀ gi (c₁ c₂ : ChainSpec), gi < groups.length →
        c₁ ∈ groupAt groups gi → c₂ ∈ groupAt groups gi →
        chainDelay c₁ = chainDelay c₂)
    (h_act : ∀ gi, gi < groups.length → groupAt groups gi ≠ [] →
        actTick gi + groupDelay (groupAt groups gi) = T)
    (h_ord : List.Perm groupOrd (List.range groups.length))
    (h_within : ∀ gi, gi < groups.length →
        List.Perm (withinOrd gi) (List.range (groupAt groups gi).length))
    (g₁ c₁ gm cm g₂ c₂ m : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_gm : gm < groups.length) (h_cm : cm < (groupAt groups gm).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_m₁ : (chainAt groups g₁ c₁).middleDelays.length = m)
    (h_m₂ : (chainAt groups g₂ c₂).middleDelays.length = m)
    (h_f₂_first : stageTarget actTick groups g₁ c₁ m <
        stageTarget actTick groups gm cm
          ((chainAt groups gm cm).middleDelays.length) →
      stageTarget actTick groups g₂ c₂ m + 1 ≤
        stageTarget actTick groups gm cm
          ((chainAt groups gm cm).middleDelays.length))
    (h_due_left : evBefore
        ((gSimWorld groups actTick groupOrd withinOrd pos T).events.filter
          (fun ev => ev.targetTick == T))
        (stageEvent actTick groups g₁ c₁ (m + 1))
        (stageEvent actTick groups gm cm
          ((chainAt groups gm cm).middleDelays.length + 1)))
    (h_due_right : evBefore
        ((gSimWorld groups actTick groupOrd withinOrd pos T).events.filter
          (fun ev => ev.targetTick == T))
        (stageEvent actTick groups gm cm
          ((chainAt groups gm cm).middleDelays.length + 1))
        (stageEvent actTick groups g₂ c₂ (m + 1))) :
    stageTarget actTick groups gm cm
        ((chainAt groups gm cm).middleDelays.length) =
      stageTarget actTick groups g₁ c₁ m := by
  by_cases h_lt : stageTarget actTick groups gm cm
      ((chainAt groups gm cm).middleDelays.length) <
    stageTarget actTick groups g₁ c₁ m
  · exfalso
    exact not_final_spawn_lt_of_dueBetween groups actTick groupOrd
      withinOrd pos T h_valid h_uniform h_act h_ord h_within
      g₁ c₁ gm cm m h_g₁ h_c₁ h_gm h_cm h_m₁ h_lt h_due_left
  · by_cases h_gt : stageTarget actTick groups g₁ c₁ m <
      stageTarget actTick groups gm cm
        ((chainAt groups gm cm).middleDelays.length)
    · exfalso
      exact not_final_spawn_gt_of_dueBetween groups actTick groupOrd
        withinOrd pos T h_valid h_uniform h_act h_ord h_within
        g₁ c₁ gm cm g₂ c₂ m h_g₁ h_c₁ h_gm h_cm h_g₂ h_c₂ h_m₂
        (h_f₂_first h_gt) h_due_right
    · omega
