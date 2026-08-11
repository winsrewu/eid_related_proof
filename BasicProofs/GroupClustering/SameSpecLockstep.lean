import BasicProofs.GroupClustering.FullTickStructure


open BasicRedstoneSim List

/-! # Group clustering — full lockstep of same-spec chains

Chains with the same `ChainSpec` move through the simulation in lockstep:
they activate at the same tick, every stage targets the same tick with the
same priority, and the relative order of their stage-`j` events in the queue
never changes while both events are queued.

Contents:

* same-spec consequences of the capstone hypotheses (shared activation tick,
  shared stage targets and priorities);
* small `evBefore` and list helpers;
* stage-event decoding from node ids;
* spawn characterization: a due stage event of stage `j ≤ m` spawns exactly
  the stage `j + 1` event of the same chain;
* queue health: every tick-start queue is duplicate-free (`Nodup`), each
  chain occupies at most one queue slot (`ChainOcc`), and every event decodes
  to a stage event (`EvDecoded`);
* the lockstep step: at a pop tick the stage `j + 1` spawns keep the order of
  the stage `j` events, through burst phases as well;
* the one-tick order-preservation theorem for non-due stage events;
* the final constancy theorem: for same-spec chains the relative order of
  their stage-`j` events is the same at every tick where both are queued.
-/

/-! ## Same-spec consequences -/

/-- In range, the `getD` result is a member of the list. -/
private theorem getD_mem {α : Type} (l : List α) (i : Nat) (d : α)
    (h : i < l.length) : l[i]?.getD d ∈ l := by
  revert i h
  induction l with
  | nil => intro i h; cases h
  | cons x xs ih =>
    intro i h
    cases i with
    | zero => simp
    | succ i' =>
      simp only [List.getElem?_cons_succ]
      apply List.mem_cons.mpr
      right
      exact ih i' (by simpa [List.length_cons] using h)

/-- An in-range `chainAt` is a member of its group. -/
theorem chainAt_mem (groups : List GroupSpec) (gi ci : Nat)
    (h_ci : ci < (groupAt groups gi).length) :
    chainAt groups gi ci ∈ groupAt groups gi := by
  dsimp only [chainAt]
  exact getD_mem (groupAt groups gi) ci defaultSpec h_ci

/-- A nonempty list has a head. -/
private theorem list_head_decomp {α : Type} (g : List α) (h_ne : g ≠ []) :
    ∃ c₀, g = c₀ :: g.drop 1 := by
  cases g with
  | nil => exact absurd rfl h_ne
  | cons c cs => exact ⟨c, rfl⟩

/-- Same spec in two groups means the same activation tick: both groups fire
    at `T - chainDelay s`. -/
theorem sameSpec_actTick_eq (groups : List GroupSpec) (T : Nat)
    (actTick : Nat → Nat)
    (h_uniform : ∀ gi (c₁ c₂ : ChainSpec), gi < groups.length →
        c₁ ∈ groupAt groups gi → c₂ ∈ groupAt groups gi →
        chainDelay c₁ = chainDelay c₂)
    (h_act : ∀ gi, gi < groups.length → groupAt groups gi ≠ [] →
        actTick gi + groupDelay (groupAt groups gi) = T)
    (g₁ c₁ g₂ c₂ : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_spec : chainAt groups g₁ c₁ = chainAt groups g₂ c₂) :
    actTick g₁ = actTick g₂ := by
  have h_s_mem₁ : chainAt groups g₁ c₁ ∈ groupAt groups g₁ :=
    chainAt_mem groups g₁ c₁ h_c₁
  have h_s_mem₂ : chainAt groups g₂ c₂ ∈ groupAt groups g₂ :=
    chainAt_mem groups g₂ c₂ h_c₂
  have h_ne₁ : groupAt groups g₁ ≠ [] := fun h => by
    have := h_c₁; rw [h] at this; cases this
  have h_ne₂ : groupAt groups g₂ ≠ [] := fun h => by
    have := h_c₂; rw [h] at this; cases this
  obtain ⟨c₀₁, h_g₁_eq⟩ := list_head_decomp (groupAt groups g₁) h_ne₁
  obtain ⟨c₀₂, h_g₂_eq⟩ := list_head_decomp (groupAt groups g₂) h_ne₂
  have h_delay₁ : groupDelay (groupAt groups g₁) =
      chainDelay (chainAt groups g₁ c₁) := by
    rw [h_g₁_eq]
    dsimp only [groupDelay]
    exact h_uniform g₁ c₀₁ (chainAt groups g₁ c₁) h_g₁ (by rw [h_g₁_eq]; simp)
      h_s_mem₁
  have h_delay₂ : groupDelay (groupAt groups g₂) =
      chainDelay (chainAt groups g₂ c₂) := by
    rw [h_g₂_eq]
    dsimp only [groupDelay]
    exact h_uniform g₂ c₀₂ (chainAt groups g₂ c₂) h_g₂ (by rw [h_g₂_eq]; simp)
      h_s_mem₂
  have h₁ := h_act g₁ h_g₁ h_ne₁
  have h₂ := h_act g₂ h_g₂ h_ne₂
  rw [h_delay₁] at h₁
  rw [h_delay₂, ← h_spec] at h₂
  omega

/-- Same spec means the same cumulative delay at every stage. -/
theorem sameSpec_stageCumDelay (groups : List GroupSpec)
    (g₁ c₁ g₂ c₂ j : Nat)
    (h_spec : chainAt groups g₁ c₁ = chainAt groups g₂ c₂) :
    stageCumDelay (chainAt groups g₁ c₁) j =
    stageCumDelay (chainAt groups g₂ c₂) j := by
  rw [h_spec]

/-- Same spec and same activation tick mean the same stage target. -/
theorem sameSpec_stageTarget (groups : List GroupSpec)
    (actTick : Nat → Nat) (g₁ c₁ g₂ c₂ j : Nat)
    (h_act_eq : actTick g₁ = actTick g₂)
    (h_spec : chainAt groups g₁ c₁ = chainAt groups g₂ c₂) :
    stageTarget actTick groups g₁ c₁ j =
    stageTarget actTick groups g₂ c₂ j := by
  dsimp [stageTarget]
  rw [h_act_eq, sameSpec_stageCumDelay groups g₁ c₁ g₂ c₂ j h_spec]

/-- Same spec means the same stage priority. -/
theorem sameSpec_stagePri (groups : List GroupSpec)
    (g₁ c₁ g₂ c₂ j : Nat)
    (h_spec : chainAt groups g₁ c₁ = chainAt groups g₂ c₂) :
    stagePri groups g₁ c₁ j = stagePri groups g₂ c₂ j := by
  dsimp [stagePri]
  rw [h_spec]

/-- Same spec and same activation tick mean the same stage window. -/
theorem sameSpec_stageWindow (groups : List GroupSpec)
    (actTick : Nat → Nat) (g₁ c₁ g₂ c₂ j t : Nat)
    (h_act_eq : actTick g₁ = actTick g₂)
    (h_spec : chainAt groups g₁ c₁ = chainAt groups g₂ c₂) :
    stageWindow actTick groups g₁ c₁ j t ↔
    stageWindow actTick groups g₂ c₂ j t := by
  dsimp [stageWindow]
  have h_prev : (if j = 0 then actTick g₁ else stageTarget actTick groups g₁ c₁ (j - 1)) =
      (if j = 0 then actTick g₂ else stageTarget actTick groups g₂ c₂ (j - 1)) := by
    split_ifs with h_j
    · rw [h_act_eq]
    · exact sameSpec_stageTarget groups actTick g₁ c₁ g₂ c₂ (j - 1) h_act_eq h_spec
  have h_this : stageTarget actTick groups g₁ c₁ j =
      stageTarget actTick groups g₂ c₂ j :=
    sameSpec_stageTarget groups actTick g₁ c₁ g₂ c₂ j h_act_eq h_spec
  rw [h_prev, h_this]

/-! ## Small list and `evBefore` helpers -/

/-- If the prefix `p` of `p ++ x :: q` is at least as long as `l`, then `x`
    sits in the appended part `r` of `l ++ r`. -/
private theorem mem_right_of_append_cons_split {α : Type} (l r p q : List α)
    (x : α) (h_eq : l ++ r = p ++ x :: q) (h_ge : l.length ≤ p.length) :
    x ∈ r := by
  induction l generalizing p r q with
  | nil =>
    simp only [List.nil_append] at h_eq
    rw [h_eq]
    exact List.mem_append_right p (List.mem_cons.mpr (Or.inl rfl))
  | cons a l' ih =>
    cases p with
    | nil =>
      exact absurd h_ge (by simp [List.length_cons])
    | cons b p' =>
      simp only [List.length_cons] at h_ge
      have h_len : l'.length ≤ p'.length := by omega
      simp only [List.cons_append] at h_eq
      have h_rest : l' ++ r = p' ++ x :: q := by
        simpa using congrArg List.tail h_eq
      -- the induction hypothesis binds the generalized vars as (r p q)
      exact ih r p' q h_rest h_len

/-- Append cancellation on the left. -/
private theorem append_left_cancel'' {α : Type} (l l₁ l₂ : List α)
    (h : l ++ l₁ = l ++ l₂) : l₁ = l₂ := by
  induction l generalizing l₁ l₂ with
  | nil => simpa using h
  | cons a l ih =>
    simp only [List.cons_append] at h
    injection h with _ h_tail
    exact ih l₁ l₂ h_tail

/-- Duplicate-free appends have disjoint parts. -/
theorem nodup_append_disjoint {α : Type} {l₁ l₂ : List α} {z : α}
    (h_nd : (l₁ ++ l₂).Nodup) (h₁ : z ∈ l₁) (h₂ : z ∈ l₂) : False := by
  induction l₁ generalizing l₂ with
  | nil => cases h₁
  | cons a l ih =>
    rw [List.cons_append, List.nodup_cons] at h_nd
    rw [List.mem_cons] at h₁
    rcases h₁ with rfl | h₁
    · exact h_nd.1 (List.mem_append.mpr (Or.inr h₂))
    · exact ih h_nd.2 h₁ h₂

/-- Splitting `l ++ r = p ++ x :: q` with `p` shorter than `l` puts `x` and
    the tail inside `l`. -/
private theorem append_cons_split {α : Type} (l r p q : List α) (x : α)
    (h_eq : l ++ r = p ++ x :: q) (h_n : p.length < l.length) :
    ∃ d, l = p ++ x :: d ∧ q = d ++ r := by
  induction p generalizing l r q with
  | nil =>
    simp only [List.nil_append] at h_eq
    cases l with
    | nil => omega
    | cons a l' =>
      simp only [List.cons_append] at h_eq
      injection h_eq with h_ax h_rest
      refine ⟨l', ?_, h_rest.symm⟩
      rw [← h_ax, List.nil_append]
  | cons b p' ih =>
    cases l with
    | nil =>
      dsimp at h_n
      omega
    | cons a l' =>
      simp only [List.length_cons] at h_n
      have h_len : p'.length < l'.length := by omega
      simp only [List.cons_append] at h_eq
      injection h_eq with h_ab h_rest
      obtain ⟨d, h_l', h_q⟩ := ih l' r q h_rest h_len
      refine ⟨d, ?_, h_q⟩
      rw [h_l', ← h_ab, List.cons_append]

/-- Converse of `evBefore.append_right`: when neither `x` nor `y` lies in the
    appended right part, `evBefore (l ++ r) x y` already holds in `l`. -/
theorem evBefore.of_append_right {l r : List ScheduledEvent} {x y : ScheduledEvent}
    (h_xr : x ∉ r) (h_yr : y ∉ r)
    (h : evBefore (l ++ r) x y) : evBefore l x y := by
  obtain ⟨p, q, h_eq, h_yq⟩ := h
  have h_n_lt : p.length < l.length := by
    by_contra h_ge
    exact h_xr (mem_right_of_append_cons_split l r p q x h_eq (by omega))
  obtain ⟨d, h_l_split, h_q_split⟩ := append_cons_split l r p q x h_eq h_n_lt
  refine ⟨p, d, h_l_split, ?_⟩
  rw [h_q_split] at h_yq
  rw [List.mem_append] at h_yq
  rcases h_yq with h_yq | h_yq
  · exact h_yq
  · exact absurd h_yq h_yr

/-- A head different from `x` can be dropped from `evBefore`. -/
theorem evBefore.of_cons_ne₂ {l : List ScheduledEvent} {a x y : ScheduledEvent}
    (h : evBefore (a :: l) x y) (h_ax : a ≠ x) : evBefore l x y := by
  rw [evBefore.cons_iff] at h
  rcases h with ⟨h_ax', _⟩ | h
  · exact absurd h_ax' h_ax
  · exact h

/-! ## Cumulative-delay monotonicity and window facts -/

/-- Sums of mapped prefixes grow with the prefix length. -/
private theorem sum_map_take_le {α : Type} (f : α → Nat) (l : List α) :
    ∀ (a b : Nat), a ≤ b →
    ((l.take a).map f).sum ≤ ((l.take b).map f).sum := by
  intro a b h_ab
  induction l generalizing a b with
  | nil => simp
  | cons x xs ih =>
    cases a with
    | zero => simp
    | succ a' =>
      cases b with
      | zero => omega
      | succ b' =>
        dsimp only [List.take]
        simp only [List.map_cons, List.sum_cons]
        exact Nat.add_le_add_left (ih a' b' (by omega)) (f x)

/-- The cumulative delay grows monotonically with the stage. -/
theorem stageCumDelay_mono (c : ChainSpec) (j₁ j₂ : Nat) (h_j : j₁ ≤ j₂) :
    stageCumDelay c j₁ ≤ stageCumDelay c j₂ := by
  dsimp only [stageCumDelay]
  simpa using sum_map_take_le id ((c.middleDelays.map PNat.val) ++
    [(c.lastDelay : Nat)]) j₁ j₂ h_j

/-- Stage targets grow monotonically with the stage. -/
theorem stageTarget_mono (actTick : Nat → Nat) (groups : List GroupSpec)
    (gi ci j₁ j₂ : Nat) (h_j : j₁ ≤ j₂) :
    stageTarget actTick groups gi ci j₁ ≤
    stageTarget actTick groups gi ci j₂ := by
  have h_cum := stageCumDelay_mono (chainAt groups gi ci) j₁ j₂ h_j
  dsimp only [stageTarget]
  omega

/-- Two different stages of the same chain are never queued at the same
    tick: their windows are disjoint. -/
theorem stageWindow_same_chain_disjoint (actTick : Nat → Nat)
    (groups : List GroupSpec) (gi ci j₁ j₂ t : Nat) (h_lt : j₁ < j₂)
    (h₁ : stageWindow actTick groups gi ci j₁ t)
    (h₂ : stageWindow actTick groups gi ci j₂ t) : False := by
  dsimp [stageWindow] at h₁ h₂
  have h_j₂_ne : j₂ ≠ 0 := by omega
  rw [if_neg h_j₂_ne] at h₂
  have h_mono := stageTarget_mono actTick groups gi ci j₁ (j₂ - 1) (by omega)
  omega

/-! ## Node-id intervals and stage-event decoding -/

/-- In range, `getD` equals the indexed element. -/
private theorem getD_getElem_eq {α : Type} (l : List α) (i : Nat) (d : α)
    (h : i < l.length) : l[i]?.getD d = l[i]'h := by
  revert i h
  induction l with
  | nil => intro i h; cases h
  | cons x xs ih =>
    intro i h
    cases i with
    | zero => simp
    | succ i' =>
      simp only [List.getElem?_cons_succ]
      exact ih i' (by simpa [List.length_cons] using h)

/-- Taking one more element appends that element. -/
private theorem take_succ_of_lt {α : Type} (l : List α) (i : Nat)
    (h_i : i < l.length) : l.take (i + 1) = l.take i ++ [l[i]'h_i] := by
  revert i h_i
  induction l with
  | nil => intro i h_i; cases h_i
  | cons x xs ih =>
    intro i h_i
    cases i with
    | zero => simp [List.take]
    | succ i' =>
      simp only [List.length_cons] at h_i
      dsimp only [List.take]
      congr 1
      exact ih i' (by omega)

/-- Every chain occupies at least four node ids. -/
private theorem chainNodeCount_ge4 (c : ChainSpec) : chainNodeCount c ≥ 4 := by
  dsimp [chainNodeCount]
  omega

/-- Moving to the next chain in a group advances the base id by the current
    chain's node count. -/
theorem chainBaseId_succ_chain (groups : List GroupSpec) (gi ci : Nat)
    (h_ci : ci < (groupAt groups gi).length) :
    chainBaseId groups gi (ci + 1) =
    chainBaseId groups gi ci + chainNodeCount (chainAt groups gi ci) := by
  dsimp [chainBaseId]
  rw [Nat.add_assoc, Nat.add_left_cancel_iff]
  set l := groupAt groups gi
  rw [take_succ_of_lt l ci h_ci, List.map_append, List.sum_append,
    Nat.add_left_cancel_iff]
  simp only [List.map_singleton]
  dsimp [chainAt]
  rw [getD_getElem_eq (groupAt groups gi) ci defaultSpec h_ci]

/-- If `(g₁, c₁)` precedes `(g₂, c₂)` lexicographically, then the id interval
    of chain `(g₁, c₁)` ends before the base id of chain `(g₂, c₂)`. -/
theorem chainBaseId_interval_le (groups : List GroupSpec)
    (g₁ c₁ g₂ c₂ : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_lex : g₁ < g₂ ∨ g₁ = g₂ ∧ c₁ < c₂) :
    chainBaseId groups g₁ c₁ + chainNodeCount (chainAt groups g₁ c₁) ≤
    chainBaseId groups g₂ c₂ := by
  rcases h_lex with h_lt | ⟨h_eq_g, h_lt_c⟩
  · -- different groups: g₁ < g₂
    have h_ge0 : chainBaseId groups g₂ 0 ≤ chainBaseId groups g₂ c₂ := by
      dsimp [chainBaseId]
      omega
    have h_Gsum := sum_map_take_le groupNodeCount groups (g₁ + 1) g₂ (by omega)
    have h_G : chainBaseId groups (g₁ + 1) 0 ≤ chainBaseId groups g₂ 0 := by
      dsimp [chainBaseId]
      omega
    have h_G_split : chainBaseId groups g₁ 0 + groupNodeCount (groupAt groups g₁) =
        chainBaseId groups (g₁ + 1) 0 := by
      dsimp [chainBaseId, groupAt, groupNodeCount]
      rw [take_succ_of_lt groups g₁ h_g₁, List.map_append, List.sum_append,
        List.map_singleton]
      rw [getD_getElem_eq groups g₁ ([] : GroupSpec) h_g₁]
      dsimp [groupNodeCount]
    have h_grp_ge : groupNodeCount (groupAt groups g₁) ≥
        (((groupAt groups g₁).take (c₁ + 1)).map chainNodeCount).sum := by
      dsimp [groupNodeCount]
      have h_take := sum_map_take_le chainNodeCount (groupAt groups g₁)
        (c₁ + 1) (groupAt groups g₁).length (by omega)
      have h_take_len : (groupAt groups g₁).take (groupAt groups g₁).length =
          groupAt groups g₁ := by
        induction (groupAt groups g₁) with
        | nil => simp
        | cons x xs ih => simp [ih]
      rwa [h_take_len] at h_take
    have h_chain_sum :
        (((groupAt groups g₁).take (c₁ + 1)).map chainNodeCount).sum =
        (((groupAt groups g₁).take c₁).map chainNodeCount).sum +
          chainNodeCount (chainAt groups g₁ c₁) := by
      dsimp [chainAt, groupAt]
      rw [take_succ_of_lt (groups[g₁]?.getD []) c₁ h_c₁, List.map_append,
        List.sum_append, List.map_singleton,
        getD_getElem_eq (groups[g₁]?.getD []) c₁ defaultSpec h_c₁]
      simp
    dsimp [chainBaseId] at h_ge0 h_G h_G_split h_chain_sum ⊢
    omega
  · -- same group
    subst h_eq_g
    have h_mono := sum_map_take_le chainNodeCount (groupAt groups g₁)
      (c₁ + 1) c₂ (by omega)
    have h_split := chainBaseId_succ_chain groups g₁ c₁ h_c₁
    dsimp [chainBaseId] at h_mono h_split ⊢
    omega

/-- A stage-event equality decodes the chain and the stage from the node
    id. -/
theorem stageEvent_injective (actTick : Nat → Nat) (groups : List GroupSpec)
    (g₁ c₁ j₁ g₂ c₂ j₂ : Nat)
    (h_g₁ : g₁ < groups.length) (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_g₂ : g₂ < groups.length) (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_j₁ : j₁ ≤ (chainAt groups g₁ c₁).middleDelays.length + 1)
    (h_j₂ : j₂ ≤ (chainAt groups g₂ c₂).middleDelays.length + 1)
    (h_ev : stageEvent actTick groups g₁ c₁ j₁ =
        stageEvent actTick groups g₂ c₂ j₂) :
    g₁ = g₂ ∧ c₁ = c₂ ∧ j₁ = j₂ := by
  have h_node : chainBaseId groups g₁ c₁ + 1 + j₁ =
      chainBaseId groups g₂ c₂ + 1 + j₂ := by
    have := congr_arg ScheduledEvent.nodeId h_ev
    dsimp [stageEvent] at this
    exact this
  have h_cnt₁ : chainNodeCount (chainAt groups g₁ c₁) =
      (chainAt groups g₁ c₁).middleDelays.length + 4 := rfl
  have h_cnt₂ : chainNodeCount (chainAt groups g₂ c₂) =
      (chainAt groups g₂ c₂).middleDelays.length + 4 := rfl
  by_cases h_lex₁₂ : g₁ < g₂ ∨ g₁ = g₂ ∧ c₁ < c₂
  · have h_le := chainBaseId_interval_le groups g₁ c₁ g₂ c₂ h_g₁ h_c₁ h_g₂ h_c₂
      h_lex₁₂
    omega
  · by_cases h_lex₂₁ : g₂ < g₁ ∨ g₂ = g₁ ∧ c₂ < c₁
    · have h_le := chainBaseId_interval_le groups g₂ c₂ g₁ c₁ h_g₂ h_c₂ h_g₁ h_c₁
        h_lex₂₁
      omega
    · have h_g : g₁ = g₂ := by omega
      have h_c : c₁ = c₂ := by omega
      refine ⟨h_g, h_c, ?_⟩
      rw [h_g, h_c] at h_node
      omega

/-- In a duplicate-free list, an element is not in its own tail split. -/
theorem nodup_cons_append_not_mem {α : Type} {l₁ l₂ : List α} {a : α}
    (h_nd : (l₁ ++ a :: l₂).Nodup) : a ∉ l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    rw [List.nil_append, List.nodup_cons] at h_nd
    exact h_nd.1
  | cons b l ih =>
    rw [List.cons_append, List.nodup_cons] at h_nd
    exact ih h_nd.2

/-! ## Spawn characterization -/

/-- Singleton lists are equal exactly when their elements are. -/
private theorem singleton_eq_singleton_iff {α : Type} (a b : α) :
    ([a] : List α) = [b] ↔ a = b := by
  constructor
  · intro h
    injection h
  · intro h
    rw [h]

/-- Firing the stage `j` event of a chain appends exactly the stage `j + 1`
    event of the same chain. -/
theorem stage_spawn (groups : List GroupSpec) (actTick : Nat → Nat)
    (v : World) (gi ci j : Nat)
    (h_gi : gi < groups.length) (h_ci : ci < (groupAt groups gi).length)
    (h_j : j ≤ (chainAt groups gi ci).middleDelays.length)
    (h_tick : v.tick = stageTarget actTick groups gi ci j)
    (h_layout : NodeLayoutOk groups v) :
    (v.onScheduledTick (chainBaseId groups gi ci + 1 + j)).events =
    v.events ++ [stageEvent actTick groups gi ci (j + 1)] := by
  dsimp [NodeLayoutOk] at h_layout
  obtain ⟨hL_obs, hL_mid, hL_last, _⟩ := h_layout
  set base := chainBaseId groups gi ci
  cases j with
  | zero =>
    obtain ⟨nd, h_gn, h_kind, h_outs⟩ := hL_obs gi ci h_gi h_ci
    by_cases h_len0 : (chainAt groups gi ci).middleDelays.length = 0
    · -- the observer fires the last repeater directly
      obtain ⟨nd₂, h_gn₂, h_kind₂, _⟩ := hL_last gi ci h_gi h_ci
      rw [h_len0] at h_gn₂
      rw [World.onScheduledTick_observer_spawns v (base + 1) (base + 2) nd nd₂
        (chainAt groups gi ci).lastDelay (-1) h_gn h_kind h_outs h_gn₂ h_kind₂]
      have h_cum1 : stageCumDelay (chainAt groups gi ci) 1 =
          stageCumDelay (chainAt groups gi ci) 0 +
            ((chainAt groups gi ci).lastDelay : Nat) := by
        have := stageCumDelay_succ_last (chainAt groups gi ci)
        rw [h_len0] at this
        exact this
      apply congrArg (fun l => v.events ++ l)
      rw [singleton_eq_singleton_iff]
      dsimp [stageEvent]
      have h_t : v.tick + ((chainAt groups gi ci).lastDelay : Nat) =
          stageTarget actTick groups gi ci 1 := by
        rw [h_tick]
        dsimp [stageTarget]
        rw [h_cum1]
        omega
      have h_p : (-1 : Int) = stagePri groups gi ci 1 := by
        dsimp [stagePri]
        split_ifs <;> omega
      have h_n : base + 2 = chainBaseId groups gi ci + 1 + 1 := by omega
      simp [h_t, h_p, h_n]
    · -- the observer fires the first middle repeater
      have h_0lt : 0 < (chainAt groups gi ci).middleDelays.length := by omega
      obtain ⟨nd₂, h_gn₂, h_kind₂, _⟩ := hL_mid gi ci 0 h_gi h_ci h_0lt
      rw [World.onScheduledTick_observer_spawns v (base + 1) (base + 2) nd nd₂
        ((chainAt groups gi ci).middleDelays[0]'h_0lt) (-3) h_gn h_kind h_outs
        h_gn₂ h_kind₂]
      apply congrArg (fun l => v.events ++ l)
      rw [singleton_eq_singleton_iff]
      dsimp [stageEvent]
      have h_t : v.tick + (((chainAt groups gi ci).middleDelays[0]'h_0lt) : Nat) =
          stageTarget actTick groups gi ci 1 := by
        rw [h_tick]
        dsimp [stageTarget]
        rw [stageCumDelay_succ_middle (chainAt groups gi ci) 0 h_0lt]
        omega
      have h_p : (-3 : Int) = stagePri groups gi ci 1 := by
        dsimp [stagePri]
        split_ifs <;> omega
      have h_n : base + 2 = chainBaseId groups gi ci + 1 + 1 := by omega
      simp [h_t, h_p, h_n]
  | succ j' =>
    rw [show base + 1 + (j' + 1) = base + 2 + j' from by omega]
    have h_j'_lt : j' < (chainAt groups gi ci).middleDelays.length := by omega
    obtain ⟨nd, h_gn, h_kind, h_outs⟩ := hL_mid gi ci j' h_gi h_ci h_j'_lt
    by_cases h_jlt : j' + 1 < (chainAt groups gi ci).middleDelays.length
    · -- the middle repeater fires the next middle repeater
      obtain ⟨nd₂, h_gn₂, h_kind₂, _⟩ := hL_mid gi ci (j' + 1) h_gi h_ci h_jlt
      have h_gn₂' : v.getNode (base + 3 + j') = some nd₂ := by
        rw [show base + 3 + j' = base + 2 + (j' + 1) by omega]
        exact h_gn₂
      rw [World.onScheduledTick_repeater_spawns v (base + 2 + j')
        (base + 3 + j') nd nd₂
        ((chainAt groups gi ci).middleDelays[j']'h_j'_lt) (-3) (-3)
        ((chainAt groups gi ci).middleDelays[j' + 1]'h_jlt)
        h_gn h_kind h_outs (by omega) h_gn₂' h_kind₂]
      apply congrArg (fun l => v.events ++ l)
      rw [singleton_eq_singleton_iff]
      dsimp [stageEvent]
      have h_t :
          v.tick + (((chainAt groups gi ci).middleDelays[j' + 1]'h_jlt) : Nat) =
          stageTarget actTick groups gi ci (j' + 1 + 1) := by
        rw [h_tick]
        dsimp [stageTarget]
        rw [stageCumDelay_succ_middle (chainAt groups gi ci) (j' + 1) h_jlt]
        omega
      have h_p : (-3 : Int) = stagePri groups gi ci (j' + 1 + 1) := by
        dsimp [stagePri]
        split_ifs <;> omega
      have h_n : base + 3 + j' = chainBaseId groups gi ci + 1 + (j' + 1 + 1) := by
        omega
      simp [h_t, h_p, h_n]
    · -- the last middle repeater fires the last repeater
      have h_jeq : j' + 1 = (chainAt groups gi ci).middleDelays.length := by omega
      obtain ⟨nd₂, h_gn₂, h_kind₂, _⟩ := hL_last gi ci h_gi h_ci
      have h_outs' :
          nd.outputs = [base + (chainAt groups gi ci).middleDelays.length + 2] := by
        rw [h_outs]
        congr 1
        omega
      rw [World.onScheduledTick_repeater_spawns v (base + 2 + j')
        (base + (chainAt groups gi ci).middleDelays.length + 2) nd nd₂
        ((chainAt groups gi ci).middleDelays[j']'h_j'_lt) (-3) (-1)
        (chainAt groups gi ci).lastDelay
        h_gn h_kind h_outs' (by omega) h_gn₂ h_kind₂]
      have h_cum : stageCumDelay (chainAt groups gi ci) (j' + 1 + 1) =
          stageCumDelay (chainAt groups gi ci) (j' + 1) +
            ((chainAt groups gi ci).lastDelay : Nat) := by
        have := stageCumDelay_succ_last (chainAt groups gi ci)
        rw [← h_jeq] at this
        exact this
      apply congrArg (fun l => v.events ++ l)
      rw [singleton_eq_singleton_iff]
      dsimp [stageEvent]
      have h_t : v.tick + ((chainAt groups gi ci).lastDelay : Nat) =
          stageTarget actTick groups gi ci (j' + 1 + 1) := by
        rw [h_tick]
        dsimp [stageTarget]
        rw [h_cum]
        omega
      have h_p : (-1 : Int) = stagePri groups gi ci (j' + 1 + 1) := by
        dsimp [stagePri]
        split_ifs <;> omega
      have h_n : base + (chainAt groups gi ci).middleDelays.length + 2 =
          chainBaseId groups gi ci + 1 + (j' + 1 + 1) := by omega
      simp [h_t, h_p, h_n]
