import BasicProofs.GroupClustering.FinalTransition
import BasicProofs.GroupClustering.ConverseSpawn

set_option linter.unusedVariables false

open BasicRedstoneSim List

/-! # Group clustering — converse spawn at the final stage

This file handles the boundary case for the converse spawn theorem at
the last stage. The middle-stage converse spawn theorem
(`converse_spawn_gSimBurst` of ConverseSpawn) accepts events with priority
-3. At the final stage, the spawned events carry priority -1. The
final-stage converse spawn theorem accepts priority -1 instead.

## Scope

* `ConverseSpawnFinal` — the bundled converse spawn conclusion at the
  final stage: event identity, parent order, prefix and target match.
* `Pri1FinalOf_of_converseSpawnFinal` — assembles `Pri1FinalOf` from
  the bundled conclusion.
* `Pri1FinalOf_of_rawConverseSpawn` — assembles `Pri1FinalOf` from
  the raw converse spawn data plus a `MiddleBlock` classification of
  the stage-`m` parent. This is the key assembly lemma. It shows that
  the only missing piece for the full converse theorem is the converse
  spawn conclusion itself (which requires private helper lemmas from
  ConverseSpawn).

## Status

The unconditional converse spawn theorem for priority -1
(`converse_spawn_gSimBurst_final`) requires private helper lemmas
from ConverseSpawn (`popSpawnAcc_left_converse`,
`popSpawnAcc_right_converse`, `popSeqFuel_priority_mono`,
`gSimBurst_filter_split`). Those lemmas will be exported in a future
revision. The present file proves the conditional form and stays
green. -/


/-! ## Bundled converse spawn conclusion -/

/-- The converse spawn conclusion at the final stage, bundled with the
    length, prefix, and target conditions needed for `Pri1FinalOf`.
    The event `e` equals the stage-(m+1) event of chain `(g, c)`. The
    stage-`m` event of `(g, c)` sits between the two reference
    stage-`m` events in the due filter. The chain `(g, c)` has the
    same number of middle delays as `(g₁, c₁)`. The prefix and target
    at stage `m + 1` agree. -/
def ConverseSpawnFinal (groups : List GroupSpec) (actTick : Nat → Nat)
    (w : World) (g₁ c₁ g₂ c₂ m : Nat) (e : ScheduledEvent) : Prop :=
  ∃ g c, g < groups.length ∧ c < (groupAt groups g).length ∧
    (chainAt groups g c).middleDelays.length =
      (chainAt groups g₁ c₁).middleDelays.length ∧
    e = stageEvent actTick groups g c (m + 1) ∧
    prefixDelays groups g c (m + 1) =
      prefixDelays groups g₁ c₁ (m + 1) ∧
    stageTarget actTick groups g c (m + 1) =
      stageTarget actTick groups g₁ c₁ (m + 1) ∧
    evBefore (w.events.filter (fun ev => ev.targetTick == w.tick))
      (stageEvent actTick groups g₁ c₁ m)
      (stageEvent actTick groups g c m) ∧
    evBefore (w.events.filter (fun ev => ev.targetTick == w.tick))
      (stageEvent actTick groups g c m)
      (stageEvent actTick groups g₂ c₂ m)


/-! ## Assembly lemmas -/

/-- `ConverseSpawnFinal` implies `Pri1FinalOf`. The witness chain and
    the prefix and target conditions transfer directly. -/
theorem Pri1FinalOf_of_converseSpawnFinal (groups : List GroupSpec)
    (actTick : Nat → Nat) (w : World)
    (g₁ c₁ g₂ c₂ m : Nat) (e : ScheduledEvent)
    (h_cs : ConverseSpawnFinal groups actTick w g₁ c₁ g₂ c₂ m e) :
    Pri1FinalOf groups actTick g₁ c₁ m e := by
  rcases h_cs with ⟨g, c, h_g, h_c, h_len, h_ev, h_pref, h_tgt, _, _⟩
  exact ⟨g, c, h_g, h_c, h_len, h_ev, h_pref, h_tgt⟩

/-- `ConverseSpawnFinal` plus the reference target gives
    `IsFinalEvent`. Chains through `Pri1FinalOf_to_IsFinalEvent` of
    FinalTransition. -/
theorem IsFinalEvent_of_converseSpawnFinal (groups : List GroupSpec)
    (actTick : Nat → Nat) (T : Nat) (w : World)
    (g₁ c₁ g₂ c₂ m : Nat) (e : ScheduledEvent)
    (h_T : stageTarget actTick groups g₁ c₁ (m + 1) = T)
    (h_m : (chainAt groups g₁ c₁).middleDelays.length = m)
    (h_cs : ConverseSpawnFinal groups actTick w g₁ c₁ g₂ c₂ m e) :
    IsFinalEvent groups actTick T e := by
  have h_fin : Pri1FinalOf groups actTick g₁ c₁ m e :=
    Pri1FinalOf_of_converseSpawnFinal groups actTick w
      g₁ c₁ g₂ c₂ m e h_cs
  exact Pri1FinalOf_to_IsFinalEvent groups actTick T g₁ c₁ m e
    h_T h_m h_fin

/-- The witness chain of `ConverseSpawnFinal` has `m` middle delays.
    The event is the last-stage event of that chain. -/
theorem converseSpawnFinal_length (groups : List GroupSpec)
    (actTick : Nat → Nat) (w : World)
    (g₁ c₁ g₂ c₂ m : Nat) (e : ScheduledEvent)
    (h_m : (chainAt groups g₁ c₁).middleDelays.length = m)
    (h_cs : ConverseSpawnFinal groups actTick w g₁ c₁ g₂ c₂ m e) :
    ∃ g c, g < groups.length ∧ c < (groupAt groups g).length ∧
      (chainAt groups g c).middleDelays.length = m ∧
      e = stageEvent actTick groups g c (m + 1) := by
  rcases h_cs with ⟨g, c, h_g, h_c, h_len, h_ev, _, _, _, _⟩
  exact ⟨g, c, h_g, h_c, h_len.trans h_m, h_ev⟩

/-- The event of `ConverseSpawnFinal` carries priority -1 when the
    reference chain has `m` middle delays. -/
theorem converseSpawnFinal_priority (groups : List GroupSpec)
    (actTick : Nat → Nat) (w : World)
    (g₁ c₁ g₂ c₂ m : Nat) (e : ScheduledEvent)
    (h_m : (chainAt groups g₁ c₁).middleDelays.length = m)
    (h_cs : ConverseSpawnFinal groups actTick w g₁ c₁ g₂ c₂ m e) :
    e.priority = (-1 : Int) := by
  rcases h_cs with ⟨g, c, _, _, h_len, h_ev, _, _, _, _⟩
  rw [h_ev]
  dsimp [stageEvent]
  have h_gc_m : (chainAt groups g c).middleDelays.length = m :=
    h_len.trans h_m
  rw [← h_gc_m]
  exact stagePri_last groups g c


/-! ## Raw converse spawn assembly

The key assembly lemma. Given the raw converse spawn conclusion
(event identity and parent order) plus the `MiddleBlock`
classification of the stage-`m` parent, derive `Pri1FinalOf`. This
shows that the only gap to the full converse theorem is the converse
spawn conclusion itself. -/

/-- A priority-(-1) stage-(m+1) event forces `m` to reach the end of
    the middle delays. The stage index `m + 1` exceeds the middle
    delay count. -/
private theorem pri1_stageSucc_ge_length (groups : List GroupSpec)
    (actTick : Nat → Nat) (g c m : Nat)
    (h_pri : (stageEvent actTick groups g c (m + 1)).priority =
        (-1 : Int)) :
    (chainAt groups g c).middleDelays.length ≤ m := by
  dsimp [stageEvent, stagePri] at h_pri
  -- After dsimp, the outer if (j = 0) is auto-reduced for j = m + 1.
  -- h_pri : (if m + 1 ≤ length then -3 else -1) = -1
  by_cases h₁ : m + 1 ≤ (chainAt groups g c).middleDelays.length
  · rw [if_pos h₁] at h_pri
    omega
  · rw [if_neg h₁] at h_pri
    omega

/-- If `take m` of one list equals another list of length `m`, the
    first list has at least `m` elements. -/
private theorem length_ge_of_take_eq_full {α : Type} (l₁ l₂ : List α)
    (m : Nat) (h_len : l₁.length = m)
    (h_take : l₂.take m = l₁) : l₂.length ≥ m := by
  have h_take_len : (l₂.take m).length = m := by
    rw [h_take, h_len]
  have h_min : (l₂.take m).length = min m l₂.length := by
    rw [List.length_take]
  rw [h_min] at h_take_len
  omega

/-- `take m` of a list of length `m` returns the full list. -/
private theorem take_length_self {α : Type} (l : List α) :
    l.take l.length = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons, List.take]
    rw [ih]

/-- The main assembly lemma. Given:
    - `e = stageEvent ... (m + 1)` (the event identity),
    - `e.priority = -1` (the final priority),
    - `e.targetTick = T` (the event targets the output tick),
    - the stage-`m` parent is classified by `MiddleBlock` (same prefix
      class as the reference chain at stage `m`),
    - the parent has priority -3 (a middle-stage event),
    derive `Pri1FinalOf`. The prefix and length conditions follow from
    the `MiddleBlock` classification. The target condition follows
    from `e.targetTick = T` and the reference target. -/
theorem Pri1FinalOf_of_rawConverseSpawn (groups : List GroupSpec)
    (actTick : Nat → Nat) (w : World)
    (T : Nat) (g₁ c₁ g₂ c₂ g c m : Nat) (e : ScheduledEvent)
    (h_g₁ : g₁ < groups.length)
    (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_g : g < groups.length)
    (h_c : c < (groupAt groups g).length)
    (h_m : (chainAt groups g₁ c₁).middleDelays.length = m)
    (h_m_ge : 1 ≤ m)
    (h_e_eq : e = stageEvent actTick groups g c (m + 1))
    (h_e_pri : e.priority = (-1 : Int))
    (h_e_tgt : e.targetTick = T)
    (h_T : stageTarget actTick groups g₁ c₁ (m + 1) = T)
    (h_parent_pri : (stageEvent actTick groups g c m).priority =
        (-3 : Int))
    (h_parent_mb : MiddleBlock groups actTick T g₁ c₁ m
        (stageEvent actTick groups g c m)) :
    Pri1FinalOf groups actTick g₁ c₁ m e := by
  -- Step 1: the event's priority forces middleDelays.length ≤ m.
  have h_len_le : (chainAt groups g c).middleDelays.length ≤ m := by
    have h := h_e_pri
    rw [h_e_eq] at h
    exact pri1_stageSucc_ge_length groups actTick g c m h
  -- Step 2: the MiddleBlock classification gives the prefix match at
  -- stage m. Case (a) (IsFinalEvent) contradicts the parent's
  -- priority -3.
  have h_pref_m : prefixDelays groups g c m =
      prefixDelays groups g₁ c₁ m := by
    rcases h_parent_mb with h_fin | h_mid
    · exfalso
      exact IsFinalEvent_priority_ne_middle groups actTick T
        (stageEvent actTick groups g c m) h_fin h_parent_pri
    · -- h_mid : ∃ g' c', ... ∧ stageEvent ... g c m = stageEvent ... g' c' m
      -- ∧ prefixDelays ... g' c' m = prefixDelays ... g₁ c₁ m
      obtain ⟨g', c', h_g', h_c', h_ev_eq, _, _, h_pref⟩ := h_mid
      -- The witness chain has priority -3 at stage m.
      have h_pri_g'c'_raw :
          (stageEvent actTick groups g' c' m).priority = (-3 : Int) := by
        rw [← h_ev_eq]
        exact h_parent_pri
      have h_j_bound :
          m ≤ (chainAt groups g' c').middleDelays.length + 1 := by
        dsimp [stageEvent, stagePri] at h_pri_g'c'_raw
        split_ifs at h_pri_g'c'_raw <;> omega
      -- Identify (g', c') with (g, c) via stageEvent_injective.
      have h_j_gc : m ≤ (chainAt groups g c).middleDelays.length + 1 := by
        have : (stageEvent actTick groups g c m).priority = (-3 : Int) :=
          h_parent_pri
        dsimp [stageEvent, stagePri] at this
        split_ifs at this <;> omega
      obtain ⟨h_g_eq, h_c_eq, _⟩ :=
        stageEvent_injective actTick groups g c m g' c' m
          h_g h_c h_g' h_c' h_j_gc h_j_bound h_ev_eq
      rw [h_g_eq, h_c_eq]
      exact h_pref
  -- Step 3: the prefix match at m with the reference having m middle
  -- delays forces the chain (g,c) to have at least m middle delays.
  have h_len_ge : (chainAt groups g c).middleDelays.length ≥ m := by
    dsimp [prefixDelays] at h_pref_m
    have h_ref_take :
        (chainAt groups g₁ c₁).middleDelays.take m =
          (chainAt groups g₁ c₁).middleDelays := by
      have : m = (chainAt groups g₁ c₁).middleDelays.length := by omega
      rw [this]
      exact take_length_self _
    have h_gc_take :
        (chainAt groups g c).middleDelays.take m =
          (chainAt groups g₁ c₁).middleDelays := by
      rw [h_pref_m, h_ref_take]
    exact length_ge_of_take_eq_full
      (chainAt groups g₁ c₁).middleDelays
      (chainAt groups g c).middleDelays m h_m h_gc_take
  -- Step 4: combine to get equal lengths.
  have h_len_eq : (chainAt groups g c).middleDelays.length =
      (chainAt groups g₁ c₁).middleDelays.length := by
    rw [h_m]
    omega
  -- Step 5: the full middle delays are equal, so the prefixes at
  -- stage m + 1 are equal.
  have h_full_eq : (chainAt groups g c).middleDelays =
      (chainAt groups g₁ c₁).middleDelays := by
    dsimp [prefixDelays] at h_pref_m
    have h_take_gc :
        (chainAt groups g c).middleDelays.take m =
          (chainAt groups g c).middleDelays := by
      have : m = (chainAt groups g c).middleDelays.length := by omega
      rw [this]
      exact take_length_self _
    have h_take_ref :
        (chainAt groups g₁ c₁).middleDelays.take m =
          (chainAt groups g₁ c₁).middleDelays := by
      have : m = (chainAt groups g₁ c₁).middleDelays.length := by omega
      rw [this]
      exact take_length_self _
    rw [← h_take_gc, h_pref_m, h_take_ref]
  have h_pref_succ : prefixDelays groups g c (m + 1) =
      prefixDelays groups g₁ c₁ (m + 1) := by
    dsimp [prefixDelays]
    have h_t_gc : (chainAt groups g c).middleDelays.take (m + 1) =
        (chainAt groups g c).middleDelays := by
      rw [List.take_of_length_le (by omega)]
    have h_t_ref :
        (chainAt groups g₁ c₁).middleDelays.take (m + 1) =
          (chainAt groups g₁ c₁).middleDelays := by
      rw [List.take_of_length_le (by omega)]
    rw [h_t_gc, h_t_ref]
    exact h_full_eq
  -- Step 6: the target at m + 1 matches because e.targetTick = T and
  -- the reference targets T at stage m + 1.
  have h_tgt_succ : stageTarget actTick groups g c (m + 1) =
      stageTarget actTick groups g₁ c₁ (m + 1) := by
    have h₁ : e.targetTick = stageTarget actTick groups g c (m + 1) := by
      rw [h_e_eq]
      rfl
    rw [← h₁, h_e_tgt, h_T]
  -- Assemble Pri1FinalOf.
  refine ⟨g, c, h_g, h_c, h_len_eq, h_e_eq, h_pref_succ, h_tgt_succ⟩

/-- The conditional converse for `FinalBlockBetween`. If the raw
    converse spawn data holds and the parent is classified by
    `MiddleBlock`, then `Pri1FinalOf` follows. The event's target
    comes from `FinalBlockBetween`. -/
theorem FinalBlockBetween_converse_of_rawSpawn
    (groups : List GroupSpec) (actTick : Nat → Nat)
    (T : Nat) (queue : List ScheduledEvent) (w : World)
    (g₁ c₁ g₂ c₂ g c m : Nat) (e : ScheduledEvent)
    (h_g₁ : g₁ < groups.length)
    (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_g : g < groups.length)
    (h_c : c < (groupAt groups g).length)
    (h_m : (chainAt groups g₁ c₁).middleDelays.length = m)
    (h_m_ge : 1 ≤ m)
    (h_T : stageTarget actTick groups g₁ c₁ (m + 1) = T)
    (h_blk : FinalBlockBetween groups actTick T queue
        g₁ c₁ g₂ c₂ m e)
    (h_e_eq : e = stageEvent actTick groups g c (m + 1))
    (h_parent_pri : (stageEvent actTick groups g c m).priority =
        (-3 : Int))
    (h_parent_mb : MiddleBlock groups actTick T g₁ c₁ m
        (stageEvent actTick groups g c m)) :
    Pri1FinalOf groups actTick g₁ c₁ m e := by
  have h_e_pri : e.priority = (-1 : Int) := h_blk.1
  have h_e_tgt : e.targetTick = T := h_blk.2.1
  exact Pri1FinalOf_of_rawConverseSpawn groups actTick w T
    g₁ c₁ g₂ c₂ g c m e
    h_g₁ h_c₁ h_g h_c h_m h_m_ge
    h_e_eq h_e_pri h_e_tgt h_T
    h_parent_pri h_parent_mb


/-! ## Basic structural lemmas for the final stage -/

/-- A stage-(m+1) event of a chain with `m` middle delays has the
    same priority as the last stage of that chain: -1. -/
theorem stageEvent_pri_lastSucc (groups : List GroupSpec)
    (actTick : Nat → Nat) (g c m : Nat)
    (h_m : (chainAt groups g c).middleDelays.length = m) :
    (stageEvent actTick groups g c (m + 1)).priority = (-1 : Int) := by
  dsimp [stageEvent]
  rw [← h_m]
  exact stagePri_last groups g c

/-- The target of a stage-(m+1) event of a chain with `m` middle
    delays is the final target of that chain. -/
theorem stageEvent_target_lastSucc (groups : List GroupSpec)
    (actTick : Nat → Nat) (g c m : Nat)
    (h_m : (chainAt groups g c).middleDelays.length = m) :
    stageTarget actTick groups g c (m + 1) =
    stageTarget actTick groups g c
      ((chainAt groups g c).middleDelays.length + 1) := by
  rw [h_m]

/-- A stage-(m+1) event of a chain with `m` middle delays is a final
    event targeting its own target tick. -/
theorem stageEvent_isFinal_lastSucc (groups : List GroupSpec)
    (actTick : Nat → Nat) (g c m : Nat)
    (h_g : g < groups.length) (h_c : c < (groupAt groups g).length)
    (h_m : (chainAt groups g c).middleDelays.length = m) :
    IsFinalEvent groups actTick
      (stageTarget actTick groups g c (m + 1))
      (stageEvent actTick groups g c (m + 1)) := by
  refine ⟨g, c, h_g, h_c, ?_, ?_⟩
  · congr 1
    omega
  · congr 1
    omega

/-- Two chains with equal `ChainSpec` have the same target at every
    stage. -/
theorem stageTarget_of_chainSpec_eq (groups : List GroupSpec)
    (actTick : Nat → Nat) (g₁ c₁ g₂ c₂ j : Nat)
    (h_chain : chainAt groups g₁ c₁ = chainAt groups g₂ c₂)
    (h_act : actTick g₁ = actTick g₂) :
    stageTarget actTick groups g₁ c₁ j =
    stageTarget actTick groups g₂ c₂ j := by
  dsimp [stageTarget]
  rw [h_act]
  congr 1
  rw [h_chain]

/-- Prefix equality at stage `m + 1` for chains with `m` middle delays
    reduces to full middle-delay equality. -/
theorem prefixDelays_final_eq_middleDelays_eq (groups : List GroupSpec)
    (g₁ c₁ g₂ c₂ m : Nat)
    (h_m₁ : (chainAt groups g₁ c₁).middleDelays.length = m)
    (h_m₂ : (chainAt groups g₂ c₂).middleDelays.length = m)
    (h_pref : prefixDelays groups g₁ c₁ (m + 1) =
        prefixDelays groups g₂ c₂ (m + 1)) :
    (chainAt groups g₁ c₁).middleDelays =
      (chainAt groups g₂ c₂).middleDelays := by
  dsimp [prefixDelays] at h_pref
  have h_t1 :
      (chainAt groups g₁ c₁).middleDelays.take (m + 1) =
        (chainAt groups g₁ c₁).middleDelays := by
    rw [List.take_of_length_le (by omega)]
  have h_t2 :
      (chainAt groups g₂ c₂).middleDelays.take (m + 1) =
        (chainAt groups g₂ c₂).middleDelays := by
    rw [List.take_of_length_le (by omega)]
  rw [h_t1, h_t2] at h_pref
  exact h_pref


/-! ## Spec equality from the converse spawn conclusion

The converse spawn conclusion carries the betweenness of the two
stage-`m` parents in the due filter of `w`. Both parents therefore
target the tick of `w`, so the witness chain and the reference chain
have equal targets at stage `m`. With equal middle delays (from the
prefix match at stage `m + 1`) this forces equal activation ticks,
and the target match at stage `m + 1` then forces equal last delays:
the witness chain has the same `ChainSpec` as the reference chain.

This is the last-delay step of the clustering argument. The
`Pri1FinalOf` projection alone does not determine the last delay;
the stage-`m` betweenness inside `ConverseSpawnFinal` is what fixes
the activation tick. -/

/-- A true `==` comparison of two Nats forces equality. -/
private theorem nat_eq_of_beq_true (a b : Nat) (h : (a == b) = true) :
    a = b := by
  by_contra h_ne
  have h_false : (a == b) = false := by simp [h_ne]
  rw [h_false] at h
  cases h

/-- Two chain specs with equal fields are equal. (`ChainSpec` carries
    no extensionality attribute.) -/
private theorem ChainSpec_eq_of_fields_eq (a b : ChainSpec)
    (h_md : a.middleDelays = b.middleDelays)
    (h_last : a.lastDelay = b.lastDelay) : a = b := by
  cases a with
  | mk md₁ ld₁ =>
    cases b with
    | mk md₂ ld₂ =>
      dsimp at h_md h_last
      rw [h_md, h_last]

/-- The witness chain of `ConverseSpawnFinal` targets the same tick
    as the reference chain at stage `m`. Repackages the bundled
    conclusion and adds the stage-`m` target equality. -/
theorem ConverseSpawnFinal_stageTarget_middle (groups : List GroupSpec)
    (actTick : Nat → Nat) (w : World)
    (g₁ c₁ g₂ c₂ m : Nat) (e : ScheduledEvent)
    (h_cs : ConverseSpawnFinal groups actTick w g₁ c₁ g₂ c₂ m e) :
    ∃ g c, g < groups.length ∧ c < (groupAt groups g).length ∧
      (chainAt groups g c).middleDelays.length =
        (chainAt groups g₁ c₁).middleDelays.length ∧
      e = stageEvent actTick groups g c (m + 1) ∧
      prefixDelays groups g c (m + 1) =
        prefixDelays groups g₁ c₁ (m + 1) ∧
      stageTarget actTick groups g c (m + 1) =
        stageTarget actTick groups g₁ c₁ (m + 1) ∧
      stageTarget actTick groups g c m =
        stageTarget actTick groups g₁ c₁ m := by
  rcases h_cs with ⟨g, c, h_g, h_c, h_len, h_ev, h_pref, h_tgt, h_b1, _⟩
  refine ⟨g, c, h_g, h_c, h_len, h_ev, h_pref, h_tgt, ?_⟩
  have h_t1 : stageTarget actTick groups g₁ c₁ m = w.tick := by
    have h_mem := evBefore.mem_left h_b1
    rw [List.mem_filter] at h_mem
    dsimp [stageEvent] at h_mem
    exact nat_eq_of_beq_true (stageTarget actTick groups g₁ c₁ m)
      w.tick h_mem.2
  have h_t2 : stageTarget actTick groups g c m = w.tick := by
    have h_mem := evBefore.mem_right h_b1
    rw [List.mem_filter] at h_mem
    dsimp [stageEvent] at h_mem
    exact nat_eq_of_beq_true (stageTarget actTick groups g c m)
      w.tick h_mem.2
  rw [h_t2, h_t1]

/-- The witness chain of `ConverseSpawnFinal` has the same `ChainSpec`
    as the reference chain. The middle delays come from the prefix
    match at stage `m + 1`. The stage-`m` target equality then gives
    equal activation ticks, and the stage-`(m + 1)` target equality
    gives equal last delays. -/
theorem chainSpec_eq_of_ConverseSpawnFinal (groups : List GroupSpec)
    (actTick : Nat → Nat) (w : World)
    (g₁ c₁ g₂ c₂ m : Nat) (e : ScheduledEvent)
    (h_m : (chainAt groups g₁ c₁).middleDelays.length = m)
    (h_cs : ConverseSpawnFinal groups actTick w g₁ c₁ g₂ c₂ m e) :
    ∃ g c, g < groups.length ∧ c < (groupAt groups g).length ∧
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
  refine ⟨g, c, h_g, h_c, h_ev, ?_⟩
  exact ChainSpec_eq_of_fields_eq (chainAt groups g c)
    (chainAt groups g₁ c₁) h_md (Subtype.ext h_last_nat)

/-- Assemble `ConverseSpawnFinal` from the raw converse spawn data.
    Mirrors `FinalBlockBetween_converse_of_rawSpawn`, but keeps the
    stage-`m` betweenness and packages the full conclusion. The
    length, prefix, and target facts at stage `m + 1` come from the
    same argument as in `Pri1FinalOf_of_rawConverseSpawn`; the
    stage-`m` betweenness is supplied directly. -/
theorem ConverseSpawnFinal_of_rawSpawn (groups : List GroupSpec)
    (actTick : Nat → Nat) (w : World)
    (T : Nat) (queue : List ScheduledEvent)
    (g₁ c₁ g₂ c₂ g c m : Nat) (e : ScheduledEvent)
    (h_g₁ : g₁ < groups.length)
    (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_g : g < groups.length)
    (h_c : c < (groupAt groups g).length)
    (h_m : (chainAt groups g₁ c₁).middleDelays.length = m)
    (h_m_ge : 1 ≤ m)
    (h_T : stageTarget actTick groups g₁ c₁ (m + 1) = T)
    (h_blk : FinalBlockBetween groups actTick T queue
        g₁ c₁ g₂ c₂ m e)
    (h_e_eq : e = stageEvent actTick groups g c (m + 1))
    (h_parent_pri : (stageEvent actTick groups g c m).priority =
        (-3 : Int))
    (h_parent_mb : MiddleBlock groups actTick T g₁ c₁ m
        (stageEvent actTick groups g c m))
    (h_b1 : evBefore (w.events.filter (fun ev => ev.targetTick == w.tick))
        (stageEvent actTick groups g₁ c₁ m)
        (stageEvent actTick groups g c m))
    (h_b2 : evBefore (w.events.filter (fun ev => ev.targetTick == w.tick))
        (stageEvent actTick groups g c m)
        (stageEvent actTick groups g₂ c₂ m)) :
    ConverseSpawnFinal groups actTick w g₁ c₁ g₂ c₂ m e := by
  have h_fin : Pri1FinalOf groups actTick g₁ c₁ m e :=
    FinalBlockBetween_converse_of_rawSpawn groups actTick T queue w
      g₁ c₁ g₂ c₂ g c m e
      h_g₁ h_c₁ h_g h_c h_m h_m_ge h_T h_blk
      h_e_eq h_parent_pri h_parent_mb
  rcases h_fin with ⟨g', c', h_g', h_c', h_len', h_ev', h_pref, h_tgt⟩
  -- the witness of the assembly is (g, c) itself
  have h_len_gc : m ≤ (chainAt groups g c).middleDelays.length := by
    dsimp [stageEvent, stagePri] at h_parent_pri
    split_ifs at h_parent_pri <;> omega
  obtain ⟨h_g_eq, h_c_eq, _⟩ :=
    stageEvent_injective actTick groups g' c' (m + 1) g c (m + 1)
      h_g' h_c' h_g h_c (by omega) (by omega)
      (h_ev'.symm.trans h_e_eq)
  rw [h_g_eq] at h_g' h_c' h_len' h_pref h_tgt
  rw [h_c_eq] at h_c' h_len' h_pref h_tgt
  exact ⟨g, c, h_g', h_c', h_len', h_e_eq, h_pref, h_tgt, h_b1, h_b2⟩
