import BasicProofs.GroupClustering.Definitions

open BasicRedstoneSim List

/-! # Group clustering — round-robin activation via singleton split

A round-robin group system: each group is a list of IDENTICAL-SPEC
observer chains. At a tick, all groups activating at that tick fire in
one atomic round-robin batch: round `k` enqueues the `k`-th chain's
observer event of every group (in a fixed group order), exhausted
groups drop out, and no queue processing happens inside the batch.

Implementation: the round-robin system is DEFINED as the ordinary
group simulation on singleton-split groups. Splitting group `gi`'s
`n` chains into `n` one-chain groups and activating those singletons
group-major in the round-robin enumeration order with zero pos
insertion produces exactly the round-robin enqueue sequence:

* one singleton activation = one observer enqueue (withinOrd `[0]`);
* zero pos insertion = no processing inside the batch;
* the singleton group order = round-robin enumeration.

The translation is therefore definitional; this file supplies the
index bookkeeping (flat indices, group-of-flat recovery) and the
round-robin order facts the capstone corollaries consume.
-/

/-! ## Split definitions -/

/-- Split every group into one-chain groups, preserving chain order
    within each group and group order. -/
def rrSplitGroups : List GroupSpec → List GroupSpec
  | [] => []
  | g :: gs =>
    (g.map (fun c => ([c] : GroupSpec)) : List GroupSpec) ++
      rrSplitGroups gs

/-- Total number of chains in the bundle. -/
def rrTotalChains (groups : List GroupSpec) : Nat :=
  (groups.map List.length).sum

/-- Number of chains in groups `0 ..< gi`. -/
def rrPrefixLen (groups : List GroupSpec) (gi : Nat) : Nat :=
  ((groups.take gi).map List.length).sum

/-- Flat (split) group index of chain `ci` of group `gi`: the number
    of chains in earlier groups plus `ci`. -/
def rrFlatIndex (groups : List GroupSpec) (gi ci : Nat) : Nat :=
  rrPrefixLen groups gi + ci

/-- Activation tick of split group `f`: `T - chainDelay` of its single
    chain. Well-defined under the capstone premises (delay ≤ T). -/
def rrActTick (T : Nat) (groups : List GroupSpec) (f : Nat) : Nat :=
  T - chainDelay (chainAt (rrSplitGroups groups) f 0)

/-- One round-robin round: the flat indices of every group's `k`-th
    chain, in `groupOrd` order. -/
def rrRound (groups : List GroupSpec) (groupOrd : List Nat) (k : Nat) :
    List Nat :=
  groupOrd.filterMap (fun gi =>
    if decide (k < (groupAt groups gi).length)
    then some (rrFlatIndex groups gi k)
    else none)

/-- The singleton-group activation order: rounds concatenated. The
    bound `rrTotalChains` rounds suffice (every round past the longest
    group is empty). -/
def rrGroupOrd (groups : List GroupSpec) (groupOrd : List Nat) :
    List Nat :=
  (List.range (rrTotalChains groups)).flatMap (rrRound groups groupOrd)

/-- Within-group order of the split singletons (trivial). -/
def rrWithinOrd : Nat → List Nat := fun _ => [0]

/-- No pos insertion inside the atomic batch. -/
def rrPos : Nat → List Nat := fun _ => []

/-- The round-robin simulation: the ordinary group simulation on the
    singleton split. -/
def groupSimulateRR (T : Nat) (groups : List GroupSpec)
    (groupOrd : List Nat) : List String :=
  groupSimulate T (rrSplitGroups groups) (rrActTick T groups)
    (rrGroupOrd groups groupOrd) rrWithinOrd rrPos

/-- Output position of bundle chain `(gi, ci)`: the split log position
    of its singleton. -/
def outputPosRR (log : List String) (groups : List GroupSpec)
    (gi ci : Nat) : Option Nat :=
  outputPos log (rrFlatIndex groups gi ci) 0

/-! ## Round-robin order -/

/-- Bundle-level round-robin activation order: round (chain index)
    first, then position in `groupOrd`. -/
def rrBefore (groupOrd : List Nat) (g₁ c₁ g₂ c₂ : Nat) : Prop :=
  c₁ < c₂ ∨
    (c₁ = c₂ ∧ ∃ pre mid post, groupOrd = pre ++ g₁ :: mid ++ g₂ :: post)

/-! ## Index bookkeeping -/

private theorem splitGroups_cons (g : GroupSpec) (gs : List GroupSpec) :
    rrSplitGroups (g :: gs) =
      (g.map (fun c => ([c] : GroupSpec)) : List GroupSpec) ++
        rrSplitGroups gs := by
  simp [rrSplitGroups]

theorem rrSplitGroups_length (groups : List GroupSpec) :
    (rrSplitGroups groups).length = rrTotalChains groups := by
  induction groups with
  | nil => rfl
  | cons g gs ih =>
    simp [rrSplitGroups, rrTotalChains, ih]
    dsimp [List.map, List.sum]

private theorem flatIndex_cons_succ (g : GroupSpec) (gs : List GroupSpec)
    (gi ci : Nat) :
    rrFlatIndex (g :: gs) (gi + 1) ci =
      g.length + rrFlatIndex gs gi ci := by
  dsimp [rrFlatIndex, rrPrefixLen, List.map, List.sum]
  omega

/-- Flat indices land inside the split list. -/
theorem rrFlatIndex_lt (groups : List GroupSpec) (gi ci : Nat)
    (h_gi : gi < groups.length) (h_ci : ci < (groupAt groups gi).length) :
    rrFlatIndex groups gi ci < (rrSplitGroups groups).length := by
  revert gi ci h_gi h_ci
  induction groups with
  | nil => intro gi; simp [groupAt]
  | cons g gs ih =>
    intro gi ci h_gi h_ci
    cases gi with
    | zero =>
      have h_g : groupAt (g :: gs) 0 = g := by simp [groupAt]
      rw [h_g] at h_ci
      dsimp [rrFlatIndex, rrPrefixLen, List.map, List.sum]
      simp [splitGroups_cons, List.length_append, List.length_map]
      omega
    | succ gi' =>
      have h_gi' : gi' < gs.length := by
        simp [List.length] at h_gi
        omega
      have h_ih := ih gi' ci h_gi' (by simpa [groupAt] using h_ci)
      simp [flatIndex_cons_succ, splitGroups_cons, List.length_append,
        List.length_map] at h_ih ⊢
      omega

private theorem getElem?_append_front {α : Type} (l r : List α) (n : Nat)
    (h : n < l.length) :
    (l ++ r)[n]? = l[n]? := by
  revert n h
  induction l with
  | nil => intro n h; simp [List.length] at h
  | cons a l ih =>
    intro n h
    cases n with
    | zero => rfl
    | succ n' => exact ih n' (by simpa [List.length] using h)

private theorem getElem?_append_back {α : Type} (l r : List α) (n : Nat)
    (h : l.length ≤ n) :
    (l ++ r)[n]? = r[n - l.length]? := by
  revert n h
  induction l with
  | nil => intro n h; rfl
  | cons a l ih =>
    intro n h
    cases n with
    | zero => simp [List.length] at h
    | succ n' =>
      have h' : l.length ≤ n' := by simpa [List.length] using h
      simpa [List.length] using ih n' h'

private theorem getElem?_map {α β : Type} (f : α → β) (l : List α)
    (n : Nat) :
    (l.map f)[n]? = (l[n]?).map f := by
  induction l generalizing n with
  | nil => rfl
  | cons a l ih =>
    cases n with
    | zero => rfl
    | succ n' => exact ih n'

private theorem getElem?_map_singleton_get {α : Type} (g : List α)
    (i : Nat) (h : i < g.length) :
    g[i]?.map (fun c => ([c] : List α)) =
      some (g[i]'h :: ([] : List α)) := by
  have h_q : g[i]? = some (g[i]'h) := List.getElem?_eq_getElem h
  rw [h_q]
  rfl

private theorem getD_eq_getElem {α : Type} (l : List α) (i : Nat) (d : α)
    (h : i < l.length) :
    (l[i]?.getD d) = l[i]'h := by
  rw [List.getElem?_eq_getElem h]
  rfl

private theorem getD_mem {α : Type} (l : List α) (i : Nat) (d : α)
    (h : i < l.length) :
    (l[i]?.getD d) ∈ l := by
  rw [getD_eq_getElem l i d h]
  exact List.getElem_mem h

/-- The split list's option-get at a flat index is the singleton of the
    bundle chain. -/
theorem rrSplitGroups_getElem? (groups : List GroupSpec) (gi ci : Nat)
    (h_gi : gi < groups.length) (h_ci : ci < (groupAt groups gi).length) :
    (rrSplitGroups groups)[rrFlatIndex groups gi ci]? =
    some [chainAt groups gi ci] := by
  revert gi ci h_gi h_ci
  induction groups with
  | nil => intro gi; simp [groupAt]
  | cons g gs ih =>
    intro gi ci h_gi h_ci
    simp only [splitGroups_cons]
    cases gi with
    | zero =>
      have h_g : groupAt (g :: gs) 0 = g := by simp [groupAt]
      rw [h_g] at h_ci
      dsimp [rrFlatIndex, rrPrefixLen, List.map, List.sum]
      rw [zero_add]
      refine (getElem?_append_front (g.map (fun c => ([c] : GroupSpec)))
        (rrSplitGroups gs) ci (by rw [List.length_map]; exact h_ci)).trans ?_
      refine (getElem?_map (fun c => ([c] : GroupSpec)) g ci).trans ?_
      rw [getElem?_map_singleton_get g ci h_ci]
      congr 1
      have h_chain : chainAt (g :: gs) 0 ci =
          (show List ChainSpec from g)[ci]'h_ci := by
        dsimp [chainAt]
        rw [h_g, getD_eq_getElem (show List ChainSpec from g) ci
          defaultSpec h_ci]
      rw [h_chain]
    | succ gi' =>
      have h_gi' : gi' < gs.length := by
        simp [List.length] at h_gi
        omega
      have h_ci' : ci < (groupAt gs gi').length := by
        simpa [groupAt] using h_ci
      have h_ih := ih gi' ci h_gi' h_ci'
      rw [flatIndex_cons_succ]
      refine (getElem?_append_back (g.map (fun c => ([c] : GroupSpec)))
        (rrSplitGroups gs) (g.length + rrFlatIndex gs gi' ci) (by
          simp)).trans ?_
      have h_rhs : some [chainAt (g :: gs) (gi' + 1) ci] =
          some [chainAt gs gi' ci] := by
        simp [chainAt, groupAt]
      rw [h_rhs]
      have h_idx : g.length + rrFlatIndex gs gi' ci -
          (g.map (fun c => ([c] : GroupSpec))).length =
        rrFlatIndex gs gi' ci := by
        rw [List.length_map]
        omega
      rw [h_idx]
      exact h_ih

/-- Group-level form: the split group at a flat index is the singleton
    of the bundle chain. -/
theorem rrGroupAt_flat (groups : List GroupSpec) (gi ci : Nat)
    (h_gi : gi < groups.length) (h_ci : ci < (groupAt groups gi).length) :
    groupAt (rrSplitGroups groups) (rrFlatIndex groups gi ci) =
    [chainAt groups gi ci] := by
  dsimp [groupAt]
  rw [rrSplitGroups_getElem? groups gi ci h_gi h_ci]
  rfl

/-- getElem form of `rrSplitGroups_getElem?`. -/
theorem rrSplitGroups_get (groups : List GroupSpec) (gi ci : Nat)
    (h_gi : gi < groups.length) (h_ci : ci < (groupAt groups gi).length) :
    (rrSplitGroups groups)[rrFlatIndex groups gi ci]'(
      rrFlatIndex_lt groups gi ci h_gi h_ci) =
    [chainAt groups gi ci] := by
  have h_q := rrSplitGroups_getElem? groups gi ci h_gi h_ci
  rw [List.getElem?_eq_getElem (rrFlatIndex_lt groups gi ci h_gi h_ci)]
    at h_q
  exact Option.some.inj h_q

/-- Every split index comes from a bundle chain. -/
theorem rrSplit_exists (groups : List GroupSpec) (f : Nat)
    (h_f : f < (rrSplitGroups groups).length) :
    ∃ gi ci, gi < groups.length ∧ ci < (groupAt groups gi).length ∧
      rrFlatIndex groups gi ci = f := by
  revert f h_f
  induction groups with
  | nil => intro f; simp [rrSplitGroups]
  | cons g gs ih =>
    intro f h_f
    simp [splitGroups_cons, List.length_append, List.length_map] at h_f
    by_cases h_lt : f < g.length
    · refine ⟨0, f, by simp [List.length], ?_, ?_⟩
      · simpa [groupAt] using h_lt
      · dsimp [rrFlatIndex, rrPrefixLen, List.map, List.sum]
        omega
    · obtain ⟨gi, ci, h_gi, h_ci, h_eq⟩ := ih (f - g.length) (by omega)
      refine ⟨gi + 1, ci, by simp [List.length]; omega, h_ci, ?_⟩
      simp [flatIndex_cons_succ]
      omega

/-- The split chain at index `f` is the bundle chain it came from. -/
theorem rrChainAt_flat (groups : List GroupSpec) (f : Nat)
    (h_f : f < (rrSplitGroups groups).length) :
    ∃ gi ci, gi < groups.length ∧ ci < (groupAt groups gi).length ∧
      rrFlatIndex groups gi ci = f ∧
      chainAt (rrSplitGroups groups) f 0 = chainAt groups gi ci := by
  obtain ⟨gi, ci, h_gi, h_ci, h_eq⟩ := rrSplit_exists groups f h_f
  refine ⟨gi, ci, h_gi, h_ci, h_eq, ?_⟩
  rw [← h_eq]
  dsimp [chainAt]
  rw [rrGroupAt_flat groups gi ci h_gi h_ci]
  simp [chainAt]

/-! ## Discharging the split premises -/

theorem rrSplit_valid (groups : List GroupSpec)
    (h_valid : ∀ gi (c : ChainSpec), gi < groups.length →
        c ∈ groupAt groups gi →
        (∀ d ∈ c.middleDelays, ValidDelay d) ∧ ValidDelay c.lastDelay) :
    ∀ f (c : ChainSpec), f < (rrSplitGroups groups).length →
      c ∈ groupAt (rrSplitGroups groups) f →
      (∀ d ∈ c.middleDelays, ValidDelay d) ∧ ValidDelay c.lastDelay := by
  intro f c h_f h_mem
  obtain ⟨gi, ci, h_gi, h_ci, h_eq, h_spec⟩ := rrChainAt_flat groups f h_f
  rw [← h_eq, rrGroupAt_flat groups gi ci h_gi h_ci] at h_mem
  have h_c : c = chainAt groups gi ci := by
    simpa using h_mem
  rw [h_c]
  have h_mem_bundle : chainAt groups gi ci ∈ groupAt groups gi := by
    dsimp [chainAt]
    exact getD_mem (groupAt groups gi) ci defaultSpec h_ci
  exact h_valid gi (chainAt groups gi ci) h_gi h_mem_bundle

theorem rrSplit_uniform (groups : List GroupSpec) :
    ∀ f (c₁ c₂ : ChainSpec), f < (rrSplitGroups groups).length →
      c₁ ∈ groupAt (rrSplitGroups groups) f →
      c₂ ∈ groupAt (rrSplitGroups groups) f →
      chainDelay c₁ = chainDelay c₂ := by
  intro f c₁ c₂ h_f h_m₁ h_m₂
  obtain ⟨gi, ci, h_gi, h_ci, h_eq, h_spec⟩ := rrChainAt_flat groups f h_f
  rw [← h_eq, rrGroupAt_flat groups gi ci h_gi h_ci] at h_m₁ h_m₂
  have h_c₁ : c₁ = chainAt groups gi ci := by simpa using h_m₁
  have h_c₂ : c₂ = chainAt groups gi ci := by simpa using h_m₂
  rw [h_c₁, h_c₂]

theorem rrSplit_act (groups : List GroupSpec)
    (h_uniform : ∀ gi (c₁ c₂ : ChainSpec), gi < groups.length →
        c₁ ∈ groupAt groups gi → c₂ ∈ groupAt groups gi →
        chainDelay c₁ = chainDelay c₂)
    (T : Nat) (actTick : Nat → Nat)
    (h_act : ∀ gi, gi < groups.length → groupAt groups gi ≠ [] →
        actTick gi + groupDelay (groupAt groups gi) = T) :
    ∀ f, f < (rrSplitGroups groups).length →
      groupAt (rrSplitGroups groups) f ≠ [] →
      rrActTick T groups f + groupDelay (groupAt (rrSplitGroups groups) f) =
        T := by
  intro f h_f h_ne
  obtain ⟨gi, ci, h_gi, h_ci, h_eq, h_spec⟩ := rrChainAt_flat groups f h_f
  have h_delay : chainDelay (chainAt groups gi ci) ≤ T := by
    have h_head : groupAt groups gi ≠ [] := by
      intro h_empty
      rw [h_empty] at h_ci
      simp at h_ci
    have h_act_gi := h_act gi h_gi h_head
    have h_gdelay : groupDelay (groupAt groups gi) =
        chainDelay (chainAt groups gi ci) := by
      cases h_decomp : groupAt groups gi with
      | nil => contradiction
      | cons c_head cs =>
        have h_head_mem : c_head ∈ groupAt groups gi := by
          rw [h_decomp]; simp
        have h_ci_mem : chainAt groups gi ci ∈ groupAt groups gi := by
          dsimp [chainAt]
          exact getD_mem (groupAt groups gi) ci defaultSpec h_ci
        dsimp [groupDelay]
        exact h_uniform gi c_head (chainAt groups gi ci) h_gi h_head_mem
          h_ci_mem
    rw [h_gdelay] at h_act_gi
    omega
  dsimp [rrActTick]
  rw [h_spec]
  rw [← h_eq, rrGroupAt_flat groups gi ci h_gi h_ci]
  dsimp [groupDelay]
  omega

/-! ## Round-robin activation order facts -/

theorem mem_split {α : Type} {x : α} {l : List α} (h : x ∈ l) :
    ∃ a b, l = a ++ x :: b := by
  induction l with
  | nil => cases h
  | cons a l ih =>
    by_cases h_eq : x = a
    · subst h_eq
      refine ⟨[], l, ?_⟩
      simp
    · have h_mem : x ∈ l := by simpa [h_eq] using h
      obtain ⟨b, c, h_bc⟩ := ih h_mem
      refine ⟨a :: b, c, ?_⟩
      simp [h_bc]

theorem filter_cons_true {α : Type} (p : α → Bool) (x : α)
    (l : List α) (h : p x = true) :
    (x :: l).filter p = x :: l.filter p := by
  simp [List.filter, h]

theorem filterMap_cons_some {α β : Type} (f : α → Option β)
    (a : α) (b : β) (l : List α) (h : f a = some b) :
    (a :: l).filterMap f = b :: l.filterMap f := by
  simp [List.filterMap, h]

/-- The members of one round, characterized. -/
theorem rrRound_mem_iff (groups : List GroupSpec) (groupOrd : List Nat)
    (k f : Nat) :
    f ∈ rrRound groups groupOrd k ↔
      ∃ gi, gi ∈ groupOrd ∧ k < (groupAt groups gi).length ∧
        rrFlatIndex groups gi k = f := by
  dsimp [rrRound]
  rw [List.mem_filterMap]
  constructor
  · intro h
    obtain ⟨gi, h_gi, h_if⟩ := h
    split_ifs at h_if with h_d
    · refine ⟨gi, h_gi, ?_, Option.some_inj.mp h_if⟩
      rw [decide_eq_true_eq] at h_d
      exact h_d
  · intro h
    obtain ⟨gi, h_gi, h_ci, h_eq⟩ := h
    refine ⟨gi, h_gi, ?_⟩
    have h_dec : decide (k < (groupAt groups gi).length) = true := by
      rw [decide_eq_true_eq]
      exact h_ci
    rw [h_dec]
    simp
    rw [h_eq]

/-- A bundle chain's flat index lies in its own round. -/
theorem rrRound_mem (groups : List GroupSpec) (groupOrd : List Nat)
    (gi ci : Nat) (h_gi_in : gi ∈ groupOrd)
    (h_ci : ci < (groupAt groups gi).length) :
    rrFlatIndex groups gi ci ∈ rrRound groups groupOrd ci := by
  have h_dec : decide (ci < (groupAt groups gi).length) = true := by
    rw [decide_eq_true_eq]
    exact h_ci
  dsimp [rrRound]
  rw [List.mem_filterMap]
  refine ⟨gi, h_gi_in, ?_⟩
  rw [h_dec]
  simp

private theorem range_cons_succ (n : Nat) :
    List.range (n + 1) = 0 :: (List.range n).map (fun x => 1 + x) := by
  rw [show n + 1 = 1 + n from by omega, List.range_add]
  simp [List.range_one]

/-- The round-robin order splits around any round that exists. -/
theorem rrGroupOrd_round_split (groups : List GroupSpec)
    (groupOrd : List Nat) (k : Nat) (h_k : k < rrTotalChains groups) :
    ∃ front back, rrGroupOrd groups groupOrd =
      front ++ rrRound groups groupOrd k ++ back := by
  dsimp only [rrGroupOrd]
  have h_split : rrTotalChains groups = k + (rrTotalChains groups - k) := by
    omega
  rw [h_split, List.range_add, List.flatMap_append]
  have h_m : rrTotalChains groups - k = (rrTotalChains groups - k - 1) + 1 :=
    by omega
  rw [h_m, range_cons_succ, List.map_cons, List.flatMap_cons]
  simp only [Nat.add_zero]
  refine ⟨(List.range k).flatMap (rrRound groups groupOrd),
    (((List.range (rrTotalChains groups - k - 1)).map
      (fun x => 1 + x)).map (fun x => k + x)).flatMap
      (rrRound groups groupOrd), ?_⟩
  simp [List.append_assoc]

/-- Decompose `rrGroupOrd` into the rounds before `k`, round `k`, and the
    rounds after `k`. -/
theorem rrGroupOrd_round_cons (groups : List GroupSpec)
    (groupOrd : List Nat) (k : Nat)
    (h_k : k < rrTotalChains groups) :
    rrGroupOrd groups groupOrd =
      (List.range k).flatMap (rrRound groups groupOrd) ++
      rrRound groups groupOrd k ++
      ((List.range (rrTotalChains groups - k - 1)).map
        (fun j => k + 1 + j)).flatMap (rrRound groups groupOrd) := by
  dsimp only [rrGroupOrd]
  have h_range : List.range (rrTotalChains groups) =
      List.range k ++
      (List.range (rrTotalChains groups - k)).map (fun x => k + x) := by
    conv => lhs; rw [show rrTotalChains groups = k + (rrTotalChains groups - k)
        from by omega]
    rw [List.range_add]
  rw [h_range, List.flatMap_append]
  have h_second : ((List.range (rrTotalChains groups - k)).map
        (fun x => k + x)).flatMap (rrRound groups groupOrd) =
      rrRound groups groupOrd k ++
      ((List.range (rrTotalChains groups - k - 1)).map
        (fun j => k + 1 + j)).flatMap (rrRound groups groupOrd) := by
    set m := rrTotalChains groups - k - 1
    have hk : rrTotalChains groups - k = m + 1 := by dsimp [m]; omega
    rw [hk, range_cons_succ, List.map_cons]
    simp only [Nat.add_zero]
    rw [List.flatMap_cons]
    have h_inner : ((List.range m).map (fun j => 1 + j)).map
        (fun x => k + x) =
        (List.range m).map (fun j => k + 1 + j) := by
      rw [List.map_map]
      rw [show (fun x => k + x) ∘ (fun j => 1 + j) =
          (fun j => k + 1 + j) from by
        funext j
        dsimp [Function.comp]
        omega]
    rw [h_inner]
  rw [h_second, ← List.append_assoc]

/-- Filtering preserves an `x`-before-`y` split when both survive. -/
theorem filter_split_preserve {α : Type} (p : α → Bool)
    (pre : List α) (x : α) (mid : List α) (y : α) (post : List α)
    (h_x : p x = true) (h_y : p y = true) :
    ∃ pre' mid' post',
      (pre ++ x :: mid ++ y :: post).filter p =
        pre' ++ x :: mid' ++ y :: post' := by
  refine ⟨pre.filter p, mid.filter p, post.filter p, ?_⟩
  rw [List.filter_append, List.filter_append]
  rw [filter_cons_true p x mid h_x]
  rw [filter_cons_true p y post h_y]

/-- filterMap preserves an `x`-before-`y` split when both map to `some`. -/
theorem filterMap_split_preserve {α β : Type} (f : α → Option β)
    (pre : List α) (x : α) (mid : List α) (y : α) (post : List α)
    (bx bz : β) (hx : f x = some bx) (hy : f y = some bz) :
    ∃ pre' mid' post',
      (pre ++ x :: mid ++ y :: post).filterMap f =
        pre' ++ bx :: mid' ++ bz :: post' := by
  refine ⟨pre.filterMap f, mid.filterMap f, post.filterMap f, ?_⟩
  rw [List.filterMap_append, List.filterMap_append]
  rw [filterMap_cons_some f x bx mid hx]
  rw [filterMap_cons_some f y bz post hy]

/-- In a duplicate-free list, two distinct members are ordered one way
    or the other. -/
theorem mem_order_total {α : Type} [DecidableEq α] (l : List α)
    (x y : α) (h_x : x ∈ l) (h_y : y ∈ l) (h_ne : x ≠ y) :
    (∃ a b c, l = a ++ x :: b ++ y :: c) ∨
      (∃ a b c, l = a ++ y :: b ++ x :: c) := by
  revert x y h_x h_y h_ne
  induction l with
  | nil => intro x y h_x; cases h_x
  | cons a l ih =>
    intro x y h_x h_y h_ne
    simp only [List.mem_cons] at h_x h_y
    cases h_x with
    | inl h_x_a =>
      cases h_y with
      | inl h_y_a =>
        exfalso
        apply h_ne
        rw [h_x_a, h_y_a]
      | inr h_y_l =>
        left
        obtain ⟨b, c, h_bc⟩ := mem_split h_y_l
        subst h_x_a
        refine ⟨[], b, c, ?_⟩
        simp [h_bc]
    | inr h_x_l =>
      cases h_y with
      | inl h_y_a =>
        right
        obtain ⟨b, c, h_bc⟩ := mem_split h_x_l
        subst h_y_a
        refine ⟨[], b, c, ?_⟩
        simp [h_bc]
      | inr h_y_l =>
        cases ih x y h_x_l h_y_l h_ne with
        | inl h_fwd =>
          obtain ⟨b, c, d, h_bcd⟩ := h_fwd
          left
          refine ⟨a :: b, c, d, ?_⟩
          simp [h_bcd]
        | inr h_rev =>
          obtain ⟨b, c, d, h_bcd⟩ := h_rev
          right
          refine ⟨a :: b, c, d, ?_⟩
          simp [h_bcd]

/-- Round-robin order is total on distinct pairs of group members. -/
theorem rrBefore_total (groupOrd : List Nat) (g₁ c₁ g₂ c₂ : Nat)
    (h_g₁ : g₁ ∈ groupOrd) (h_g₂ : g₂ ∈ groupOrd)
    (h_ne : g₁ ≠ g₂ ∨ c₁ ≠ c₂) :
    rrBefore groupOrd g₁ c₁ g₂ c₂ ∨
      rrBefore groupOrd g₂ c₂ g₁ c₁ := by
  dsimp [rrBefore]
  by_cases h_c : c₁ = c₂
  · have h_ne_g : g₁ ≠ g₂ := by
      intro h_eq
      cases h_ne with
      | inl h_ne_g' => exact h_ne_g' h_eq
      | inr h_ne_c' => exact h_ne_c' h_c
    obtain ⟨a, b, c, h_ord⟩ | ⟨a, b, c, h_ord⟩ :=
      mem_order_total groupOrd g₁ g₂ h_g₁ h_g₂ h_ne_g
    · left
      right
      exact ⟨h_c, a, b, c, h_ord⟩
    · right
      right
      exact ⟨h_c.symm, a, b, c, h_ord⟩
  · have h_lt : c₁ < c₂ ∨ c₂ < c₁ := by omega
    cases h_lt with
    | inl h_lt =>
      left
      exact Or.inl h_lt
    | inr h_lt =>
      right
      exact Or.inl h_lt

/-! ## The split activation order is a permutation -/

private theorem prefixLen_zero (g : GroupSpec) (gs : List GroupSpec) :
    rrPrefixLen (g :: gs) 0 = 0 := by
  dsimp [rrPrefixLen, List.take, List.map, List.sum]

private theorem prefixLen_succ (g : GroupSpec) (gs : List GroupSpec)
    (gi : Nat) :
    rrPrefixLen (g :: gs) (gi + 1) = g.length + rrPrefixLen gs gi := by
  dsimp [rrPrefixLen, List.take, List.map, List.sum]

private theorem groupAt_zero (g : GroupSpec) (gs : List GroupSpec) :
    groupAt (g :: gs) 0 = g := by
  simp [groupAt]

private theorem groupAt_succ (g : GroupSpec) (gs : List GroupSpec)
    (gi : Nat) :
    groupAt (g :: gs) (gi + 1) = groupAt gs gi := by
  simp [groupAt]

/-- The prefix length strictly increases across a nonempty group. -/
theorem rrPrefixLen_step (groups : List GroupSpec) (gi gj : Nat)
    (h_gi : gi < groups.length) (h_lt : gi < gj) :
    rrPrefixLen groups gi + (groupAt groups gi).length ≤
      rrPrefixLen groups gj := by
  revert gi gj h_gi h_lt
  induction groups with
  | nil =>
    intro gi gj h_gi h_lt
    change gi < 0 at h_gi
    omega
  | cons g gs ih =>
    intro gi gj h_gi h_lt
    cases gi with
    | zero =>
      cases gj with
      | zero => omega
      | succ gj' =>
        rw [prefixLen_zero, prefixLen_succ, groupAt_zero]
        omega
    | succ gi' =>
      cases gj with
      | zero => omega
      | succ gj' =>
        rw [prefixLen_succ, prefixLen_succ, groupAt_succ]
        have h_gi' : gi' < gs.length := by
          dsimp [List.length] at h_gi
          omega
        have h_ih := ih gi' gj' h_gi' (by omega)
        omega

/-- Flat indices determine their group and chain. -/
theorem rrFlatIndex_inj (groups : List GroupSpec) (g₁ g₂ c₁ c₂ : Nat)
    (h_g₁ : g₁ < groups.length) (h_g₂ : g₂ < groups.length)
    (h_c₁ : c₁ < (groupAt groups g₁).length)
    (h_c₂ : c₂ < (groupAt groups g₂).length)
    (h_eq : rrFlatIndex groups g₁ c₁ = rrFlatIndex groups g₂ c₂) :
    g₁ = g₂ ∧ c₁ = c₂ := by
  by_cases h_le : g₁ ≤ g₂
  · by_cases h_eq_g : g₁ = g₂
    · refine ⟨h_eq_g, ?_⟩
      subst h_eq_g
      dsimp [rrFlatIndex] at h_eq
      omega
    · have h_prefix := rrPrefixLen_step groups g₁ g₂ h_g₁ (by omega)
      dsimp [rrFlatIndex] at h_eq
      omega
  · have h_prefix := rrPrefixLen_step groups g₂ g₁ h_g₂ (by omega)
    dsimp [rrFlatIndex] at h_eq
    omega

/-- A group index in a permutation of `range n` lies below `n`. -/
private theorem lt_length_of_mem_perm_range (groupOrd : List Nat)
    (groups : List GroupSpec)
    (h_ord : List.Perm groupOrd (List.range groups.length))
    (gi : Nat) (h_mem : gi ∈ groupOrd) :
    gi < groups.length := by
  have h_range : gi ∈ List.range groups.length :=
    (List.Perm.mem_iff h_ord).mp h_mem
  exact List.mem_range.mp h_range

/-- A positive `groupAt` length forces the index in range. -/
private theorem lt_length_of_groupAt_length_pos (groups : List GroupSpec)
    (gi : Nat) (h : 0 < (groupAt groups gi).length) :
    gi < groups.length := by
  by_contra h_ge
  have h_none : groups[gi]? = none :=
    List.getElem?_eq_none (Nat.le_of_not_lt h_ge)
  dsimp [groupAt] at h
  rw [h_none] at h
  dsimp at h
  omega

/-- Every member of the round-robin order is a valid flat index. -/
theorem rrGroupOrd_mem_lt (groups : List GroupSpec)
    (groupOrd : List Nat)
    (f : Nat) (h_f : f ∈ rrGroupOrd groups groupOrd) :
    f < rrTotalChains groups := by
  dsimp [rrGroupOrd] at h_f
  rw [List.mem_flatMap] at h_f
  obtain ⟨k, h_k_range, h_k⟩ := h_f
  rw [rrRound_mem_iff] at h_k
  obtain ⟨gi, _, h_ci, h_eq⟩ := h_k
  have h_gi : gi < groups.length :=
    lt_length_of_groupAt_length_pos groups gi (by omega)
  rw [← h_eq, ← rrSplitGroups_length]
  exact rrFlatIndex_lt groups gi k h_gi h_ci

/-- Every valid flat index appears in the round-robin order. -/
theorem rrGroupOrd_mem_of_lt (groups : List GroupSpec)
    (groupOrd : List Nat)
    (h_ord : List.Perm groupOrd (List.range groups.length))
    (f : Nat) (h_f : f < rrTotalChains groups) :
    f ∈ rrGroupOrd groups groupOrd := by
  have h_f_len : f < (rrSplitGroups groups).length := by
    rwa [rrSplitGroups_length]
  obtain ⟨gi, ci, h_gi, h_ci, h_eq⟩ := rrSplit_exists groups f h_f_len
  have h_gi_ord : gi ∈ groupOrd :=
    (List.Perm.mem_iff h_ord).mpr (List.mem_range.mpr h_gi)
  rw [← h_eq]
  dsimp [rrGroupOrd]
  rw [List.mem_flatMap]
  refine ⟨ci, ?_, rrRound_mem groups groupOrd gi ci h_gi_ord h_ci⟩
  rw [List.mem_range]
  dsimp [rrFlatIndex] at h_eq
  omega

/-- The round-robin order contains exactly the valid flat indices. -/
theorem rrGroupOrd_mem (groups : List GroupSpec) (groupOrd : List Nat)
    (h_ord : List.Perm groupOrd (List.range groups.length)) (f : Nat) :
    f ∈ rrGroupOrd groups groupOrd ↔ f < rrTotalChains groups := by
  exact ⟨rrGroupOrd_mem_lt groups groupOrd f,
    rrGroupOrd_mem_of_lt groups groupOrd h_ord f⟩

/-- One round is duplicate-free. -/
private theorem rrRound_nodup (groups : List GroupSpec)
    (groupOrd : List Nat)
    (h_ord : List.Perm groupOrd (List.range groups.length)) (k : Nat) :
    (rrRound groups groupOrd k).Nodup := by
  dsimp [rrRound]
  apply List.Nodup.filterMap
  · intro gi gj b h_bi h_bj
    split_ifs at h_bi with h_dgi
    · split_ifs at h_bj with h_dgj
      · have h_b_i : b = rrFlatIndex groups gi k :=
          (Option.some_inj.mp h_bi).symm
        have h_b_j : b = rrFlatIndex groups gj k :=
          (Option.some_inj.mp h_bj).symm
        have h_ci : k < (groupAt groups gi).length := by
          rw [decide_eq_true_eq] at h_dgi
          exact h_dgi
        have h_cj : k < (groupAt groups gj).length := by
          rw [decide_eq_true_eq] at h_dgj
          exact h_dgj
        have h_gi : gi < groups.length :=
          lt_length_of_groupAt_length_pos groups gi (by omega)
        have h_gj : gj < groups.length :=
          lt_length_of_groupAt_length_pos groups gj (by omega)
        exact (rrFlatIndex_inj groups gi gj k k h_gi h_gj h_ci h_cj
          (by rw [← h_b_i, ← h_b_j])).1
      · cases h_bj
    · cases h_bi
  · exact (List.Perm.nodup_iff h_ord).mpr List.nodup_range

/-- Two different rounds are disjoint. -/
private theorem rrRound_disjoint (groups : List GroupSpec)
    (groupOrd : List Nat) (k₁ k₂ : Nat) (h_ne : k₁ ≠ k₂) :
    Disjoint (rrRound groups groupOrd k₁) (rrRound groups groupOrd k₂) :=
  by
  rw [List.disjoint_left]
  intro f h_f₁ h_f₂
  rw [rrRound_mem_iff] at h_f₁ h_f₂
  obtain ⟨gi, _, h_c₁, h_eq₁⟩ := h_f₁
  obtain ⟨gj, _, h_c₂, h_eq₂⟩ := h_f₂
  have h_gi : gi < groups.length :=
    lt_length_of_groupAt_length_pos groups gi (by omega)
  have h_gj : gj < groups.length :=
    lt_length_of_groupAt_length_pos groups gj (by omega)
  have h_inj := rrFlatIndex_inj groups gi gj k₁ k₂ h_gi h_gj h_c₁ h_c₂
    (h_eq₁.trans h_eq₂.symm)
  exact h_ne h_inj.2

/-- Rounds are pairwise disjoint across any range of round indices. -/
private theorem rrRound_pairwise_disjoint (groups : List GroupSpec)
    (groupOrd : List Nat) (n : Nat) :
    (List.range n).Pairwise (fun k₁ k₂ =>
        Disjoint (rrRound groups groupOrd k₁)
          (rrRound groups groupOrd k₂)) := by
  induction n with
  | zero => dsimp [List.range]; exact List.Pairwise.nil
  | succ n ih =>
    rw [List.range_succ, List.pairwise_append]
    refine ⟨ih, ?_, ?_⟩
    · simp
    · intro k₁ h_k₁ k₂ h_k₂
      simp at h_k₂
      rw [h_k₂]
      have h_ne : k₁ ≠ n := by
        rw [List.mem_range] at h_k₁
        omega
      exact rrRound_disjoint groups groupOrd k₁ n h_ne

/-- The round-robin order is duplicate-free. -/
theorem rrGroupOrd_nodup (groups : List GroupSpec) (groupOrd : List Nat)
    (h_ord : List.Perm groupOrd (List.range groups.length)) :
    (rrGroupOrd groups groupOrd).Nodup := by
  dsimp [rrGroupOrd]
  apply List.nodup_flatMap.mpr
  refine ⟨fun k _ => rrRound_nodup groups groupOrd h_ord k,
    rrRound_pairwise_disjoint groups groupOrd (rrTotalChains groups)⟩

/-- The round-robin order permutes the split group indices. -/
theorem rrGroupOrd_perm (groups : List GroupSpec) (groupOrd : List Nat)
    (h_ord : List.Perm groupOrd (List.range groups.length)) :
    List.Perm (rrGroupOrd groups groupOrd)
      (List.range (rrSplitGroups groups).length) := by
  rw [rrSplitGroups_length]
  apply (List.perm_ext_iff_of_nodup
    (rrGroupOrd_nodup groups groupOrd h_ord) List.nodup_range).mpr
  intro f
  rw [rrGroupOrd_mem groups groupOrd h_ord f, List.mem_range]

/-- The trivial within-order permutes each singleton's chain range. -/
theorem rrWithinOrd_perm (groups : List GroupSpec) (f : Nat)
    (h_f : f < (rrSplitGroups groups).length) :
    List.Perm (rrWithinOrd f)
      (List.range (groupAt (rrSplitGroups groups) f).length) := by
  have h_len : (groupAt (rrSplitGroups groups) f).length = 1 := by
    obtain ⟨gi, ci, h_gi, h_ci, h_eq⟩ := rrSplit_exists groups f h_f
    rw [← h_eq, rrGroupAt_flat groups gi ci h_gi h_ci]
    simp
  rw [h_len, List.range_one]
  dsimp [rrWithinOrd]
  exact List.Perm.refl _

/-- The split chain at a bundle flat index is the bundle chain. -/
theorem rrChainAt_flat_self (groups : List GroupSpec) (gi ci : Nat)
    (h_gi : gi < groups.length) (h_ci : ci < (groupAt groups gi).length) :
    chainAt (rrSplitGroups groups) (rrFlatIndex groups gi ci) 0 =
      chainAt groups gi ci := by
  change (groupAt (rrSplitGroups groups)
      (rrFlatIndex groups gi ci))[0]?.getD defaultSpec =
    chainAt groups gi ci
  rw [rrGroupAt_flat groups gi ci h_gi h_ci]
  simp
