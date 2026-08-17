import Proofs.Model.Classification

open BasicRedstoneSim
open World
open List

/-! # Same-spec classes, their activation order and the observer base. -/

/-! ## Same-spec classes and their activation order

Chains with the same spec cascade in lockstep: every stage fires at the
same tick with the same priority. The descent below shows their stage
events keep the activation order as they march down the chain. -/

/-- Chains sharing spec `c`, in activation order. -/
def classActOrder (specs : List ChainSpec) (actOrd : List Nat)
    (c : ChainSpec) : List Nat :=
  actOrd.filter (fun i => decide (specAt specs i = c))

/-- The observer events of a same-spec class in activation order. -/
def classObsEvts (T : Nat) (specs : List ChainSpec) (actOrd : List Nat)
    (c : ChainSpec) :
    List ScheduledEvent :=
  (classActOrder specs actOrd c).map (obsEventOf T specs)

/-- The stage-`s` events of a same-spec class in activation order. -/
def classStageEvts (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (c : ChainSpec)
    (s : Nat) : List ScheduledEvent :=
  (classActOrder specs actOrd c).map (stageEventOf T specs · s)

/-! ## Stage quantities depend only on the spec -/

theorem repLenAt_spec (specs : List ChainSpec) (i j : Nat)
    (h : specAt specs i = specAt specs j) :
    repLenAt specs i = repLenAt specs j := by
  dsimp [repLenAt]
  rw [h]

theorem stageDelayAt_spec (specs : List ChainSpec) (i j s : Nat)
    (h : specAt specs i = specAt specs j) :
    stageDelayAt specs i s = stageDelayAt specs j s := by
  dsimp [stageDelayAt]
  rw [h]

theorem stagePriAt_spec (specs : List ChainSpec) (i j s : Nat)
    (h : specAt specs i = specAt specs j) :
    stagePriAt specs i s = stagePriAt specs j s := by
  dsimp [stagePriAt]
  rw [h]

theorem actTickOf_spec (T : Nat) (specs : List ChainSpec) (i j : Nat)
    (h : specAt specs i = specAt specs j) :
    actTickOf T specs i = actTickOf T specs j := by
  dsimp [actTickOf]
  rw [h]

theorem obsTickOf_spec (T : Nat) (specs : List ChainSpec) (i j : Nat)
    (h : specAt specs i = specAt specs j) :
    obsTickOf T specs i = obsTickOf T specs j := by
  dsimp [obsTickOf]
  rw [actTickOf_spec T specs i j h]

theorem stageTickOf_spec (T : Nat) (specs : List ChainSpec)
    (i j s : Nat) (h : specAt specs i = specAt specs j) :
    stageTickOf T specs i s = stageTickOf T specs j s := by
  dsimp [stageTickOf]
  rw [h, actTickOf_spec T specs i j h]

/-! ## Sublist and filter helpers -/

/-- A filter that keeps every element of the list is the identity. -/
private theorem filter_eq_self_of_forall {α : Type} (p : α → Bool)
    (l : List α) (h : ∀ x ∈ l, p x = true) : l.filter p = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    dsimp [List.filter]
    rw [ih (fun y hy => h y (List.mem_cons.mpr (Or.inr hy)))]
    rw [h x (List.mem_cons.mpr (Or.inl rfl))]

/-- `filter` preserves sublists. -/
private theorem sublist_filter {α : Type} (p : α → Bool)
    {l₁ l₂ : List α} (hs : l₁ <+ l₂) : l₁.filter p <+ l₂.filter p := by
  induction hs with
  | slnil =>
    dsimp [List.filter]
    exact Sublist.slnil
  | cons a hs' ih =>
    by_cases hpa : p a = true
    · simp only [List.filter, hpa]
      exact Sublist.cons a ih
    · simp only [List.filter, hpa]
      exact ih
  | cons_cons a hs' ih =>
    by_cases hpa : p a = true
    · simp only [List.filter, hpa]
      exact Sublist.cons_cons a ih
    · simp only [List.filter, hpa]
      exact ih

/-- A sublist whose elements all satisfy the filter embeds into the
    filtered host. -/
theorem sublist_filter_of_forall {α : Type} (p : α → Bool)
    {l₁ l₂ : List α} (hs : l₁ <+ l₂)
    (h : ∀ x ∈ l₁, p x = true) : l₁ <+ l₂.filter p := by
  rw [← filter_eq_self_of_forall p l₁ h]
  exact sublist_filter p hs

/-- `spawnFold` of singleton spawns is the pointwise map. -/
theorem spawnFold_singleton (f : ScheduledEvent → ScheduledEvent)
    (l : List ScheduledEvent) :
    spawnFold (fun e => [f e]) l = l.map f := by
  induction l with
  | nil => dsimp [spawnFold, List.map]
  | cons x xs ih =>
    dsimp [spawnFold, List.map]
    congr 1

/-! ## Sublist embedding machinery -/

/-- The empty list embeds anywhere (polymorphic). -/
private theorem nil_sublist_poly {α : Type} (l : List α) : [] <+ l := by
  induction l with
  | nil => exact Sublist.slnil
  | cons x xs ih => exact Sublist.cons x ih

/-- A list embeds into its own append. -/
private theorem sublist_append_self {α : Type} (l₁ l₂ : List α) :
    l₁ <+ l₁ ++ l₂ := by
  induction l₁ with
  | nil =>
    dsimp [List.append]
    exact nil_sublist_poly l₂
  | cons x xs ih =>
    dsimp [List.append]
    exact Sublist.cons_cons x ih

/-- `(n == n)` is true. -/
private theorem nat_beq_self_true (n : Nat) : (n == n) = true := by
  change decide (n = n) = true
  rw [decide_eq_true_eq]

/-- Prefixing the host preserves a sublist. -/
private theorem sublist_cons_right {α : Type} (a : α) {l₁ l₂ : List α}
    (hs : l₁ <+ l₂) : l₁ <+ a :: l₂ := by
  exact Sublist.trans hs (Sublist.cons a (Sublist.refl l₂))

/-- Filtering with a stronger predicate keeps a sublist of the weaker
    filter. -/
private theorem filter_sublist_filter_of_imp {α : Type}
    (p q : α → Bool) (l : List α)
    (h : ∀ x ∈ l, p x = true → q x = true) :
    l.filter p <+ l.filter q := by
  induction l with
  | nil =>
    dsimp [List.filter]
    exact Sublist.slnil
  | cons x xs ih =>
    dsimp [List.filter]
    by_cases hpx : p x = true
    · have hqx : q x = true :=
        h x (List.mem_cons.mpr (Or.inl rfl)) hpx
      simp only [hpx, hqx]
      exact Sublist.cons_cons x
        (ih (fun y hy => h y (List.mem_cons.mpr (Or.inr hy))))
    · simp only [hpx]
      by_cases hqx : q x = true
      · simp only [hqx]
        exact sublist_cons_right x
          (ih (fun y hy => h y (List.mem_cons.mpr (Or.inr hy))))
      · simp only [hqx]
        exact ih (fun y hy => h y (List.mem_cons.mpr (Or.inr hy)))

/-- `map g` over a sublist embeds into `filterMap f` of the host when
    `f` agrees with `some ∘ g` on the sublist. -/
private theorem map_sublist_filterMap {α β : Type}
    (f : α → Option β) (g : α → β) {l₁ l₂ : List α}
    (hs : l₁ <+ l₂) (h : ∀ x ∈ l₁, f x = some (g x)) :
    l₁.map g <+ l₂.filterMap f := by
  induction hs with
  | slnil =>
    dsimp [List.map, List.filterMap]
    exact Sublist.slnil
  | cons a hs' ih =>
    dsimp [List.filterMap]
    cases hf : f a with
    | none => exact ih (fun x hx => h x hx)
    | some b =>
      exact sublist_cons_right b (ih (fun x hx => h x hx))
  | cons_cons a hs' ih =>
    dsimp [List.map, List.filterMap]
    cases hf : f a with
    | none =>
      have := h a (List.mem_cons.mpr (Or.inl rfl))
      rw [hf] at this
      cases this
    | some b =>
      have hb : b = g a := by
        have := h a (List.mem_cons.mpr (Or.inl rfl))
        rw [hf] at this
        exact Option.some.inj this
      subst hb
      exact Sublist.cons_cons (g a)
        (ih (fun x hx => h x (List.mem_cons.mpr (Or.inr hx))))

/-- `filterMap` over `zipIdx` ignores the index. -/
private theorem filterMap_zipIdx {α β : Type} (F : α → Option β)
    (l : List α) (n : Nat) :
    (l.zipIdx n).filterMap (fun p => F p.1) = l.filterMap F := by
  induction l generalizing n with
  | nil => dsimp [List.zipIdx, List.filterMap]
  | cons a rest ih =>
    dsimp [List.zipIdx, List.filterMap]
    rw [ih (n + 1)]

/-! ## The class embeds into its burst's activations -/

/-- A same-spec class's observer events embed into the activation
    events of its burst, in activation order. -/
theorem classObsEvts_sublist_obsActEvts (T : Nat)
    (specs : List ChainSpec) (actOrd observers : List Nat)
    (c : ChainSpec) (t : Nat)
    (hact : ∀ i ∈ classActOrder specs actOrd c,
      actTickOf T specs i = t)
    (hlt : ∀ i ∈ classActOrder specs actOrd c, i < observers.length)
    (hoid : ∀ i ∈ classActOrder specs actOrd c,
      observers[i]? = some (chainObserverId specs i)) :
    classObsEvts T specs actOrd c <+
      obsActEvts t observers
        ((actOrd.filter (fun i =>
          decide (i < observers.length) &&
            (actTickOf T specs i == t))).zipIdx) := by
  dsimp [classObsEvts, obsActEvts]
  rw [filterMap_zipIdx (fun i => (observers[i]?).map (obsActEvt t))]
  apply map_sublist_filterMap
    (fun i => (observers[i]?).map (obsActEvt t))
    (obsEventOf T specs)
  · dsimp [classActOrder]
    apply filter_sublist_filter_of_imp
    intro i hiOrd hp
    have hi : i ∈ classActOrder specs actOrd c := by
      dsimp [classActOrder]
      exact List.mem_filter.mpr ⟨hiOrd, hp⟩
    rw [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hlt i hi, by rw [hact i hi]; exact nat_beq_self_true t⟩
  · intro i hi
    rw [hoid i hi]
    dsimp [Option.map]
    congr 1
    dsimp [obsEventOf, obsActEvt, obsTickOf]
    rw [hact i hi]

/-! ## Surviving a tick -/

/-- A not-due sublist survives one `simWorld` tick. -/
theorem simWorld_sublist_survive (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat) (t : Nat)
    (evts : List ScheduledEvent)
    (hs : evts <+ (simWorld T specs actOrd pos t).events)
    (hnot : ∀ e ∈ evts, e.targetTick ≠ t) :
    evts <+ (simWorld T specs actOrd pos (t + 1)).events := by
  rw [simWorld_succ]
  set wT := simWorld T specs actOrd pos t
  dsimp only [simBody]
  set wLog := wT.logOutput s!"tick {wT.tick}"
  apply stepUntilNextTick_sublist_carry (carry := evts)
  · set F := actOrd.filter (fun i =>
      decide (i < (buildChains specs).2.length) &&
        (actTickOf T specs i == wLog.tick))
    have hc : evts <+ wLog.events := by
      dsimp only [wLog, World.logOutput]
      exact hs
    have hcarry := simBurst_sublist_carry wLog.tick
      (buildChains specs).2 pos wLog (F.zipIdx) evts hc
      (by
        intro e he
        dsimp only [wLog]
        rw [World.logOutput_tick]
        dsimp only [wT]
        rw [simWorld_tick]
        exact hnot e he) rfl
    exact Sublist.trans
      (sublist_append_self evts
        (obsActEvts wLog.tick (buildChains specs).2 (F.zipIdx)))
      hcarry
  · intro e he
    dsimp only [wLog, wT]
    rw [simBurst_tick, World.logOutput_tick, simWorld_tick]
    exact hnot e he

/-! ## Observer base of the descent -/

/-- A same-spec class's observer events reach their firing tick
    `a + 2` in activation order, due and at priority 0. -/
theorem classObsEvts_due_sublist (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat) (c : ChainSpec)
    (h_perm : actOrd.Perm (List.range specs.length)) (a : Nat)
    (hact : ∀ i ∈ classActOrder specs actOrd c,
      actTickOf T specs i = a) :
    classObsEvts T specs actOrd c <+
      ((simWorld T specs actOrd pos (a + 2)).events.filter
        (fun e => e.targetTick == a + 2 && e.priority == 0)) := by
  have hcls : classObsEvts T specs actOrd c <+
      (simWorld T specs actOrd pos (a + 1)).events := by
    rw [simWorld_succ]
    have hobs := simBody_obsActs_sublist (actTickOf T specs)
      (buildChains specs).2 actOrd pos
      (simWorld T specs actOrd pos a) a
    rw [simWorld_tick] at hobs
    have hemb : classObsEvts T specs actOrd c <+
        obsActEvts a (buildChains specs).2
          ((actOrd.filter (fun i =>
            decide (i < (buildChains specs).2.length) &&
              (actTickOf T specs i == a))).zipIdx) := by
      apply classObsEvts_sublist_obsActEvts T specs actOrd
        (buildChains specs).2 c a hact
      · intro i hi
        have hiOrd : i ∈ actOrd := by
          dsimp [classActOrder] at hi
          exact (List.mem_filter.mp hi).1
        rw [buildChains_observers_length]
        exact List.mem_range.mp ((List.Perm.mem_iff h_perm).mp hiOrd)
      · intro i hi
        have hiLen : i < (buildChains specs).2.length := by
          have hiOrd : i ∈ actOrd := by
            dsimp [classActOrder] at hi
            exact (List.mem_filter.mp hi).1
          rw [buildChains_observers_length]
          exact List.mem_range.mp ((List.Perm.mem_iff h_perm).mp hiOrd)
        rw [List.getElem?_eq_getElem hiLen]
        rw [observers_getElem_eq_chainObserverId specs i hiLen]
    exact Sublist.trans hemb hobs
  have hsurv : classObsEvts T specs actOrd c <+
      (simWorld T specs actOrd pos (a + 2)).events := by
    apply simWorld_sublist_survive T specs actOrd pos (a + 1)
      (classObsEvts T specs actOrd c) hcls
    intro e he
    obtain ⟨i, hi, heq⟩ := List.mem_map.mp he
    rw [← heq]
    dsimp [obsEventOf, obsTickOf]
    rw [hact i hi]
    omega
  apply sublist_filter_of_forall
    (fun e => e.targetTick == a + 2 && e.priority == 0) hsurv
  intro e he
  obtain ⟨i, hi, heq⟩ := List.mem_map.mp he
  rw [← heq]
  dsimp [obsEventOf, obsTickOf]
  rw [hact i hi]
  rw [Bool.and_eq_true]
  exact ⟨nat_beq_self_true (a + 2), by dsimp⟩

