import BasicProofs.GroupClustering.Dynamics


open BasicRedstoneSim

/-! # Group clustering — stage events and queue evolution

Every event ever queued is a **stage event** of some chain `(gi, ci)`:
stage 0 is the observer event, stages `1..m` are the middle repeaters,
stage `m + 1` is the last repeater. The cumulative delay up to stage `j`
is the sum of the first `j` entries of `middleDelays ++ [lastDelay]`, so
stage `j` targets `actTick gi + 2 + stageCumDelay c j`, with priority
0 / -3 / -1 for observer / middle / last.

The queue at the start of tick `t` is `(gSimWorld ... t).events`; later
parts of this development prove the membership characterization

    ev ∈ events(t)  ↔  ev = stageEvent gi ci j ∧ stageWindow gi ci j t

(the window says the predecessor has fired but the event has not) and the
evolution fact `events(t+1) = events(t).filter (target ≠ t) ++ new`.
-/

/-! ## Stage-event definitions -/

/-- Cumulative delay up to stage `j`: the sum of the first `j` entries of
    `middleDelays ++ [lastDelay]`. -/
def stageCumDelay (c : ChainSpec) (j : Nat) : Nat :=
  (((c.middleDelays.map PNat.val) ++ [(c.lastDelay : Nat)]).take j).sum

/-- Target tick of chain `(gi, ci)`'s stage-`j` event. -/
def stageTarget (actTick : Nat → Nat) (groups : List GroupSpec)
    (gi ci j : Nat) : Nat :=
  actTick gi + 2 + stageCumDelay (chainAt groups gi ci) j

/-- Priority of chain `(gi, ci)`'s stage-`j` event. -/
def stagePri (groups : List GroupSpec) (gi ci j : Nat) : Int :=
  if j = 0 then 0
  else if j ≤ (chainAt groups gi ci).middleDelays.length then (-3 : Int) else (-1 : Int)

/-- Chain `(gi, ci)`'s stage-`j` event. -/
def stageEvent (actTick : Nat → Nat) (groups : List GroupSpec)
    (gi ci j : Nat) : ScheduledEvent :=
  { targetTick := stageTarget actTick groups gi ci j, priority := stagePri groups gi ci j, nodeId := chainBaseId groups gi ci + 1 + j }

/-- The stage-`j` event of chain `(gi, ci)` is queued at tick-start `t` iff
    its predecessor has fired (`prev < t`) but it has not (`t ≤ target`). -/
def stageWindow (actTick : Nat → Nat) (groups : List GroupSpec)
    (gi ci j t : Nat) : Prop :=
  (if j = 0 then actTick gi else stageTarget actTick groups gi ci (j - 1)) < t ∧
  t ≤ stageTarget actTick groups gi ci j

/-- The world at the start of tick `t`. -/
def gSimWorld (groups : List GroupSpec) (actTick : Nat → Nat)
    (groupOrd : List Nat) (withinOrd pos : Nat → List Nat) (t : Nat) : World :=
  gSimFoldl actTick (buildGroups groups).2 groupOrd withinOrd pos
    (buildGroups groups).1 t

/-! ## Small list helpers -/

@[simp] private theorem length_append' {α : Type} (l r : List α) :
    (l ++ r).length = l.length + r.length := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih]; omega

@[simp] private theorem length_map' {α β : Type} (l : List α) (f : α → β) :
    (l.map f).length = l.length := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih]

private theorem getElem_append_lt {α : Type} (l : List α) (r : List α) (j : Nat)
    (h_j : j < l.length) : (l ++ r)[j]'(by simp; omega) = l[j] := by
  induction l generalizing j with
  | nil => simp at h_j
  | cons x xs ih =>
    cases j with
    | zero => simp
    | succ j' =>
      simp only [List.getElem_cons_succ]
      exact ih j' (by simpa using h_j)

private theorem getElem_append_last {α : Type} (l : List α) (d : α) :
    (l ++ [d])[l.length]'(by simp) = d := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp

private theorem getElem_map' {α β : Type} (l : List α) (f : α → β) (j : Nat)
    (h_j : j < l.length) : (l.map f)[j]'(by simp; omega) = f l[j] := by
  induction l generalizing j with
  | nil => simp at h_j
  | cons x xs ih =>
    cases j with
    | zero => simp
    | succ j' =>
      simp only [List.map_cons, List.getElem_cons_succ]
      exact ih j' (by simpa using h_j)

private theorem take_append_of_le {α : Type} (l r : List α) (j : Nat)
    (h_j : j ≤ l.length) : (l ++ r).take j = l.take j := by
  induction j generalizing l with
  | zero => simp
  | succ j' ih =>
    cases l with
    | nil => simp at h_j
    | cons x xs =>
      simp only [List.length_cons] at h_j
      show x :: (xs ++ r).take j' = x :: xs.take j'
      congr 1
      exact ih xs (by omega)

private theorem take_map' {α β : Type} (l : List α) (f : α → β) (j : Nat) :
    (l.map f).take j = (l.take j).map f := by
  induction j generalizing l with
  | zero => simp
  | succ j' ih =>
    cases l with
    | nil => simp
    | cons x xs =>
      show f x :: (xs.map f).take j' = f x :: (xs.take j').map f
      congr 1
      exact ih xs

private theorem take_self {α : Type} (l : List α) : l.take l.length = l := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih]

/-! ## Cumulative-delay arithmetic -/

@[simp] theorem stageCumDelay_zero (c : ChainSpec) : stageCumDelay c 0 = 0 := by
  simp [stageCumDelay]

private theorem cum_take_succ (l : List Nat) (d : Nat) (j : Nat)
    (h_j : j < l.length + 1) :
    ((l ++ [d]).take (j + 1)).sum = ((l ++ [d]).take j).sum +
      (l ++ [d])[j]'(by simp; omega) := by
  induction j generalizing l with
  | zero =>
    cases l with
    | nil => simp
    | cons x xs => simp
  | succ j' ih =>
    cases l with
    | nil => simp at h_j
    | cons x xs =>
      simp only [List.length_cons] at h_j
      show x + ((xs ++ [d]).take (j' + 1)).sum =
        x + ((xs ++ [d]).take j').sum + (xs ++ [d])[j']'(by simp; omega)
      rw [ih xs (by omega)]
      omega

/-- The cumulative delay grows by the next entry of
    `middleDelays ++ [lastDelay]`. -/
theorem stageCumDelay_succ (c : ChainSpec) (j : Nat)
    (h_j : j < c.middleDelays.length + 1) :
    stageCumDelay c (j + 1) = stageCumDelay c j +
      ((c.middleDelays.map PNat.val) ++
        [(c.lastDelay : Nat)])[j]'(by simp; omega) :=
  cum_take_succ (c.middleDelays.map PNat.val) (c.lastDelay : Nat) j
    (by simpa using h_j)

/-- For middle stages, the increment is the corresponding middle delay. -/
theorem stageCumDelay_succ_middle (c : ChainSpec) (j : Nat)
    (h_j : j < c.middleDelays.length) :
    stageCumDelay c (j + 1) = stageCumDelay c j + (c.middleDelays[j] : Nat) := by
  rw [stageCumDelay_succ c j (by omega)]
  congr 1
  rw [getElem_append_lt (c.middleDelays.map PNat.val)
    [(c.lastDelay : Nat)] j (by simpa using h_j)]
  exact getElem_map' c.middleDelays PNat.val j h_j

/-- At the last middle index, the increment is the last delay. -/
theorem stageCumDelay_succ_last (c : ChainSpec) :
    stageCumDelay c (c.middleDelays.length + 1) =
    stageCumDelay c c.middleDelays.length + (c.lastDelay : Nat) := by
  rw [stageCumDelay_succ c c.middleDelays.length (by omega)]
  congr 1
  convert getElem_append_last (c.middleDelays.map PNat.val) (c.lastDelay : Nat) using 1
  simp

/-- Cumulative delays are strictly increasing. -/
theorem stageCumDelay_lt_succ (c : ChainSpec) (j : Nat)
    (h_j : j < c.middleDelays.length + 1) :
    stageCumDelay c j < stageCumDelay c (j + 1) := by
  rw [stageCumDelay_succ c j h_j]
  have h_pos : ((c.middleDelays.map PNat.val) ++
      [(c.lastDelay : Nat)])[j]'(by simp; omega) ≥ 1 := by
    by_cases h_lt : j < c.middleDelays.length
    · rw [getElem_append_lt (c.middleDelays.map PNat.val)
        [(c.lastDelay : Nat)] j (by simpa using h_lt), getElem_map' c.middleDelays PNat.val j h_lt]
      have h_gt : 0 < (c.middleDelays[j] : Nat) := (c.middleDelays[j]).2
      omega
    · have h_eq : j = c.middleDelays.length := by omega
      subst h_eq
      have h_last : ((c.middleDelays.map PNat.val) ++
          [(c.lastDelay : Nat)])[c.middleDelays.length]'(by simp) =
          (c.lastDelay : Nat) := by
        convert getElem_append_last (c.middleDelays.map PNat.val) (c.lastDelay : Nat) using 1
        simp
      rw [h_last]
      have h_gt : 0 < (c.lastDelay : Nat) := c.lastDelay.2
      omega
  omega

/-- For indices up to the middle count, the cumulative delay is just the sum
    of the first middle delays. -/
theorem stageCumDelay_of_le_middle (c : ChainSpec) (j : Nat)
    (h_j : j ≤ c.middleDelays.length) :
    stageCumDelay c j =
      ((c.middleDelays.take j).map PNat.val).sum := by
  simp only [stageCumDelay]
  rw [take_append_of_le (c.middleDelays.map PNat.val)
    [(c.lastDelay : Nat)] j (by simpa using h_j)]
  rw [take_map' c.middleDelays PNat.val j]

/-- The elaborated form of `middleDelays.map (fun d => (d : Nat))` (a
    monadic bind) equals the plain `map PNat.val`. -/
private theorem monadic_map_eq_map (l : List PNat) :
    List.map (fun (d : Nat) => d) (do let a ← l; pure (↑a : Nat)) =
    l.map PNat.val := by
  have h_do : (do let a ← l; pure (↑a : Nat)) =
      List.flatMap (fun (a : PNat) => [(↑a : Nat)]) l := by
    simp
  rw [h_do]
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp [ih]

/-- The last stage targets `actTick + chainDelay`. -/
theorem stageTarget_last (actTick : Nat → Nat) (groups : List GroupSpec)
    (gi ci : Nat) :
    stageTarget actTick groups gi ci
      ((chainAt groups gi ci).middleDelays.length + 1) =
    actTick gi + chainDelay (chainAt groups gi ci) := by
  set c := chainAt groups gi ci
  simp only [stageTarget, chainDelay]
  rw [stageCumDelay_succ_last c,
    stageCumDelay_of_le_middle c c.middleDelays.length (by omega), take_self]
  rw [monadic_map_eq_map c.middleDelays]
  omega

/-! ## The tick of the built world -/

private theorem connectChain_tick (w : World) (ids : List Nat) :
    (connectChain w ids).tick = w.tick := by
  dsimp [connectChain]
  induction ids.zip (ids.drop 1) generalizing w with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.foldl_cons]
    rcases p with ⟨prev, curr⟩
    rw [ih]
    rfl

private theorem buildChainPre_tick (w : World) (name : String) (c : ChainSpec) :
    (buildChainPre w name c).2.1.tick = w.tick := by
  dsimp (config := { zeta := true }) [buildChainPre]
  suffices h_fl : ∀ (l : List PNat) (ids : List Nat) (w' : World),
      (l.foldl repFoldlStep (ids, w')).2.tick = w'.tick by
    simp [World.addNode, h_fl]
  intro l ids w'
  induction l generalizing ids w' with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.foldl_cons, repFoldlStep]
    rw [ih]
    simp [World.addNode]

theorem buildChain_tick (w : World) (name : String) (c : ChainSpec) :
    (buildChain w name c).2.tick = w.tick := by
  dsimp (config := { zeta := true }) [buildChain]
  rw [connectChain_tick, buildChainPre_tick]

theorem buildGroupChainsFrom_tick (gi start : Nat) (w : World)
    (g : List ChainSpec) :
    (buildGroupChainsFrom gi start w g).1.tick = w.tick := by
  induction g generalizing w start with
  | nil => simp [buildGroupChainsFrom]
  | cons c cs ih =>
    simp only [buildGroupChainsFrom]
    have h_w' : (buildChain w (chainName gi start) c).2.tick = w.tick :=
      buildChain_tick w (chainName gi start) c
    rw [← h_w']
    apply ih

theorem buildGroupChains_tick (gi : Nat) (w : World) (g : List ChainSpec) :
    (buildGroupChains gi w g).1.tick = w.tick := by
  simpa [buildGroupChains] using buildGroupChainsFrom_tick gi 0 w g

theorem buildGroupsFrom_tick (start : Nat) (w : World) (groups : List GroupSpec) :
    (buildGroupsFrom start w groups).1.tick = w.tick := by
  induction groups generalizing w start with
  | nil => simp [buildGroupsFrom]
  | cons g gs ih =>
    simp only [buildGroupsFrom]
    have h_w' : (buildGroupChains start w g).1.tick = w.tick :=
      buildGroupChains_tick start w g
    rw [← h_w']
    apply ih

/-- The world built by `buildGroups` starts at tick 0. -/
theorem buildGroups_tick (groups : List GroupSpec) :
    (buildGroups groups).1.tick = 0 := by
  simpa [buildGroups, World.empty] using buildGroupsFrom_tick 0 World.empty groups

/-- `gSimWorld ... t` is at tick `t`. -/
theorem gSimWorld_tick (groups : List GroupSpec) (actTick : Nat → Nat)
    (groupOrd : List Nat) (withinOrd pos : Nat → List Nat) (t : Nat) :
    (gSimWorld groups actTick groupOrd withinOrd pos t).tick = t := by
  dsimp [gSimWorld]
  rw [gSimFoldl_tick, buildGroups_tick]
  omega

/-! ## Queue evolution: filter-append split per tick

Events are only ever removed by popping (which only targets events whose
`targetTick` equals the current tick) and appended at the end. The result
of a full tick is therefore

    events(t+1) = events(t).filter (target ≠ t) ++ new,   new targets ≥ t+2
-/

instance : DecidableEq ScheduledEvent
  | e, f =>
    if ht : e.targetTick = f.targetTick then
      if hp : e.priority = f.priority then
        if hn : e.nodeId = f.nodeId then
          isTrue (by
            cases e; cases f
            simp only at ht hp hn
            subst ht; subst hp; subst hn
            rfl)
        else isFalse (fun h => hn (congr_arg (·.nodeId) h))
      else isFalse (fun h => hp (congr_arg (·.priority) h))
    else isFalse (fun h => ht (congr_arg (·.targetTick) h))

/-- Erasing an element that `filter p` would remove anyway commutes with
    the filter. -/
private theorem filter_eraseIdx_of_neg {α : Type} (p : α → Bool) (l : List α)
    (i : Nat) (h_i : i < l.length) (h_neg : p l[i] = false) :
    (l.eraseIdx i).filter p = l.filter p := by
  induction l generalizing i with
  | nil => exact absurd h_i (by simp)
  | cons x xs ih =>
    cases i with
    | zero =>
      have h_px : p x = false := by simpa using h_neg
      simp [List.eraseIdx, h_px]
    | succ i' =>
      simp only [List.eraseIdx, List.getElem_cons_succ] at h_neg ⊢
      dsimp only [List.filter]
      rw [ih i' (by simpa using h_i) h_neg]

/-- `filter` keeps a list unchanged when the predicate holds everywhere. -/
private theorem filter_eq_self_of_forall {α : Type} (p : α → Bool) (l : List α)
    (h : ∀ x ∈ l, p x = true) : l.filter p = l := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have h_x : p x = true := h x (List.mem_cons.mpr (Or.inl rfl))
    have h_xs : ∀ x ∈ xs, p x = true :=
      fun x' hx' => h x' (List.mem_cons.mpr (Or.inr hx'))
    simp [h_x, ih h_xs]

/-- One `processNEvents` phase, seen through the target-≠-tick filter: the
    old future events stay, and everything new targets a strictly later
    tick. -/
theorem processNEvents_events_filter_split (w : World) (n : Nat)
    (h_delay : ∀ nid nd, w.getNode nid = some nd → ∀ d p,
        nd.kind = .repeater d p → d ≥ 2) :
    ∃ new, (processNEvents w n).events.filter (fun ev => ev.targetTick ≠ w.tick) =
      w.events.filter (fun ev => ev.targetTick ≠ w.tick) ++ new ∧
    ∀ ev ∈ new, ev.targetTick > w.tick := by
  induction n generalizing w h_delay with
  | zero =>
    have h_red : (processNEvents w 0).events = w.events := by simp [processNEvents]
    exact ⟨[], by simp [h_red], by simp⟩
  | succ n' ih =>
    simp only [processNEvents]
    cases h_step : w.step with
    | none =>
      exact ⟨[], by simp, by simp⟩
    | some w' =>
      simp only
      cases h_pop : w.popNextEvent with
      | none => simp [World.step, h_pop] at h_step
      | some p =>
        cases p with | mk ev₀ w_pop =>
        have h_tick_w' : w'.tick = w.tick := World.step_tick w w' h_step
        have h_delay_w' : ∀ nid nd, w'.getNode nid = some nd → ∀ d p,
            nd.kind = .repeater d p → d ≥ 2 :=
          step_delay_preserved w w' h_step h_delay
        simp only [World.step, h_pop] at h_step
        injection h_step with h_w'_eq
        obtain ⟨idx, h_idx, h_erase, h_tick₀, _, h_idx_eq⟩ :=
          World.popNextEvent_eraseIdx w ev₀ w_pop h_pop
        have h_tick_w : w_pop.tick = w.tick := World.popNextEvent_tick w ev₀ w_pop h_pop
        have h_delay_pop : ∀ nid nd, w_pop.getNode nid = some nd → ∀ d p,
            nd.kind = .repeater d p → d ≥ 2 := by
          intro nid nd h_nd d p h_kind
          have h_nodes_pop : w_pop.nodes = w.nodes :=
            World.popNextEvent_nodes w ev₀ w_pop h_pop
          have h_nd_w : w.getNode nid = some nd := by
            dsimp [World.getNode]; rw [← h_nodes_pop]; exact h_nd
          exact h_delay nid nd h_nd_w d p h_kind
        obtain ⟨new₀, h_app₀, h_fut₀⟩ := World.onScheduledTick_events_append w_pop
          ev₀.nodeId h_delay_pop
        have h_w'_events : w'.events = w_pop.events ++ new₀ := by
          rw [← h_w'_eq, h_app₀]
        obtain ⟨new', h_new', h_fut'⟩ := ih w' h_delay_w'
        refine ⟨new₀ ++ new', ?_, ?_⟩
        · have h_keep : new₀.filter (fun ev => ev.targetTick ≠ w.tick) = new₀ :=
            filter_eq_self_of_forall (fun ev => ev.targetTick ≠ w.tick) new₀ (by
              intro ev h_ev
              have h_gt : ev.targetTick > w.tick := by
                have := h_fut₀ ev h_ev
                rw [h_tick_w] at this
                exact this
              simp [Nat.ne_of_gt h_gt])
          have h_filter_pop : w_pop.events.filter (fun ev => ev.targetTick ≠ w.tick) =
              w.events.filter (fun ev => ev.targetTick ≠ w.tick) := by
            rw [h_erase]
            exact filter_eraseIdx_of_neg (fun ev => ev.targetTick ≠ w.tick)
              w.events idx h_idx (by rw [h_idx_eq, h_tick₀]; simp)
          rw [← h_tick_w', h_new', h_w'_events, h_tick_w', List.filter_append,
            h_filter_pop, h_keep, List.append_assoc]
        · intro ev h_ev
          rw [List.mem_append] at h_ev
          rcases h_ev with h_ev | h_ev
          · have := h_fut₀ ev h_ev
            rw [h_tick_w] at this
            exact this
          · have := h_fut' ev h_ev
            rw [h_tick_w'] at this
            exact this

/-- `stepUntilNextTick` removes exactly the events targeting the current
    tick; everything appended targets a strictly later tick. -/
theorem World.stepUntilNextTick_events_filter_split (w : World)
    (h_delay : ∀ nid nd, w.getNode nid = some nd → ∀ d p,
        nd.kind = .repeater d p → d ≥ 2) :
    ∃ new, (w.stepUntilNextTick).events =
      w.events.filter (fun ev => ev.targetTick ≠ w.tick) ++ new ∧
    ∀ ev ∈ new, ev.targetTick > w.tick := by
  induction w using World.stepUntilNextTick.induct with
  | case1 x h_step =>
    have h_no_target : ∀ ev ∈ x.events, ev.targetTick ≠ x.tick := by
      intro ev h_ev h_eq
      dsimp [World.step] at h_step
      cases h_pop : x.popNextEvent with
      | some p => simp [h_pop] at h_step
      | none => exact popNextEvent_none_no_events x h_pop ev h_ev h_eq
    have h_filter : x.events.filter (fun ev => ev.targetTick ≠ x.tick) = x.events :=
      filter_eq_self_of_forall (fun ev => ev.targetTick ≠ x.tick) x.events (by
        intro ev h_ev
        simp [h_no_target ev h_ev])
    refine ⟨[], ?_, by simp⟩
    rw [stepUntilNextTick_of_step_none x h_step]
    dsimp
    rw [h_filter, List.append_nil]
  | case2 x w' h_step ih =>
    obtain ⟨new', h_new', h_fut'⟩ := ih (by
      intro nid nd h_nd d p h_kind
      exact step_delay_preserved x w' h_step h_delay nid nd h_nd d p h_kind)
    cases h_pop : x.popNextEvent with
    | none => simp [World.step, h_pop] at h_step
    | some p =>
      cases p with | mk ev₀ w_pop =>
      have h_tick_w' : w'.tick = x.tick := World.step_tick x w' h_step
      have h_sunt : x.stepUntilNextTick = w'.stepUntilNextTick := by
        rw [World.stepUntilNextTick, h_step]
      simp only [World.step, h_pop] at h_step
      injection h_step with h_w'_eq
      obtain ⟨idx, h_idx, h_erase, h_tick₀, _, h_idx_eq⟩ :=
        World.popNextEvent_eraseIdx x ev₀ w_pop h_pop
      have h_tick_pop : w_pop.tick = x.tick := World.popNextEvent_tick x ev₀ w_pop h_pop
      have h_delay_pop : ∀ nid nd, w_pop.getNode nid = some nd → ∀ d p,
          nd.kind = .repeater d p → d ≥ 2 := by
        intro nid nd h_nd d p h_kind
        have h_nodes_pop : w_pop.nodes = x.nodes :=
          World.popNextEvent_nodes x ev₀ w_pop h_pop
        have h_nd_x : x.getNode nid = some nd := by
          dsimp [World.getNode]; rw [← h_nodes_pop]; exact h_nd
        exact h_delay nid nd h_nd_x d p h_kind
      obtain ⟨new₀, h_app₀, h_fut₀⟩ := World.onScheduledTick_events_append w_pop
        ev₀.nodeId h_delay_pop
      refine ⟨new₀ ++ new', ?_, ?_⟩
      · have h_w'_events : w'.events = w_pop.events ++ new₀ := by
          rw [← h_w'_eq, h_app₀]
        have h_keep₀ : new₀.filter (fun ev => ev.targetTick ≠ x.tick) = new₀ :=
          filter_eq_self_of_forall (fun ev => ev.targetTick ≠ x.tick) new₀ (by
            intro ev h_ev
            have h_gt : ev.targetTick > x.tick := by
              have := h_fut₀ ev h_ev
              rw [h_tick_pop] at this
              exact this
            simp [Nat.ne_of_gt h_gt])
        have h_filter_pop : w_pop.events.filter (fun ev => ev.targetTick ≠ x.tick) =
            x.events.filter (fun ev => ev.targetTick ≠ x.tick) := by
          rw [h_erase]
          exact filter_eraseIdx_of_neg (fun ev => ev.targetTick ≠ x.tick)
            x.events idx h_idx (by rw [h_idx_eq, h_tick₀]; simp)
        calc (x.stepUntilNextTick).events = (w'.stepUntilNextTick).events := by rw [h_sunt]
          _ = w'.events.filter (fun ev => ev.targetTick ≠ w'.tick) ++ new' := h_new'
          _ = (w_pop.events ++ new₀).filter (fun ev => ev.targetTick ≠ x.tick) ++ new' := by rw [h_w'_events, h_tick_w']
          _ = w_pop.events.filter (fun ev => ev.targetTick ≠ x.tick) ++ new₀.filter (fun ev => ev.targetTick ≠ x.tick) ++ new' := by rw [List.filter_append]
          _ = x.events.filter (fun ev => ev.targetTick ≠ x.tick) ++ (new₀ ++ new') := by rw [h_filter_pop, h_keep₀, List.append_assoc]
      · intro ev h_ev
        rw [List.mem_append] at h_ev
        rcases h_ev with h_ev | h_ev
        · have := h_fut₀ ev h_ev
          rw [h_tick_pop] at this
          exact this
        · have := h_fut' ev h_ev
          rw [h_tick_w'] at this
          exact this

/-- The burst phase, seen through the target-≠-tick filter: old future events
    stay, and everything new targets a strictly later tick. -/
theorem gSimBurst_events_filter_split (t : Nat) (obsAll : List (List Nat))
    (withinOrd : Nat → List Nat) (pos : Nat → List Nat) (w : World)
    (pairs : List (Nat × Nat))
    (h_delay : ∀ nid nd, w.getNode nid = some nd → ∀ d p,
        nd.kind = .repeater d p → d ≥ 2) :
    ∃ new, (gSimBurst t obsAll withinOrd pos w pairs).events.filter
        (fun ev => ev.targetTick ≠ w.tick) =
      w.events.filter (fun ev => ev.targetTick ≠ w.tick) ++ new ∧
    ∀ ev ∈ new, ev.targetTick > w.tick := by
  induction pairs generalizing w h_delay with
  | nil =>
    simp [gSimBurst]
  | cons p ps ih =>
    simp only [gSimBurst, List.foldl_cons]
    rcases p with ⟨gi, k⟩
    set m := (pos t)[k]?.getD 0
    set ordered : List Nat := (withinOrd gi).foldl (fun acc ci =>
      match (obsAll[gi]?.getD [])[ci]? with
      | some oid => acc ++ [oid]
      | none => acc) []
    set Wproc := processNEvents w m
    set W₁ := activateGroup Wproc ordered
    have h_tick_proc : Wproc.tick = w.tick := by dsimp [Wproc]; exact processNEvents_tick w m
    have h_tick_W₁ : W₁.tick = w.tick := by
      dsimp [W₁, Wproc]
      rw [activateGroup_tick, processNEvents_tick]
    obtain ⟨new_p, h_new_p, h_fut_p⟩ := processNEvents_events_filter_split w m h_delay
    obtain ⟨new_s, h_new_s, h_fut_s⟩ := ih W₁ (by
      dsimp [W₁, Wproc]
      exact activateGroup_delay_preserved (processNEvents w m) ordered
        (processNEvents_delay_preserved w m h_delay))
    set obsEvs := ordered.map (fun nid =>
      ({ targetTick := Wproc.tick + 2, priority := 0, nodeId := nid } : ScheduledEvent))
    have h_W₁_events : W₁.events = Wproc.events ++ obsEvs := by
      dsimp [W₁, Wproc, obsEvs]
      rw [activateGroup_events_map, h_tick_proc]
    have h_keep_obs : obsEvs.filter (fun ev => ev.targetTick ≠ w.tick) = obsEvs :=
      filter_eq_self_of_forall (fun ev => ev.targetTick ≠ w.tick) obsEvs (by
        intro ev h_ev
        have h_tgt : ev.targetTick = Wproc.tick + 2 := by
          dsimp [obsEvs] at h_ev
          rcases List.mem_map.mp h_ev with ⟨nid, _, h_ev_eq⟩
          rw [← h_ev_eq]
        simp [show ev.targetTick ≠ w.tick from by rw [h_tgt, h_tick_proc]; omega])
    refine ⟨new_p ++ obsEvs ++ new_s, ?_, ?_⟩
    · rw [h_tick_W₁.symm]
      change (gSimBurst t obsAll withinOrd pos W₁ ps).events.filter
          (fun ev => ev.targetTick ≠ W₁.tick) =
        w.events.filter (fun ev => ev.targetTick ≠ W₁.tick) ++
          (new_p ++ obsEvs ++ new_s)
      rw [h_new_s, h_tick_W₁, h_W₁_events, List.filter_append, h_new_p, h_keep_obs]
      simp only [List.append_assoc]
    · intro ev h_ev
      rw [List.mem_append] at h_ev
      rcases h_ev with h_ev | h_ev
      · rw [List.mem_append] at h_ev
        rcases h_ev with h_ev | h_ev
        · exact h_fut_p ev h_ev
        · have h_tgt : ev.targetTick = Wproc.tick + 2 := by
            dsimp [obsEvs] at h_ev
            rcases List.mem_map.mp h_ev with ⟨nid, _, h_ev_eq⟩
            rw [← h_ev_eq]
          rw [h_tgt, h_tick_proc]
          omega
      · have := h_fut_s ev h_ev
        rw [h_tick_W₁] at this
        exact this

/-- One `gSimBody` call: the next tick's queue is the target-≠-tick filter of
    the old queue plus strictly-future new events. -/
theorem gSimBody_events_filter_split (actTick : Nat → Nat) (obsAll : List (List Nat))
    (groupOrd : List Nat) (withinOrd : Nat → List Nat) (pos : Nat → List Nat)
    (w : World) (i : Nat)
    (h_delay : ∀ nid nd, w.getNode nid = some nd → ∀ d p,
        nd.kind = .repeater d p → d ≥ 2) :
    ∃ new, (gSimBody actTick obsAll groupOrd withinOrd pos w i).events =
      w.events.filter (fun ev => ev.targetTick ≠ w.tick) ++ new ∧
    ∀ ev ∈ new, ev.targetTick > w.tick := by
  dsimp [gSimBody]
  split_ifs with h_active
  · obtain ⟨new, h_new, h_fut⟩ := World.stepUntilNextTick_events_filter_split
      (w.logOutput s!"tick {w.tick}") (by
      intro nid nd h_nd d p h_kind
      have h_nd_w : w.getNode nid = some nd := by
        dsimp [World.getNode, World.logOutput] at h_nd ⊢
        exact h_nd
      exact h_delay nid nd h_nd_w d p h_kind)
    refine ⟨new, ?_, h_fut⟩
    rw [h_new, World.logOutput_events, World.logOutput_tick]
  · set W₁ := w.logOutput s!"tick {w.tick}"
    have h_delay_W₁ : ∀ nid nd, W₁.getNode nid = some nd → ∀ d p,
        nd.kind = .repeater d p → d ≥ 2 := by
      intro nid nd h_nd d p h_kind
      have h_nd_w : w.getNode nid = some nd := by
        dsimp [W₁, World.getNode, World.logOutput] at h_nd ⊢
        exact h_nd
      exact h_delay nid nd h_nd_w d p h_kind
    set active := groupOrd.filter (fun gi =>
      decide (gi < obsAll.length) && (actTick gi == w.tick))
    obtain ⟨new_b, h_new_b, h_fut_b⟩ := gSimBurst_events_filter_split w.tick obsAll
      withinOrd pos W₁ (active.zipIdx) h_delay_W₁
    obtain ⟨new_s, h_new_s, h_fut_s⟩ := World.stepUntilNextTick_events_filter_split
      (gSimBurst w.tick obsAll withinOrd pos W₁ (active.zipIdx))
      (gSimBurst_delay_preserved w.tick obsAll withinOrd pos W₁ (active.zipIdx)
        h_delay_W₁)
    have h_tick_W₁_eq : W₁.tick = w.tick := by dsimp [W₁]
    have h_B_tick : (gSimBurst w.tick obsAll withinOrd pos W₁ (active.zipIdx)).tick =
        W₁.tick :=
      gSimBurst_tick w.tick obsAll withinOrd pos W₁ (active.zipIdx)
    refine ⟨new_b ++ new_s, ?_, ?_⟩
    · rw [h_new_s, h_B_tick, h_new_b, h_tick_W₁_eq]
      dsimp [W₁]
      rw [← List.append_assoc]
    · intro ev h_ev
      rw [List.mem_append] at h_ev
      rcases h_ev with h_ev | h_ev
      · have := h_fut_b ev h_ev
        rw [h_tick_W₁_eq] at this
        exact this
      · have := h_fut_s ev h_ev
        rw [h_B_tick, h_tick_W₁_eq] at this
        exact this

/-- One full tick of the group simulation: the queue at tick-start `t + 1` is
    the target-≠-`t` filter of the queue at tick-start `t`, plus new events
    that all target strictly later ticks. -/
theorem gSimWorld_events_filter_split (groups : List GroupSpec)
    (actTick : Nat → Nat) (groupOrd : List Nat)
    (withinOrd pos : Nat → List Nat) (t : Nat)
    (h_valid : ∀ gi (c : ChainSpec), gi < groups.length → c ∈ groupAt groups gi →
        (∀ d ∈ c.middleDelays, ValidDelay d) ∧ ValidDelay c.lastDelay) :
    ∃ new, (gSimWorld groups actTick groupOrd withinOrd pos (t + 1)).events =
      (gSimWorld groups actTick groupOrd withinOrd pos t).events.filter
        (fun ev => ev.targetTick ≠ t) ++ new ∧
    ∀ ev ∈ new, ev.targetTick > t := by
  dsimp [gSimWorld]
  simp only [gSimFoldl, List.range_succ, List.foldl_append, List.foldl_cons,
    List.foldl_nil]
  set W : World := List.foldl (gSimBody actTick (buildGroups groups).2 groupOrd
      withinOrd pos) (buildGroups groups).1 (List.range t)
  have h_tick_W : W.tick = t := by
    change (gSimFoldl actTick (buildGroups groups).2 groupOrd withinOrd pos
      (buildGroups groups).1 t).tick = t
    rw [gSimFoldl_tick, buildGroups_tick]
    omega
  obtain ⟨new, h_new, h_fut⟩ := gSimBody_events_filter_split actTick
    (buildGroups groups).2 groupOrd withinOrd pos W t (by
    dsimp [W]
    exact gSimFoldl_delay_preserved actTick (buildGroups groups).2 groupOrd
      withinOrd pos (buildGroups groups).1 t
      (buildGroups_delay_ge2 groups h_valid))
  refine ⟨new, ?_, ?_⟩
  · rw [h_new, h_tick_W]
  · intro ev h_ev
    have := h_fut ev h_ev
    rw [h_tick_W] at this
    exact this
