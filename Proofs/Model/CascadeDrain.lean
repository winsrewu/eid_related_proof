import Proofs.Model.Basic
import Proofs.Model.SimLemmas
import Proofs.Model.Cascade
import Mathlib.Data.List.Defs
import Mathlib.Data.List.Basic
import Mathlib.Tactic

open BasicRedstoneSim
open World

/-! # Draining a uniform tick

Pop discipline for ticks whose pending events share one priority, and the
drain characterization that will carry the cascade stage by stage. -/

/-- `popNextEvent` is `none` when no event targets the current tick. -/
theorem popNextEvent_none_of_count_zero (w : World)
    (h : countEventAtThisTick w w.tick = 0) : w.popNextEvent = none := by
  unfold popNextEvent
  dsimp (config := { zeta := true })
  have hnil : (List.zip (List.range w.events.length) w.events).filter
      (fun x => x.2.targetTick == w.tick) = [] := by
    have hlen : ((List.zip (List.range w.events.length) w.events).filter
        (fun x => x.2.targetTick == w.tick)).length = 0 := by
      rw [popNextEvent_candidates_length, h]
    cases hl : (List.zip (List.range w.events.length) w.events).filter
        (fun x => x.2.targetTick == w.tick)
    · rfl
    · simp [hl] at hlen
  simp [hnil]

/-- `step = none` iff no event targets the current tick. -/
theorem step_none_iff (w : World) :
    w.step = none ↔ countEventAtThisTick w w.tick = 0 := by
  constructor
  · exact step_none_countEventAtThisTick w
  · intro h
    dsimp [World.step]
    rw [popNextEvent_none_of_count_zero w h]

/-- A min-fold over a list of values all equal to the seed stays at the
    seed. -/
theorem foldl_min_const {α : Type} (f : α → Int) (l : List α) (c : Int)
    (h : ∀ x ∈ l, f x = c) :
    l.foldl (fun acc x => min acc (f x)) c = c := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons, h x (List.mem_cons.mpr (Or.inl rfl)), min_self]
    apply ih
    intro y hy
    exact h y (List.mem_cons.mpr (Or.inr hy))

/-- Cons form of `range (n + 1)` (Mathlib's `range_succ` appends). -/
private theorem range_succ_cons (n : Nat) :
    List.range (n + 1) = 0 :: (List.range n).map (· + 1) := by
  induction n with
  | zero => rw [List.range_succ]; dsimp [List.range]
  | succ n ih =>
    conv => lhs; rw [List.range_succ, ih, List.cons_append]
    conv => rhs; rw [List.range_succ, List.map_append]
    simp

/-- The second component of a pair in a zip belongs to the second list. -/
private theorem snd_mem_zip {α β : Type} (l₁ : List α) (l₂ : List β)
    (a : α) (b : β) (h : (a, b) ∈ l₁.zip l₂) : b ∈ l₂ := by
  revert a b h
  induction l₁ generalizing l₂ with
  | nil => intro a b h; dsimp [List.zip, List.zipWith] at h; cases h
  | cons x xs ih =>
    intro a b h
    cases l₂ with
    | nil => dsimp [List.zip, List.zipWith] at h; cases h
    | cons y ys =>
      dsimp [List.zip, List.zipWith] at h ⊢
      rcases List.mem_cons.mp h with hxy | h
      · rw [Prod.mk.injEq] at hxy
        rcases hxy with ⟨rfl, rfl⟩
        exact List.mem_cons.mpr (Or.inl rfl)
      · exact List.mem_cons.mpr (Or.inr (ih ys a b h))

/-- When the event list starts with an event `e0` targeting the current
    tick and every current-tick event shares `e0`'s priority,
    `popNextEvent` pops `e0` (the list head). -/
theorem popNextEvent_uniform_head (w : World) (e0 : ScheduledEvent)
    (rest : List ScheduledEvent) (e : ScheduledEvent) (w' : World)
    (h : w.popNextEvent = some (e, w'))
    (hev : w.events = e0 :: rest)
    (hhead : e0.targetTick = w.tick)
    (hpri : ∀ ev ∈ e0 :: rest, ev.targetTick = w.tick →
      ev.priority = e0.priority) :
    e = e0 ∧ w' = { w with events := rest } := by
  unfold popNextEvent at h
  rw [hev] at h
  dsimp (config := { zeta := true }) at h
  set candidates := (List.zip (List.range (e0 :: rest).length) (e0 :: rest)).filter
    (fun x => x.2.targetTick == w.tick) with hcdef
  set minPri := candidates.foldl (fun acc x => min acc x.2.priority)
    ((candidates.head?.map (fun x => x.2.priority)).getD 0) with hmdef
  -- the filtered candidates start with `(0, e0)`
  have hQ0 : (e0.targetTick == w.tick) = true := by simp [hhead]
  have hcands0 : (List.zip (List.range (rest.length + 1)) (e0 :: rest)).filter
      (fun x => x.2.targetTick == w.tick) = (0, e0) ::
      ((List.zip ((List.range rest.length).map (· + 1)) rest).filter
        (fun x => x.2.targetTick == w.tick)) := by
    rw [range_succ_cons]
    dsimp [List.zip, List.zipWith, List.filter]
    rw [hQ0]
  have hcands : candidates = (0, e0) ::
      ((List.zip ((List.range rest.length).map (· + 1)) rest).filter
        (fun x => x.2.targetTick == w.tick)) := by
    rw [hcdef]
    exact hcands0
  -- every candidate carries priority `e0.priority`
  have hcandpri : ∀ x ∈ candidates, x.2.priority = e0.priority := by
    intro x hx
    rw [hcdef] at hx
    rcases x with ⟨xi, ev⟩
    have hmem : ev ∈ e0 :: rest :=
      snd_mem_zip (List.range (e0 :: rest).length) (e0 :: rest) xi ev
        ((List.mem_filter.mp hx).1)
    have htick : ev.targetTick = w.tick :=
      Nat.eq_of_beq_eq_true (by simpa using (List.mem_filter.mp hx).2)
    exact hpri ev hmem htick
  -- the min-fold seed and result are both `e0.priority`
  have hmin : ((List.zip (List.range (rest.length + 1)) (e0 :: rest)).filter
      (fun x => x.2.targetTick == w.tick)).foldl
      (fun acc x => min acc x.2.priority)
      ((((List.zip (List.range (rest.length + 1)) (e0 :: rest)).filter
        (fun x => x.2.targetTick == w.tick)).head?.map
        (fun x => x.2.priority)).getD 0) = e0.priority := by
    rw [hcands0]
    dsimp [List.head?, Option.map, Option.getD, List.foldl]
    rw [min_self]
    apply foldl_min_const
    intro x hx
    exact hcandpri x (by rw [hcands]; exact List.mem_cons.mpr (Or.inr hx))
  split at h
  · contradiction
  · split at h
    · contradiction
    · rename_i idx evM hfind
      rw [hmin] at hfind
      rw [hcands0] at hfind
      dsimp [List.find?] at hfind
      have hbeq : (e0.priority == e0.priority) = true := by simp
      rw [hbeq] at hfind
      dsimp at hfind
      rw [Option.some_inj, Prod.mk.injEq] at hfind
      rcases hfind with ⟨rfl, rfl⟩
      rw [Option.some_inj, Prod.mk.injEq] at h
      rcases h with ⟨rfl, hww⟩
      have herase : (e0 :: rest).eraseIdx 0 = rest := rfl
      exact ⟨rfl, by rw [← hww, herase]⟩

/-- Append each event's spawn list, in order. -/
def spawnFold (spawn : ScheduledEvent → List ScheduledEvent) :
    List ScheduledEvent → List ScheduledEvent :=
  List.foldr (fun e a => spawn e ++ a) []

/-- Draining a tick whose front segment `es` consists of same-priority
    current-tick events fires them in list order, regardless of the
    future-tick tail `acc`. Abstractly: firing event `e` appends
    `spawn e` events (at future ticks) and `logLen e` log entries. The
    final events are `acc` followed by the spawns in order; the log gains
    the total number of entries.

    `hfire` carries the node-level content: for the k-th firing it
    receives the *frame* (every node outside the fired prefix still reads
    as in `w`) and must deliver the event/log effect plus *locality*
    (the firing changes no node other than its own). -/
theorem stepUntilNextTick_uniform_drain (w : World)
    (es acc : List ScheduledEvent) (p : Int)
    (spawn : ScheduledEvent → List ScheduledEvent)
    (logLen : ScheduledEvent → Nat)
    (hes : w.events = es ++ acc)
    (hcur : ∀ e ∈ es, e.targetTick = w.tick)
    (hpri : ∀ e ∈ es, e.priority = p)
    (hacc : ∀ e ∈ acc, e.targetTick > w.tick)
    (hfut : ∀ e ∈ es, ∀ e' ∈ spawn e, e'.targetTick > w.tick)
    (hfire : ∀ (k : Nat) (hk : k < es.length) (u : World),
        u.tick = w.tick →
        u.events = es.drop (k + 1) ++ acc ++ spawnFold spawn (es.take k) →
        (∀ id, id ∉ (es.take k).map (fun e => e.nodeId) →
          u.getNode id = w.getNode id) →
        ∃ msgs : List String,
          (u.onScheduledTick (es[k]'hk).nodeId).events =
            u.events ++ spawn (es[k]'hk) ∧
          (u.onScheduledTick (es[k]'hk).nodeId).outputLog =
            u.outputLog ++ msgs ∧
          msgs.length = logLen (es[k]'hk) ∧
          ∀ id, id ≠ (es[k]'hk).nodeId →
            (u.onScheduledTick (es[k]'hk).nodeId).getNode id = u.getNode id) :
    w.stepUntilNextTick.tick = w.tick + 1 ∧
    w.stepUntilNextTick.events = acc ++ spawnFold spawn es ∧
    ∃ msgs, w.stepUntilNextTick.outputLog = w.outputLog ++ msgs ∧
      msgs.length = (es.map logLen).sum := by
  induction es generalizing w acc with
  | nil =>
    have hcnt : countEventAtThisTick w w.tick = 0 := by
      dsimp [countEventAtThisTick]
      have hfil : w.events.filter (fun ev => ev.targetTick == w.tick) = [] := by
        rw [hes]
        dsimp
        apply List.filter_eq_nil_iff.mpr
        intro e he
        have := hacc e he
        simp; omega
      simp [hfil]
    have hstepn : w.step = none := (step_none_iff w).mpr hcnt
    rw [stepUntilNextTick_of_step_none w hstepn]
    refine ⟨rfl, ?_, ?_⟩
    · dsimp [spawnFold]
      rw [hes]
      dsimp
      rw [List.append_nil]
    · refine ⟨[], ?_, ?_⟩
      · rw [List.append_nil]
      · simp
  | cons e0 es' ih =>
    -- e0 is a current-tick event, so the count is positive
    have hcnt : 0 < countEventAtThisTick w w.tick := by
      dsimp [countEventAtThisTick]
      have hmem : e0 ∈ w.events.filter (fun ev => ev.targetTick == w.tick) := by
        rw [List.mem_filter]
        refine ⟨?_, ?_⟩
        · rw [hes]
          exact List.mem_append.mpr
            (Or.inl (List.mem_cons.mpr (Or.inl rfl)))
        · simp [hcur e0 (List.mem_cons.mpr (Or.inl rfl))]
      exact List.length_pos_of_mem hmem
    obtain ⟨ev, wpop, hpop⟩ := popNextEvent_some_of_count_pos w hcnt
    -- the pop takes the head e0
    have hpri' : ∀ evv ∈ e0 :: (es' ++ acc), evv.targetTick = w.tick →
        evv.priority = e0.priority := by
      intro evv hmem htick
      rcases List.mem_cons.mp hmem with rfl | hmem
      · rfl
      · rcases List.mem_append.mp hmem with hmem | hmem
        · rw [hpri evv (List.mem_cons.mpr (Or.inr hmem)),
            ← hpri e0 (List.mem_cons.mpr (Or.inl rfl))]
        · exfalso
          have := hacc evv hmem
          omega
    obtain ⟨heveq, hwpop⟩ := popNextEvent_uniform_head w e0 (es' ++ acc) ev
      wpop hpop (show w.events = e0 :: (es' ++ acc) from hes)
      (hcur e0 (List.mem_cons.mpr (Or.inl rfl))) hpri'
    rw [heveq] at hpop
    clear heveq ev
    set w1 := wpop.onScheduledTick e0.nodeId with hw1
    have hw1tick : w1.tick = w.tick := by
      dsimp [w1]
      rw [World.onScheduledTick_tick, World.popNextEvent_tick w e0 wpop hpop]
    have hstep : w.step = some w1 := by
      dsimp [World.step, w1]
      rw [hpop]
    have hsun : w.stepUntilNextTick = w1.stepUntilNextTick := by
      rw [World.stepUntilNextTick, hstep]
    -- firing e0 (k = 0)
    have hwpop_tick : wpop.tick = w.tick :=
      World.popNextEvent_tick w e0 wpop hpop
    have hwpop_events : wpop.events =
        (e0 :: es').drop 1 ++ acc ++ spawnFold spawn ((e0 :: es').take 0) := by
      rw [hwpop]
      dsimp [spawnFold]
      rw [List.append_nil]
    obtain ⟨msgs0, hev0, hlog0, hlen0, hloc0⟩ :=
      hfire 0 (show 0 < es'.length + 1 from Nat.zero_lt_succ _) wpop
        hwpop_tick hwpop_events (by intro id _; rw [hwpop]; rfl)
    -- normalize the `es[0]` lookups to `e0`
    have hev0' : w1.events = wpop.events ++ spawn e0 := by
      simpa [w1] using hev0
    have hlog0' : w1.outputLog = wpop.outputLog ++ msgs0 := by
      simpa [w1] using hlog0
    -- firing e0 changes no node outside e0
    have hloc0' : ∀ id, id ≠ e0.nodeId → w1.getNode id = wpop.getNode id := by
      simpa [w1] using hloc0
    -- the IH applies to the rest of the cohort
    have hih_hes : w1.events = es' ++ (acc ++ spawn e0) := by
      rw [hev0', hwpop]
      rw [List.append_assoc]
    have hih_hcur : ∀ e ∈ es', e.targetTick = w1.tick := by
      intro e he
      rw [hw1tick]
      exact hcur e (List.mem_cons.mpr (Or.inr he))
    have hih_hpri : ∀ e ∈ es', e.priority = p := by
      intro e he
      exact hpri e (List.mem_cons.mpr (Or.inr he))
    have hih_hacc : ∀ e ∈ acc ++ spawn e0, e.targetTick > w1.tick := by
      intro e he
      rw [hw1tick]
      rcases List.mem_append.mp he with he | he
      · exact hacc e he
      · exact hfut e0 (List.mem_cons.mpr (Or.inl rfl)) e he
    have hih_hfut : ∀ e ∈ es', ∀ e' ∈ spawn e, e'.targetTick > w1.tick := by
      intro e he e' he'
      rw [hw1tick]
      exact hfut e (List.mem_cons.mpr (Or.inr he)) e' he'
    have hih_hfire : ∀ (j : Nat) (hj : j < es'.length) (u : World),
        u.tick = w1.tick →
        u.events = es'.drop (j + 1) ++ (acc ++ spawn e0) ++
          spawnFold spawn (es'.take j) →
        (∀ id, id ∉ (es'.take j).map (fun e => e.nodeId) →
          u.getNode id = w1.getNode id) →
        ∃ msgs : List String,
          (u.onScheduledTick (es'[j]'hj).nodeId).events =
            u.events ++ spawn (es'[j]'hj) ∧
          (u.onScheduledTick (es'[j]'hj).nodeId).outputLog =
            u.outputLog ++ msgs ∧
          msgs.length = logLen (es'[j]'hj) ∧
          ∀ id, id ≠ (es'[j]'hj).nodeId →
            (u.onScheduledTick (es'[j]'hj).nodeId).getNode id = u.getNode id := by
      intro j hj u hutik hevs hfrmu
      have hjk : j + 1 < (e0 :: es').length :=
        show j + 1 < es'.length + 1 from by omega
      have hshape : u.events =
          (e0 :: es').drop (j + 2) ++ acc ++
            spawnFold spawn ((e0 :: es').take (j + 1)) := by
        rw [hevs]
        dsimp [spawnFold]
        rw [List.append_assoc, List.append_assoc, ← List.append_assoc]
      -- frame relative to w: everything off the fired prefix keeps w's nodes
      have hfrm : ∀ id,
          id ∉ ((e0 :: es').take (j + 1)).map (fun e => e.nodeId) →
          u.getNode id = w.getNode id := by
        intro id hid
        have hne0 : id ≠ e0.nodeId := by
          intro heq
          exact hid (by rw [heq]; exact List.mem_cons.mpr (Or.inl rfl))
        have hnotin : id ∉ (es'.take j).map (fun e => e.nodeId) := by
          intro hm
          exact hid (List.mem_cons.mpr (Or.inr hm))
        rw [hfrmu id hnotin, hloc0' id hne0, hwpop]
        rfl
      obtain ⟨msgs, hmev, hmlg, hmlen, hlocj⟩ :=
        hfire (j + 1) hjk u (by rw [hutik, hw1tick]) hshape hfrm
      exact ⟨msgs, hmev, hmlg, hmlen, hlocj⟩
    obtain ⟨htik, hevs, msgs', hlog, hlen⟩ :=
      ih w1 (acc ++ spawn e0) hih_hes hih_hcur hih_hpri hih_hacc
        hih_hfut hih_hfire
    rw [hsun]
    refine ⟨?_, ?_, ?_⟩
    · rw [htik, hw1tick]
    · dsimp [spawnFold] at hevs ⊢
      rw [← List.append_assoc]
      exact hevs
    · refine ⟨msgs0 ++ msgs', ?_, ?_⟩
      · rw [hlog, hlog0']
        have hlogw : wpop.outputLog = w.outputLog := by rw [hwpop]
        rw [hlogw, ← List.append_assoc]
      · rw [List.length_append, hlen0, hlen]
        simp
