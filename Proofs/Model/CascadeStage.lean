import Proofs.Model.Basic
import Proofs.Model.SimLemmas
import Proofs.Model.WorldInvariants
import Proofs.Model.Cascade
import Proofs.Model.CascadeDrain
import Proofs.Model.CascadeRealization
import Mathlib.Data.List.Defs
import Mathlib.Data.List.Basic
import Mathlib.Tactic

open BasicRedstoneSim
open World

/-! # One cascade stage for a cohort

A cohort of chains that all stand at the same cascade stage: every chain's
current repeater has a pending event at the same tick with the same
priority. Draining the tick fires them in cohort order, and each schedules
its successor. Instantiates `stepUntilNextTick_uniform_drain`. -/

/-- One cohort chain's data at a cascade stage: the repeater to fire and
    its successor's id, delay and priority. -/
structure StageEntry where
  rep : Nat
  next : Nat
  nextDelay : PNat
  nextPri : Int

/-- The pending stage event of one cohort chain. -/
def stageEvent (τ : Nat) (p : Int) (s : StageEntry) : ScheduledEvent :=
  { targetTick := τ, priority := p, nodeId := s.rep }

/-- The event a fired cohort chain schedules for its successor. -/
def stageNextEvent (τ : Nat) (s : StageEntry) : ScheduledEvent :=
  { targetTick := τ + (s.nextDelay : Nat), priority := s.nextPri,
    nodeId := s.next }

/-- The spawn function of a cohort stage: an event whose node is a cohort
    repeater spawns that chain's successor event; anything else spawns
    nothing. -/
def stageSpawn (τ : Nat) (stage : List StageEntry)
    (e : ScheduledEvent) : List ScheduledEvent :=
  match stage.find? (fun s => s.rep == e.nodeId) with
  | some s => [stageNextEvent τ s]
  | none => []

/-! ## List helpers for the cohort shape -/

private theorem take_map {α β : Type} (f : α → β) (l : List α) (k : Nat) :
    (l.map f).take k = (l.take k).map f := by
  induction l generalizing k with
  | nil => simp [List.take_nil]
  | cons x xs ih =>
    cases k with
    | zero => rfl
    | succ k' =>
      change (f x :: xs.map f).take (k' + 1) =
        ((x :: xs).take (k' + 1)).map f
      rw [List.take_succ_cons, ih, List.take_succ_cons]
      rfl

private theorem mem_of_take {α : Type} (l : List α) (k : Nat) (x : α)
    (h : x ∈ l.take k) : x ∈ l := by
  induction l generalizing k with
  | nil => rw [List.take_nil] at h; cases h
  | cons x' xs ih =>
    cases k with
    | zero => rw [List.take_zero] at h; cases h
    | succ k' =>
      rw [List.take_succ_cons] at h
      rcases List.mem_cons.mp h with heq | h
      · subst heq
        exact List.mem_cons.mpr (Or.inl rfl)
      · exact List.mem_cons.mpr (Or.inr (ih k' h))

/-- In a duplicate-free list, an element at position `j` that also lies in
    `take k` must satisfy `j < k`. -/
private theorem lt_of_getElem_mem_take {α : Type} (l : List α) (k j : Nat)
    (hj : j < l.length) (hl : l.Nodup) (hmem : l[j]'hj ∈ l.take k) :
    j < k := by
  induction l generalizing k j with
  | nil => dsimp at hj; omega
  | cons x xs ih =>
    cases k with
    | zero => rw [List.take_zero] at hmem; cases hmem
    | succ k' =>
      rw [List.take_succ_cons] at hmem
      cases j with
      | zero => omega
      | succ j' =>
        have hj' : j' < xs.length := by dsimp [List.length] at hj; omega
        rcases List.mem_cons.mp hmem with heq | hmem'
        · exfalso
          exact (List.nodup_cons.mp hl).1 (heq ▸ List.getElem_mem hj')
        · exact Nat.succ_lt_succ_iff.mpr
            (ih k' j' hj' (List.nodup_cons.mp hl).2 hmem')

/-- Duplicate-free `rep`s mean equal `rep`s at two positions force equal
    positions. -/
private theorem rep_inj_of_nodup (stage : List StageEntry) (i j : Nat)
    (hi : i < stage.length) (hj : j < stage.length)
    (hnodup : (stage.map StageEntry.rep).Nodup)
    (heq : (stage[i]'hi).rep = (stage[j]'hj).rep) : i = j := by
  induction stage generalizing i j with
  | nil => simp at hi
  | cons s ss ih =>
    dsimp [List.map] at hnodup
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j' =>
        exfalso
        have hj' : j' < ss.length := by dsimp [List.length] at hj; omega
        exact (List.nodup_cons.mp hnodup).1
          (heq.symm ▸ List.mem_map.mpr ⟨ss[j']'hj', List.getElem_mem hj', rfl⟩)
    | succ i' =>
      cases j with
      | zero =>
        exfalso
        have hi' : i' < ss.length := by dsimp [List.length] at hi; omega
        exact (List.nodup_cons.mp hnodup).1
          (heq ▸ List.mem_map.mpr ⟨ss[i']'hi', List.getElem_mem hi', rfl⟩)
      | succ j' =>
        have hi' : i' < ss.length := by dsimp [List.length] at hi; omega
        have hj' : j' < ss.length := by dsimp [List.length] at hj; omega
        have heq' : (ss[i']'hi').rep = (ss[j']'hj').rep := by
          simpa using heq
        exact congrArg (· + 1)
          (ih i' j' hi' hj' (List.nodup_cons.mp hnodup).2 heq')

/-- Over a duplicate-free cohort, `find?` locates the k-th entry by its
    repeater id. -/
theorem find?_stage_getElem (stage : List StageEntry) (k : Nat)
    (hk : k < stage.length)
    (hnodup : (stage.map StageEntry.rep).Nodup) :
    stage.find? (fun s => s.rep == (stage[k]'hk).rep) =
      some (stage[k]'hk) := by
  generalize hs0 : (stage[k]'hk) = s0
  induction stage generalizing k with
  | nil => simp at hk
  | cons s ss ih =>
    dsimp [List.find?, List.map] at hnodup ⊢
    cases k with
    | zero =>
      have hs : s = s0 := by simpa using hs0
      rw [hs, nat_beq_true_self]
    | succ k' =>
      have hk' : k' < ss.length := by dsimp [List.length] at hk; omega
      have hs0' : ss[k']'hk' = s0 := by simpa using hs0
      have hne : s.rep ≠ s0.rep := by
        rw [← hs0']
        intro heq
        exact (List.nodup_cons.mp hnodup).1
          (heq.symm ▸ List.mem_map.mpr ⟨ss[k']'hk', List.getElem_mem hk', rfl⟩)
      rw [nat_beq_false_of_ne _ _ hne]
      dsimp
      exact ih k' hk' (List.nodup_cons.mp hnodup).2 hs0'

/-- `spawnFold` with per-element-equal spawn functions agrees. -/
private theorem spawnFold_congr (l : List ScheduledEvent)
    (f g : ScheduledEvent → List ScheduledEvent)
    (h : ∀ e ∈ l, f e = g e) :
    spawnFold f l = spawnFold g l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    dsimp [spawnFold]
    rw [h x (List.mem_cons.mpr (Or.inl rfl))]
    apply congrArg (List.append (g x))
    apply ih
    intro e he
    exact h e (List.mem_cons.mpr (Or.inr he))

/-- `spawnFold` over the cohort's stage events is the successor-event list
    in cohort order. -/
theorem spawnFold_stage_map (stage : List StageEntry) (τ : Nat) (p : Int)
    (hnodup : (stage.map StageEntry.rep).Nodup) :
    spawnFold (stageSpawn τ stage) (stage.map (stageEvent τ p)) =
      stage.map (stageNextEvent τ) := by
  induction stage with
  | nil => rfl
  | cons s ss ih =>
    have hnodup' : (ss.map StageEntry.rep).Nodup :=
      (List.nodup_cons.mp hnodup).2
    have htail : ∀ e ∈ ss.map (stageEvent τ p),
        stageSpawn τ (s :: ss) e = stageSpawn τ ss e := by
      intro e he
      obtain ⟨t, ht, htE⟩ := List.mem_map.mp he
      have hne : s.rep ≠ e.nodeId := by
        rw [← htE]
        dsimp [stageEvent]
        intro heq
        exact (List.nodup_cons.mp hnodup).1
          (heq.symm ▸ List.mem_map.mpr ⟨t, ht, rfl⟩)
      dsimp [stageSpawn, List.find?]
      rw [nat_beq_false_of_ne _ _ hne]
    change stageSpawn τ (s :: ss) (stageEvent τ p s) ++
      spawnFold (stageSpawn τ (s :: ss)) (ss.map (stageEvent τ p)) =
      stageNextEvent τ s :: ss.map (stageNextEvent τ)
    rw [spawnFold_congr (ss.map (stageEvent τ p))
      (stageSpawn τ (s :: ss)) (stageSpawn τ ss) htail]
    rw [ih hnodup']
    dsimp [stageSpawn, stageEvent, List.find?]
    rw [nat_beq_true_self]
    dsimp [stageNextEvent]

/-- Draining one cohort stage: all pending stage events fire in cohort
    order, each scheduling its successor; no output is logged. -/
theorem stepUntilNextTick_repeater_stage (w : World) (τ : Nat) (p : Int)
    (stage : List StageEntry) (acc : List ScheduledEvent)
    (hτ : τ = w.tick)
    (hes : w.events = stage.map (stageEvent τ p) ++ acc)
    (hnext_notrep : ∀ s t, s ∈ stage → t ∈ stage → s.next ≠ t.rep)
    (hnodup : (stage.map StageEntry.rep).Nodup)
    (hrep : ∀ s ∈ stage, ∃ (nd : NodeData) (d : PNat) (pri : Int),
        w.getNode s.rep = some nd ∧ nd.kind = NodeKind.repeater d pri ∧
        nd.outputs = [s.next])
    (hnextkind : ∀ s ∈ stage, ∃ nd, w.getNode s.next = some nd ∧
        nd.kind = NodeKind.repeater s.nextDelay s.nextPri)
    (hacc : ∀ e ∈ acc, e.targetTick > w.tick) :
    w.stepUntilNextTick.tick = w.tick + 1 ∧
    w.stepUntilNextTick.events = acc ++ stage.map (stageNextEvent τ) ∧
    w.stepUntilNextTick.outputLog = w.outputLog := by
  -- the cohort events as the drain's front segment
  have hcur : ∀ e ∈ stage.map (stageEvent τ p), e.targetTick = w.tick := by
    intro e he
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp he
    dsimp [stageEvent]
    exact hτ
  have hpri : ∀ e ∈ stage.map (stageEvent τ p), e.priority = p := by
    intro e he
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp he
    dsimp [stageEvent]
  have hfut : ∀ e ∈ stage.map (stageEvent τ p),
      ∀ e' ∈ stageSpawn τ stage e, e'.targetTick > w.tick := by
    intro e he e' he'
    dsimp [stageSpawn] at he'
    generalize hfind : stage.find? (fun s => s.rep == e.nodeId) = fo at he'
    cases fo with
    | none => cases he'
    | some s =>
      have heq : e' = stageNextEvent τ s := by simpa using he'
      subst heq
      dsimp [stageNextEvent]
      rw [hτ]
      exact Nat.lt_add_of_pos_right (PNat.pos s.nextDelay)
  -- the per-event firing obligation
  have hfire : ∀ (k : Nat) (hk : k < (stage.map (stageEvent τ p)).length)
      (u : World),
      u.tick = w.tick →
      u.events = (stage.map (stageEvent τ p)).drop (k + 1) ++ acc ++
        spawnFold (stageSpawn τ stage)
          ((stage.map (stageEvent τ p)).take k) →
      (∀ id, id ∉ ((stage.map (stageEvent τ p)).take k).map
          (fun e => e.nodeId) → u.getNode id = w.getNode id) →
      ∃ msgs : List String,
        (u.onScheduledTick ((stage.map (stageEvent τ p))[k]'hk).nodeId).events =
          u.events ++ stageSpawn τ stage ((stage.map (stageEvent τ p))[k]'hk) ∧
        (u.onScheduledTick ((stage.map (stageEvent τ p))[k]'hk).nodeId).outputLog =
          u.outputLog ++ msgs ∧
        msgs.length = 0 ∧
        ∀ id, id ≠ ((stage.map (stageEvent τ p))[k]'hk).nodeId →
          (u.onScheduledTick ((stage.map (stageEvent τ p))[k]'hk).nodeId).getNode id =
            u.getNode id := by
    intro k hk u hutik hevs hframe
    have hk' : k < stage.length := by simpa [List.length_map] using hk
    set s := stage[k]'hk' with hsdef
    obtain ⟨ndRep, d, pri, hgetRep, hkindRep, houtsRep⟩ :=
      hrep s (List.getElem_mem hk')
    obtain ⟨ndNext, hgetNext, hkindNext⟩ :=
      hnextkind s (List.getElem_mem hk')
    -- the take-k nodeIds are exactly the take-k reps
    have htake_map : ((stage.map (stageEvent τ p)).take k).map
        (fun e => e.nodeId) = (stage.take k).map StageEntry.rep := by
      rw [take_map, List.map_map]
      have hpoint : ((fun e => e.nodeId) ∘ stageEvent τ p) =
          (fun e : StageEntry => e.rep) := by
        ext e
        dsimp [stageEvent]
      rw [hpoint]
    -- frame at the fired repeater
    have hframeRep : u.getNode s.rep = w.getNode s.rep := by
      apply hframe
      intro hm
      rw [htake_map] at hm
      obtain ⟨s'', hs'', hs''rep⟩ := List.mem_map.mp hm
      obtain ⟨j, hj, hjE⟩ :=
        List.mem_iff_getElem.mp (mem_of_take stage k s'' hs'')
      have hjk : j = k := by
        apply rep_inj_of_nodup stage j k hj hk' hnodup
        rw [hjE]
        exact hs''rep
      have hin : (stage.map StageEntry.rep)[j]'(by
            simpa [List.length_map] using hj) ∈
            (stage.map StageEntry.rep).take k := by
        have h1 : (stage.map StageEntry.rep)[j]'(by
            simpa [List.length_map] using hj) = s''.rep := by
          simp [hjE]
        rw [h1, take_map]
        exact List.mem_map.mpr ⟨s'', hs'', rfl⟩
      exact (ne_of_lt (lt_of_getElem_mem_take
        (stage.map StageEntry.rep) k j
        (by simpa [List.length_map] using hj) hnodup hin)) hjk
    -- frame at the successor
    have hframeNext : u.getNode s.next = w.getNode s.next := by
      apply hframe
      intro hm
      rw [htake_map] at hm
      obtain ⟨s'', hs'', hs''rep⟩ := List.mem_map.mp hm
      have heq2 : s.next = s''.rep := by
        dsimp [s] at hs''rep
        exact hs''rep.symm
      exact hnext_notrep s s'' (List.getElem_mem hk')
        (mem_of_take stage k s'' hs'') heq2
    have hgetRep' : u.getNode s.rep = some ndRep := by
      rw [hframeRep, hgetRep]
    have hgetNext' : u.getNode s.next = some ndNext := by
      rw [hframeNext, hgetNext]
    have hne : s.next ≠ s.rep :=
      hnext_notrep s s (List.getElem_mem hk') (List.getElem_mem hk')
    have hevEff := onScheduledTick_repeater_schedules_next u s.rep
      s.next ndRep ndNext d pri s.nextPri s.nextDelay hne hgetRep'
      hkindRep houtsRep hgetNext' hkindNext
    have hlogEff := onScheduledTick_repeater_outputLog u s.rep
      s.next ndRep ndNext d pri s.nextPri s.nextDelay hne hgetRep'
      hkindRep houtsRep hgetNext' hkindNext
    have hevnode : ((stage.map (stageEvent τ p))[k]'hk).nodeId = s.rep := by
      simp [s, stageEvent]
    have hspawn : stageSpawn τ stage
        ((stage.map (stageEvent τ p))[k]'hk) = [stageNextEvent τ s] := by
      dsimp [stageSpawn]
      rw [hevnode, find?_stage_getElem stage k hk' hnodup]
    refine ⟨[], ?_, ?_, rfl, ?_⟩
    · rw [hevnode, hspawn, hevEff]
      congr 1
      dsimp [stageNextEvent]
      rw [hutik, hτ.symm]
    · rw [hevnode, List.append_nil]
      exact hlogEff
    · intro id hne'
      rw [hevnode] at hne'
      rw [hevnode]
      exact onScheduledTick_getNode_of_ne u s.rep id hne'
  -- run the drain
  have hdrain := stepUntilNextTick_uniform_drain w
    (stage.map (stageEvent τ p)) acc p (stageSpawn τ stage) (fun _ => 0)
    hes hcur hpri hacc hfut hfire
  rcases hdrain with ⟨htick, hevents, msgs, hlog, hlen⟩
  have hsum : ((stage.map (stageEvent τ p)).map (fun _ => 0)).sum = 0 := by
    generalize hstage : stage.map (stageEvent τ p) = es
    clear hstage
    induction es with
    | nil => rfl
    | cons e es ih =>
      change 0 + (es.map (fun _ => 0)).sum = 0
      rw [ih]
  rw [hsum] at hlen
  refine ⟨htick, ?_, ?_⟩
  · rw [hevents, spawnFold_stage_map stage τ p hnodup]
  · cases msgs with
    | nil => simpa using hlog
    | cons m ms =>
      simp at hlen
