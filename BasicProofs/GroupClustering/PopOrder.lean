import BasicProofs.GroupClustering.QueueMembership


open BasicRedstoneSim List

/-! # Group clustering — pop order

`popNextEvent` pops, among the events due at the current tick, the one with the
minimum priority, breaking ties by list position (first in list wins). This file
characterizes that choice: the popped event is due, has minimum priority among
due events, and is the first element of the due-sublist achieving that minimum.
Later parts use this to show same-priority due events pop in list order.
-/

/-- Split a list around index `i`: `l = l.take i ++ [l[i]] ++ l.drop (i + 1)`. -/
private theorem take_getElem_drop_split {α : Type} (l : List α) (i : Nat)
    (h : i < l.length) :
    l = l.take i ++ l[i]'h :: l.drop (i + 1) := by
  revert i h
  induction l with
  | nil => intro i h; cases h
  | cons x xs ih =>
    intro i
    cases i with
    | zero =>
      intro h
      simp [List.take, List.drop]
    | succ i' =>
      intro h
      have h' : i' < xs.length := by simpa [List.length] using h
      simp only [List.take, List.drop, List.getElem_cons_succ]
      congr 1
      exact ih i' h'

/-- The popped event is due, has minimum priority among the due events, and is
    the first due event (in list order) whose priority attains that minimum. -/
theorem popNextEvent_first_min_priority (w : World) (ev : ScheduledEvent) (w' : World)
    (h : w.popNextEvent = some (ev, w')) :
    ev.targetTick = w.tick ∧
    (∀ e ∈ w.events.filter (fun e => e.targetTick == w.tick), ev.priority ≤ e.priority) ∧
    ∃ l₁ l₂, w.events.filter (fun e => e.targetTick == w.tick) = l₁ ++ ev :: l₂ ∧
      ∀ e ∈ l₁, ev.priority < e.priority := by
  have h_pop := h
  unfold World.popNextEvent at h
  dsimp (config := { zeta := true }) at h
  set indexed := List.zip (List.range w.events.length) w.events
  set candidates := indexed.filter (fun (_, e) => e.targetTick == w.tick)
  set initPri := candidates.head?.map (fun (_, e) => e.priority) |>.getD 0
  set minPri := candidates.foldl (fun acc (_, e) => min acc e.priority) initPri
  split at h
  · injection h
  · split at h
    · injection h
    · rename_i idx ev_found h_find
      rw [Option.some_inj, Prod.mk.injEq] at h
      rcases h with ⟨h_ev, _⟩
      -- rewrite the found event (idx, ev_found) to (idx, ev); keeps `ev` in scope
      rw [h_ev] at h_find
      obtain ⟨h_pri_b, i, h_i, h_cand_i, h_earlier⟩ :=
        List.find?_eq_some_iff_getElem.mp h_find
      have h_pri : ev.priority = minPri := of_decide_eq_true h_pri_b
      have h_map : candidates.map Prod.snd =
          w.events.filter (fun e => e.targetTick == w.tick) := by
        dsimp [candidates, indexed]
        exact zip_filter_map_snd_eq (List.range w.events.length) w.events w.tick
          (by simp)
      constructor
      · -- ev is due
        have h_mem : candidates[i]'h_i ∈ candidates := List.getElem_mem h_i
        dsimp [candidates] at h_mem
        rw [List.mem_filter] at h_mem
        obtain ⟨_, h_due⟩ := h_mem
        rw [h_cand_i] at h_due
        dsimp at h_due
        simpa [Nat.beq_eq] using h_due
      · constructor
        · -- minimum priority among due events
          have h_min := popNextEvent_min_priority w ev w' h_pop
          intro e h_e
          rw [List.mem_filter] at h_e
          obtain ⟨h_e_mem, h_e_due⟩ := h_e
          exact h_min e h_e_mem (by simpa [Nat.beq_eq] using h_e_due)
        · -- first due event attaining the minimum
          use (candidates.map Prod.snd).take i, (candidates.map Prod.snd).drop (i + 1)
          constructor
          · have h_D_len : i < (candidates.map Prod.snd).length := by
              rwa [List.length_map]
            have h_D_i : (candidates.map Prod.snd)[i]'h_D_len = ev := by
              rw [List.getElem_map, h_cand_i]
            have h_Dsplit := take_getElem_drop_split (candidates.map Prod.snd) i h_D_len
            rw [h_D_i] at h_Dsplit
            exact h_map.symm.trans h_Dsplit
          · intro e h_e
            obtain ⟨m, h_m_lt, h_m_eq⟩ := List.getElem_of_mem h_e
            have h_m_lt_i : m < i := by
              have h_len : ((candidates.map Prod.snd).take i).length ≤ i := by
                rw [List.length_take]; exact min_le_left i _
              exact Nat.lt_of_lt_of_le h_m_lt h_len
            have h_m_lt_len : m < candidates.length := Nat.lt_trans h_m_lt_i h_i
            have h_e_cand : e = (candidates[m]'h_m_lt_len).2 := by
              rw [← h_m_eq, List.getElem_take, List.getElem_map]
            have h_ne : (candidates[m]'h_m_lt_len).2.priority ≠ minPri := by
              simpa using h_earlier m h_m_lt_i
            have h_le : minPri ≤ (candidates[m]'h_m_lt_len).2.priority :=
              foldl_min_le_all candidates initPri (candidates[m]'h_m_lt_len)
                (List.getElem_mem h_m_lt_len)
            rw [h_pri, h_e_cand]
            omega

/-- If `A` and `D` are both due events, `A` appears strictly before `D` in the due-sublist,
    the due-sublist is duplicate-free, and `A.priority ≤ D.priority`, then `popNextEvent`
    does not return `D`: the popped event is the first due event attaining the minimum
    priority, and `A` attains that minimum no later than `D`. -/
theorem popNextEvent_not_later_same_priority (w : World) (A D ev : ScheduledEvent)
    (w' : World) (h_pop : w.popNextEvent = some (ev, w'))
    (h_nodup : (w.events.filter (fun e => e.targetTick == w.tick)).Nodup)
    (iA iD : Nat)
    (hA : iA < (w.events.filter (fun e => e.targetTick == w.tick)).length)
    (hD : iD < (w.events.filter (fun e => e.targetTick == w.tick)).length)
    (h_lt : iA < iD)
    (h_getA : (w.events.filter (fun e => e.targetTick == w.tick))[iA]'hA = A)
    (h_getD : (w.events.filter (fun e => e.targetTick == w.tick))[iD]'hD = D)
    (h_pri : A.priority ≤ D.priority) :
    ev ≠ D := by
  set due := w.events.filter (fun e => e.targetTick == w.tick)
  obtain ⟨_, h_min_all, m₁, m₂, h_split, h_m₁⟩ := popNextEvent_first_min_priority w ev w' h_pop
  intro h_ev_D
  subst ev
  -- restate the split with the `due` abbreviation so `rw` can find it
  have h_split' : due = m₁ ++ D :: m₂ := h_split
  -- A is due, and D is the minimum-priority due event, so their priorities coincide
  have hA_mem : A ∈ due := by
    rw [← h_getA]
    exact List.getElem_mem hA
  have h_le_DA : D.priority ≤ A.priority := h_min_all A hA_mem
  have h_pri_eq : A.priority = D.priority := le_antisymm h_pri h_le_DA
  -- D cannot sit in the strict-minimum prefix m₁
  have h_D_not_mem : D ∉ m₁ := by
    intro h_D_mem
    have := h_m₁ D h_D_mem
    omega
  -- due[m₁.length] = D via the split
  have h_len_lt : m₁.length < due.length := by
    rw [h_split']
    simp
  have h_get_mid : due[m₁.length]'h_len_lt = D :=
    List.getElem_of_append h_split' rfl
  -- the due-sublist is Nodup, so D occurs at the unique index m₁.length
  have h_iD : iD = m₁.length :=
    (List.Nodup.getElem_inj_iff h_nodup).mp (h_getD.trans h_get_mid.symm)
  -- hence iA < m₁.length and A lies in due.take m₁.length = m₁
  have h_iA_lt_m1 : iA < m₁.length := by omega
  have hA_take : A ∈ due.take (m₁.length) := by
    rw [← h_getA]
    rw [List.getElem_take' hA h_iA_lt_m1]
    exact List.getElem_mem (by
      rw [List.length_take]
      exact Nat.lt_min.mpr ⟨h_iA_lt_m1, hA⟩)
  have h_take_eq : due.take (m₁.length) = m₁ := by
    rw [h_split', List.take_append_length]
  have hA_mem_m1 : A ∈ m₁ := by rwa [← h_take_eq]
  -- but every element of m₁ has priority strictly above D's
  have := h_m₁ A hA_mem_m1
  omega
