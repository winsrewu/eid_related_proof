import Proofs.Model.DescentConclusion
import Proofs.Model.OutputPos
import Proofs.Model.ChainIds
import Proofs.Model.ListOrder

open BasicRedstoneSim
open List

/-! # Order preservation theorem (no-group model)

All chains output on a common tick `T`. Within any one spec class, the order
in which the chains output equals the order in which they activated
(`actOrd`). -/

/-- An injective map preserves first-occurrence position. -/
theorem findIdx?_getD_map_inj {α : Type} [DecidableEq α] (l : List Nat) (f : Nat → α)
    (i : Nat) (hi : i ∈ l) (hinj : ∀ k ∈ l, ∀ k' ∈ l, f k = f k' → k = k') :
    (_root_.findIdx? (fun a => decide (a = f i)) (l.map f)).getD 0 =
      (_root_.findIdx? (fun k => decide (k = i)) l).getD 0 := by
  rw [_root_.findIdx?_map]
  congr 1
  refine findIdx?_congr_pointwise ((fun a => decide (a = f i)) ∘ f)
    (fun k => decide (k = i)) l l rfl ?_
  intro k hk
  have hmem : l[k] ∈ l := List.getElem_mem hk
  have hiff : f (l[k]) = f i ↔ l[k] = i := by
    constructor
    · intro h
      exact hinj (l[k]) hmem i hi h
    · intro h
      rw [h]
  simp [hiff]

/-- The activation position equals the `decide (=)`-based first occurrence. -/
private theorem actPos_eq_findIdx (l : List Nat) (i : Nat) :
    actPos l i = (_root_.findIdx? (fun x => decide (x = i)) l).getD 0 := by
  dsimp [actPos]
  have hfind : _root_.findIdx? (fun x => x == i) l =
      _root_.findIdx? (fun x => decide (x = i)) l :=
    findIdx?_congr_pointwise (fun x => x == i) (fun x => decide (x = i)) l l rfl
      (by intro k _hk; exact _root_.beq_eq_decide (l[k]) i)
  rw [hfind]

/-- **Order preservation.** For any valid no-group system whose chains all
    output on tick `T`, two same-spec chains output in the same relative
    order as they appear in the global activation order `actOrd`. -/
theorem order_preservation
    (T : Nat) (specs : List ChainSpec) (actOrd : List Nat)
    (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (h_fit : ∀ i < specs.length, chainDelay (specAt specs i) ≤ T) :
    let log := simulate T specs actOrd pos
    ∀ i j p_i p_j,
      i < specs.length → j < specs.length →
      outputPos log i = some p_i → outputPos log j = some p_j →
      specAt specs i = specAt specs j →
      (p_i < p_j ↔ actPos actOrd i < actPos actOrd j) := by
  intro log i j p_i p_j hi hj hpi hpj hspec
  set wT := simWorld T specs actOrd pos T
  set c := specAt specs i
  -- class membership
  have hclass_lt : ∀ k ∈ classActOrder specs actOrd c, k < specs.length := by
    intro k hk
    exact List.mem_range.mp ((List.Perm.mem_iff h_perm).mp (List.mem_filter.mp hk).1)
  have hclass_spec : ∀ k ∈ classActOrder specs actOrd c, specAt specs k = c := by
    intro k hk
    exact of_decide_eq_true (List.mem_filter.mp hk).2
  have hi_mem : i ∈ classActOrder specs actOrd c := by
    dsimp [classActOrder]
    rw [List.mem_filter]
    exact ⟨(List.Perm.mem_iff h_perm).mpr (List.mem_range.mpr hi), by simp [c]⟩
  have hj_mem : j ∈ classActOrder specs actOrd c := by
    dsimp [classActOrder]
    rw [List.mem_filter]
    exact ⟨(List.Perm.mem_iff h_perm).mpr (List.mem_range.mpr hj), by simp [c, hspec]⟩
  -- the class's last-repeater events appear in activation order in the pop seq
  have hdescent : classStageEvts T specs actOrd c (repLenAt specs i) <+ popSeq wT :=
    classLastReps_popSeq_sublist T specs actOrd pos c i h_valid h_perm h_fit
      hi_mem hclass_lt
  have hpopNd : (popSeq wT).Nodup := popSeq_nodup_of_tickInv T specs h_valid T
    wT.events [] wT (by dsimp [wT]; rw [simWorld_tick])
    (simWorld_tickInv T specs actOrd pos h_valid h_perm T)
  have hactNd : actOrd.Nodup := h_perm.nodup_iff.mpr List.nodup_range
  -- membership of the two last-repeater events in the class stage events
  have hfi_mem : stageEventOf T specs i (repLenAt specs i) ∈
      classStageEvts T specs actOrd c (repLenAt specs i) := by
    dsimp [classStageEvts]
    exact List.mem_map.mpr ⟨i, hi_mem, rfl⟩
  have hfj_mem : stageEventOf T specs j (repLenAt specs i) ∈
      classStageEvts T specs actOrd c (repLenAt specs i) := by
    dsimp [classStageEvts]
    exact List.mem_map.mpr ⟨j, hj_mem, rfl⟩
  have hev_i_mem : stageEventOf T specs i (repLenAt specs i) ∈ popSeq wT :=
    List.Sublist.mem hfi_mem hdescent
  have hev_j_mem : stageEventOf T specs j (repLenAt specs i) ∈ popSeq wT :=
    List.Sublist.mem hfj_mem hdescent
  -- injectivity of `stageEventOf T specs · (repLenAt specs i)` on the class
  have hinj : ∀ k ∈ classActOrder specs actOrd c, ∀ k' ∈ classActOrder specs actOrd c,
      stageEventOf T specs k (repLenAt specs i) = stageEventOf T specs k' (repLenAt specs i) →
        k = k' := by
    intro k hk k' hk' hff
    have hnode : chainRepId specs k (repLenAt specs i) =
        chainRepId specs k' (repLenAt specs i) := by
      exact congrArg ScheduledEvent.nodeId hff
    have hk_lt : k < specs.length := hclass_lt k hk
    have hk'_lt : k' < specs.length := hclass_lt k' hk'
    have hrepk : (specAt specs k).middleDelays.length = repLenAt specs i := by
      rw [hclass_spec k hk]
      rfl
    have hrepk' : (specAt specs k').middleDelays.length = repLenAt specs i := by
      rw [hclass_spec k' hk']
      rfl
    have hb : repLenAt specs i ≤ (specAt specs k).middleDelays.length := by rw [hrepk]
    have hb' : repLenAt specs i ≤ (specAt specs k').middleDelays.length := by rw [hrepk']
    have hpri : (specAt specs k).priLenOk := (h_valid k hk_lt).1
    have hpri' : (specAt specs k').priLenOk := (h_valid k' hk'_lt).1
    exact (chainRepId_inj specs k k' (repLenAt specs i) (repLenAt specs i)
      hk_lt hk'_lt hb hb' hpri hpri' hnode).1
  -- the pop-sequence order equals the class activation order
  have hcore :
      (_root_.findIdx? (fun e => decide (e = stageEventOf T specs i (repLenAt specs i)))
        (popSeq wT)).getD 0 <
        (_root_.findIdx? (fun e => decide (e = stageEventOf T specs j (repLenAt specs i)))
        (popSeq wT)).getD 0 ↔
      actPos actOrd i < actPos actOrd j := by
    calc
      (_root_.findIdx? (fun e => decide (e = stageEventOf T specs i (repLenAt specs i)))
          (popSeq wT)).getD 0 <
        (_root_.findIdx? (fun e => decide (e = stageEventOf T specs j (repLenAt specs i)))
          (popSeq wT)).getD 0
          ↔ (_root_.findIdx? (fun e => decide (e = stageEventOf T specs i (repLenAt specs i)))
              (classStageEvts T specs actOrd c (repLenAt specs i))).getD 0 <
            (_root_.findIdx? (fun e => decide (e = stageEventOf T specs j (repLenAt specs i)))
              (classStageEvts T specs actOrd c (repLenAt specs i))).getD 0 :=
            findIdx?_getD_lt_sublist hdescent hpopNd hfi_mem hfj_mem
      _ ↔ (_root_.findIdx? (fun k => decide (k = i)) (classActOrder specs actOrd c)).getD 0 <
            (_root_.findIdx? (fun k => decide (k = j)) (classActOrder specs actOrd c)).getD 0 := by
            dsimp only [classStageEvts]
            rw [findIdx?_getD_map_inj (classActOrder specs actOrd c)
                (fun k => stageEventOf T specs k (repLenAt specs i)) i hi_mem hinj,
              findIdx?_getD_map_inj (classActOrder specs actOrd c)
                (fun k => stageEventOf T specs k (repLenAt specs i)) j hj_mem hinj]
      _ ↔ (_root_.findIdx? (fun k => decide (k = i)) actOrd).getD 0 <
            (_root_.findIdx? (fun k => decide (k = j)) actOrd).getD 0 := by
            dsimp only [classActOrder]
            exact (findIdx?_getD_lt_sublist
              (List.filter_sublist (l := actOrd)
                (p := fun k => decide (specAt specs k = c)))
              hactNd hi_mem hj_mem).symm
      _ ↔ actPos actOrd i < actPos actOrd j := by
            rw [← actPos_eq_findIdx actOrd i, ← actPos_eq_findIdx actOrd j]
  -- connect output positions to the pop-sequence positions
  obtain ⟨ki, hki⟩ := findIdx?_some_of_mem (popSeq wT)
    (stageEventOf T specs i (repLenAt specs i)) hev_i_mem
  obtain ⟨kj, hkj⟩ := findIdx?_some_of_mem (popSeq wT)
    (stageEventOf T specs j (repLenAt specs i)) hev_j_mem
  have hpi_simplified : outputPos log i =
      some (T + 1 + (_root_.findIdx? (fun e => decide (e = stageEventOf T specs i (repLenAt specs i)))
        (popSeq wT)).getD 0) := by
    rw [outputPos_simulate T specs actOrd pos i h_valid h_perm h_fit hi]
    rw [hki]
    rfl
  have hpj_simplified : outputPos log j =
      some (T + 1 + (_root_.findIdx? (fun e => decide (e = stageEventOf T specs j (repLenAt specs i)))
        (popSeq wT)).getD 0) := by
    rw [outputPos_simulate T specs actOrd pos j h_valid h_perm h_fit hj]
    have heq : stageEventOf T specs j (repLenAt specs j) =
        stageEventOf T specs j (repLenAt specs i) := by
      exact congrArg (stageEventOf T specs j) (repLenAt_spec specs i j hspec).symm
    rw [heq]
    rw [hkj]
    rfl
  have hp_i : p_i = T + 1 + (_root_.findIdx?
      (fun e => decide (e = stageEventOf T specs i (repLenAt specs i))) (popSeq wT)).getD 0 := by
    have : some (T + 1 + (_root_.findIdx?
        (fun e => decide (e = stageEventOf T specs i (repLenAt specs i))) (popSeq wT)).getD 0) =
        some p_i := by
      rw [← hpi_simplified, hpi]
    exact (Option.some_inj.mp this).symm
  have hp_j : p_j = T + 1 + (_root_.findIdx?
      (fun e => decide (e = stageEventOf T specs j (repLenAt specs i))) (popSeq wT)).getD 0 := by
    have : some (T + 1 + (_root_.findIdx?
        (fun e => decide (e = stageEventOf T specs j (repLenAt specs i))) (popSeq wT)).getD 0) =
        some p_j := by
      rw [← hpj_simplified, hpj]
    exact (Option.some_inj.mp this).symm
  -- assemble
  constructor
  · intro hpij
    have hlt : (_root_.findIdx? (fun e => decide (e = stageEventOf T specs i (repLenAt specs i)))
        (popSeq wT)).getD 0 <
        (_root_.findIdx? (fun e => decide (e = stageEventOf T specs j (repLenAt specs i)))
        (popSeq wT)).getD 0 := by
      rw [hp_i, hp_j] at hpij
      omega
    exact hcore.mp hlt
  · intro hactij
    have hlt : (_root_.findIdx? (fun e => decide (e = stageEventOf T specs i (repLenAt specs i)))
        (popSeq wT)).getD 0 <
        (_root_.findIdx? (fun e => decide (e = stageEventOf T specs j (repLenAt specs i)))
        (popSeq wT)).getD 0 := hcore.mpr hactij
    rw [hp_i, hp_j]
    omega
