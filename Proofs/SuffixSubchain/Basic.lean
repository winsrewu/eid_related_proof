import Proofs.SuffixSubchain.OrderTransport
import Proofs.Clustering.Basic
import Proofs.Model.OutputPos
import Proofs.Model.ListOrder
import Mathlib.Data.List.Perm.Basic

open BasicRedstoneSim

/-! # Suffix sub-chains

The last `n` repeaters of a chain form a suffix sub-chain. Two chains that
share their last `n` repeaters form one family.

The file states two results. A chain family outputs as one block at the
common tick `T`. Within a family, the output order equals the order in
which the first suffix repeater events are added to the queue.

The suffix algebra (definitions and the matching lemmas) lives in
`Proofs.SuffixSubchain.Algebra`. The descent lives in
`Proofs.SuffixSubchain.Descent`. -/

/-- The time from the first suffix repeater to the output. It is the sum
    of the suffix delays after the first repeater. -/
def suffixTailDelay (sfx : List (PNat × Int)) : Nat :=
  ((sfx.drop 1).map fun dp => (dp.1 : Nat)).sum

/-- The firing tick of the first suffix repeater. All chains that share
    the suffix `sfx` fire at this tick. -/
def suffixFirstTick (T : Nat) (sfx : List (PNat × Int)) : Nat :=
  T - suffixTailDelay sfx

/-- The position of chain `i`'s first suffix repeater event in the pop
    sequence, at the common suffix tick. -/
def firstSuffixRepPos (T : Nat) (specs : List ChainSpec) (actOrd : List Nat)
    (pos : Nat → Nat → Nat) (n : Nat) (sfx : List (PNat × Int)) (i : Nat) : Nat :=
  (_root_.findIdx? (fun e => decide (e = stageEventOf T specs i (repLenAt specs i + 1 - n)))
    (popSeq (simWorld T specs actOrd pos (suffixFirstTick T sfx)))).getD 0

/-- `suffixTailDelay s` is the sum of the delays of the last `n - 1`
    repeaters of any chain sharing the `n`-suffix `s`. -/
theorem suffixTailDelay_eq (specs : List ChainSpec) (i n : Nat) (s : List (PNat × Int))
    (hpri : (specAt specs i).priLenOk) (hspec : (specAt specs i).suffixSpec n = some s) :
    suffixTailDelay s = suffixDelaySum specs i (n - 1) := by
  induction n generalizing s with
  | zero =>
      dsimp [suffixTailDelay, suffixDelaySum]
      have hs : s = [] := by
        dsimp [ChainSpec.suffixSpec] at hspec
        simp_all [List.drop_length]
      subst s
      rfl
  | succ n' ih =>
      cases n' with
      | zero =>
          dsimp [suffixTailDelay, suffixDelaySum]
          have hs_len : s.length = 1 := by
            have hs : s = (specAt specs i).repeaterSeq.drop
                ((specAt specs i).repeaterSeq.length - 1) := by
              dsimp [ChainSpec.suffixSpec] at hspec
              split at hspec <;> simp_all
            rw [hs, List.length_drop]
            have hn_le : 1 ≤ (specAt specs i).repeaterSeq.length := by
              have h := suffixSpec_repLen_ge specs i 1 s hpri hspec
              rw [← repeaterSeq_length specs i hpri] at h
              exact h
            exact Nat.sub_sub_self hn_le
          have hdrop : s.drop 1 = [] := by
            rw [List.drop_eq_nil_iff]
            omega
          rw [hdrop]
          rfl
      | succ m =>
          have hdrop_spec : (specAt specs i).suffixSpec (m + 1) = some (s.drop 1) := by
            exact suffixSpec_drop_one specs i (m + 2) s hpri (by omega) hspec
          have hih := ih (s.drop 1) hdrop_spec
          have hlen_gt : 1 < s.length := by
            have hs_len : s.length = m + 2 := by
              have hs : s = (specAt specs i).repeaterSeq.drop
                  ((specAt specs i).repeaterSeq.length - (m + 2)) := by
                dsimp [ChainSpec.suffixSpec] at hspec
                split at hspec <;> simp_all
              rw [hs, List.length_drop]
              have hn_le : m + 2 ≤ (specAt specs i).repeaterSeq.length := by
                have h := suffixSpec_repLen_ge specs i (m + 2) s hpri hspec
                rw [← repeaterSeq_length specs i hpri] at h
                exact h
              exact Nat.sub_sub_self hn_le
            omega
          have hdrop_cons : s.drop 1 = s[1] :: s.drop 2 := by
            exact List.drop_eq_getElem_cons hlen_gt
          have hget : s[1] =
              (stageDelayAt specs i (repLenAt specs i - m),
                stagePriAt specs i (repLenAt specs i - m)) := by
            have hq : s[1]? =
                some (stageDelayAt specs i (repLenAt specs i - m),
                  stagePriAt specs i (repLenAt specs i - m)) := by
              have hq0 := suffixSpec_getElem specs i (m + 2) m s hpri hspec (by omega)
              have hidx : (m + 2) - 1 - m = 1 := by omega
              simpa [hidx] using hq0
            have hq1 : s[1]? = some (s[1]) := List.getElem?_eq_getElem hlen_gt
            exact Option.some_inj.mp (hq1.symm.trans hq)
          dsimp [suffixTailDelay]
          rw [hdrop_cons]
          simp only [List.map_cons, List.sum_cons]
          have hget1 : (s[1].1 : Nat) =
              (stageDelayAt specs i (repLenAt specs i - m) : Nat) := by
            exact congrArg (fun p : PNat × Int => (p.1 : Nat)) hget
          rw [hget1]
          dsimp [suffixDelaySum]
          have hdrop2 : s.drop 2 = (s.drop 1).drop 1 := by
            rw [List.drop_drop]
          have hsdrop2 : ((s.drop 2).map (fun dp => (dp.1 : Nat))).sum =
              suffixDelaySum specs i m := by
            rw [hdrop2]
            dsimp [suffixTailDelay] at hih
            exact hih
          rw [hsdrop2]

/-- The first suffix repeater of a chain sharing suffix `s` fires at
    `suffixFirstTick T s`. -/
theorem suffixFirstTick_stageTickOf (T : Nat) (specs : List ChainSpec) (i n : Nat)
    (s : List (PNat × Int))
    (hpri : (specAt specs i).priLenOk)
    (hfit : chainDelay (specAt specs i) ≤ T)
    (hspec : (specAt specs i).suffixSpec n = some s)
    (hn : 1 ≤ n) :
    stageTickOf T specs i (repLenAt specs i + 1 - n) = suffixFirstTick T s := by
  have hi_ge : n ≤ repLenAt specs i + 1 := suffixSpec_repLen_ge specs i n s hpri hspec
  have hsub := stageTickOf_sub_delays T specs i hfit (n - 1) (by omega)
  have harg : repLenAt specs i - (n - 1) = repLenAt specs i + 1 - n := by omega
  rw [harg] at hsub
  have htail := suffixTailDelay_eq specs i n s hpri hspec
  dsimp [suffixFirstTick]
  rw [← htail] at hsub
  omega

/-- `outputPos` being `some px` pins the pop-sequence position of the
    last-repeater event. -/
private theorem outputPos_findIdx_some (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (h_fit : ∀ i < specs.length, chainDelay (specAt specs i) ≤ T)
    (x : Nat) (hx : x < specs.length) (px : Nat)
    (hp : outputPos (simulate T specs actOrd pos) x = some px) :
    ∃ r, _root_.findIdx?
        (fun e => decide (e = stageEventOf T specs x (repLenAt specs x)))
        (popSeq (simWorld T specs actOrd pos T)) = some r ∧
      px = T + 1 + r := by
  have hs := outputPos_simulate T specs actOrd pos x h_valid h_perm h_fit hx
  rw [hs] at hp
  cases hf : _root_.findIdx?
      (fun e => decide (e = stageEventOf T specs x (repLenAt specs x)))
      (popSeq (simWorld T specs actOrd pos T)) with
  | none => simp [hf] at hp
  | some r =>
      refine ⟨r, ?_⟩
      constructor
      · rfl
      · simp [hf] at hp
        exact hp.symm

/-- **Suffix clustering.** Two chains share their last `n` repeaters. If a
    third chain outputs between these two chains at the common tick `T`,
    then the third chain shares the same last `n` repeaters.

    The shared suffix is `some s`. A chain with fewer than `n` repeaters
    gives `none` and is not in the family. -/
theorem suffix_clustering
    (n : Nat)
    (T : Nat) (specs : List ChainSpec) (actOrd : List Nat)
    (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (h_fit : ∀ i < specs.length, chainDelay (specAt specs i) ≤ T) :
    let log := simulate T specs actOrd pos
    ∀ i j k p_i p_j p_k s,
      i < specs.length → j < specs.length → k < specs.length →
      outputPos log i = some p_i → outputPos log j = some p_j →
      outputPos log k = some p_k →
      p_i < p_j → p_j < p_k →
      (specAt specs i).suffixSpec n = some s →
      (specAt specs k).suffixSpec n = some s →
      (specAt specs j).suffixSpec n = some s := by
  intro log i j k p_i p_j p_k s hi hj hk hpi hpj hpk hpij hpjk hi_spec hk_spec
  by_cases hn0 : n = 0
  · subst n
    have hs : s = [] := by
      simp [ChainSpec.suffixSpec] at hi_spec
      exact hi_spec
    subst s
    simp [ChainSpec.suffixSpec]
  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
    set wT := simWorld T specs actOrd pos T
    have hpri_i : (specAt specs i).priLenOk := (h_valid i hi).1
    have hpri_j : (specAt specs j).priLenOk := (h_valid j hj).1
    have hpri_k : (specAt specs k).priLenOk := (h_valid k hk).1
    -- pin the three pop-sequence positions
    obtain ⟨ri, hfi, hpi_eq⟩ := outputPos_findIdx_some T specs actOrd pos
      h_valid h_perm h_fit i hi p_i hpi
    obtain ⟨rj, hfj, hpj_eq⟩ := outputPos_findIdx_some T specs actOrd pos
      h_valid h_perm h_fit j hj p_j hpj
    obtain ⟨rk, hfk, hpk_eq⟩ := outputPos_findIdx_some T specs actOrd pos
      h_valid h_perm h_fit k hk p_k hpk
    have hpos_i : (_root_.findIdx?
        (fun e => decide (e = stageEventOf T specs i (repLenAt specs i)))
        (popSeq wT)).getD 0 = ri :=
      findIdx?_getD_eq_of_some (popSeq wT) (stageEventOf T specs i (repLenAt specs i)) ri hfi
    have hpos_j : (_root_.findIdx?
        (fun e => decide (e = stageEventOf T specs j (repLenAt specs j)))
        (popSeq wT)).getD 0 = rj :=
      findIdx?_getD_eq_of_some (popSeq wT) (stageEventOf T specs j (repLenAt specs j)) rj hfj
    have hpos_k : (_root_.findIdx?
        (fun e => decide (e = stageEventOf T specs k (repLenAt specs k)))
        (popSeq wT)).getD 0 = rk :=
      findIdx?_getD_eq_of_some (popSeq wT) (stageEventOf T specs k (repLenAt specs k)) rk hfk
    have hrij : ri < rj := by
      rw [hpi_eq, hpj_eq] at hpij
      omega
    have hrjk : rj < rk := by
      rw [hpj_eq, hpk_eq] at hpjk
      omega
    have hfindij : (_root_.findIdx?
        (fun e => decide (e = stageEventOf T specs i (repLenAt specs i)))
        (popSeq wT)).getD 0 <
          (_root_.findIdx?
            (fun e => decide (e = stageEventOf T specs j (repLenAt specs j)))
            (popSeq wT)).getD 0 := by
      rw [hpos_i, hpos_j]
      exact hrij
    have hfindjk : (_root_.findIdx?
        (fun e => decide (e = stageEventOf T specs j (repLenAt specs j)))
        (popSeq wT)).getD 0 <
          (_root_.findIdx?
            (fun e => decide (e = stageEventOf T specs k (repLenAt specs k)))
            (popSeq wT)).getD 0 := by
      rw [hpos_j, hpos_k]
      exact hrjk
    -- membership of the three last-repeater events
    have hev_i_mem : stageEventOf T specs i (repLenAt specs i) ∈ popSeq wT :=
      findIdx?_mem_of_some (popSeq wT) (stageEventOf T specs i (repLenAt specs i)) ri hfi
    have hev_j_mem : stageEventOf T specs j (repLenAt specs j) ∈ popSeq wT :=
      findIdx?_mem_of_some (popSeq wT) (stageEventOf T specs j (repLenAt specs j)) rj hfj
    have hev_k_mem : stageEventOf T specs k (repLenAt specs k) ∈ popSeq wT :=
      findIdx?_mem_of_some (popSeq wT) (stageEventOf T specs k (repLenAt specs k)) rk hfk
    -- the pop sequence is priority-sorted
    have hsorted : (popSeq wT).Pairwise (fun a b => a.priority ≤ b.priority) :=
      popSeq_sorted_priority wT
    -- suffix matching at distance 0 (the last repeater)
    have hpri_ik0 : stagePriAt specs i (repLenAt specs i) =
        stagePriAt specs k (repLenAt specs k) := by
      simpa [Nat.sub_zero] using
        (suffixStage_eq specs i k n 0 s hpri_i hpri_k hi_spec hk_spec (by omega)).2
    have hdelay_ik0 : stageDelayAt specs i (repLenAt specs i) =
        stageDelayAt specs k (repLenAt specs k) := by
      simpa [Nat.sub_zero] using
        (suffixStage_eq specs i k n 0 s hpri_i hpri_k hi_spec hk_spec (by omega)).1
    -- priority sandwich: last priorities agree
    have hxz : (stageEventOf T specs i (repLenAt specs i)).priority =
        (stageEventOf T specs k (repLenAt specs k)).priority := by
      dsimp [stageEventOf]
      exact hpri_ik0
    have hpri_eq : stagePriAt specs j (repLenAt specs j) =
        stagePriAt specs i (repLenAt specs i) :=
      pairwise_le_sandwich (popSeq wT) (fun e => e.priority) hsorted
        hev_i_mem hev_j_mem hev_k_mem hfindij hfindjk hxz
    have hlastPri_eq : (specAt specs j).lastPriority =
        (specAt specs i).lastPriority := by
      have hle_i : (specAt specs i).middleDelays.length ≤ repLenAt specs i := by
        simp [repLenAt]
      have hle_j : (specAt specs j).middleDelays.length ≤ repLenAt specs j := by
        simp [repLenAt]
      rw [stagePriAt_of_eq specs i hpri_i hle_i,
        stagePriAt_of_eq specs j hpri_j hle_j] at hpri_eq
      exact hpri_eq
    -- delay equality: the sandwiched chain shares the reference lastDelay
    have hlastPri_ik : (specAt specs i).lastPriority = (specAt specs k).lastPriority := by
      have hle_i : (specAt specs i).middleDelays.length ≤ repLenAt specs i := by
        simp [repLenAt]
      have hle_k : (specAt specs k).middleDelays.length ≤ repLenAt specs k := by
        simp [repLenAt]
      rw [stagePriAt_of_eq specs i hpri_i hle_i,
        stagePriAt_of_eq specs k hpri_k hle_k] at hpri_ik0
      exact hpri_ik0
    have hlastPri_jk : (specAt specs j).lastPriority = (specAt specs k).lastPriority := by
      rw [hlastPri_eq, hlastPri_ik]
    have hdelay_ij := lastRep_delay_ge_of_before T specs actOrd pos h_valid h_perm h_fit
      i j hi hj hev_i_mem hev_j_mem hlastPri_eq.symm hfindij
    have hdelay_jk := lastRep_delay_ge_of_before T specs actOrd pos h_valid h_perm h_fit
      j k hj hk hev_j_mem hev_k_mem hlastPri_jk hfindjk
    have hdelay_ki : (specAt specs k).lastDelay = (specAt specs i).lastDelay := by
      have hle_i : (specAt specs i).middleDelays.length ≤ repLenAt specs i := by
        simp [repLenAt]
      have hle_k : (specAt specs k).middleDelays.length ≤ repLenAt specs k := by
        simp [repLenAt]
      rw [stageDelayAt_of_eq specs i hle_i, stageDelayAt_of_eq specs k hle_k] at hdelay_ik0
      exact hdelay_ik0.symm
    have hdelay_jge_i : (specAt specs j).lastDelay ≥ (specAt specs i).lastDelay := by
      rw [hdelay_ki] at hdelay_jk
      exact hdelay_jk
    have hlastDelay_eq : (specAt specs j).lastDelay = (specAt specs i).lastDelay :=
      le_antisymm hdelay_ij hdelay_jge_i
    -- the suffix sandwich descent and the suffix equality
    obtain ⟨hj_ge, hstage⟩ := suffix_sandwich_descent n T specs actOrd pos
      h_valid h_perm h_fit i j k hi hj hk s hi_spec hk_spec hfindij hfindjk
      hlastPri_eq hlastDelay_eq
    exact suffixSpec_eq_of_stage_eq specs i j n s hpri_i hpri_j hi_spec hj_ge hstage

/-- **Suffix order preservation.** Within a suffix family, the output order
    equals the order in which the first suffix repeater events are added to
    the queue. -/
theorem suffix_order_preservation
    (n : Nat) (hn : 1 ≤ n)
    (T : Nat) (specs : List ChainSpec) (actOrd : List Nat)
    (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (h_fit : ∀ i < specs.length, chainDelay (specAt specs i) ≤ T) :
    let log := simulate T specs actOrd pos
    ∀ i j p_i p_j s,
      i < specs.length → j < specs.length →
      outputPos log i = some p_i → outputPos log j = some p_j →
      (specAt specs i).suffixSpec n = some s →
      (specAt specs j).suffixSpec n = some s →
      (p_i < p_j ↔
        firstSuffixRepPos T specs actOrd pos n s i <
        firstSuffixRepPos T specs actOrd pos n s j) := by
  intro log i j p_i p_j s hi hj hpi hpj hi_spec hj_spec
  set wT := simWorld T specs actOrd pos T
  have hpri_i : (specAt specs i).priLenOk := (h_valid i hi).1
  have hpri_j : (specAt specs j).priLenOk := (h_valid j hj).1
  -- pin the two output positions to the last-repeater pop positions
  obtain ⟨ri, hfi, hpi_eq⟩ := outputPos_findIdx_some T specs actOrd pos
    h_valid h_perm h_fit i hi p_i hpi
  obtain ⟨rj, hfj, hpj_eq⟩ := outputPos_findIdx_some T specs actOrd pos
    h_valid h_perm h_fit j hj p_j hpj
  have hpos_i : (_root_.findIdx?
      (fun e => decide (e = stageEventOf T specs i (repLenAt specs i)))
      (popSeq wT)).getD 0 = ri :=
    findIdx?_getD_eq_of_some (popSeq wT) (stageEventOf T specs i (repLenAt specs i)) ri hfi
  have hpos_j : (_root_.findIdx?
      (fun e => decide (e = stageEventOf T specs j (repLenAt specs j)))
      (popSeq wT)).getD 0 = rj :=
    findIdx?_getD_eq_of_some (popSeq wT) (stageEventOf T specs j (repLenAt specs j)) rj hfj
  -- last-repeater pop order ↔ output order
  have hlast : (_root_.findIdx?
      (fun e => decide (e = stageEventOf T specs i (repLenAt specs i)))
      (popSeq wT)).getD 0 <
      (_root_.findIdx?
        (fun e => decide (e = stageEventOf T specs j (repLenAt specs j)))
        (popSeq wT)).getD 0 ↔ p_i < p_j := by
    constructor
    · intro hlt
      have hri : ri < rj := by
        rw [hpos_i, hpos_j] at hlt
        exact hlt
      rw [hpi_eq, hpj_eq]
      omega
    · intro hlt
      have hri : ri < rj := by
        rw [hpi_eq, hpj_eq] at hlt
        omega
      rw [hpos_i, hpos_j]
      exact hri
  -- last-repeater pop order ↔ the pair transport's `wI 0` order
  have hlast0 : (eventIdx (wI T specs actOrd pos i 0) (evI T specs i 0) <
      eventIdx (wI T specs actOrd pos i 0) (evJ T specs j 0)) ↔
      (_root_.findIdx?
        (fun e => decide (e = stageEventOf T specs i (repLenAt specs i)))
        (popSeq wT)).getD 0 <
      (_root_.findIdx?
        (fun e => decide (e = stageEventOf T specs j (repLenAt specs j)))
        (popSeq wT)).getD 0 := by
    dsimp [eventIdx, evI, evJ, wI, wT]
    rw [stageTickOf_last T specs i (h_fit i hi)]
  -- the pair transport across the whole suffix
  have hpair := suffix_pair_order_forward n T specs actOrd pos h_valid h_perm h_fit
    i j hi hj s hi_spec hj_spec hn
  -- the pair transport's `wI (n - 1)` order ↔ first-suffix-repeater order
  have hfirst0 : (eventIdx (wI T specs actOrd pos i (n - 1)) (evI T specs i (n - 1)) <
      eventIdx (wI T specs actOrd pos i (n - 1)) (evJ T specs j (n - 1))) ↔
      firstSuffixRepPos T specs actOrd pos n s i <
        firstSuffixRepPos T specs actOrd pos n s j := by
    dsimp [eventIdx, evI, evJ, wI, firstSuffixRepPos]
    have harg_i : repLenAt specs i - (n - 1) = repLenAt specs i + 1 - n := by omega
    have harg_j : repLenAt specs j - (n - 1) = repLenAt specs j + 1 - n := by omega
    rw [harg_i, harg_j]
    have htick_i : stageTickOf T specs i (repLenAt specs i + 1 - n) = suffixFirstTick T s :=
      suffixFirstTick_stageTickOf T specs i n s hpri_i (h_fit i hi) hi_spec hn
    rw [htick_i]
  -- assemble
  constructor
  · intro hlt_p
    have h1 := hlast.mpr hlt_p
    have h2 := hlast0.mpr h1
    have h3 := hpair.mp h2
    exact hfirst0.mp h3
  · intro hlt_f
    have h1 := hfirst0.mpr hlt_f
    have h2 := hpair.mpr h1
    have h3 := hlast0.mp h2
    exact hlast.mp h3
