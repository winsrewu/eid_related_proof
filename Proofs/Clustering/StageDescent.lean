import Proofs.Clustering.Chronology


open BasicRedstoneSim
open List

/-! # Stage-descent primitives (no-group clustering)

One-step delay/order monotonicity and the spawn-membership facts that
ground the recursive descent. -/

/-- A stage-`s` event is enqueued at tick `stageTickOf … (s - 1)` when its
    predecessor middle repeater fires. -/
theorem stageRep_mem_spawn (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (c : Nat) (hc : c < specs.length)
    (h_fit : chainDelay (specAt specs c) ≤ T)
    (s : Nat) (hs : s < repLenAt specs c) :
    stageEventOf T specs c (s + 1) ∈
      spawnFold (cascadeSpawn T specs)
        (popSeq (simWorld T specs actOrd pos (stageTickOf T specs c s))) := by
  have hpresent : stageEventOf T specs c s ∈
      (simWorld T specs actOrd pos (stageTickOf T specs c s)).events :=
    stageEvent_present T specs actOrd pos h_valid h_perm c hc h_fit s (Nat.le_of_lt hs)
  have hdue : (stageEventOf T specs c s).targetTick = stageTickOf T specs c s := by
    dsimp [stageEventOf]
  have hpop : stageEventOf T specs c s ∈
      popSeq (simWorld T specs actOrd pos (stageTickOf T specs c s)) := by
    have htick := simWorld_tick T specs actOrd pos (stageTickOf T specs c s)
    exact mem_popSeq_of_due
      (simWorld T specs actOrd pos (stageTickOf T specs c s))
      (stageEventOf T specs c s) hpresent (by simpa [htick] using hdue)
  have hspawn : cascadeSpawn T specs (stageEventOf T specs c s) =
      [stageEventOf T specs c (s + 1)] :=
    cascadeSpawn_stage T specs h_valid c s hc hs
  exact mem_spawnFold_of_mem (cascadeSpawn T specs)
    (popSeq (simWorld T specs actOrd pos (stageTickOf T specs c s)))
    (stageEventOf T specs c (s + 1))
    (stageEventOf T specs c s) hpop (by rw [hspawn]; simp)

/-- A stage-`0` event is enqueued at the observer's firing tick. -/
theorem stageRep_mem_spawn_zero (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (c : Nat) (hc : c < specs.length) :
    stageEventOf T specs c 0 ∈
      spawnFold (cascadeSpawn T specs)
        (popSeq (simWorld T specs actOrd pos (obsTickOf T specs c))) := by
  have hpresent : obsEventOf T specs c ∈
      (simWorld T specs actOrd pos (obsTickOf T specs c)).events :=
    obsEvent_present T specs actOrd pos h_valid h_perm c hc
  have hdue : (obsEventOf T specs c).targetTick = obsTickOf T specs c := by
    dsimp [obsEventOf]
  have hpop : obsEventOf T specs c ∈
      popSeq (simWorld T specs actOrd pos (obsTickOf T specs c)) := by
    have htick := simWorld_tick T specs actOrd pos (obsTickOf T specs c)
    exact mem_popSeq_of_due
      (simWorld T specs actOrd pos (obsTickOf T specs c))
      (obsEventOf T specs c) hpresent (by simpa [htick] using hdue)
  have hspawn : cascadeSpawn T specs (obsEventOf T specs c) =
      [stageEventOf T specs c 0] := by
    rw [cascadeSpawn_obs T specs c hc]
  exact mem_spawnFold_of_mem (cascadeSpawn T specs)
    (popSeq (simWorld T specs actOrd pos (obsTickOf T specs c)))
    (stageEventOf T specs c 0)
    (obsEventOf T specs c) hpop (by rw [hspawn]; simp)

/-- Chronological half at an arbitrary stage: a smaller stage delay enqueues
    later, so it sits later in the queue at the (common) firing tick. -/
theorem stageRep_index_gt_of_delay_lt (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (h_fit : ∀ i < specs.length, chainDelay (specAt specs i) ≤ T)
    (x y s : Nat) (hx : x < specs.length) (hy : y < specs.length)
    (hsx : s < repLenAt specs x) (hsy : s < repLenAt specs y)
    (hpos : 0 < s)
    (htick_eq : stageTickOf T specs x s = stageTickOf T specs y s)
    (hlt : stageDelayAt specs x s < stageDelayAt specs y s) :
    (_root_.findIdx? (fun e => decide (e = stageEventOf T specs x s))
        ((simWorld T specs actOrd pos (stageTickOf T specs x s)).events)).getD 0 >
      (_root_.findIdx? (fun e => decide (e = stageEventOf T specs y s))
        ((simWorld T specs actOrd pos (stageTickOf T specs y s)).events)).getD 0 := by
  set ex := stageEventOf T specs x s
  set ey := stageEventOf T specs y s
  set τ := stageTickOf T specs x s
  have hτy : stageTickOf T specs y s = τ := htick_eq.symm
  set px := stageTickOf T specs x (s - 1)
  set py := stageTickOf T specs y (s - 1)
  set dx := (stageDelayAt specs x s : Nat)
  set dy := (stageDelayAt specs y s : Nat)
  have htick_ex : ex.targetTick = τ := by
    dsimp [ex, stageEventOf, τ]
  have htick_ey : ey.targetTick = τ := by
    dsimp [ey, stageEventOf]
    rw [hτy]
  have hsucc_x : τ = px + dx := by
    have hsx' : (s - 1) + 1 ≤ (specAt specs x).middleDelays.length := by
      dsimp [repLenAt] at hsx
      omega
    have hsucc := stageTickOf_succ T specs x (s - 1) hsx'
    have hpred : s - 1 + 1 = s := by omega
    simpa [px, dx, τ, hpred] using hsucc
  have hsucc_y : τ = py + dy := by
    have hsy' : (s - 1) + 1 ≤ (specAt specs y).middleDelays.length := by
      dsimp [repLenAt] at hsy
      omega
    have hsucc := stageTickOf_succ T specs y (s - 1) hsy'
    have hpred : s - 1 + 1 = s := by omega
    have hsucc' : stageTickOf T specs y s = py + dy := by
      simpa [py, dy, hpred] using hsucc
    simpa [hτy] using hsucc'
  have hltN : dx < dy := by
    exact_mod_cast hlt
  have hpx_eq : px = τ - dx := by
    omega
  have hpy_eq : py = τ - dy := by
    omega
  have hpos_dx : 1 ≤ dx := by
    have h := PNat.pos (stageDelayAt specs x s)
    dsimp [dx]
    omega
  have hdelay_x_le : dx ≤ τ := by
    omega
  have hdelay_y_le : dy ≤ τ := by
    omega
  have hpy_lt_px : py < px := by
    rw [hpy_eq, hpx_eq]
    omega
  have hpx_ge : py + 1 ≤ px := by omega
  have hpx_le_τ : px ≤ τ := by
    rw [hpx_eq]
    omega
  -- y's stage-s event is enqueued at py and present at py + 1
  have hspawn_y : stageEventOf T specs y s ∈
      spawnFold (cascadeSpawn T specs)
        (popSeq (simWorld T specs actOrd pos py)) := by
    have hsy_prev : s - 1 < repLenAt specs y := by
      dsimp [repLenAt] at hsy ⊢
      omega
    have hsp := stageRep_mem_spawn T specs actOrd pos h_valid h_perm y hy
      (h_fit y hy) (s - 1) hsy_prev
    have hpred : s - 1 + 1 = s := by omega
    simpa [py, hpred] using hsp
  have hsub_py := simWorld_succ_survivors_before_spawns T specs actOrd pos h_valid h_perm py
  have hey_py1 : ey ∈ (simWorld T specs actOrd pos (py + 1)).events := by
    have hm : ey ∈
        (simWorld T specs actOrd pos py).events.filter (fun e => e.targetTick > py) ++
          spawnFold (cascadeSpawn T specs) (popSeq (simWorld T specs actOrd pos py)) := by
      rw [List.mem_append]
      exact Or.inr (by simpa [ey] using hspawn_y)
    exact List.Sublist.mem hm hsub_py
  -- ey survives from py + 1 to px
  have hsurv_delta : [ey] <+ (simWorld T specs actOrd pos px).events := by
    have h := simWorld_sublist_survive_delta T specs actOrd pos (py + 1) (px - (py + 1)) [ey]
      (List.singleton_sublist.mpr hey_py1)
      (by
        intro e he
        rw [List.mem_singleton] at he
        subst e
        rw [htick_ey]
        have hsum : (py + 1) + (px - (py + 1)) = px := by omega
        rw [hsum]
        exact hpx_le_τ)
    have harg : (py + 1) + (px - (py + 1)) = px := by omega
    simpa [harg] using h
  have hey_px : ey ∈ (simWorld T specs actOrd pos px).events :=
    List.singleton_sublist.mp hsurv_delta
  -- x's stage-s event spawns at px
  have hspawn_x : stageEventOf T specs x s ∈
      spawnFold (cascadeSpawn T specs)
        (popSeq (simWorld T specs actOrd pos px)) := by
    have hsx_prev : s - 1 < repLenAt specs x := by
      dsimp [repLenAt] at hsx ⊢
      omega
    have hsp := stageRep_mem_spawn T specs actOrd pos h_valid h_perm x hx
      (h_fit x hx) (s - 1) hsx_prev
    have hpred : s - 1 + 1 = s := by omega
    simpa [px, hpred] using hsp
  -- survivor ey precedes fresh spawn ex at tick px
  have hsub_px := simWorld_succ_survivors_before_spawns T specs actOrd pos h_valid h_perm px
  set pre := (simWorld T specs actOrd pos px).events.filter (fun e => e.targetTick > px)
  set rest := spawnFold (cascadeSpawn T specs) (popSeq (simWorld T specs actOrd pos px))
  have hsub_px' : pre ++ rest <+ (simWorld T specs actOrd pos (px + 1)).events := by
    simpa [pre, rest] using hsub_px
  have hey_pre : ey ∈ pre := by
    dsimp [pre]
    rw [List.mem_filter]
    exact ⟨hey_px, decide_eq_true_eq.mpr (by rw [htick_ey, hpx_eq]; omega)⟩
  have hex_rest : ex ∈ rest := by
    dsimp [rest, ex]
    simpa using hspawn_x
  have hex_in_concat : ex ∈ pre ++ rest := by
    rw [List.mem_append]; exact Or.inr hex_rest
  have hey_in_concat : ey ∈ pre ++ rest := by
    rw [List.mem_append]; exact Or.inl hey_pre
  have hnodup_next : (simWorld T specs actOrd pos (px + 1)).events.Nodup :=
    (simWorld_tickInv T specs actOrd pos h_valid h_perm (px + 1)).1
  have hnd_concat : (pre ++ rest).Nodup := List.Sublist.nodup hsub_px' hnodup_next
  have hdisj := (List.nodup_append.mp hnd_concat).2.2
  have hex_not_pre : ex ∉ pre := by
    intro h
    exact hdisj ex h ex hex_rest rfl
  have hlt_concat : (_root_.findIdx? (fun e => decide (e = ey)) (pre ++ rest)).getD 0 <
      (_root_.findIdx? (fun e => decide (e = ex)) (pre ++ rest)).getD 0 :=
    findIdx?_lt_of_prefix_mem pre rest (x := ey) (y := ex)
      hey_pre hex_in_concat hex_not_pre
  have hlt_next : (_root_.findIdx? (fun e => decide (e = ey))
      (simWorld T specs actOrd pos (px + 1)).events).getD 0 <
        (_root_.findIdx? (fun e => decide (e = ex))
          (simWorld T specs actOrd pos (px + 1)).events).getD 0 :=
    (findIdx?_getD_lt_sublist (l₁ := pre ++ rest)
      (l₂ := (simWorld T specs actOrd pos (px + 1)).events)
      hsub_px' hnodup_next (x := ey) (y := ex) hey_in_concat hex_in_concat).mpr hlt_concat
  -- survive from px + 1 to τ (both fire at τ)
  have hex_next : ex ∈ (simWorld T specs actOrd pos (px + 1)).events :=
    List.Sublist.mem hex_in_concat hsub_px'
  have hey_next : ey ∈ (simWorld T specs actOrd pos (px + 1)).events :=
    List.Sublist.mem hey_in_concat hsub_px'
  have hargτ : (px + 1) + (τ - (px + 1)) = τ := by
    rw [hpx_eq]
    omega
  have htgt_exN : (px + 1) + (τ - (px + 1)) ≤ ex.targetTick := by
    simp [htick_ex, hargτ]
  have htgt_eyN : (px + 1) + (τ - (px + 1)) ≤ ey.targetTick := by
    simp [htick_ey, hargτ]
  have horder := simWorld_findIdx_order_survive T specs actOrd pos h_valid h_perm
    (px + 1) (τ - (px + 1)) (e₁ := ey) (e₂ := ex)
    hey_next hex_next htgt_eyN htgt_exN hlt_next
  rw [hτy]
  simpa [hargτ] using horder

/-- **Stage delay monotonicity.** Among equal-priority stage-`s` events in a
    common firing tick, an earlier pop has `stageDelay` at least as large. -/
theorem stageRep_delay_ge_of_before
    (T : Nat) (specs : List ChainSpec) (actOrd : List Nat) (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (h_fit : ∀ i < specs.length, chainDelay (specAt specs i) ≤ T)
    (x y s : Nat) (hx : x < specs.length) (hy : y < specs.length)
    (hsx : s < repLenAt specs x) (hsy : s < repLenAt specs y)
    (hpos : 0 < s)
    (htick_eq : stageTickOf T specs x s = stageTickOf T specs y s)
    (hx_mem : stageEventOf T specs x s ∈
        popSeq (simWorld T specs actOrd pos (stageTickOf T specs x s)))
    (hy_mem : stageEventOf T specs y s ∈
        popSeq (simWorld T specs actOrd pos (stageTickOf T specs y s)))
    (hpri : stagePriAt specs x s = stagePriAt specs y s)
    (hb : (_root_.findIdx? (fun e => decide (e = stageEventOf T specs x s))
            (popSeq (simWorld T specs actOrd pos (stageTickOf T specs x s)))).getD 0 <
          (_root_.findIdx? (fun e => decide (e = stageEventOf T specs y s))
            (popSeq (simWorld T specs actOrd pos (stageTickOf T specs y s)))).getD 0) :
    stageDelayAt specs x s ≥ stageDelayAt specs y s := by
  set wT := simWorld T specs actOrd pos (stageTickOf T specs x s)
  have hpri_ev : (stageEventOf T specs x s).priority =
      (stageEventOf T specs y s).priority := by
    dsimp [stageEventOf]
    exact hpri
  have hnodup : wT.events.Nodup :=
    (simWorld_tickInv T specs actOrd pos h_valid h_perm (stageTickOf T specs x s)).1
  have hpopNd : (popSeq wT).Nodup :=
    popSeq_nodup_of_tickInv T specs h_valid (stageTickOf T specs x s) wT.events [] wT
      (by dsimp [wT]; rw [simWorld_tick])
      (simWorld_tickInv T specs actOrd pos h_valid h_perm (stageTickOf T specs x s))
  have hy_mem' : stageEventOf T specs y s ∈ popSeq wT := by
    simpa [wT, htick_eq] using hy_mem
  have hb' : (_root_.findIdx? (fun e => decide (e = stageEventOf T specs x s))
      (popSeq wT)).getD 0 <
        (_root_.findIdx? (fun e => decide (e = stageEventOf T specs y s))
          (popSeq wT)).getD 0 := by
    simpa [wT, htick_eq] using hb
  have hindex : (_root_.findIdx? (fun e => decide (e = stageEventOf T specs x s))
      wT.events).getD 0 <
        (_root_.findIdx? (fun e => decide (e = stageEventOf T specs y s))
          wT.events).getD 0 :=
    popSeq_same_priority_findIdx_order wT hx_mem hy_mem' hnodup hpopNd hpri_ev hb'
  by_contra hnotge
  have hlt : stageDelayAt specs x s < stageDelayAt specs y s :=
    Nat.lt_of_not_ge hnotge
  have hgt := stageRep_index_gt_of_delay_lt T specs actOrd pos h_valid h_perm h_fit
    x y s hx hy hsx hsy hpos htick_eq hlt
  have hgt' : (_root_.findIdx? (fun e => decide (e = stageEventOf T specs x s))
      wT.events).getD 0 >
        (_root_.findIdx? (fun e => decide (e = stageEventOf T specs y s))
          wT.events).getD 0 := by
    simpa [wT, htick_eq] using hgt
  omega

/-- Chronological half at two (possibly different) stages: a smaller stage
    delay enqueues later, so it sits later in the queue at the common firing
    tick. -/
theorem stageRep_index_gt_of_delay_lt_sep (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (h_fit : ∀ i < specs.length, chainDelay (specAt specs i) ≤ T)
    (x y sx sy : Nat) (hx : x < specs.length) (hy : y < specs.length)
    (hsx : sx < repLenAt specs x) (hsy : sy < repLenAt specs y)
    (hposx : 0 < sx) (hposy : 0 < sy)
    (htick_eq : stageTickOf T specs x sx = stageTickOf T specs y sy)
    (hlt : stageDelayAt specs x sx < stageDelayAt specs y sy) :
    (_root_.findIdx? (fun e => decide (e = stageEventOf T specs x sx))
        ((simWorld T specs actOrd pos (stageTickOf T specs x sx)).events)).getD 0 >
      (_root_.findIdx? (fun e => decide (e = stageEventOf T specs y sy))
        ((simWorld T specs actOrd pos (stageTickOf T specs y sy)).events)).getD 0 := by
  set ex := stageEventOf T specs x sx
  set ey := stageEventOf T specs y sy
  set τ := stageTickOf T specs x sx
  have hτy : stageTickOf T specs y sy = τ := htick_eq.symm
  set px := stageTickOf T specs x (sx - 1)
  set py := stageTickOf T specs y (sy - 1)
  set dx := (stageDelayAt specs x sx : Nat)
  set dy := (stageDelayAt specs y sy : Nat)
  have htick_ex : ex.targetTick = τ := by
    dsimp [ex, stageEventOf, τ]
  have htick_ey : ey.targetTick = τ := by
    dsimp [ey, stageEventOf]
    rw [hτy]
  have hsucc_x : τ = px + dx := by
    have hsx' : (sx - 1) + 1 ≤ (specAt specs x).middleDelays.length := by
      dsimp [repLenAt] at hsx
      omega
    have hsucc := stageTickOf_succ T specs x (sx - 1) hsx'
    have hpred : sx - 1 + 1 = sx := by omega
    simpa [px, dx, τ, hpred] using hsucc
  have hsucc_y : τ = py + dy := by
    have hsy' : (sy - 1) + 1 ≤ (specAt specs y).middleDelays.length := by
      dsimp [repLenAt] at hsy
      omega
    have hsucc := stageTickOf_succ T specs y (sy - 1) hsy'
    have hpred : sy - 1 + 1 = sy := by omega
    have hsucc' : stageTickOf T specs y sy = py + dy := by
      simpa [py, dy, hpred] using hsucc
    simpa [hτy] using hsucc'
  have hltN : dx < dy := by
    exact_mod_cast hlt
  have hpx_eq : px = τ - dx := by
    omega
  have hpy_eq : py = τ - dy := by
    omega
  have hpos_dx : 1 ≤ dx := by
    have h := PNat.pos (stageDelayAt specs x sx)
    dsimp [dx]
    omega
  have hdelay_x_le : dx ≤ τ := by
    omega
  have hdelay_y_le : dy ≤ τ := by
    omega
  have hpy_lt_px : py < px := by
    rw [hpy_eq, hpx_eq]
    omega
  have hpx_ge : py + 1 ≤ px := by omega
  have hpx_le_τ : px ≤ τ := by
    rw [hpx_eq]
    omega
  -- y's stage-sy event is enqueued at py and present at py + 1
  have hspawn_y : stageEventOf T specs y sy ∈
      spawnFold (cascadeSpawn T specs)
        (popSeq (simWorld T specs actOrd pos py)) := by
    have hsy_prev : sy - 1 < repLenAt specs y := by
      dsimp [repLenAt] at hsy ⊢
      omega
    have hsp := stageRep_mem_spawn T specs actOrd pos h_valid h_perm y hy
      (h_fit y hy) (sy - 1) hsy_prev
    have hpred : sy - 1 + 1 = sy := by omega
    simpa [py, hpred] using hsp
  have hsub_py := simWorld_succ_survivors_before_spawns T specs actOrd pos h_valid h_perm py
  have hey_py1 : ey ∈ (simWorld T specs actOrd pos (py + 1)).events := by
    have hm : ey ∈
        (simWorld T specs actOrd pos py).events.filter (fun e => e.targetTick > py) ++
          spawnFold (cascadeSpawn T specs) (popSeq (simWorld T specs actOrd pos py)) := by
      rw [List.mem_append]
      exact Or.inr (by simpa [ey] using hspawn_y)
    exact List.Sublist.mem hm hsub_py
  -- ey survives from py + 1 to px
  have hsurv_delta : [ey] <+ (simWorld T specs actOrd pos px).events := by
    have h := simWorld_sublist_survive_delta T specs actOrd pos (py + 1) (px - (py + 1)) [ey]
      (List.singleton_sublist.mpr hey_py1)
      (by
        intro e he
        rw [List.mem_singleton] at he
        subst e
        rw [htick_ey]
        have hsum : (py + 1) + (px - (py + 1)) = px := by omega
        rw [hsum]
        exact hpx_le_τ)
    have harg : (py + 1) + (px - (py + 1)) = px := by omega
    simpa [harg] using h
  have hey_px : ey ∈ (simWorld T specs actOrd pos px).events :=
    List.singleton_sublist.mp hsurv_delta
  -- x's stage-sx event spawns at px
  have hspawn_x : stageEventOf T specs x sx ∈
      spawnFold (cascadeSpawn T specs)
        (popSeq (simWorld T specs actOrd pos px)) := by
    have hsx_prev : sx - 1 < repLenAt specs x := by
      dsimp [repLenAt] at hsx ⊢
      omega
    have hsp := stageRep_mem_spawn T specs actOrd pos h_valid h_perm x hx
      (h_fit x hx) (sx - 1) hsx_prev
    have hpred : sx - 1 + 1 = sx := by omega
    simpa [px, hpred] using hsp
  -- survivor ey precedes fresh spawn ex at tick px
  have hsub_px := simWorld_succ_survivors_before_spawns T specs actOrd pos h_valid h_perm px
  set pre := (simWorld T specs actOrd pos px).events.filter (fun e => e.targetTick > px)
  set rest := spawnFold (cascadeSpawn T specs) (popSeq (simWorld T specs actOrd pos px))
  have hsub_px' : pre ++ rest <+ (simWorld T specs actOrd pos (px + 1)).events := by
    simpa [pre, rest] using hsub_px
  have hey_pre : ey ∈ pre := by
    dsimp [pre]
    rw [List.mem_filter]
    exact ⟨hey_px, decide_eq_true_eq.mpr (by rw [htick_ey, hpx_eq]; omega)⟩
  have hex_rest : ex ∈ rest := by
    dsimp [rest, ex]
    simpa using hspawn_x
  have hex_in_concat : ex ∈ pre ++ rest := by
    rw [List.mem_append]; exact Or.inr hex_rest
  have hey_in_concat : ey ∈ pre ++ rest := by
    rw [List.mem_append]; exact Or.inl hey_pre
  have hnodup_next : (simWorld T specs actOrd pos (px + 1)).events.Nodup :=
    (simWorld_tickInv T specs actOrd pos h_valid h_perm (px + 1)).1
  have hnd_concat : (pre ++ rest).Nodup := List.Sublist.nodup hsub_px' hnodup_next
  have hdisj := (List.nodup_append.mp hnd_concat).2.2
  have hex_not_pre : ex ∉ pre := by
    intro h
    exact hdisj ex h ex hex_rest rfl
  have hlt_concat : (_root_.findIdx? (fun e => decide (e = ey)) (pre ++ rest)).getD 0 <
      (_root_.findIdx? (fun e => decide (e = ex)) (pre ++ rest)).getD 0 :=
    findIdx?_lt_of_prefix_mem pre rest (x := ey) (y := ex)
      hey_pre hex_in_concat hex_not_pre
  have hlt_next : (_root_.findIdx? (fun e => decide (e = ey))
      (simWorld T specs actOrd pos (px + 1)).events).getD 0 <
        (_root_.findIdx? (fun e => decide (e = ex))
          (simWorld T specs actOrd pos (px + 1)).events).getD 0 :=
    (findIdx?_getD_lt_sublist (l₁ := pre ++ rest)
      (l₂ := (simWorld T specs actOrd pos (px + 1)).events)
      hsub_px' hnodup_next (x := ey) (y := ex) hey_in_concat hex_in_concat).mpr hlt_concat
  -- survive from px + 1 to τ (both fire at τ)
  have hex_next : ex ∈ (simWorld T specs actOrd pos (px + 1)).events :=
    List.Sublist.mem hex_in_concat hsub_px'
  have hey_next : ey ∈ (simWorld T specs actOrd pos (px + 1)).events :=
    List.Sublist.mem hey_in_concat hsub_px'
  have hargτ : (px + 1) + (τ - (px + 1)) = τ := by
    rw [hpx_eq]
    omega
  have htgt_exN : (px + 1) + (τ - (px + 1)) ≤ ex.targetTick := by
    simp [htick_ex, hargτ]
  have htgt_eyN : (px + 1) + (τ - (px + 1)) ≤ ey.targetTick := by
    simp [htick_ey, hargτ]
  have horder := simWorld_findIdx_order_survive T specs actOrd pos h_valid h_perm
    (px + 1) (τ - (px + 1)) (e₁ := ey) (e₂ := ex)
    hey_next hex_next htgt_eyN htgt_exN hlt_next
  rw [hτy]
  simpa [hargτ] using horder

/-- **Stage delay monotonicity (separate stages).** Among equal-priority
    events at a common firing tick, an earlier pop has `stageDelay` at least
    as large. -/
theorem stageRep_delay_ge_of_before_sep
    (T : Nat) (specs : List ChainSpec) (actOrd : List Nat) (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (h_fit : ∀ i < specs.length, chainDelay (specAt specs i) ≤ T)
    (x y sx sy : Nat) (hx : x < specs.length) (hy : y < specs.length)
    (hsx : sx < repLenAt specs x) (hsy : sy < repLenAt specs y)
    (hposx : 0 < sx) (hposy : 0 < sy)
    (htick_eq : stageTickOf T specs x sx = stageTickOf T specs y sy)
    (hx_mem : stageEventOf T specs x sx ∈
        popSeq (simWorld T specs actOrd pos (stageTickOf T specs x sx)))
    (hy_mem : stageEventOf T specs y sy ∈
        popSeq (simWorld T specs actOrd pos (stageTickOf T specs y sy)))
    (hpri : stagePriAt specs x sx = stagePriAt specs y sy)
    (hb : (_root_.findIdx? (fun e => decide (e = stageEventOf T specs x sx))
            (popSeq (simWorld T specs actOrd pos (stageTickOf T specs x sx)))).getD 0 <
          (_root_.findIdx? (fun e => decide (e = stageEventOf T specs y sy))
            (popSeq (simWorld T specs actOrd pos (stageTickOf T specs y sy)))).getD 0) :
    stageDelayAt specs x sx ≥ stageDelayAt specs y sy := by
  set wT := simWorld T specs actOrd pos (stageTickOf T specs x sx)
  have hpri_ev : (stageEventOf T specs x sx).priority =
      (stageEventOf T specs y sy).priority := by
    dsimp [stageEventOf]
    exact hpri
  have hnodup : wT.events.Nodup :=
    (simWorld_tickInv T specs actOrd pos h_valid h_perm (stageTickOf T specs x sx)).1
  have hpopNd : (popSeq wT).Nodup :=
    popSeq_nodup_of_tickInv T specs h_valid (stageTickOf T specs x sx) wT.events [] wT
      (by dsimp [wT]; rw [simWorld_tick])
      (simWorld_tickInv T specs actOrd pos h_valid h_perm (stageTickOf T specs x sx))
  have hy_mem' : stageEventOf T specs y sy ∈ popSeq wT := by
    simpa [wT, htick_eq] using hy_mem
  have hb' : (_root_.findIdx? (fun e => decide (e = stageEventOf T specs x sx))
      (popSeq wT)).getD 0 <
        (_root_.findIdx? (fun e => decide (e = stageEventOf T specs y sy))
          (popSeq wT)).getD 0 := by
    simpa [wT, htick_eq] using hb
  have hindex : (_root_.findIdx? (fun e => decide (e = stageEventOf T specs x sx))
      wT.events).getD 0 <
        (_root_.findIdx? (fun e => decide (e = stageEventOf T specs y sy))
          wT.events).getD 0 :=
    popSeq_same_priority_findIdx_order wT hx_mem hy_mem' hnodup hpopNd hpri_ev hb'
  by_contra hnotge
  have hlt : stageDelayAt specs x sx < stageDelayAt specs y sy :=
    Nat.lt_of_not_ge hnotge
  have hgt := stageRep_index_gt_of_delay_lt_sep T specs actOrd pos h_valid h_perm h_fit
    x y sx sy hx hy hsx hsy hposx hposy htick_eq hlt
  have hgt' : (_root_.findIdx? (fun e => decide (e = stageEventOf T specs x sx))
      wT.events).getD 0 >
        (_root_.findIdx? (fun e => decide (e = stageEventOf T specs y sy))
          wT.events).getD 0 := by
    simpa [wT, htick_eq] using hgt
  omega

/-- Chronological half at stage 0: a smaller stage-0 delay enqueues later
    (its observer fires later), so it sits later in the queue at the common
    firing tick. -/
theorem obsRep_index_gt_of_delay_lt (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (_h_fit : ∀ i < specs.length, chainDelay (specAt specs i) ≤ T)
    (x y : Nat) (hx : x < specs.length) (hy : y < specs.length)
    (htick_eq : stageTickOf T specs x 0 = stageTickOf T specs y 0)
    (hlt : stageDelayAt specs x 0 < stageDelayAt specs y 0) :
    (_root_.findIdx? (fun e => decide (e = stageEventOf T specs x 0))
        ((simWorld T specs actOrd pos (stageTickOf T specs x 0)).events)).getD 0 >
      (_root_.findIdx? (fun e => decide (e = stageEventOf T specs y 0))
        ((simWorld T specs actOrd pos (stageTickOf T specs y 0)).events)).getD 0 := by
  set ex := stageEventOf T specs x 0
  set ey := stageEventOf T specs y 0
  set τ := stageTickOf T specs x 0
  have hτy : stageTickOf T specs y 0 = τ := htick_eq.symm
  set px := obsTickOf T specs x
  set py := obsTickOf T specs y
  set dx := (stageDelayAt specs x 0 : Nat)
  set dy := (stageDelayAt specs y 0 : Nat)
  have htick_ex : ex.targetTick = τ := by
    dsimp [ex, stageEventOf, τ]
  have htick_ey : ey.targetTick = τ := by
    dsimp [ey, stageEventOf]
    rw [hτy]
  have hsucc_x : τ = px + dx := by
    dsimp [τ, px, dx, obsTickOf]
    rw [stageTickOf_zero T specs x]
  have hsucc_y : τ = py + dy := by
    rw [← hτy]
    dsimp [py, dy, obsTickOf]
    rw [stageTickOf_zero T specs y]
  have hltN : dx < dy := by
    exact_mod_cast hlt
  have hpx_eq : px = τ - dx := by
    omega
  have hpy_eq : py = τ - dy := by
    omega
  have hpos_dx : 1 ≤ dx := by
    have h := PNat.pos (stageDelayAt specs x 0)
    dsimp [dx]
    omega
  have hdelay_x_le : dx ≤ τ := by
    omega
  have hdelay_y_le : dy ≤ τ := by
    omega
  have hpy_lt_px : py < px := by
    rw [hpy_eq, hpx_eq]
    omega
  have hpx_ge : py + 1 ≤ px := by omega
  have hpx_le_τ : px ≤ τ := by
    rw [hpx_eq]
    omega
  -- y's stage-0 event is enqueued at py and present at py + 1
  have hspawn_y : stageEventOf T specs y 0 ∈
      spawnFold (cascadeSpawn T specs)
        (popSeq (simWorld T specs actOrd pos py)) := by
    simpa [py] using (stageRep_mem_spawn_zero T specs actOrd pos h_valid h_perm y hy)
  have hsub_py := simWorld_succ_survivors_before_spawns T specs actOrd pos h_valid h_perm py
  have hey_py1 : ey ∈ (simWorld T specs actOrd pos (py + 1)).events := by
    have hm : ey ∈
        (simWorld T specs actOrd pos py).events.filter (fun e => e.targetTick > py) ++
          spawnFold (cascadeSpawn T specs) (popSeq (simWorld T specs actOrd pos py)) := by
      rw [List.mem_append]
      exact Or.inr (by simpa [ey] using hspawn_y)
    exact List.Sublist.mem hm hsub_py
  -- ey survives from py + 1 to px
  have hsurv_delta : [ey] <+ (simWorld T specs actOrd pos px).events := by
    have h := simWorld_sublist_survive_delta T specs actOrd pos (py + 1) (px - (py + 1)) [ey]
      (List.singleton_sublist.mpr hey_py1)
      (by
        intro e he
        rw [List.mem_singleton] at he
        subst e
        rw [htick_ey]
        have hsum : (py + 1) + (px - (py + 1)) = px := by omega
        rw [hsum]
        exact hpx_le_τ)
    have harg : (py + 1) + (px - (py + 1)) = px := by omega
    simpa [harg] using h
  have hey_px : ey ∈ (simWorld T specs actOrd pos px).events :=
    List.singleton_sublist.mp hsurv_delta
  -- x's stage-0 event spawns at px
  have hspawn_x : stageEventOf T specs x 0 ∈
      spawnFold (cascadeSpawn T specs)
        (popSeq (simWorld T specs actOrd pos px)) := by
    simpa [px] using (stageRep_mem_spawn_zero T specs actOrd pos h_valid h_perm x hx)
  -- survivor ey precedes fresh spawn ex at tick px
  have hsub_px := simWorld_succ_survivors_before_spawns T specs actOrd pos h_valid h_perm px
  set pre := (simWorld T specs actOrd pos px).events.filter (fun e => e.targetTick > px)
  set rest := spawnFold (cascadeSpawn T specs) (popSeq (simWorld T specs actOrd pos px))
  have hsub_px' : pre ++ rest <+ (simWorld T specs actOrd pos (px + 1)).events := by
    simpa [pre, rest] using hsub_px
  have hey_pre : ey ∈ pre := by
    dsimp [pre]
    rw [List.mem_filter]
    exact ⟨hey_px, decide_eq_true_eq.mpr (by rw [htick_ey, hpx_eq]; omega)⟩
  have hex_rest : ex ∈ rest := by
    dsimp [rest, ex]
    simpa using hspawn_x
  have hex_in_concat : ex ∈ pre ++ rest := by
    rw [List.mem_append]; exact Or.inr hex_rest
  have hey_in_concat : ey ∈ pre ++ rest := by
    rw [List.mem_append]; exact Or.inl hey_pre
  have hnodup_next : (simWorld T specs actOrd pos (px + 1)).events.Nodup :=
    (simWorld_tickInv T specs actOrd pos h_valid h_perm (px + 1)).1
  have hnd_concat : (pre ++ rest).Nodup := List.Sublist.nodup hsub_px' hnodup_next
  have hdisj := (List.nodup_append.mp hnd_concat).2.2
  have hex_not_pre : ex ∉ pre := by
    intro h
    exact hdisj ex h ex hex_rest rfl
  have hlt_concat : (_root_.findIdx? (fun e => decide (e = ey)) (pre ++ rest)).getD 0 <
      (_root_.findIdx? (fun e => decide (e = ex)) (pre ++ rest)).getD 0 :=
    findIdx?_lt_of_prefix_mem pre rest (x := ey) (y := ex)
      hey_pre hex_in_concat hex_not_pre
  have hlt_next : (_root_.findIdx? (fun e => decide (e = ey))
      (simWorld T specs actOrd pos (px + 1)).events).getD 0 <
        (_root_.findIdx? (fun e => decide (e = ex))
          (simWorld T specs actOrd pos (px + 1)).events).getD 0 :=
    (findIdx?_getD_lt_sublist (l₁ := pre ++ rest)
      (l₂ := (simWorld T specs actOrd pos (px + 1)).events)
      hsub_px' hnodup_next (x := ey) (y := ex) hey_in_concat hex_in_concat).mpr hlt_concat
  -- survive from px + 1 to τ (both fire at τ)
  have hex_next : ex ∈ (simWorld T specs actOrd pos (px + 1)).events :=
    List.Sublist.mem hex_in_concat hsub_px'
  have hey_next : ey ∈ (simWorld T specs actOrd pos (px + 1)).events :=
    List.Sublist.mem hey_in_concat hsub_px'
  have hargτ : (px + 1) + (τ - (px + 1)) = τ := by
    rw [hpx_eq]
    omega
  have htgt_exN : (px + 1) + (τ - (px + 1)) ≤ ex.targetTick := by
    simp [htick_ex, hargτ]
  have htgt_eyN : (px + 1) + (τ - (px + 1)) ≤ ey.targetTick := by
    simp [htick_ey, hargτ]
  have horder := simWorld_findIdx_order_survive T specs actOrd pos h_valid h_perm
    (px + 1) (τ - (px + 1)) (e₁ := ey) (e₂ := ex)
    hey_next hex_next htgt_eyN htgt_exN hlt_next
  rw [hτy]
  simpa [hargτ] using horder

/-- **Stage-0 delay monotonicity.** Among equal-priority stage-0 events in a
    common firing tick, an earlier pop has `stageDelay` at least as large. -/
theorem obsRep_delay_ge_of_before
    (T : Nat) (specs : List ChainSpec) (actOrd : List Nat) (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (h_fit : ∀ i < specs.length, chainDelay (specAt specs i) ≤ T)
    (x y : Nat) (hx : x < specs.length) (hy : y < specs.length)
    (htick_eq : stageTickOf T specs x 0 = stageTickOf T specs y 0)
    (hx_mem : stageEventOf T specs x 0 ∈
        popSeq (simWorld T specs actOrd pos (stageTickOf T specs x 0)))
    (hy_mem : stageEventOf T specs y 0 ∈
        popSeq (simWorld T specs actOrd pos (stageTickOf T specs y 0)))
    (hpri : stagePriAt specs x 0 = stagePriAt specs y 0)
    (hb : (_root_.findIdx? (fun e => decide (e = stageEventOf T specs x 0))
            (popSeq (simWorld T specs actOrd pos (stageTickOf T specs x 0)))).getD 0 <
          (_root_.findIdx? (fun e => decide (e = stageEventOf T specs y 0))
            (popSeq (simWorld T specs actOrd pos (stageTickOf T specs y 0)))).getD 0) :
    stageDelayAt specs x 0 ≥ stageDelayAt specs y 0 := by
  set wT := simWorld T specs actOrd pos (stageTickOf T specs x 0)
  have hpri_ev : (stageEventOf T specs x 0).priority =
      (stageEventOf T specs y 0).priority := by
    dsimp [stageEventOf]
    exact hpri
  have hnodup : wT.events.Nodup :=
    (simWorld_tickInv T specs actOrd pos h_valid h_perm (stageTickOf T specs x 0)).1
  have hpopNd : (popSeq wT).Nodup :=
    popSeq_nodup_of_tickInv T specs h_valid (stageTickOf T specs x 0) wT.events [] wT
      (by dsimp [wT]; rw [simWorld_tick])
      (simWorld_tickInv T specs actOrd pos h_valid h_perm (stageTickOf T specs x 0))
  have hy_mem' : stageEventOf T specs y 0 ∈ popSeq wT := by
    simpa [wT, htick_eq] using hy_mem
  have hb' : (_root_.findIdx? (fun e => decide (e = stageEventOf T specs x 0))
      (popSeq wT)).getD 0 <
        (_root_.findIdx? (fun e => decide (e = stageEventOf T specs y 0))
          (popSeq wT)).getD 0 := by
    simpa [wT, htick_eq] using hb
  have hindex : (_root_.findIdx? (fun e => decide (e = stageEventOf T specs x 0))
      wT.events).getD 0 <
        (_root_.findIdx? (fun e => decide (e = stageEventOf T specs y 0))
          wT.events).getD 0 :=
    popSeq_same_priority_findIdx_order wT hx_mem hy_mem' hnodup hpopNd hpri_ev hb'
  by_contra hnotge
  have hlt : stageDelayAt specs x 0 < stageDelayAt specs y 0 :=
    Nat.lt_of_not_ge hnotge
  have hgt := obsRep_index_gt_of_delay_lt T specs actOrd pos h_valid h_perm h_fit
    x y hx hy htick_eq hlt
  have hgt' : (_root_.findIdx? (fun e => decide (e = stageEventOf T specs x 0))
      wT.events).getD 0 >
        (_root_.findIdx? (fun e => decide (e = stageEventOf T specs y 0))
          wT.events).getD 0 := by
    simpa [wT, htick_eq] using hgt
  omega
