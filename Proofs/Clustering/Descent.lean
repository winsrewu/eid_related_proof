import Proofs.Clustering.ParentBridge


open BasicRedstoneSim
open List

/-! # Descent scaffolding (no-group clustering)

`eventIdx`/`eventIdxEvents`, the `evI`/`evJ`/`evK`/`wI` abbreviations, the
event-index bridges, and the spawner-agnostic order/delay/contradiction
lemmas that `DescentTrace` and `Basic` build on. -/

/-- First-occurrence position of an event in a world's pop sequence. -/
def eventIdx (w : World) (ev : ScheduledEvent) : Nat :=
  (_root_.findIdx? (fun e => decide (e = ev)) (popSeq w)).getD 0

/-- First-occurrence position of an event in a world's event list. -/
def eventIdxEvents (w : World) (ev : ScheduledEvent) : Nat :=
  (_root_.findIdx? (fun e => decide (e = ev)) w.events).getD 0

/-- Chain `i`'s stage-`(repLenAt i - r)` event, at descent distance `r`. -/
def evI (T : Nat) (specs : List ChainSpec) (i r : Nat) : ScheduledEvent :=
  stageEventOf T specs i (repLenAt specs i - r)

/-- Chain `j`'s stage-`(repLenAt j - r)` event, at descent distance `r`. -/
def evJ (T : Nat) (specs : List ChainSpec) (j r : Nat) : ScheduledEvent :=
  stageEventOf T specs j (repLenAt specs j - r)

/-- Chain `k`'s stage-`(repLenAt i - r)` event, at descent distance `r`
    (same stage index as chain `i` since they share a spec). -/
def evK (T : Nat) (specs : List ChainSpec) (k i r : Nat) : ScheduledEvent :=
  stageEventOf T specs k (repLenAt specs i - r)

/-- The world at chain `i`'s stage-`(repLenAt i - r)` firing tick. -/
def wI (T : Nat) (specs : List ChainSpec) (actOrd : List Nat)
    (pos : Nat → Nat → Nat) (i r : Nat) : World :=
  simWorld T specs actOrd pos (stageTickOf T specs i (repLenAt specs i - r))

/-- Bridge: `stageRep_succ_order` in `eventIdx`/`eventIdxEvents` form, so the
    descent never re-expands the `stageEventOf`/`simWorld` terms. -/
theorem stageRep_succ_order_ev (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (h_fit : ∀ i < specs.length, chainDelay (specAt specs i) ≤ T)
    (x y sx sy : Nat) (hx : x < specs.length) (hy : y < specs.length)
    (hsx : sx < repLenAt specs x) (hsy : sy < repLenAt specs y)
    (htick : stageTickOf T specs x sx = stageTickOf T specs y sy)
    (htick_succ : stageTickOf T specs x (sx + 1) = stageTickOf T specs y (sy + 1))
    (ex ey : ScheduledEvent) (wx : World)
    (hex : ex = stageEventOf T specs x sx) (hey : ey = stageEventOf T specs y sy)
    (hwx : wx = simWorld T specs actOrd pos (stageTickOf T specs x sx))
    (hx_mem : ex ∈ popSeq wx) (hy_mem : ey ∈ popSeq wx)
    (hb : eventIdx wx ex < eventIdx wx ey) :
    eventIdxEvents (simWorld T specs actOrd pos (stageTickOf T specs x (sx + 1)))
        (stageEventOf T specs x (sx + 1)) <
      eventIdxEvents (simWorld T specs actOrd pos (stageTickOf T specs y (sy + 1)))
        (stageEventOf T specs y (sy + 1)) := by
  dsimp [eventIdx, eventIdxEvents] at hb ⊢
  exact stageRep_succ_order T specs actOrd pos h_valid h_perm h_fit x y sx sy hx hy hsx hsy
    htick htick_succ (by simpa [hex, hwx] using hx_mem)
    (by simpa [hey, hwx, htick] using hy_mem)
    (by simpa [hex, hey, hwx, htick] using hb)

/-- Bridge: `stageRep_delay_ge_of_before` in `eventIdx` form. -/
theorem stageRep_delay_ge_of_before_ev (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (h_fit : ∀ i < specs.length, chainDelay (specAt specs i) ≤ T)
    (x y s : Nat) (hx : x < specs.length) (hy : y < specs.length)
    (hsx : s < repLenAt specs x) (hsy : s < repLenAt specs y) (hpos : 0 < s)
    (htick_eq : stageTickOf T specs x s = stageTickOf T specs y s)
    (ex ey : ScheduledEvent) (wx : World)
    (hex : ex = stageEventOf T specs x s) (hey : ey = stageEventOf T specs y s)
    (hwx : wx = simWorld T specs actOrd pos (stageTickOf T specs x s))
    (hx_mem : ex ∈ popSeq wx) (hy_mem : ey ∈ popSeq wx)
    (hpri : stagePriAt specs x s = stagePriAt specs y s)
    (hb : eventIdx wx ex < eventIdx wx ey) :
    stageDelayAt specs x s ≥ stageDelayAt specs y s := by
  dsimp [eventIdx] at hb
  exact stageRep_delay_ge_of_before T specs actOrd pos h_valid h_perm h_fit x y s hx hy hsx hsy
    hpos htick_eq (by simpa [hex, hwx] using hx_mem)
    (by simpa [hey, hwx, htick_eq] using hy_mem) hpri
    (by simpa [hex, hey, hwx, htick_eq] using hb)

/-- Bridge: `stageRep_delay_ge_of_before_sep` in `eventIdx` form. -/
theorem stageRep_delay_ge_of_before_sep_ev (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (h_fit : ∀ i < specs.length, chainDelay (specAt specs i) ≤ T)
    (x y sx sy : Nat) (hx : x < specs.length) (hy : y < specs.length)
    (hsx : sx < repLenAt specs x) (hsy : sy < repLenAt specs y)
    (hposx : 0 < sx) (hposy : 0 < sy)
    (htick_eq : stageTickOf T specs x sx = stageTickOf T specs y sy)
    (ex ey : ScheduledEvent) (wx : World)
    (hex : ex = stageEventOf T specs x sx) (hey : ey = stageEventOf T specs y sy)
    (hwx : wx = simWorld T specs actOrd pos (stageTickOf T specs x sx))
    (hx_mem : ex ∈ popSeq wx) (hy_mem : ey ∈ popSeq wx)
    (hpri : stagePriAt specs x sx = stagePriAt specs y sy)
    (hb : eventIdx wx ex < eventIdx wx ey) :
    stageDelayAt specs x sx ≥ stageDelayAt specs y sy := by
  dsimp [eventIdx] at hb
  exact stageRep_delay_ge_of_before_sep T specs actOrd pos h_valid h_perm h_fit x y sx sy hx hy hsx hsy
    hposx hposy htick_eq (by simpa [hex, hwx] using hx_mem)
    (by simpa [hey, hwx, htick_eq] using hy_mem) hpri
    (by simpa [hex, hey, hwx, htick_eq] using hb)

/-- Bridge: `obsRep_delay_ge_of_before` in `eventIdx` form. -/
theorem obsRep_delay_ge_of_before_ev (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (h_fit : ∀ i < specs.length, chainDelay (specAt specs i) ≤ T)
    (x y : Nat) (hx : x < specs.length) (hy : y < specs.length)
    (htick_eq : stageTickOf T specs x 0 = stageTickOf T specs y 0)
    (ex ey : ScheduledEvent) (wx : World)
    (hex : ex = stageEventOf T specs x 0) (hey : ey = stageEventOf T specs y 0)
    (hwx : wx = simWorld T specs actOrd pos (stageTickOf T specs x 0))
    (hx_mem : ex ∈ popSeq wx) (hy_mem : ey ∈ popSeq wx)
    (hpri : stagePriAt specs x 0 = stagePriAt specs y 0)
    (hb : eventIdx wx ex < eventIdx wx ey) :
    stageDelayAt specs x 0 ≥ stageDelayAt specs y 0 := by
  dsimp [eventIdx] at hb
  exact obsRep_delay_ge_of_before T specs actOrd pos h_valid h_perm h_fit x y hx hy htick_eq
    (by simpa [hex, hwx] using hx_mem) (by simpa [hey, hwx, htick_eq] using hy_mem) hpri
    (by simpa [hex, hey, hwx, htick_eq] using hb)

/-- Chronological half, spawner-agnostic. If `ex` and `ey` both fire at the
    common tick `τ`, are spawned at `px` and `py` respectively, and `dx < dy`,
    then `ey` sits earlier than `ex` in the queue at `τ`. The spawner of each
    event (observer for stage 0, previous stage otherwise) is opaque here. -/
theorem rep_index_gt_of_delay_lt (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (ex ey : ScheduledEvent) (px py dx dy τ : Nat)
    (htick_ex : ex.targetTick = τ) (htick_ey : ey.targetTick = τ)
    (hsucc_x : τ = px + dx) (hsucc_y : τ = py + dy)
    (hdx_pos : 1 ≤ dx)
    (hspawn_x : ex ∈ spawnFold (cascadeSpawn T specs)
        (popSeq (simWorld T specs actOrd pos px)))
    (hspawn_y : ey ∈ spawnFold (cascadeSpawn T specs)
        (popSeq (simWorld T specs actOrd pos py)))
    (hlt : dx < dy) :
    (_root_.findIdx? (fun e => decide (e = ex))
        ((simWorld T specs actOrd pos τ).events)).getD 0 >
      (_root_.findIdx? (fun e => decide (e = ey))
        ((simWorld T specs actOrd pos τ).events)).getD 0 := by
  have hpx_eq : px = τ - dx := by omega
  have hpy_eq : py = τ - dy := by omega
  have hdelay_x_le : dx ≤ τ := by omega
  have hdelay_y_le : dy ≤ τ := by omega
  have hpy_lt_px : py < px := by
    rw [hpy_eq, hpx_eq]
    omega
  have hpx_ge : py + 1 ≤ px := by omega
  have hpx_le_τ : px ≤ τ := by
    rw [hpx_eq]
    omega
  -- y's event is enqueued at py and present at py + 1
  have hsub_py := simWorld_succ_survivors_before_spawns T specs actOrd pos h_valid h_perm py
  have hey_py1 : ey ∈ (simWorld T specs actOrd pos (py + 1)).events := by
    have hm : ey ∈
        (simWorld T specs actOrd pos py).events.filter (fun e => e.targetTick > py) ++
          spawnFold (cascadeSpawn T specs) (popSeq (simWorld T specs actOrd pos py)) := by
      rw [List.mem_append]
      exact Or.inr hspawn_y
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
  -- x's event spawns at px
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
    dsimp [rest]
    exact hspawn_x
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
  simpa [hargτ] using horder

/-- Delay monotonicity, spawner-agnostic. Among equal-priority events in a
    common firing tick, an earlier pop has delay at least as large. -/
theorem rep_delay_ge_of_before (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (ex ey : ScheduledEvent) (px py dx dy τ : Nat)
    (htick_ex : ex.targetTick = τ) (htick_ey : ey.targetTick = τ)
    (hsucc_x : τ = px + dx) (hsucc_y : τ = py + dy)
    (hdx_pos : 1 ≤ dx)
    (hspawn_x : ex ∈ spawnFold (cascadeSpawn T specs)
        (popSeq (simWorld T specs actOrd pos px)))
    (hspawn_y : ey ∈ spawnFold (cascadeSpawn T specs)
        (popSeq (simWorld T specs actOrd pos py)))
    (hpri : ex.priority = ey.priority)
    (hx_mem : ex ∈ popSeq (simWorld T specs actOrd pos τ))
    (hy_mem : ey ∈ popSeq (simWorld T specs actOrd pos τ))
    (hb : (_root_.findIdx? (fun e => decide (e = ex))
            (popSeq (simWorld T specs actOrd pos τ))).getD 0 <
          (_root_.findIdx? (fun e => decide (e = ey))
            (popSeq (simWorld T specs actOrd pos τ))).getD 0) :
    dx ≥ dy := by
  set wT := simWorld T specs actOrd pos τ
  have hnodup : wT.events.Nodup :=
    (simWorld_tickInv T specs actOrd pos h_valid h_perm τ).1
  have hpopNd : (popSeq wT).Nodup :=
    popSeq_nodup_of_tickInv T specs h_valid τ wT.events [] wT
      (by dsimp [wT]; rw [simWorld_tick])
      (simWorld_tickInv T specs actOrd pos h_valid h_perm τ)
  have hb' : (_root_.findIdx? (fun e => decide (e = ex))
      (popSeq wT)).getD 0 <
        (_root_.findIdx? (fun e => decide (e = ey))
          (popSeq wT)).getD 0 := by
    simpa [wT] using hb
  have hindex : (_root_.findIdx? (fun e => decide (e = ex))
      wT.events).getD 0 <
        (_root_.findIdx? (fun e => decide (e = ey))
          wT.events).getD 0 :=
    popSeq_same_priority_findIdx_order wT hx_mem hy_mem hnodup hpopNd hpri hb'
  by_contra hnotge
  have hlt : dx < dy := Nat.lt_of_not_ge hnotge
  have hgt := rep_index_gt_of_delay_lt T specs actOrd pos h_valid h_perm
    ex ey px py dx dy τ htick_ex htick_ey hsucc_x hsucc_y hdx_pos
    hspawn_x hspawn_y hlt
  have hgt' : (_root_.findIdx? (fun e => decide (e = ex))
      wT.events).getD 0 >
        (_root_.findIdx? (fun e => decide (e = ey))
          wT.events).getD 0 := by
    simpa [wT] using hgt
  omega

/-- In a pairwise-sorted list, a strict key ordering forces the position
    order. -/
private theorem pairwise_lt_of_findIdx_of_lt {α : Type} [DecidableEq α] (l : List α)
    (f : α → Int) (hsorted : l.Pairwise (fun a b => f a ≤ f b))
    {x y : α} (hx : x ∈ l) (hy : y ∈ l) (hne : x ≠ y) (hlt : f x < f y) :
    (_root_.findIdx? (fun a => decide (a = x)) l).getD 0 <
      (_root_.findIdx? (fun a => decide (a = y)) l).getD 0 := by
  have hne_idx : (_root_.findIdx? (fun a => decide (a = x)) l).getD 0 ≠
      (_root_.findIdx? (fun a => decide (a = y)) l).getD 0 :=
    findIdx?_ne_of_ne l hx hy hne
  rcases lt_or_gt_of_ne hne_idx with hlt_idx | hgt_idx
  · exact hlt_idx
  · have hle := pairwise_le_of_findIdx_lt l f hsorted hy hx hgt_idx
    omega

/-- Parent bridge, spawner-agnostic. If two parents pop in order at the common
    spawn tick `σ` and spawn `fx`/`fy` (both firing at `τ ≥ σ + 1`), then the
    children keep that order in the event queue at `τ`. -/
theorem mixed_succ_order (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (ex ey fx fy : ScheduledEvent) (σ τ : Nat)
    (htick_fx : fx.targetTick = τ) (htick_fy : fy.targetTick = τ)
    (hσ_le : σ + 1 ≤ τ)
    (hx_mem : ex ∈ popSeq (simWorld T specs actOrd pos σ))
    (hy_mem : ey ∈ popSeq (simWorld T specs actOrd pos σ))
    (hspawn_x : cascadeSpawn T specs ex = [fx])
    (hspawn_y : cascadeSpawn T specs ey = [fy])
    (hfx_ne : fx ≠ fy)
    (hb : (_root_.findIdx? (fun e => decide (e = ex))
            (popSeq (simWorld T specs actOrd pos σ))).getD 0 <
          (_root_.findIdx? (fun e => decide (e = ey))
            (popSeq (simWorld T specs actOrd pos σ))).getD 0) :
    (_root_.findIdx? (fun e => decide (e = fx))
        (simWorld T specs actOrd pos τ).events).getD 0 <
      (_root_.findIdx? (fun e => decide (e = fy))
        (simWorld T specs actOrd pos τ).events).getD 0 := by
  set l := popSeq (simWorld T specs actOrd pos σ)
  have hx_l : ex ∈ l := hx_mem
  have hy_l : ey ∈ l := hy_mem
  have hb_l : (_root_.findIdx? (fun e => decide (e = ex)) l).getD 0 <
      (_root_.findIdx? (fun e => decide (e = ey)) l).getD 0 := hb
  have hnodup_fold : (spawnFold (cascadeSpawn T specs) l).Nodup := by
    have hsub := simWorld_popSeq_spawn_sublist T specs actOrd pos σ h_valid h_perm
    have hnd := (simWorld_tickInv T specs actOrd pos h_valid h_perm (σ + 1)).1
    exact List.Sublist.nodup hsub hnd
  have hfold : (_root_.findIdx? (fun e => decide (e = fx))
      (spawnFold (cascadeSpawn T specs) l)).getD 0 <
        (_root_.findIdx? (fun e => decide (e = fy))
          (spawnFold (cascadeSpawn T specs) l)).getD 0 :=
    spawnFold_findIdx_order (cascadeSpawn T specs) l hx_l hy_l hnodup_fold
      hspawn_x hspawn_y hfx_ne hb_l
  have hsub_next : spawnFold (cascadeSpawn T specs) l <+
      (simWorld T specs actOrd pos (σ + 1)).events :=
    simWorld_popSeq_spawn_sublist T specs actOrd pos σ h_valid h_perm
  have hnodup_next : (simWorld T specs actOrd pos (σ + 1)).events.Nodup :=
    (simWorld_tickInv T specs actOrd pos h_valid h_perm (σ + 1)).1
  have hfx_mem_fold : fx ∈ spawnFold (cascadeSpawn T specs) l := by
    have hsub : [ex] <+ l := List.singleton_sublist.mpr hx_l
    have hfold_sub : spawnFold (cascadeSpawn T specs) [ex] <+
        spawnFold (cascadeSpawn T specs) l :=
      spawnFold_sublist (cascadeSpawn T specs) hsub
    have hmem : fx ∈ spawnFold (cascadeSpawn T specs) [ex] := by
      simp [spawnFold, hspawn_x]
    exact List.Sublist.mem hmem hfold_sub
  have hfy_mem_fold : fy ∈ spawnFold (cascadeSpawn T specs) l := by
    have hsub : [ey] <+ l := List.singleton_sublist.mpr hy_l
    have hfold_sub : spawnFold (cascadeSpawn T specs) [ey] <+
        spawnFold (cascadeSpawn T specs) l :=
      spawnFold_sublist (cascadeSpawn T specs) hsub
    have hmem : fy ∈ spawnFold (cascadeSpawn T specs) [ey] := by
      simp [spawnFold, hspawn_y]
    exact List.Sublist.mem hmem hfold_sub
  have hfold_next : (_root_.findIdx? (fun e => decide (e = fx))
      (simWorld T specs actOrd pos (σ + 1)).events).getD 0 <
        (_root_.findIdx? (fun e => decide (e = fy))
          (simWorld T specs actOrd pos (σ + 1)).events).getD 0 :=
    (findIdx?_getD_lt_sublist (l₁ := spawnFold (cascadeSpawn T specs) l)
      (l₂ := (simWorld T specs actOrd pos (σ + 1)).events)
      hsub_next hnodup_next (x := fx) (y := fy) hfx_mem_fold hfy_mem_fold).mpr hfold
  have hfx_next : fx ∈ (simWorld T specs actOrd pos (σ + 1)).events :=
    List.Sublist.mem hfx_mem_fold hsub_next
  have hfy_next : fy ∈ (simWorld T specs actOrd pos (σ + 1)).events :=
    List.Sublist.mem hfy_mem_fold hsub_next
  have hargτ : (σ + 1) + (τ - (σ + 1)) = τ :=
    Nat.add_sub_of_le hσ_le
  have htgt_fxN : (σ + 1) + (τ - (σ + 1)) ≤ fx.targetTick := by
    simp [htick_fx, hargτ]
  have htgt_fyN : (σ + 1) + (τ - (σ + 1)) ≤ fy.targetTick := by
    simp [htick_fy, hargτ]
  have horder := simWorld_findIdx_order_survive T specs actOrd pos h_valid h_perm
    (σ + 1) (τ - (σ + 1)) (e₁ := fx) (e₂ := fy)
    hfx_next hfy_next htgt_fxN htgt_fyN hfold_next
  simpa [hargτ] using horder

/-- Contradiction for the short-chain case: if `a`'s stage-0 event pops before
    `b`'s stage-`sb` event at a common tick while their stage delays and
    priorities agree, then `b`'s middle repeater (negative priority) is forced
    before `a`'s observer (priority 0) at the shared spawn tick, so `b`'s stage
    `sb` pops before `a`'s stage 0 — impossible. -/
theorem obs_middle_contradiction (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (h_fit : ∀ i < specs.length, chainDelay (specAt specs i) ≤ T)
    (a b sb : Nat) (ha : a < specs.length) (hb_chain : b < specs.length)
    (hsb : sb ≤ repLenAt specs b) (hsb_pos : 0 < sb)
    (htick : stageTickOf T specs a 0 = stageTickOf T specs b sb)
    (hdelay_eq : stageDelayAt specs a 0 = stageDelayAt specs b sb)
    (hpri : stagePriAt specs a 0 = stagePriAt specs b sb)
    (hb_before : (_root_.findIdx? (fun e => decide (e = stageEventOf T specs a 0))
          (popSeq (simWorld T specs actOrd pos (stageTickOf T specs a 0)))).getD 0 <
        (_root_.findIdx? (fun e => decide (e = stageEventOf T specs b sb))
          (popSeq (simWorld T specs actOrd pos (stageTickOf T specs a 0)))).getD 0) :
    False := by
  set τ := stageTickOf T specs a 0
  have hτb : stageTickOf T specs b sb = τ := htick.symm
  set σ := obsTickOf T specs a
  have hsb_pred_lt : sb - 1 < repLenAt specs b := by omega
  have hsb_le : sb - 1 ≤ repLenAt specs b := Nat.le_of_lt hsb_pred_lt
  have hsb_le_rep : sb ≤ repLenAt specs b := hsb
  have hsb_pred_md : sb - 1 < (specAt specs b).middleDelays.length := by
    dsimp [repLenAt] at hsb
    omega
  have hsb_md_le : (sb - 1) + 1 ≤ (specAt specs b).middleDelays.length := by
    dsimp [repLenAt] at hsb
    omega
  have hdx : (stageDelayAt specs a 0 : Nat) = (stageDelayAt specs b sb : Nat) := by
    rw [hdelay_eq]
  have hsucc_a : τ = σ + (stageDelayAt specs a 0 : Nat) := by
    dsimp [τ, σ, obsTickOf]
    rw [stageTickOf_zero T specs a]
  have hsucc_b : τ = stageTickOf T specs b (sb - 1) + (stageDelayAt specs b sb : Nat) := by
    have hsucc := stageTickOf_succ T specs b (sb - 1) hsb_md_le
    have hpred : sb - 1 + 1 = sb := by omega
    simpa [hpred, hτb, τ] using hsucc
  have hσ_eq : stageTickOf T specs b (sb - 1) = σ := by
    rw [← hdx] at hsucc_b
    omega
  -- membership of both parents at σ
  have hobs_mem : obsEventOf T specs a ∈ popSeq (simWorld T specs actOrd pos σ) := by
    have hpresent := obsEvent_present T specs actOrd pos h_valid h_perm a ha
    have hdue : (obsEventOf T specs a).targetTick = obsTickOf T specs a := by
      dsimp [obsEventOf]
    have htick_σ := simWorld_tick T specs actOrd pos σ
    exact mem_popSeq_of_due (simWorld T specs actOrd pos σ) (obsEventOf T specs a)
      (by simpa [σ] using hpresent) (by simpa [σ, htick_σ] using hdue)
  have hstage_mem : stageEventOf T specs b (sb - 1) ∈ popSeq (simWorld T specs actOrd pos σ) := by
    have hpresent := stageEvent_present T specs actOrd pos h_valid h_perm b hb_chain
      (h_fit b hb_chain) (sb - 1) hsb_le
    have hdue : (stageEventOf T specs b (sb - 1)).targetTick =
        stageTickOf T specs b (sb - 1) := by
      dsimp [stageEventOf]
    have htick_σ := simWorld_tick T specs actOrd pos σ
    exact mem_popSeq_of_due (simWorld T specs actOrd pos σ)
      (stageEventOf T specs b (sb - 1))
      (by simpa [hσ_eq] using hpresent) (by simpa [hσ_eq, htick_σ] using hdue)
  -- priority: b's middle repeater is negative, a's observer is 0
  have hpri_b : (specAt specs b).priLenOk := (h_valid b hb_chain).1
  have hsb_pred_p : sb - 1 < (specAt specs b).middlePriorities.length := by
    dsimp [ChainSpec.priLenOk] at hpri_b
    rw [hpri_b]
    exact hsb_pred_md
  have hpri_val : ValidPriority (stagePriAt specs b (sb - 1)) := by
    rw [stagePriAt_of_lt specs b (sb - 1) hpri_b hsb_pred_md]
    exact (h_valid b hb_chain).2.2.2.1 _ (List.getElem_mem hsb_pred_p)
  have hpri_neg : stagePriAt specs b (sb - 1) < 0 := ValidPriority.neg hpri_val
  have hpri_lt : (stageEventOf T specs b (sb - 1)).priority <
      (obsEventOf T specs a).priority := by
    dsimp [stageEventOf, obsEventOf]
    exact hpri_neg
  have hne_par : stageEventOf T specs b (sb - 1) ≠ obsEventOf T specs a := by
    intro h
    have hpr := congrArg ScheduledEvent.priority h
    dsimp [stageEventOf, obsEventOf] at hpr
    have hz : stagePriAt specs b (sb - 1) = 0 := hpr
    omega
  -- sortedness forces b's stage (sb-1) before a's observer at σ
  have hsorted_σ : (popSeq (simWorld T specs actOrd pos σ)).Pairwise
      (fun e₁ e₂ => e₁.priority ≤ e₂.priority) :=
    popSeq_sorted_priority (simWorld T specs actOrd pos σ)
  have hpop_order : (_root_.findIdx? (fun e => decide (e = stageEventOf T specs b (sb - 1)))
      (popSeq (simWorld T specs actOrd pos σ))).getD 0 <
        (_root_.findIdx? (fun e => decide (e = obsEventOf T specs a))
          (popSeq (simWorld T specs actOrd pos σ))).getD 0 :=
    pairwise_lt_of_findIdx_of_lt (popSeq (simWorld T specs actOrd pos σ))
      (fun e => e.priority) hsorted_σ hstage_mem hobs_mem hne_par hpri_lt
  -- spawn order: b's stage sb before a's stage 0 at τ
  have hspawn_b : cascadeSpawn T specs (stageEventOf T specs b (sb - 1)) =
      [stageEventOf T specs b sb] := by
    have hpred : sb - 1 + 1 = sb := by omega
    simpa [hpred] using (cascadeSpawn_stage T specs h_valid b (sb - 1) hb_chain hsb_pred_lt)
  have hspawn_a : cascadeSpawn T specs (obsEventOf T specs a) =
      [stageEventOf T specs a 0] :=
    cascadeSpawn_obs T specs a ha
  have hfx_ne : stageEventOf T specs b sb ≠ stageEventOf T specs a 0 := by
    intro h
    have hnode := congrArg ScheduledEvent.nodeId h
    dsimp [stageEventOf, chainRepId] at hnode
    have hxy := chainRepId_inj specs b a sb 0 hb_chain ha
      hsb_le_rep
      (by simp)
      (h_valid b hb_chain).1 (h_valid a ha).1 hnode
    have hs_eq : sb = 0 := hxy.2
    omega
  have hσ_le : σ + 1 ≤ τ := by
    have hdelay_pos : 1 ≤ (stageDelayAt specs a 0 : Nat) := by
      have h := PNat.pos (stageDelayAt specs a 0)
      omega
    rw [hsucc_a]
    omega
  have hchild_order : (_root_.findIdx? (fun e => decide (e = stageEventOf T specs b sb))
      (simWorld T specs actOrd pos τ).events).getD 0 <
        (_root_.findIdx? (fun e => decide (e = stageEventOf T specs a 0))
          (simWorld T specs actOrd pos τ).events).getD 0 :=
    mixed_succ_order T specs actOrd pos h_valid h_perm
      (stageEventOf T specs b (sb - 1)) (obsEventOf T specs a)
      (stageEventOf T specs b sb) (stageEventOf T specs a 0) σ τ
      (by dsimp [stageEventOf]; rw [hτb]) (by dsimp [stageEventOf, τ])
      hσ_le hstage_mem hobs_mem hspawn_b hspawn_a hfx_ne hpop_order
  -- convert hb_before to the event queue and contradict
  have hpri_ev : (stageEventOf T specs a 0).priority =
      (stageEventOf T specs b sb).priority := by
    dsimp [stageEventOf]
    exact hpri
  have hmem_a : stageEventOf T specs a 0 ∈ popSeq (simWorld T specs actOrd pos τ) := by
    have hpresent := stageEvent_present T specs actOrd pos h_valid h_perm a ha
      (h_fit a ha) 0 (by simp [repLenAt])
    have hdue : (stageEventOf T specs a 0).targetTick = stageTickOf T specs a 0 := by
      dsimp [stageEventOf]
    have htick_τ := simWorld_tick T specs actOrd pos τ
    exact mem_popSeq_of_due (simWorld T specs actOrd pos τ) (stageEventOf T specs a 0)
      (by simpa [τ] using hpresent) (by simpa [τ, htick_τ] using hdue)
  have hmem_b : stageEventOf T specs b sb ∈ popSeq (simWorld T specs actOrd pos τ) := by
    have hpresent := stageEvent_present T specs actOrd pos h_valid h_perm b hb_chain
      (h_fit b hb_chain) sb hsb_le_rep
    have hdue : (stageEventOf T specs b sb).targetTick = stageTickOf T specs b sb := by
      dsimp [stageEventOf]
    have htick_τ := simWorld_tick T specs actOrd pos τ
    exact mem_popSeq_of_due (simWorld T specs actOrd pos τ) (stageEventOf T specs b sb)
      (by simpa [hτb] using hpresent) (by simpa [hτb, htick_τ] using hdue)
  have hnodup_τ : (simWorld T specs actOrd pos τ).events.Nodup :=
    (simWorld_tickInv T specs actOrd pos h_valid h_perm τ).1
  have hpopNd_τ : (popSeq (simWorld T specs actOrd pos τ)).Nodup :=
    popSeq_nodup_of_tickInv T specs h_valid τ (simWorld T specs actOrd pos τ).events []
      (simWorld T specs actOrd pos τ)
      (by rw [simWorld_tick])
      (simWorld_tickInv T specs actOrd pos h_valid h_perm τ)
  have hb_ev : (_root_.findIdx? (fun e => decide (e = stageEventOf T specs a 0))
      (simWorld T specs actOrd pos τ).events).getD 0 <
        (_root_.findIdx? (fun e => decide (e = stageEventOf T specs b sb))
          (simWorld T specs actOrd pos τ).events).getD 0 :=
    popSeq_same_priority_findIdx_order (simWorld T specs actOrd pos τ)
      hmem_a hmem_b hnodup_τ hpopNd_τ hpri_ev hb_before
  omega

/-- Mixed delay monotonicity: a middle stage-`sx` event (of chain `x`) that
    pops before chain `y`'s stage-`0` event at a common tick, with equal
    priority, has delay at least as large. -/
theorem rep_delay_ge_of_before_mid0 (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (h_fit : ∀ i < specs.length, chainDelay (specAt specs i) ≤ T)
    (x y sx : Nat) (hx : x < specs.length) (hy : y < specs.length)
    (hsx_pos : 0 < sx) (hsx_le : sx ≤ repLenAt specs x)
    (htick : stageTickOf T specs x sx = stageTickOf T specs y 0)
    (hpri : stagePriAt specs x sx = stagePriAt specs y 0)
    (hx_mem : stageEventOf T specs x sx ∈
        popSeq (simWorld T specs actOrd pos (stageTickOf T specs x sx)))
    (hy_mem : stageEventOf T specs y 0 ∈
        popSeq (simWorld T specs actOrd pos (stageTickOf T specs x sx)))
    (hb : (_root_.findIdx? (fun e => decide (e = stageEventOf T specs x sx))
            (popSeq (simWorld T specs actOrd pos (stageTickOf T specs x sx)))).getD 0 <
          (_root_.findIdx? (fun e => decide (e = stageEventOf T specs y 0))
            (popSeq (simWorld T specs actOrd pos (stageTickOf T specs x sx)))).getD 0) :
    stageDelayAt specs x sx ≥ stageDelayAt specs y 0 := by
  have hspawn_x : stageEventOf T specs x sx ∈ spawnFold (cascadeSpawn T specs)
      (popSeq (simWorld T specs actOrd pos (stageTickOf T specs x (sx - 1)))) := by
    have hsx_pred : sx - 1 < repLenAt specs x := by omega
    have hsp := stageRep_mem_spawn T specs actOrd pos h_valid h_perm x hx (h_fit x hx) (sx - 1) hsx_pred
    have hpred : sx - 1 + 1 = sx := by omega
    simpa [hpred] using hsp
  have hspawn_y : stageEventOf T specs y 0 ∈ spawnFold (cascadeSpawn T specs)
      (popSeq (simWorld T specs actOrd pos (obsTickOf T specs y))) :=
    stageRep_mem_spawn_zero T specs actOrd pos h_valid h_perm y hy
  have hsucc_x : stageTickOf T specs x sx =
      stageTickOf T specs x (sx - 1) + (stageDelayAt specs x sx : Nat) := by
    have hle : (sx - 1) + 1 ≤ (specAt specs x).middleDelays.length := by
      dsimp [repLenAt] at hsx_le
      omega
    have hsucc := stageTickOf_succ T specs x (sx - 1) hle
    have hpred : sx - 1 + 1 = sx := by omega
    simpa [hpred] using hsucc
  have hsucc_y : stageTickOf T specs x sx =
      obsTickOf T specs y + (stageDelayAt specs y 0 : Nat) := by
    simpa [obsTickOf] using (htick.trans (stageTickOf_zero T specs y))
  have hdx_pos : 1 ≤ (stageDelayAt specs x sx : Nat) := by
    have h := PNat.pos (stageDelayAt specs x sx)
    omega
  exact rep_delay_ge_of_before T specs actOrd pos h_valid h_perm
    (stageEventOf T specs x sx) (stageEventOf T specs y 0)
    (stageTickOf T specs x (sx - 1)) (obsTickOf T specs y)
    (stageDelayAt specs x sx : Nat) (stageDelayAt specs y 0 : Nat)
    (stageTickOf T specs x sx)
    (by dsimp [stageEventOf]) (by dsimp [stageEventOf]; exact htick.symm)
    hsucc_x hsucc_y hdx_pos hspawn_x hspawn_y
    (by dsimp [stageEventOf]; exact hpri)
    hx_mem hy_mem hb

/-- Mixed delay monotonicity: chain `x`'s stage-`0` event that pops before a
    middle stage-`sy` event of chain `y` at a common tick, with equal priority,
    has delay at least as large. -/
theorem rep_delay_ge_of_before_0mid (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (h_fit : ∀ i < specs.length, chainDelay (specAt specs i) ≤ T)
    (x y sy : Nat) (hx : x < specs.length) (hy : y < specs.length)
    (hsy_pos : 0 < sy) (hsy_le : sy ≤ repLenAt specs y)
    (htick : stageTickOf T specs x 0 = stageTickOf T specs y sy)
    (hpri : stagePriAt specs x 0 = stagePriAt specs y sy)
    (hx_mem : stageEventOf T specs x 0 ∈
        popSeq (simWorld T specs actOrd pos (stageTickOf T specs x 0)))
    (hy_mem : stageEventOf T specs y sy ∈
        popSeq (simWorld T specs actOrd pos (stageTickOf T specs x 0)))
    (hb : (_root_.findIdx? (fun e => decide (e = stageEventOf T specs x 0))
            (popSeq (simWorld T specs actOrd pos (stageTickOf T specs x 0)))).getD 0 <
          (_root_.findIdx? (fun e => decide (e = stageEventOf T specs y sy))
            (popSeq (simWorld T specs actOrd pos (stageTickOf T specs x 0)))).getD 0) :
    stageDelayAt specs x 0 ≥ stageDelayAt specs y sy := by
  have hspawn_x : stageEventOf T specs x 0 ∈ spawnFold (cascadeSpawn T specs)
      (popSeq (simWorld T specs actOrd pos (obsTickOf T specs x))) :=
    stageRep_mem_spawn_zero T specs actOrd pos h_valid h_perm x hx
  have hspawn_y : stageEventOf T specs y sy ∈ spawnFold (cascadeSpawn T specs)
      (popSeq (simWorld T specs actOrd pos (stageTickOf T specs y (sy - 1)))) := by
    have hsy_pred : sy - 1 < repLenAt specs y := by omega
    have hsp := stageRep_mem_spawn T specs actOrd pos h_valid h_perm y hy (h_fit y hy) (sy - 1) hsy_pred
    have hpred : sy - 1 + 1 = sy := by omega
    simpa [hpred] using hsp
  have hsucc_x : stageTickOf T specs x 0 =
      obsTickOf T specs x + (stageDelayAt specs x 0 : Nat) := by
    dsimp [obsTickOf]
    rw [stageTickOf_zero T specs x]
  have hsucc_y : stageTickOf T specs x 0 =
      stageTickOf T specs y (sy - 1) + (stageDelayAt specs y sy : Nat) := by
    have hle : (sy - 1) + 1 ≤ (specAt specs y).middleDelays.length := by
      dsimp [repLenAt] at hsy_le
      omega
    have hsucc := stageTickOf_succ T specs y (sy - 1) hle
    have hpred : sy - 1 + 1 = sy := by omega
    simpa [hpred, htick] using hsucc
  have hdx_pos : 1 ≤ (stageDelayAt specs x 0 : Nat) := by
    have h := PNat.pos (stageDelayAt specs x 0)
    omega
  exact rep_delay_ge_of_before T specs actOrd pos h_valid h_perm
    (stageEventOf T specs x 0) (stageEventOf T specs y sy)
    (obsTickOf T specs x) (stageTickOf T specs y (sy - 1))
    (stageDelayAt specs x 0 : Nat) (stageDelayAt specs y sy : Nat)
    (stageTickOf T specs x 0)
    (by dsimp [stageEventOf]) (by dsimp [stageEventOf]; exact htick.symm)
    hsucc_x hsucc_y hdx_pos hspawn_x hspawn_y
    (by dsimp [stageEventOf]; exact hpri)
    hx_mem hy_mem hb

