import Proofs.Clustering.StageDescent


open BasicRedstoneSim
open List

/-! # Parent bridges (no-group clustering)

`spawnFold` order transport and the stage parent bridge that carry pop order
from one stage to the next. -/

/-- `spawnFold` of singleton spawns preserves first-occurrence order: if `x`
    precedes `y` in a list, then `f x` precedes `f y` in the fold. -/
theorem spawnFold_findIdx_order (spawn : ScheduledEvent → List ScheduledEvent)
    (l : List ScheduledEvent) {x y fx fy : ScheduledEvent}
    (hx : x ∈ l) (hy : y ∈ l)
    (hnodup_fold : (spawnFold spawn l).Nodup)
    (hx_spawn : spawn x = [fx]) (hy_spawn : spawn y = [fy])
    (hfx_ne : fx ≠ fy)
    (hxy : (_root_.findIdx? (fun a => decide (a = x)) l).getD 0 <
           (_root_.findIdx? (fun a => decide (a = y)) l).getD 0) :
    (_root_.findIdx? (fun e => decide (e = fx)) (spawnFold spawn l)).getD 0 <
      (_root_.findIdx? (fun e => decide (e = fy)) (spawnFold spawn l)).getD 0 := by
  have hsub_pair : [x, y] <+ l := sublist_pair_of_findIdx_lt l hx hy hxy
  have hspawn_sub : spawnFold spawn [x, y] <+ spawnFold spawn l :=
    spawnFold_sublist spawn hsub_pair
  have hspawn_pair : spawnFold spawn [x, y] = [fx, fy] := by
    simp [spawnFold, hx_spawn, hy_spawn]
  have hf_pair_sub : [fx, fy] <+ spawnFold spawn l := by
    simpa [hspawn_pair] using hspawn_sub
  have hfx_mem_pair : fx ∈ [fx, fy] := List.mem_cons.mpr (Or.inl rfl)
  have hfy_mem_pair : fy ∈ [fx, fy] :=
    List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
  exact (findIdx?_getD_lt_sublist (l₁ := [fx, fy]) (l₂ := spawnFold spawn l)
    hf_pair_sub hnodup_fold (x := fx) (y := fy) hfx_mem_pair hfy_mem_pair).mpr
    (by
      have hfx_pos : (_root_.findIdx? (fun e => decide (e = fx)) [fx, fy]).getD 0 = 0 :=
        findIdx?_getD_self_cons fx [fy]
      have hfy_pos : (_root_.findIdx? (fun e => decide (e = fy)) [fx, fy]).getD 0 = 1 := by
        rw [findIdx?_getD_cons fx fy [fy] (by simp) hfx_ne,
          findIdx?_getD_self_cons fy []]
      rw [hfx_pos, hfy_pos]
      decide)

/-- **Parent bridge (forward).** If two stage events fire in a common tick and
    one pops before the other, then their stage-successor spawns keep that
    order at their (common) firing tick. -/
theorem stageRep_succ_order (T : Nat) (specs : List ChainSpec)
    (actOrd : List Nat) (pos : Nat → Nat → Nat)
    (h_valid : ∀ i < specs.length, (specAt specs i).valid)
    (h_perm : actOrd.Perm (List.range specs.length))
    (_h_fit : ∀ i < specs.length, chainDelay (specAt specs i) ≤ T)
    (x y sx sy : Nat) (hx : x < specs.length) (hy : y < specs.length)
    (hsx : sx < repLenAt specs x) (hsy : sy < repLenAt specs y)
    (htick : stageTickOf T specs x sx = stageTickOf T specs y sy)
    (htick_succ : stageTickOf T specs x (sx + 1) = stageTickOf T specs y (sy + 1))
    (hx_mem : stageEventOf T specs x sx ∈
        popSeq (simWorld T specs actOrd pos (stageTickOf T specs x sx)))
    (hy_mem : stageEventOf T specs y sy ∈
        popSeq (simWorld T specs actOrd pos (stageTickOf T specs y sy)))
    (hb : (_root_.findIdx? (fun e => decide (e = stageEventOf T specs x sx))
            (popSeq (simWorld T specs actOrd pos (stageTickOf T specs x sx)))).getD 0 <
          (_root_.findIdx? (fun e => decide (e = stageEventOf T specs y sy))
            (popSeq (simWorld T specs actOrd pos (stageTickOf T specs y sy)))).getD 0) :
    (_root_.findIdx? (fun e => decide (e = stageEventOf T specs x (sx + 1)))
        (simWorld T specs actOrd pos (stageTickOf T specs x (sx + 1))).events).getD 0 <
      (_root_.findIdx? (fun e => decide (e = stageEventOf T specs y (sy + 1)))
        (simWorld T specs actOrd pos (stageTickOf T specs y (sy + 1))).events).getD 0 := by
  set ex := stageEventOf T specs x sx
  set ey := stageEventOf T specs y sy
  set fx := stageEventOf T specs x (sx + 1)
  set fy := stageEventOf T specs y (sy + 1)
  set τ := stageTickOf T specs x sx
  set τ' := stageTickOf T specs x (sx + 1)
  have hτy : stageTickOf T specs y sy = τ := htick.symm
  have hτy' : stageTickOf T specs y (sy + 1) = τ' := htick_succ.symm
  have hex_ne : ex ≠ ey := by
    intro h
    have hb'' : (_root_.findIdx? (fun e => decide (e = ex))
        (popSeq (simWorld T specs actOrd pos τ))).getD 0 <
          (_root_.findIdx? (fun e => decide (e = ey))
            (popSeq (simWorld T specs actOrd pos τ))).getD 0 := by
      simpa [ex, ey, τ, hτy] using hb
    rw [← h] at hb''
    omega
  have hfx_ne : fx ≠ fy := by
    intro h
    have hnode := congrArg ScheduledEvent.nodeId h
    dsimp [fx, fy, stageEventOf] at hnode
    have hxy' := chainRepId_inj specs x y (sx + 1) (sy + 1) hx hy
      (by dsimp [repLenAt] at hsx; omega)
      (by dsimp [repLenAt] at hsy; omega)
      (h_valid x hx).1 (h_valid y hy).1 hnode
    have hx_eq : x = y := hxy'.1
    have hs_eq : sx = sy := by omega
    have hex_eq : ex = ey := by
      dsimp [ex, ey]
      rw [hx_eq, hs_eq]
    exact hex_ne hex_eq
  have hspawn_x : cascadeSpawn T specs ex = [fx] := by
    dsimp [ex, fx]
    exact cascadeSpawn_stage T specs h_valid x sx hx hsx
  have hspawn_y : cascadeSpawn T specs ey = [fy] := by
    dsimp [ey, fy]
    exact cascadeSpawn_stage T specs h_valid y sy hy hsy
  set l := popSeq (simWorld T specs actOrd pos τ)
  have hx_l : ex ∈ l := by simpa [l, ex, τ] using hx_mem
  have hy_l : ey ∈ l := by simpa [l, ey, τ, hτy] using hy_mem
  have hb_l : (_root_.findIdx? (fun e => decide (e = ex)) l).getD 0 <
      (_root_.findIdx? (fun e => decide (e = ey)) l).getD 0 := by
    simpa [l, ex, ey, τ, hτy] using hb
  have hnodup_fold : (spawnFold (cascadeSpawn T specs) l).Nodup := by
    have hsub := simWorld_popSeq_spawn_sublist T specs actOrd pos τ h_valid h_perm
    have hnd := (simWorld_tickInv T specs actOrd pos h_valid h_perm (τ + 1)).1
    exact List.Sublist.nodup hsub hnd
  have hfold : (_root_.findIdx? (fun e => decide (e = fx))
      (spawnFold (cascadeSpawn T specs) l)).getD 0 <
        (_root_.findIdx? (fun e => decide (e = fy))
          (spawnFold (cascadeSpawn T specs) l)).getD 0 :=
    spawnFold_findIdx_order (cascadeSpawn T specs) l hx_l hy_l hnodup_fold
      hspawn_x hspawn_y hfx_ne hb_l
  have hsub_next : spawnFold (cascadeSpawn T specs) l <+
      (simWorld T specs actOrd pos (τ + 1)).events := by
    simpa [l] using (simWorld_popSeq_spawn_sublist T specs actOrd pos τ h_valid h_perm)
  have hnodup_next : (simWorld T specs actOrd pos (τ + 1)).events.Nodup :=
    (simWorld_tickInv T specs actOrd pos h_valid h_perm (τ + 1)).1
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
      (simWorld T specs actOrd pos (τ + 1)).events).getD 0 <
        (_root_.findIdx? (fun e => decide (e = fy))
          (simWorld T specs actOrd pos (τ + 1)).events).getD 0 :=
    (findIdx?_getD_lt_sublist (l₁ := spawnFold (cascadeSpawn T specs) l)
      (l₂ := (simWorld T specs actOrd pos (τ + 1)).events)
      hsub_next hnodup_next (x := fx) (y := fy) hfx_mem_fold hfy_mem_fold).mpr hfold
  have hfx_next : fx ∈ (simWorld T specs actOrd pos (τ + 1)).events :=
    List.Sublist.mem hfx_mem_fold hsub_next
  have hfy_next : fy ∈ (simWorld T specs actOrd pos (τ + 1)).events :=
    List.Sublist.mem hfy_mem_fold hsub_next
  have hτ_ge : τ + 1 ≤ τ' := by
    dsimp [τ, τ']
    have hsucc := stageTickOf_succ T specs x sx (by
      dsimp [repLenAt] at hsx
      omega)
    have hdelay_pos : 1 ≤ (stageDelayAt specs x (sx + 1) : Nat) := by
      have h := PNat.pos (stageDelayAt specs x (sx + 1))
      omega
    rw [hsucc]
    omega
  have htick_fx : fx.targetTick = τ' := by
    dsimp [fx, stageEventOf, τ']
  have htick_fy : fy.targetTick = τ' := by
    dsimp [fy, stageEventOf]
    rw [hτy']
  have hargτ' : (τ + 1) + (τ' - (τ + 1)) = τ' := by
    exact Nat.add_sub_of_le hτ_ge
  have htgt_fxN : (τ + 1) + (τ' - (τ + 1)) ≤ fx.targetTick := by
    simp [htick_fx, hargτ']
  have htgt_fyN : (τ + 1) + (τ' - (τ + 1)) ≤ fy.targetTick := by
    simp [htick_fy, hargτ']
  have horder := simWorld_findIdx_order_survive T specs actOrd pos h_valid h_perm
    (τ + 1) (τ' - (τ + 1)) (e₁ := fx) (e₂ := fy)
    hfx_next hfy_next htgt_fxN htgt_fyN hfold_next
  rw [hτy']
  simpa [fx, fy, τ', hargτ'] using horder
