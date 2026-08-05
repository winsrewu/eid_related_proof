import BasicProofs.PrefixChain.Part17


open BasicRedstoneSim

/-- **Activation Order Independence (with arbitrary insertion)**

For any two valid prefix chains whose outputs fire on the same tick,
the activation order is the same no matter where the second input
is inserted during the first chain's processing. -/
theorem activation_order_independent_of_insertion
  (c1 c2 : ChainSpec)
  (h1_middle : ∀ d ∈ c1.middleDelays, ValidDelay d)
  (h1_last : ValidDelay c1.lastDelay)
  (h2_middle : ∀ d ∈ c2.middleDelays, ValidDelay d)
  (h2_last : ValidDelay c2.lastDelay)
  (t1 : Nat)
  (t2 t2' : Nat)
  (pos pos' : Nat)
  (h_same  : t1 + c1.totalDelay = t2  + c2.totalDelay)
  (h_same' : t1 + c1.totalDelay = t2' + c2.totalDelay)
  : aActivatesFirst (simulateWithInsertion c1 c2 t1 t2  pos) =
    aActivatesFirst (simulateWithInsertion c1 c2 t1 t2' pos') := by
  have ht2 : t2 = t2' := by omega
  subst ht2
  congr 1
  exact simulateWithInsertion_pos_indep c1 c2 t1 t2 pos pos'
    h1_middle h1_last h2_middle h2_last h_same
