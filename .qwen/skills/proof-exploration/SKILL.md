---
name: proof-exploration
description: Workflow for attacking a new proof obligation in this repo — empirical cross-check first, auto-tactic exploration, then finishing. Use when starting a new theorem, stuck on a goal, or deciding whether a claim is true.
---

# Order of operations for a new claim

1. **Empirical check first.** Test the claim against the Python reference
   model (`python/basic_redstone_sim.py`) with random configs and small
   exhaustive sweeps before investing in a formal route. Counterexamples are
   cheap in Python and expensive in Lean. Precedent: insertion-independence
   was validated on ~1364 random configs + an exhaustive small-chain sweep;
   the n-group order-preservation claim turned out to need an atomicity
   assumption, with counterexample found by hand search (specs a=[2,4],
   b=[4,2]). See the `python-crosscheck` skill.

2. **Pin the statement.** Write the exact theorem type first, with all
   hypotheses explicit (validity conditions, tick relations). A wrong or
   under-hypothesized statement is the most expensive error in this repo.

3. **Explore with automation.** `aesop`, `tauto`, `simp_all`, `omega`,
   `norm_num`, `interval_cases` are all encouraged here. Sketch top-down
   with `sorry` in intermediate `have`s; fill branches in any order. Use
   `lean-profile` (skill) if a sketch elaborates slowly — a slow sketch
   usually means the context is bloated and wants decomposition.

4. **Decompose early.** If the proof body approaches ~500 lines, promote
   inner `have`s to top-level lemmas parameterized over the local state
   (pattern: the `pos_indep_*` family extracted from
   `simulateWithInsertion_pos_indep`). Smaller declarations elaborate
   faster, profile cleanly, and reuse across branches.

5. **Finish per `proof-style`.** Replace every `aesop`/`tauto` with explicit
   steps, remove dead/unused tactics, verify the declaration fits the
   default heartbeat budget, and confirm the full build is at 0 warnings
   and 51/51 tests still pass (`lean-build` skill).
