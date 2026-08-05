---
name: proof-style
description: Tactic discipline and known Lean 4 gotchas for writing or editing proofs in this repo. Use when writing new lemmas or modifying proofs under BasicProofs/ or BasicRedstoneSim/.
---

# Proof style for this repo

Proofs live in two phases, with different rules.

## Phase 1 — exploring: auto tactics ENCOURAGED

When hunting for a proof route, automate freely:

- `aesop`, `tauto`, `simp_all`, `simp [...] at *`, `omega`, `norm_num`,
  `interval_cases`, `decide`, `linarith`, `convert` — all welcome here.
- Sketch top-down with `sorry` in intermediate `have`s to pin the structure.
- If an automated call finds the route, note *what* it did (the trace, or the
  `Try this` suggestion) — that becomes the finished proof.

Nothing in this phase needs to be pretty; it only needs to find the route.

## Phase 2 — finishing: explicit and lean

A proof is **done** only when all of these hold:

1. Every `aesop` is replaced by the explicit tactic sequence that does the
   same work (`rw`/`simp`/`rcases`/`exact`/...). No `aesop` survives into a
   finished proof.
2. `tauto` is replaced by direct steps (`exact h`, `rcases h with ...`,
   `Or.elim`, `exfalso; apply ...`). Tauto backtracking over large contexts
   is the single most expensive pattern seen in this repo (seconds per call).
3. No unused simp arguments, no dead tactics, no "tactic does nothing" /
   "never executed" linter warnings — the build must stay at **0 warnings**.
4. The declaration elaborates within the default 200k-heartbeat budget.
   `set_option maxHeartbeats` overrides are banned; if a declaration busts
   the budget, the proof is too coarse — decompose or sharpen it.
5. `simp [...] at *` over huge contexts (100+ hypotheses) is replaced by
   `simp only [explicit list] at h` scoped to the hypotheses that matter, or
   by applying the relevant projection lemma directly.
6. `<;> try A <;> try B` catch-all chains after `split_ifs` are replaced by
   explicit per-branch proofs when the branch structure is known — the
   catch-all form runs the expensive *failing* tactic in every branch.

## Prefer in finished proofs

- Precise steps: `rw`/`simp only [explicit lemmas]` scoped to the hypotheses
  that matter, `exact` with projection lemmas (e.g. `World.updateNode_events`)
  instead of `simp [w']` unfolding.
- `decide` for closed Nat/PNat goals — kernel reduction, no tactic search.
- `omega` for Nat/Int linear arithmetic (core tactic; handles casts).
- Decomposition: when a proof body grows past ~500 lines, promote inner
  `have`s to top-level lemmas parameterized over the let-bound state
  (this is how `simulateWithInsertion_pos_indep` was broken into the
  `pos_indep_*` family).

## Common patterns in this repo

- `List.Mem` on a cons: `rw [List.mem_cons] at hx ⊢; rcases hx with rfl | hx`
  (`cases hx` directly is rejected — needs the mem_cons rewrite first).
- Dependent `getElem` rewrites: plain `simp` fails on the index proofs;
  use `simp_all [h_f, h_take_f, List.getElem_cons_succ]`.
- Cross-list `getElem` transport: `simpa [h_filter_p.symm] using h_k_eq`.
- `interval_cases` equality branches: `exact heq ▸ h_priN`.
- Split-branch beq contradictions: `exfalso; simp_all`, or
  `exfalso; apply h_eq; rename_i h; simpa using h` (match the goal's
  direction — don't assume `.symm` is needed).
- World equality: `ext` + the five fields `nodes/events/tick/nextId/outputLog`.
- Two-sided `split_ifs` comparisons (`simBody` unfolds to 2 ifs per side, so
  4 conditions / 16 branches across an equality): expect most branches to be
  contradictions via tick arithmetic (`omega` after simplifying the
  condition hypothesis).

## Gotchas (verified in this repo, Lean/Mathlib v4.32.0)

- `omega` does NOT normalize `(x == y) = true`; plain `simp` does (beq
  normalization lives in the default simp set). Reduce beq-hyps with simp
  before calling omega.
- `split_ifs with h₁ h₂` names conditions by syntactic identity across
  branches; a condition that differs between branches comes out as `h✝` in
  some goals. Check each branch before relying on the names.
- `change X = _` elaborates the hole through refine — slow in huge contexts.
  Write the full target or use `show`.
- `List.enum` no longer exists in Mathlib v4.32; use `List.zipIdx` — note the
  pair order flips: enum was (index, element), zipIdx is (element, index).
- `norm_num` can stall on PNat coercions; `decide` works.
- `push_neg` is deprecated → `push Not at h`.
- `simpa [lems] using h` — when the linter says "try simp", the goal closes
  with `simp [lems]` alone; drop the simpa.
- Record literals inside `some (...)` annotations break the parser — bind via
  `set nd : NodeData := {...}` first.
- `in2 :: in2 + 1 :: rest` parses as `in2 :: (in2 + (1 :: rest))` — always
  parenthesize `in2 :: (in2 + 1) :: rest`.
- Imports must lead the file; a `/-- ... -/` doc comment before the first
  `import` is rejected by this toolchain ("invalid 'import' command").
- Blanket `import Mathlib.Tactic` is banned — it loads hundreds of modules
  into every downstream file. Import only what is used (this repo needs:
  `Mathlib.Tactic.ByContra`, `.Convert`, `.IntervalCases`, `.Linarith`,
  `.NormNum`, `.Push`).
