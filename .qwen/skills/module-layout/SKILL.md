---
name: module-layout
description: Where declarations live and how to split or extend the proof modules in this repo. Use when adding a theorem file, splitting a large file, or deciding where a lemma belongs.
---

# Module map

```
BasicRedstoneSim/
  Basic.lean        — the model: World, nodes, scheduled-event queue,
                      stepUntilNextTick, simFoldl. Model + API lemmas only.
  Tests.lean        — 51 generated simulation tests (via gen_tests.py)
Main.lean           — imports Tests + PrefixChain.Basic; `lake exe main`
BasicProofs.lean    — library root. Imports PrefixChain.Basic only.
                      REQUIRED: without this file `lake build BasicProofs`
                      fails with "some modules have bad imports".
BasicProofs/
  PrefixChain/
    Part01..Part17  — the proof development, serial chain
    Basic.lean      — public capstone statements; imports Part17
  GroupClustering.lean — WIP n-group extension (2 known sorries). Builds
                      only via its own module target; never drag it into
                      the default closure.
python/             — reference model + test generator (see python-crosscheck)
```

## Rules

- **Parts chain**: `PartNN` imports `Part(NN-1)` only. Downstream parts see
  everything transitively. Never reorder existing declarations across parts —
  later parts reference them through the chain.
- **Names**: each Part starts with `open BasicRedstoneSim`, so declarations
  named `World.foo` land in `BasicRedstoneSim.World.foo`; unqualified
  top-level names are module-qualified (`BasicProofs.PrefixChain.PartNN.x`)
  but visible unqualified downstream through the import chain.
- **Size**: keep every Part under ~950 lines. When one approaches the limit,
  move finished blocks into the next Part.
- **Part header template**:
  ```lean
  import BasicProofs.PrefixChain.Part(NN-1)

  open BasicRedstoneSim
  ```
  No `set_option maxHeartbeats` — banned repo-wide.
- **New top-level results** (finished theorems meant to be cited) go in
  `PrefixChain/Basic.lean`, not inside a Part.
- **Imports lead the file**; doc comments go below the import block (this
  toolchain rejects a module doc before the first import).
- **Import discipline**: targeted Mathlib imports only (see proof-style).
  New tactic usage may require adding the specific `Mathlib.Tactic.*` module
  to Part01 so the whole chain sees it.
