---
name: python-crosscheck
description: Using the Python reference redstone model in python/ to test claims and regenerate the Lean simulation tests. Use before formalizing a new claim, when Lean and intuition disagree, or when regenerating BasicRedstoneSim/Tests.lean.
---

# The reference model

`python/basic_redstone_sim.py` is an executable reference model mirroring
`BasicRedstoneSim/Basic.lean` semantics: same node kinds, same
scheduled-event queue discipline (priority, then list order), same
tick-stepping. The 51 Lean tests are generated from it, so it is the oracle
for "what the game does"; the Lean model must agree with it.

## Testing a claim before formalizing

Script against `basic_redstone_sim` from `python/`:

```python
from basic_redstone_sim import InputNode, OutputNode, Repeater, Observer, World
```

- Random sweeps: sample chain specs/delays/start ticks, run the property,
  count violations. The insertion-independence theorem was validated on
  ~1364 random configs before the proof was finished.
- Exhaustive sweeps over small chains (all delay combinations up to a small
  bound) catch structured counterexamples that random sampling misses.
- A single counterexample beats a week of Lean. If the property fails here,
  the theorem statement needs an extra hypothesis (precedent: n-group
  order-preservation requires atomic group activation).

## Regenerating the Lean tests

```bash
cd /mnt/g/eid_related_proofs/python
python gen_tests.py [seed] [num_tests]
```

Overwrites `BasicRedstoneSim/Tests.lean` with fresh generated cases. After
regenerating: `lake.exe build` then `lake.exe exe main` (expect all tests to
pass; a failure means the Lean model drifted from the reference).
