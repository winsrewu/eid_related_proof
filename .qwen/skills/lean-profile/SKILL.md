---
name: lean-profile
description: Find slow declarations and tactic hotspots in this Lean 4 repo using per-declaration elaboration profiling. Use when a module builds slowly or when optimizing build speed.
---

# Profiling elaboration time

`lean --profile` prints a line per tactic/phase above ~100 ms:
`tactic execution of <tactic> took <N>ms`, plus `import took <N>s` and
`linting took <N>ms` entries. Entries appear in execution order.

## Workflow

```bash
cd /mnt/g/eid_related_proofs
lake.exe env lean --profile BasicProofs/PrefixChain/Part17.lean > /tmp/profile17.txt 2>&1
```

Parse/aggregate (Python):

```python
import re
rows = []
for l in open('/tmp/profile17.txt'):
    m = re.match(r'\s*(.*?) took ([\d.]+)(ms|s)\s*$', l.rstrip())
    if m:
        ms = float(m.group(2)) * (1000 if m.group(3) == 's' else 1)
        rows.append((ms, m.group(1).strip()))
for ms, name in sorted(rows, reverse=True)[:15]:
    print(f'{ms:8.1f}ms  {name}')
```

Correlate entries with source: warnings interleaved in the same output carry
`file:line:col`; within one declaration entries are execution-ordered.

## What to look for

- `contradiction` entries in the seconds range ⇒ search-heavy tactic running
  internally (historically `tauto` backtracking over 100-hyp contexts). Replace
  with explicit `exact`/`rcases` proofs.
- Many `simp` entries at 300–700 ms ⇒ `simp [...] at *` over huge contexts or
  default-simp-set blowups. Prefer `simp only [explicit]` scoped to specific
  hypotheses, or rewrite with the projection lemmas directly.
- `refine` entries with no literal `refine` in source ⇒ `change ... = _` holes,
  `⟨a, by ...⟩` constructor terms, or macro-expanded tactics; give explicit
  terms instead of holes.
- `import took` ⇒ module-load floor; reducible only by trimming imports
  (this repo already replaced blanket `import Mathlib.Tactic` with targeted
  tactic modules — keep it that way).

## Budgets

Default heartbeat budget is 200k per declaration; this repo has no
`maxHeartbeats` overrides anywhere. If a declaration legitimately needs more,
optimize the proof rather than re-adding the override.
