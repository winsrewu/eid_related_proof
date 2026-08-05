---
name: lean-build
description: Build, test, and verify the eid_related_proofs Lean 4 project in WSL. Use when building this repo, running its 51 simulation tests, or checking proof invariants (sorry/axiom/aesop/warning counts).
---

# Building this repo

Environment: WSL, repo on a Windows mount (`/mnt/g`), Lean via the Windows-side elan.

## Hard rules

- Always `lake.exe`, never `lake` (the Linux wrapper hangs/returns nothing here).
- Foreground builds only — never `is_background: true` for builds (user directive).
- Channel output: `... > /tmp/build_out.txt 2>&1`, then grep; builds are long.
- One build at a time. Concurrent lake processes race on `.lake` and corrupt it.
- Raise the tool timeout to 600000 ms for full builds.

## Commands

```bash
cd /mnt/g/eid_related_proofs

# Default target (main exe; does NOT compile GroupClustering)
lake.exe build > /tmp/build_out.txt 2>&1; grep -cE "error:|^warning:" /tmp/build_out.txt

# Whole BasicProofs library (includes GroupClustering, which carries 2 known sorries)
lake.exe build BasicProofs

# Single module (pulls its import prefix)
lake.exe build BasicProofs.PrefixChain.Part17

# Tests (expect 51 PASS / 0 FAIL)
lake.exe exe main 2>&1 | grep -cE "✓ PASS"

# Invariant checks (all must be empty outside GroupClustering's 2 sorries)
grep -rn "sorry\|axiom\|aesop" BasicProofs/PrefixChain/ BasicRedstoneSim/
grep -rn "maxHeartbeats" BasicProofs/ BasicRedstoneSim/ Main.lean
```

## Known flake

`failed to read file '...olean.private'` (a different olean each attempt) is
Windows-mount I/O flakiness, not a compile error. Just re-run the same build.

## Timing expectations (cached Mathlib)

Full rebuild of project modules ≈ 4 min. Per-module `Built X (Ns)` lines in the
build output give the breakdown; the 17 PrefixChain parts form a serial import
chain (Part01 → … → Part17), so they cannot parallelize.

## Never

- `lake clean` casually — if anything looks stale afterward, check `.lake` state
  before rebuilding; interrupted builds can leave the cache inconsistent.
