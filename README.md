# Entity ID Based Wireless Redstone Related Proofs

This repository contains Lean 4 proofs of the redstone scheduling
properties that entity-ID (EID) based wireless redstone relies on. The
proofs use Mathlib v4.32.0.

## Model

`BasicRedstoneSim` defines a deterministic, tick-accurate model of
Minecraft redstone. The model has these parts:

- `World`: nodes and a priority queue of scheduled events. The nodes
  are inputs, observers, repeaters with configurable delays, and
  outputs.
- `stepUntilNextTick`: processes all events of the current tick, then
  advances the tick. The termination proof uses the event structure
  and no fuel parameter.
- Repeater, observer, and input semantics that match the in-game
  behavior.

The model has 51 simulation tests. `python/gen_tests.py` generates
these tests from an independent Python implementation of the same
mechanics (`python/basic_redstone_sim.py`).

## What is proved

### Prefix chains

A *prefix chain* is a wire of this shape:

```
Input → Observer → [Repeater, delay dᵢ]* → Repeater, delay d_last → Output
```

`ChainSpec` formalizes the chain. Every delay is *valid*: one of the
repeater delays 2, 4, 6, 8 ticks.

`simulateWithInsertion c1 c2 t1 t2 pos` simulates two such chains
started at ticks `t1` and `t2`. The simulation inserts the input pulse
of chain `c2` at queue position `pos` while chain `c1` processes its
events. `aActivatesFirst` reads the output log and reports the chain
that activated first.

The main theorem is `activation_order_independent_of_insertion` in
`BasicProofs.PrefixChain.Basic`:

> Take two valid prefix chains whose outputs fire on the same tick.
> The relative activation order of the two outputs does not depend on
> the insertion position `pos`.

When two chains land on the same output tick, the one that activates
first is a function only of the two chain specifications. The queue
interleaving from the insertion cannot change the order. This
guarantee lets EID wireless redstone encode ordering through
activation order.

### Group clustering

A *group* is a set of chains. The last node of every chain in the
group fires at the same tick `T`, and all chains in the group have
equal total delay. The simulation activates a group by firing all of
its observers directly at tick `T − D`, where `D` is the group delay.
These choices are arbitrary:

- the activation order of the groups (`groupOrd`),
- the firing order of the observers within a group (`withinOrd`),
- queue insertions between activations (`pos`).

`BasicProofs.GroupClustering.Basic` states the two capstone theorems:

- **Clustering** — `group_output_clustering`: between any two outputs
  of chains with identical `ChainSpec`, only outputs of that same
  spec appear.
- **Order preservation** — `group_order_preservation`: groups A and B
  both contain chains of spec `sa` and of spec `sb`. If the
  `sa` instances order A before B, then the `sb` instances also order
  A before B. The relative order of two groups does not depend on the
  spec used to observe it.

### Round-robin activation

A round-robin group is a list of chains with identical `ChainSpec`.
All groups that activate on the same tick fire in one atomic
round-robin batch: round `k` enqueues the observer event of the `k`-th
chain of every group, in a fixed group order (`groupOrd`); exhausted
groups drop out; no queue processing happens inside the batch.

`groupSimulateRR` is defined as the ordinary group simulation on
singleton-split groups: every bundle chain becomes a one-chain group,
and the singletons are activated in the round-robin enumeration order
with no queue insertion. The two capstone theorems in
`BasicProofs.GroupClustering.RoundRobinTheorems` follow from the
group-clustering cores applied to this split system:

- **Clustering** — `group_rr_output_clustering`: identical-spec
  bundle-chain outputs are contiguous in the round-robin output order.
- **Order preservation** — `group_rr_order_preservation`: for two
  same-spec bundle chains, the output order is exactly the
  round-robin activation order (`rrBefore`): round (chain index)
  first, then position in `groupOrd`. The equivalence is strict:
  output position `p₁ < p₂` if and only if the first chain activates
  before the second.

## Repository layout

```
BasicRedstoneSim/Basic.lean     the redstone model
BasicProofs.lean                library root
BasicProofs/PrefixChain/        prefix chain development (Part01 to
                                Part17, plus Basic)
BasicProofs/GroupClustering/    group clustering and round-robin
                                development (78 named modules, plus
                                Basic)
python/                         reference implementation and test
                                generator
Main.lean                       executable entry point
```

## Build and test

Install elan. The build reads the Lean toolchain from
`lean-toolchain` and fetches Mathlib v4.32.0 on the first build.

1. Build all proofs and the executable: `lake build`. The first build
   also compiles Mathlib.
2. Generate the simulation tests: run `python3 python/gen_tests.py`.
   The script writes `BasicRedstoneSim/Tests.lean`.
3. To run the tests, add the import of `BasicRedstoneSim.Tests` to
   `Main.lean`. Then build again. Then run `lake exe main`. Each of
   the 51 tests prints `✓ PASS`.

`BasicRedstoneSim/Tests.lean` is git-ignored. A fresh checkout builds
without it, and `main` runs no tests in that case.

If you work in WSL with the repository on a Windows mount, use
`lake.exe` instead of `lake`. The Linux wrapper can hang on this file
system.
