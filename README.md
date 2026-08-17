# Entity ID Based Wireless Redstone Proofs

This repository uses the Lean 4 proof assistant. It proves four facts
about redstone repeater chains. Entity-ID based wireless redstone
depends on these facts.

## Read this first: what a chain is

You do not need to know redstone to read this section.

A redstone signal is a short pulse of power.

A repeater is a block. It receives a signal. It waits for a fixed time.
Then it sends the signal on. That wait is a delay. In this model, a
delay is 2, 4, 6, or 8 game ticks.

A chain is a line of parts. The line starts with an observer. The
observer detects a change and starts the signal. Then the signal passes
through a row of repeaters. Each repeater adds its delay. The line ends
with an output. The output lights when the signal reaches it.

A priority is a number from -3 to -1. When two repeaters fire at the
same tick, the priority breaks the tie.

A spec is the list of delays and priorities of the repeaters in a
chain. Two chains have the same spec when their repeaters match, in
order.

The activation order is the order in which the chains start.

The output log is the list of outputs, in the order that they light.
The output position of a chain is its place in that log.

## The four facts

The four facts are theorems in the `Proofs` library. Each fact assumes
a valid system. In a valid system, every chain is valid. All the chains
finish on one common tick.

### Clustering

Suppose that two chains have the same spec. Suppose that a third chain
lights its output after the first chain and before the second chain.
Then the third chain has the same spec too.

In other words, chains with the same spec light as one block. No chain
with a different spec can split that block.

### Order preservation

Chains with the same spec light in the same order as their activation
order.

### Suffix clustering

The last `n` repeaters of a chain form its `n`-suffix. Two chains share
a suffix when their last `n` repeaters match.

Suppose that two chains share their last `n` repeaters. Suppose that a
third chain lights its output after the first chain and before the
second chain. Then the third chain also shares those last `n` repeaters.

### Suffix order preservation

Chains that share their last `n` repeaters light in the order in which
their first shared repeater enters the queue.

## Technical details

### The no-group model

The `Proofs` library uses the no-group model. In this model, the chains
activate one at a time. Between two activations, the simulator
processes any number of events from the queue. All the chains finish on
one common tick `T`.

### The simulator

`BasicRedstoneSim` is the executable redstone simulator.

- The world is immutable. It holds the nodes, a queue of scheduled
  events, the current tick, and the output log.
- The nodes are inputs, observers, repeaters, and outputs.
- Each scheduled event has a target tick, a priority, and a node.
- One step processes all the events of the current tick. Then it
  advances the tick.
- When an output lights, the simulator writes its name to the output
  log.

The `python/` folder holds an independent Python model of the same
mechanics. The Python sweeps act as an oracle. They do an independent
check of each claim before the formal proof. The file
`python/gen_tests.py` generates the 51 simulation tests in
`BasicRedstoneSim/Tests.lean`. Git ignores that generated file.

### The spec

A `ChainSpec` has four fields. They are the middle delays, the middle
priorities, the last delay, and the last priority. The chain structure
is:

```
Input → Observer → [middle repeaters] → last Repeater → Output
```

The observer adds 2 ticks. The total delay of a chain is:

```
2 + (sum of middle delays) + last delay
```

A valid delay is 2, 4, 6, or 8 ticks. A valid priority is -3, -2, or
-1. A spec is valid when its priorities match its delays, and every
delay and priority is in range.

### Library layout

```
Proofs/Model/               the model: specs, chain building, the
                            simulation driver, and output positions
Proofs/Clustering/          the clustering theorem
Proofs/OrderPreservation/   the order preservation theorem
Proofs/SuffixSubchain/      the suffix clustering and suffix order
                            preservation theorems
```

### Status

The four theorems are proved. The `Proofs` library has no `sorry`, no
`axiom`, and no `admit`.

## The old library: `BasicProofs/`

`BasicProofs/` holds an older formalization. That formalization uses
groups of chains. It contains the `PrefixChain` and `GroupClustering`
developments.

This library is deprecated. The repository keeps it for reference only.
The new `Proofs` library does not import it. Use the `Proofs` library
for new work.

## Build

The toolchain is Lean v4.32.0 with Mathlib v4.32.0. The files
`lean-toolchain` and `lakefile.toml` state these versions.

Install elan before the first build. The first build downloads Mathlib.

On this machine, use `lake.exe`. The Linux `lake` wrapper can hang on
this file system.

- To build the active library, run `lake.exe build Proofs`.
- To build the whole repository, run `lake.exe build`. This command also
  builds the deprecated `BasicProofs` library.

## Repository layout

```
BasicRedstoneSim/   the redstone simulator
Proofs/             the active library (the four facts)
BasicProofs/        the older group-based library (deprecated)
python/             the Python reference model, the sweeps, and the
                    test generator
Main.lean           the executable entry point
```
