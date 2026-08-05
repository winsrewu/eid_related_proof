# Entity ID Based Wireless Redstone Related Proofs

A Lean 4 formalization (with Mathlib v4.32.0) of the redstone scheduling
properties that entity-ID (EID) based wireless redstone constructions rely on.

## Model

`BasicRedstoneSim` defines a deterministic, tick-accurate model of Minecraft
redstone:

- a `World` of nodes (inputs, observers, repeaters with configurable delays,
  outputs) together with a priority queue of scheduled events,
- `stepUntilNextTick`: process all events of the current tick, then advance
  the tick — termination is proved from the event structure itself (no fuel),
- repeater / observer / input semantics matching in-game behaviour.

The model is validated by 51 simulation tests (run via `lake exe main`),
generated from an independent Python implementation of the same mechanics.

## What is proved

### Setup

A *prefix chain* is a wire of the shape

```
Input → Observer → [Repeater, delay dᵢ]* → Repeater, delay d_last → Output
```

formalized as `ChainSpec`, where every delay is *valid* (`ValidDelay`: one of
2, 4, 6, 8 ticks — the repeater delays).

`simulateWithInsertion c1 c2 t1 t2 pos` simulates two such chains started at
ticks `t1` and `t2`, where chain `c2`'s input pulse is inserted at queue
position `pos` while chain `c1`'s events are being processed.
`aActivatesFirst` reads the resulting output log and reports which chain's
output activated first.

### Main theorem

`activation_order_independent_of_insertion` in `BasicProofs.PrefixChain.Basic`:

> For any two valid prefix chains whose outputs fire on the same tick, the
> relative activation order of the two outputs does not depend on the
> insertion position `pos` (nor on redundant variation of the second chain's
> start tick).

That is, when two chains land on the same output tick, which one activates
first is a function only of the two chain specifications — the event-queue
interleaving introduced by inserting one chain's input into the other's
processing cannot change the order. This is the correctness guarantee that
lets EID wireless redstone encode ordering through activation order.

## Work in progress

- `BasicProofs.GroupClustering` — the n-group extension: groups of
  same-output-tick chains activated directly at their observers; clustering
  and inter-group order-preservation claims (incomplete).
