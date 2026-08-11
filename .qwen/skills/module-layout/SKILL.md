---
name: module-layout
description: Where declarations live and how to split or extend the proof modules in this repo. Use when adding a theorem file, splitting a large file, or deciding where a lemma belongs.
---

# Module map

```
BasicRedstoneSim/
  Basic.lean        — the model: World, nodes, scheduled-event queue,
                      stepUntilNextTick, simFoldl. Model + API lemmas only.
  Tests.lean        — 51 generated simulation tests (via gen_tests.py);
                      git-ignored, may be absent.
Main.lean           — imports PrefixChain.Basic + GroupClustering.Basic;
                      `lake exe main`
BasicProofs.lean    — library root. Imports both Basic modules.
                      REQUIRED: without this file `lake build BasicProofs`
                      fails with "some modules have bad imports".
BasicProofs/
  PrefixChain/
    Part01..Part17  — the proof development, serial chain
    Basic.lean      — public capstone statements; imports Part17
  GroupClustering/
    Definitions.lean .. ClusteringCore.lean
                      — 76 descriptively named modules (see the old-Part
                      mapping below), import DAG (not a strict chain)
    Basic.lean      — the two public capstone statements; imports
                      Definitions, OrderPreservationCore, ClusteringCore
python/             — reference model + test generator (see python-crosscheck)
```

## Rules

- **PrefixChain parts chain**: `PartNN` imports `Part(NN-1)` only.
  Downstream parts see everything transitively. Never reorder existing
  declarations across parts — later parts reference them through the chain.
- **GroupClustering modules**: named by topic; each module imports the
  modules it needs (a DAG). New lemmas go into the module of their topic,
  or into a new module that imports what it needs.
- **Names**: each module starts with `open BasicRedstoneSim` (plus `List` in
  GroupClustering), so declarations named `World.foo` land in
  `BasicRedstoneSim.World.foo`; unqualified top-level names are
  module-qualified (`BasicProofs.GroupClustering.X.y`) but visible
  unqualified downstream through imports.
- **Size**: keep every module under ~950 lines. GroupClustering's
  ClusteringCore is a known 2500-line exception (capstone assembly).
  When a module approaches the limit, move finished blocks into a new
  module.
- **Module header template** (GroupClustering):
  ```lean
  import BasicProofs.GroupClustering.<Dependency>

  open BasicRedstoneSim List
  ```
  No `set_option maxHeartbeats` — banned repo-wide.
- **New top-level results** (finished theorems meant to be cited) go in the
  development's `Basic.lean`, not inside a working module.
- **Imports lead the file**; doc comments go below the import block (this
  toolchain rejects a module doc before the first import).
- **Import discipline**: targeted Mathlib imports only (see proof-style).
  GroupClustering imports Mathlib only transitively via
  `BasicProofs.PrefixChain.Part17` — keep it that way.

## GroupClustering old-Part → module mapping

Historic references (memory files, git history, older summaries) use the
`PartNN` names. Mapping:

```
Part01 Definitions                   Part42 ActivationListOrder
Part02 TickBookkeeping               Part43 FinalsBundle
Part03 BurstEventShape               Part44 OrderPreservationCore
Part04 BurstEventAccounting          Part45 OutputBetweennessBridge
Part05 SimulationHealth              Part46 BackwardTransport
Part06 NodeLayout                    Part47 ForwardTransport
Part07 Dynamics                      Part48 ConverseStage0
Part08 StageEvents                   Part49 Stage1BaseClassification
Part09 QueueMembership               Part50 PreStepWorldFacts
Part10 PopOrder                      Part51 Stage1BaseTransport
Part11 PopSeqFuel                    Part52 Stage1PostDrainBase
Part12 FullTickStructure             Part53 InterloperIsSpawn
Part13 SameSpecLockstep              Part54 Stage1BaseCase
Part14 LockstepComposition           Part55 SuccessorMembershipRange
Part15 MiddleBlockInvariant          Part56 CrossPriorityPopDiscipline
Part16 ConverseSpawn                 Part57 BurstCrossPrioritySpawnOrder
Part17 MiddleBlockPopStep            Part58 Stage1BaseGeneral
Part18 LogBridge                     Part59 FinalsBackwardTransportI
Part19 SameSpecBeforeness            Part60 FinalsBackwardTransportII
Part20 QSideOrder                    Part61 FinalsBackwardTransportIII
Part21 MiddleBlockOkTicks            Part62 MiddleFinalSpawnTick
Part22 OutputPositionBridge          Part63 StageInductionSideFacts
Part23 GSimBodyIteration             Part70 EarlyParentIntruder
Part24 OrderPreservationPremises     Part71 ConverseStageJ
Part25 StageEventNodup               Part72 InductionStepPayload
Part26 MiddleBlockOkStageInduction   Part74 MiddleBlockOkActiveTick
Part27 NodupChain                    Part75 SurvivalFreeStageInduction
Part28 BurstSurvival                 Part76 SideHypothesisDischarge
Part29 FinalTransition               Part77 MiddleBlockOkLastMiddleStage
Part30 OutputLogEntries              Part78 SamePriorityPopOrder
Part31 ConverseSpawnFinal            Part79 FinalStageAssemblySetup
Part32 SuccessorSurvival             Part80 FinalConverseDrainPhase
Part33 Stage0BaseOrder               Part81 FinalConverseBurstPhase
Part34 ConverseFinalUnconditional    Part82 FinalConverseMixedPhase
Part35 FinalPopIndex                 Part83 ClusteringCore
Part36 QSideOrderDischarged
Part37 LogShape                      (Part64–69 and Part73 never existed:
Part38 SimulationLevelFacts           the old numbering had gaps)
Part39 QSideOrderNoSurvival
Part40 NoEarlyChainEntries
Part41 StageEventCompleteness
```
