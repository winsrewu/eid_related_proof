"""Random test generator for the redstone simulator.

Generates random configurations, runs them through the Python reference model,
and writes a Lean 4 test file to BasicRedstoneSim/Tests.lean.

Usage: python gen_tests.py [seed] [num_tests]
"""

import io
import random
import sys
from contextlib import redirect_stdout
from pathlib import Path

from basic_redstone_sim import (
    InputNode,
    OutputNode,
    Repeater,
    Observer,
    World,
    connect_chain,
)

PROJECT_ROOT = Path(__file__).resolve().parent.parent
OUTPUT_FILE = PROJECT_ROOT / "BasicRedstoneSim" / "Tests.lean"


def run_python_sim_with_ticks(chains, signals, num_ticks):
    """Run sim and interleave tick markers like the original sim.py."""
    world = World()
    input_nodes = []

    for chain in chains:
        nodes = []
        for spec in chain:
            if spec[0] == "input":
                n = InputNode(world)
                input_nodes.append(n)
            elif spec[0] == "repeater":
                n = Repeater(world, spec[1], spec[2])
            elif spec[0] == "observer":
                n = Observer(world)
            elif spec[0] == "output":
                n = OutputNode(world, spec[1])
            nodes.append(n)
        connect_chain(nodes)

    for chain_idx, level in signals:
        input_nodes[chain_idx].set_signal(level)

    log = []
    for _ in range(num_ticks):
        log.append(f"tick {world.tick}")
        buf = io.StringIO()
        with redirect_stdout(buf):
            world.step_until_next_tick()
        for line in buf.getvalue().split("\n"):
            if line.strip():
                log.append(line.strip())
    return log


def gen_random_test(rng, test_id):
    """Generate a random test case."""
    num_chains = rng.randint(1, 4)
    chains = []
    signals = []

    for i in range(num_chains):
        name = chr(ord("A") + i)
        chain = [("input",)]

        num_repeaters = rng.randint(1, 4)
        for _ in range(num_repeaters):
            delay = rng.randint(1, 4)  # in redstone ticks
            priority = rng.randint(-5, 5)
            chain.append(("repeater", delay, priority))

        if rng.random() < 0.2:
            chain.append(("observer",))

        chain.append(("output", name))
        chains.append(chain)

        sig = rng.choice([0, 15])
        signals.append((i, sig))

    num_ticks = rng.randint(5, 20)
    return chains, signals, num_ticks


def emit_lean_test(test_id, chains, signals, num_ticks, expected_log):
    """Emit Lean 4 test code for a single test case."""
    lines = []
    lines.append(f"/-- Random test {test_id} -/")
    lines.append(f"def testRandom{test_id} : World :=")
    lines.append(f"  let w := World.empty")
    lines.append(f"")

    input_var_names = []
    for i in range(len(chains)):
        var = f"input{i}"
        input_var_names.append(var)
        lines.append(
            f"  let ({var}, w) := w.addNode {{ kind := .input, sigLevel := 0, inputs := [], outputs := [] }}"
        )

    lines.append(f"")

    for ci, chain in enumerate(chains):
        node_vars = [input_var_names[ci]]
        for ni, spec in enumerate(chain[1:], 1):
            if spec[0] == "repeater":
                delay_gt = spec[1] * 2
                priority = spec[2]
                var = f"rep{ci}_{ni}"
                pri_str = f"({priority})" if priority < 0 else str(priority)
                lines.append(
                    f"  let ({var}, w) := w.addNode {{ kind := .repeater {delay_gt} {pri_str}, sigLevel := 0, inputs := [], outputs := [] }}"
                )
                node_vars.append(var)
            elif spec[0] == "observer":
                var = f"obs{ci}_{ni}"
                lines.append(
                    f"  let ({var}, w) := w.addNode {{ kind := .observer, sigLevel := 0, inputs := [], outputs := [] }}"
                )
                node_vars.append(var)
            elif spec[0] == "output":
                var = f"out{ci}_{ni}"
                name = spec[1]
                lines.append(
                    f'  let ({var}, w) := w.addNode {{ kind := .output "{name}", sigLevel := 0, inputs := [], outputs := [] }}'
                )
                node_vars.append(var)

        ids_str = ", ".join(node_vars)
        lines.append(f"  let w := connectChain w [{ids_str}]")
        lines.append(f"")

    for chain_idx, level in signals:
        var = input_var_names[chain_idx]
        lines.append(f"  let w := w.setInput {var} {level}")

    lines.append(f"")
    lines.append(f"  w.runTicks {num_ticks}")
    lines.append(f"")

    log_items = ", ".join(f'"{s}"' for s in expected_log)
    lines.append(f"def expectedLog{test_id} : List String := [{log_items}]")
    lines.append(f"")

    return "\n".join(lines)


def emit_run_all(num_tests):
    """Emit the runAllTests function."""
    lines = []
    lines.append("/-- Run all tests and report results. -/")
    lines.append("def runAllTests : IO Unit := do")
    lines.append("  let mut allPassed := true")
    lines.append("")

    lines.append("  -- Original three-chain test")
    lines.append("  let r0 := testThreeChainSim")
    lines.append("  if r0.outputLog == expectedLog then")
    lines.append('    IO.println "✓ PASS: testThreeChainSim"')
    lines.append("  else do")
    lines.append('    IO.println "✗ FAIL: testThreeChainSim"')
    lines.append('    IO.println s!"  Expected: {expectedLog}"')
    lines.append('    IO.println s!"  Got:      {r0.outputLog}"')
    lines.append("    allPassed := false")
    lines.append("")

    for i in range(1, num_tests + 1):
        lines.append(f"  let r{i} := testRandom{i}")
        lines.append(f"  if r{i}.outputLog == expectedLog{i} then")
        lines.append(f'    IO.println "✓ PASS: testRandom{i}"')
        lines.append(f"  else do")
        lines.append(f'    IO.println "✗ FAIL: testRandom{i}"')
        lines.append(f'    IO.println s!"  Expected: {{expectedLog{i}}}"')
        lines.append(f'    IO.println s!"  Got:      {{r{i}.outputLog}}"')
        lines.append(f"    allPassed := false")
        lines.append("")

    lines.append("  if !allPassed then")
    lines.append("    IO.Process.exit 1")
    lines.append("")

    return "\n".join(lines)


ORIGINAL_TEST = """/-! # Test: Three-chain simulation (replicates python/sim.py)

Setup:
- Chain A: InputA → Repeater(4rt=8gt, priority=-1) → OutputA
- Chain B: InputB → Repeater(2rt=4gt, priority=-3) → Repeater(2rt=4gt, priority=-1) → OutputB
- Chain C: InputC → Repeater(2rt=4gt, priority=-3) → Repeater(2rt=4gt, priority=0) → OutputC

All inputs set to 15. Run for 10 ticks.
Expected: All outputs fire at tick 8 with signal 15. -/
def testThreeChainSim : World :=
  let w := World.empty

  let (inputA, w) := w.addNode { kind := .input, sigLevel := 0, inputs := [], outputs := [] }
  let (inputB, w) := w.addNode { kind := .input, sigLevel := 0, inputs := [], outputs := [] }
  let (inputC, w) := w.addNode { kind := .input, sigLevel := 0, inputs := [], outputs := [] }

  let (repA, w) := w.addNode { kind := .repeater 8 (-1), sigLevel := 0, inputs := [], outputs := [] }
  let (outA, w) := w.addNode { kind := .output "A", sigLevel := 0, inputs := [], outputs := [] }
  let w := connectChain w [inputA, repA, outA]

  let (repB1, w) := w.addNode { kind := .repeater 4 (-3), sigLevel := 0, inputs := [], outputs := [] }
  let (repB2, w) := w.addNode { kind := .repeater 4 (-1), sigLevel := 0, inputs := [], outputs := [] }
  let (outB, w) := w.addNode { kind := .output "B", sigLevel := 0, inputs := [], outputs := [] }
  let w := connectChain w [inputB, repB1, repB2, outB]

  let (repC1, w) := w.addNode { kind := .repeater 4 (-3), sigLevel := 0, inputs := [], outputs := [] }
  let (repC2, w) := w.addNode { kind := .repeater 4 0, sigLevel := 0, inputs := [], outputs := [] }
  let (outC, w) := w.addNode { kind := .output "C", sigLevel := 0, inputs := [], outputs := [] }
  let w := connectChain w [inputC, repC1, repC2, outC]

  let w := w.setInput inputC 15
  let w := w.setInput inputB 15
  let w := w.setInput inputA 15

  w.runTicks 10

def expectedLog : List String := [
  "tick 0", "tick 1", "tick 2", "tick 3",
  "tick 4", "tick 5", "tick 6", "tick 7",
  "tick 8", "A: 15", "B: 15", "C: 15",
  "tick 9"
]

"""


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 42
    num_tests = int(sys.argv[2]) if len(sys.argv) > 2 else 10

    rng = random.Random(seed)

    lean_tests = []
    for i in range(1, num_tests + 1):
        chains, signals, num_ticks = gen_random_test(rng, i)
        expected = run_python_sim_with_ticks(chains, signals, num_ticks)
        lean_code = emit_lean_test(i, chains, signals, num_ticks, expected)
        lean_tests.append(lean_code)
        print(
            f"  Test {i}: {len(chains)} chains, {num_ticks} ticks, {len(expected)} log lines",
            file=sys.stderr,
        )

    header = "-- Auto-generated by python/gen_tests.py — do not edit manually.\n"
    header += f"-- Seed: {seed}, Tests: {num_tests}\n\n"
    header += "import BasicRedstoneSim.Basic\n\n"
    header += "open BasicRedstoneSim\n\n"

    content = (
        header + ORIGINAL_TEST + "\n".join(lean_tests) + "\n" + emit_run_all(num_tests)
    )

    OUTPUT_FILE.write_text(content, encoding="utf-8")
    print(
        f"Wrote {OUTPUT_FILE} ({num_tests} random tests + 1 original)", file=sys.stderr
    )


if __name__ == "__main__":
    main()
