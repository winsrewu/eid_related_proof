#!/usr/bin/env python3
"""Empirical sweep for the NO-GROUP model: chains activate one at a time
(one observer enqueue per activation), with arbitrary pos-insertion between
EVERY pair of consecutive activations — including same-spec chains that
activate on the same tick.

Checked properties (all chains output on a common tick T):
  1. clustering: same-spec outputs form contiguous blocks in the log;
  2. order preservation: within each spec class, output order equals
     activation (input) order.

Repeater priorities in {-3,-2,-1}, delays in {2,4,6,8}.
"""

import random
import sys
from basic_redstone_sim import World
from rr_sweep import (DELTAS, PRIS, build_chain, chain_delay,
                      clustering_violation, output_positions,
                      rand_composition, run_group_sim)


def rand_spec(total, rng):
    parts = rand_composition(total, rng)
    pris = [rng.choice(PRIS) for _ in parts]
    return (tuple(zip(parts[:-1], pris[:-1])), (parts[-1], pris[-1]))


def sweep(n_cases, seed, pos_max):
    rng = random.Random(seed)
    viol_clust = viol_order = bad_sanity = 0
    first = {}
    for case in range(n_cases):
        # delay-sum classes; several specs may share a sum (same-tick
        # activation across different specs)
        sums = [rng.choice(range(4, 17, 2)) for _ in range(rng.randint(1, 3))]
        specs = []
        for s in sums:
            for _ in range(rng.randint(1, 3)):
                specs.append(rand_spec(s, rng))
        # 2-4 chains per spec
        chains = []
        spec_of = {}
        for spec in specs:
            for _k in range(rng.randint(2, 4)):
                name = "{}:0".format(len(chains))
                chains.append((name, spec))
                spec_of[name] = spec
        t_max = max(chain_delay(sp) for (_n, sp) in chains)
        # activation schedule: tick T - D, random order within each tick
        by_tick = {}
        for (name, spec) in chains:
            by_tick.setdefault(t_max - chain_delay(spec), []).append(name)
        for t in by_tick:
            rng.shuffle(by_tick[t])
        input_order = {spec: [] for spec in specs}
        for t in sorted(by_tick):
            for name in by_tick[t]:
                input_order[spec_of[name]].append(name)
        # build the world
        world = World()
        log = []
        observers = {}
        for i, (name, spec) in enumerate(chains):
            observers[name] = build_chain(world, i, 0, spec, log)
        bursts = {t: [[observers[name]] for name in by_tick[t]]
                  for t in by_tick}
        pos_fn = lambda t, k: rng.randint(0, pos_max)
        run_group_sim(world, t_max + 2, bursts, pos_fn)
        # sanity: exactly one output per chain, all on tick T
        if len(log) != len(chains) or any(
                t != t_max for (t, _n, _s) in log):
            bad_sanity += 1
            if "sanity" not in first:
                first["sanity"] = "case {}: log={}".format(case, log)
            continue
        v = clustering_violation(log, spec_of)
        if v:
            viol_clust += 1
            if "clust" not in first:
                first["clust"] = "case {}: {}".format(case, v)
        pos = output_positions(log)
        for spec, names in input_order.items():
            if len(names) < 2:
                continue
            outs = sorted(names, key=lambda n: pos[n])
            if outs != names:
                viol_order += 1
                if "order" not in first:
                    first["order"] = (
                        "case {}: spec {} input={} output={} "
                        "(log={})").format(case, spec, names, outs, log)
                break
    return n_cases, viol_clust, viol_order, bad_sanity, first


def sweep_small_exhaustive():
    """2 specs sharing one delay sum, <=2 repeaters each, all priority
    assignments, both relative class orders, pos 0..2."""
    import itertools
    parts_options = [(2,), (4,), (2, 2), (6,), (2, 4), (4, 2), (8,)]
    specs_by_sum = {}
    for parts in parts_options:
        for pri_combo in itertools.product(PRIS, repeat=len(parts)):
            spec = (tuple(zip(parts[:-1], pri_combo[:-1])),
                    (parts[-1], pri_combo[-1]))
            specs_by_sum.setdefault(sum(parts), []).append(spec)
    viol_clust = viol_order = bad_sanity = 0
    first = {}
    cases = 0
    rng = random.Random(0)
    for total, spec_list in specs_by_sum.items():
        for s1 in spec_list:
            for s2 in spec_list:
                for n1 in (1, 2):
                    for n2 in (1, 2):
                        for posv in (0, 1, 2):
                            for perm_mid in (False, True):
                                cases += 1
                                specs = [s1] * n1 + [s2] * n2
                                chains = []
                                spec_of = {}
                                for name_i, spec in enumerate(specs):
                                    name = "{}:0".format(name_i)
                                    chains.append((name, spec))
                                    spec_of[name] = spec
                                # common output tick = full chain delay
                                t_max = chain_delay(s1)
                                assert chain_delay(s2) == t_max
                                # order: class blocks, optionally split by
                                # an opposite-class activation in the middle.
                                # Slice by chain index (first n1 are the s1
                                # class), NOT by spec equality — when s1==s2
                                # equality-matching would put every chain in
                                # both blocks and double-schedule them.
                                names = [n for n, _sp in chains]
                                order = names[:n1]
                                order2 = names[n1:]
                                if perm_mid and order and order2:
                                    seq = (order[:1] + order2 + order[1:])
                                else:
                                    seq = order + order2
                                world = World()
                                log = []
                                observers = {}
                                for i, (name, spec) in enumerate(chains):
                                    observers[name] = build_chain(
                                        world, i, 0, spec, log)
                                bursts = {t_max - chain_delay(s1):
                                          [[observers[n]] for n in seq]}
                                run_group_sim(world, t_max + 2, bursts,
                                              lambda t, k, pv=posv: pv)
                                if len(log) != len(chains) or any(
                                        t != t_max
                                        for (t, _n, _s) in log):
                                    bad_sanity += 1
                                    if "sanity" not in first:
                                        first["sanity"] = (
                                            "s1={} s2={} log={}".format(
                                                s1, s2, log))
                                    continue
                                v = clustering_violation(log, spec_of)
                                if v:
                                    viol_clust += 1
                                    if "clust" not in first:
                                        first["clust"] = (
                                            "s1={} s2={} {}".format(
                                                s1, s2, v))
                                pos = output_positions(log)
                                input_order = {}
                                for name in seq:
                                    input_order.setdefault(
                                        spec_of[name], []).append(name)
                                for spec, names in input_order.items():
                                    outs = sorted(names,
                                                  key=lambda n: pos[n])
                                    if outs != names:
                                        viol_order += 1
                                        if "order" not in first:
                                            first["order"] = (
                                                "s1={} s2={} in={} "
                                                "out={}".format(
                                                    s1, s2, names, outs))
                                        break
    return cases, viol_clust, viol_order, bad_sanity, first


if __name__ == "__main__":
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 20260813
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 30000
    pos_max = int(sys.argv[3]) if len(sys.argv) > 3 else 3

    c, vc, vo, bs, first = sweep(n, seed, pos_max)
    print("NOGROUP cases={} clustering_fail={} order_fail={} "
          "sanity_bad={} (pos 0..{})".format(c, vc, vo, bs, pos_max))
    for k, v in first.items():
        print("  first[{}]: {}".format(k, v))

    c, vc, vo, bs, first = sweep_small_exhaustive()
    print("EXHAUST cases={} clustering_fail={} order_fail={} "
          "sanity_bad={}".format(c, vc, vo, bs))
    for k, v in first.items():
        print("  first[{}]: {}".format(k, v))
