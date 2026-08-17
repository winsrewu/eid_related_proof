#!/usr/bin/env python3
"""Phase-0 empirical sweep: clustering / order preservation / round-robin
under per-repeater priorities in {-3,-2,-1} and delays in {2,4,6,8}.

Builds on basic_redstone_sim (the oracle for the Lean model). A chain is
Observer -> [Repeater(d,p)]* -> Repeater(d_last,p_last) -> Output. Group
activation = atomic enqueue of observer events (target = tick+2, pri 0),
with pos-style processing of pending events between activations, exactly
as gSimBody does in the Lean model.
"""

import random
import sys
from basic_redstone_sim import (
    Event,
    Observer,
    OutputNode,
    Repeater,
    World,
    connect_chain,
)

DELTAS = (2, 4, 6, 8)
PRIS = (-3, -2, -1)


class RecOutput(OutputNode):
    def __init__(self, world, name, log):
        super().__init__(world, name)
        self.log = log

    def on_neighbor_update(self):
        self.log.append((self.world.tick, self.name, self.get_input_signal()))


def build_chain(world, gi, ci, spec, log):
    """spec = (middles, last); middles = [(d_gt, pri)...], last = (d_gt, pri).
    Returns the observer node."""
    obs = Observer(world)
    reps = [Repeater(world, d // 2, p) for (d, p) in spec[0]]
    d_last, p_last = spec[1]
    last = Repeater(world, d_last // 2, p_last)
    out = RecOutput(world, "{}:{}".format(gi, ci), log)
    connect_chain([obs] + reps + [last, out])
    return obs


def chain_delay(spec):
    return 2 + sum(d for (d, _) in spec[0]) + spec[1][0]


def process_n(world, n):
    for _ in range(n):
        if not world.step():
            break


def run_group_sim(world, t_end, bursts, pos_fn):
    """bursts: dict tick -> ordered list of activations; each activation is
    an ordered list of observer nodes fired atomically. pos_fn(t, k) = how
    many pending events to process before the k-th activation of tick t."""
    while world.tick <= t_end:
        t = world.tick
        for k, observers in enumerate(bursts.get(t, [])):
            process_n(world, pos_fn(t, k))
            for obs in observers:
                world.schedule_tick(Event(t + 2, 0, obs))
        world.step_until_next_tick()


def output_positions(log):
    """name -> first log index."""
    pos = {}
    for i, (_t, name, _sig) in enumerate(log):
        if name not in pos:
            pos[name] = i
    return pos


# ---------------------------------------------------------------- checks

def clustering_violation(log, spec_of):
    """same-spec outputs must form contiguous blocks."""
    by_spec = {}
    for i, (_t, name, _sig) in enumerate(log):
        by_spec.setdefault(spec_of[name], []).append(i)
    for s, idxs in by_spec.items():
        if idxs != list(range(idxs[0], idxs[0] + len(idxs))):
            return "spec {} not contiguous at {} (log={})".format(s, idxs, log)
    return None


def order_violation(log, spec_of, groups):
    """groups: list of lists of chain names. For each group pair and each
    spec cleanly separating the pair, all separating specs must agree on
    direction."""
    pos = output_positions(log)
    n = len(groups)
    for a in range(n):
        for b in range(n):
            if a == b:
                continue
            dirs = {}
            for s in set(spec_of[c] for c in groups[a]) & set(
                    spec_of[c] for c in groups[b]):
                a_idxs = [pos[c] for c in groups[a] if spec_of[c] == s]
                b_idxs = [pos[c] for c in groups[b] if spec_of[c] == s]
                if max(a_idxs) < min(b_idxs):
                    dirs[s] = "A<B"
                elif max(b_idxs) < min(a_idxs):
                    dirs[s] = "B<A"
            if len(set(dirs.values())) > 1:
                return ("groups {},{} ordered inconsistently: {} "
                        "(log={})").format(a, b, dirs, log)
    return None


# ---------------------------------------------------------------- random

def rand_composition(total, rng):
    """Random ordered composition of `total` into parts from DELTAS."""
    while True:
        parts = []
        rest = total
        while rest > 0:
            choices = [d for d in DELTAS if d <= rest]
            if not choices:
                break
            d = rng.choice(choices)
            parts.append(d)
            rest -= d
        if rest == 0 and parts:
            return parts


def rand_spec_with_sum(total, rng):
    parts = rand_composition(total, rng)
    pris = [rng.choice(PRIS) for _ in parts]
    middles = list(zip(parts[:-1], pris[:-1]))
    last = (parts[-1], pris[-1])
    return (tuple(middles), last)


def sweep_groups(n_cases, seed):
    rng = random.Random(seed)
    viol_clust = viol_order = bad_sanity = 0
    first = {}
    for case in range(n_cases):
        # pool of specs per delay-sum class
        sums = [rng.choice(range(4, 17, 2)) for _ in range(rng.randint(1, 3))]
        pool = {}
        for s in sums:
            pool[s] = [rand_spec_with_sum(s, rng)
                       for _ in range(rng.randint(2, 3))]
        # groups: pick a sum class, sample chains from its specs
        n_groups = rng.randint(2, 4)
        groups_specs = []
        for _g in range(n_groups):
            s = rng.choice(sums)
            chains = [rng.choice(pool[s])
                      for _ in range(rng.randint(2, 4))]
            groups_specs.append(chains)
        delays = [chain_delay(gs[0]) for gs in groups_specs]
        t_max = max(delays)
        world = World()
        log = []
        observers = []
        spec_of = {}
        groups_names = []
        for gi, gs in enumerate(groups_specs):
            obs_list = []
            names = []
            for ci, spec in enumerate(gs):
                obs_list.append(build_chain(world, gi, ci, spec, log))
                spec_of["{}:{}".format(gi, ci)] = spec
                names.append("{}:{}".format(gi, ci))
            observers.append(obs_list)
            groups_names.append(names)
        # activation order and within-order
        group_ord = list(range(n_groups))
        rng.shuffle(group_ord)
        bursts = {}
        for gi in group_ord:
            t_act = t_max - delays[gi]
            obs_ord = observers[gi][:]
            rng.shuffle(obs_ord)
            bursts.setdefault(t_act, []).append(obs_ord)
        pos_fn = lambda t, k: rng.randint(0, 3)
        run_group_sim(world, t_max + 2, bursts, pos_fn)
        # sanity: one entry per chain, all at t_max
        if len(log) != sum(len(g) for g in groups_names) or any(
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
        v = order_violation(log, spec_of, groups_names)
        if v:
            viol_order += 1
            if "order" not in first:
                first["order"] = "case {}: {}".format(case, v)
    return n_cases, viol_clust, viol_order, bad_sanity, first


# ---------------------------------------------------------------- RR

def rr_violation_check(log, spec_of, group_ord, groups_names):
    pos = output_positions(log)
    ord_idx = {gi: k for k, gi in enumerate(group_ord)}
    for g1 in groups_names:
        for g2 in groups_names:
            for c1n in g1:
                for c2n in g2:
                    if c1n == c2n or spec_of[c1n] != spec_of[c2n]:
                        continue
                    g1i, c1 = c1n.split(":")
                    g2i, c2 = c2n.split(":")
                    c1, c2 = int(c1), int(c2)
                    lhs = pos[c1n] < pos[c2n]
                    rhs = (c1 < c2) or (
                        c1 == c2 and ord_idx[int(g1i)] < ord_idx[int(g2i)])
                    if lhs != rhs:
                        return ("iff fails for {} vs {}: pos {} vs {}, "
                                "lhs={} rhs={} (log={})").format(
                                    c1n, c2n, pos[c1n], pos[c2n], lhs, rhs,
                                    log)
    return None


def sweep_rr(n_cases, seed):
    rng = random.Random(seed)
    viol = bad_sanity = 0
    first = None
    for case in range(n_cases):
        # all specs share one delay sum: single RR batch at one tick
        total = rng.choice(range(4, 17, 2))
        pool = [rand_spec_with_sum(total, rng)
                for _ in range(rng.randint(1, 3))]
        n_groups = rng.randint(2, 4)
        groups_specs = [[rng.choice(pool)
                         for _ in range(rng.randint(2, 4))]
                        for _g in range(n_groups)]
        group_ord = list(range(n_groups))
        rng.shuffle(group_ord)
        world = World()
        log = []
        observers = []
        spec_of = {}
        groups_names = []
        for gi, gs in enumerate(groups_specs):
            obs_list = []
            names = []
            for ci, spec in enumerate(gs):
                obs_list.append(build_chain(world, gi, ci, spec, log))
                spec_of["{}:{}".format(gi, ci)] = spec
                names.append("{}:{}".format(gi, ci))
            observers.append(obs_list)
            groups_names.append(names)
        t_max = chain_delay(groups_specs[0][0])
        # round-robin batch at tick 0: rounds concatenated, no processing
        max_len = max(len(gs) for gs in groups_specs)
        acts = []
        for k in range(max_len):
            for gi in group_ord:
                if k < len(groups_specs[gi]):
                    acts.append([observers[gi][k]])
        pos_fn = lambda t, kk: 0
        run_group_sim(world, t_max + 2, {0: acts}, pos_fn)
        if len(log) != sum(len(g) for g in groups_names) or any(
                t != t_max for (t, _n, _s) in log):
            bad_sanity += 1
            if first is None:
                first = "case {}: sanity log={}".format(case, log)
            continue
        v = rr_violation_check(log, spec_of, group_ord, groups_names)
        if v:
            viol += 1
            if first is None:
                first = "case {}: {}".format(case, v)
    return n_cases, viol, bad_sanity, first


# ---------------------------------------------------------------- exhaustive

def sweep_exhaustive():
    """2 groups x <=2 chains, delays in {2,4}, all priority assignments,
    all group orders / within orders / pos values. Uniform delay sum."""
    parts_options = [(4,), (2, 2), (2, 2, 2), (8,), (4, 2), (2, 4), (6,),
                     (4, 4), (2, 6), (6, 2), (2, 2, 4), (2, 4, 2),
                     (4, 2, 2)]
    specs = set()
    for parts in parts_options:
        if sum(parts) > 8:
            continue
        for pri_combo in __import__("itertools").product(
                PRIS, repeat=len(parts)):
            middles = tuple(zip(parts[:-1], pri_combo[:-1]))
            specs.add((middles, (parts[-1], pri_combo[-1])))
    # group specs by equal delay sum
    by_sum = {}
    for s in specs:
        by_sum.setdefault(chain_delay(s), []).append(s)
    viol_clust = viol_order = bad_sanity = 0
    first = {}
    cases = 0
    for total, spec_list in by_sum.items():
        for s1 in spec_list:
            for s2 in spec_list:
                for group_ord in ([0, 1], [1, 0]):
                    for wo0 in ([0, 1], [1, 0]):
                        for wo1 in ([0, 1], [1, 0]):
                            for posv in (0, 1, 2, 3):
                                cases += 1
                                world = World()
                                log = []
                                groups_specs = [[s1, s1], [s2, s2]]
                                observers = []
                                spec_of = {}
                                groups_names = []
                                for gi, gs in enumerate(groups_specs):
                                    obs_list = []
                                    names = []
                                    for ci, spec in enumerate(gs):
                                        obs_list.append(build_chain(
                                            world, gi, ci, spec, log))
                                        spec_of["{}:{}".format(gi, ci)] = spec
                                        names.append("{}:{}".format(gi, ci))
                                    observers.append(obs_list)
                                    groups_names.append(names)
                                t_max = chain_delay(s1)
                                wo = [wo0, wo1]
                                bursts = {}
                                for gi in group_ord:
                                    t_act = t_max - chain_delay(
                                        groups_specs[gi][0])
                                    bursts.setdefault(t_act, []).append(
                                        [observers[gi][c] for c in wo[gi]])
                                pos_fn = lambda t, k, pv=posv: pv
                                run_group_sim(world, t_max + 2, bursts,
                                              pos_fn)
                                if len(log) != 4 or any(
                                        t != t_max for (t, _n, _s) in log):
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
                                v = order_violation(log, spec_of,
                                                    groups_names)
                                if v:
                                    viol_order += 1
                                    if "order" not in first:
                                        first["order"] = (
                                            "s1={} s2={} {}".format(
                                                s1, s2, v))
    return cases, viol_clust, viol_order, bad_sanity, first


if __name__ == "__main__":
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 20260812
    n_grp = int(sys.argv[2]) if len(sys.argv) > 2 else 20000
    n_rr = int(sys.argv[3]) if len(sys.argv) > 3 else 10000

    n, vc, vo, bs, first = sweep_groups(n_grp, seed)
    print("GROUPS  cases={} clustering_fail={} order_fail={} sanity_bad={}"
          .format(n, vc, vo, bs))
    for k, v in first.items():
        print("  first[{}]: {}".format(k, v))

    n, vr, bs, first = sweep_rr(n_rr, seed + 1)
    print("RR      cases={} iff_fail={} sanity_bad={}".format(n, vr, bs))
    if first:
        print("  first: {}".format(first))

    n, vc, vo, bs, first = sweep_exhaustive()
    print("EXHAUST cases={} clustering_fail={} order_fail={} sanity_bad={}"
          .format(n, vc, vo, bs))
    for k, v in first.items():
        print("  first[{}]: {}".format(k, v))
