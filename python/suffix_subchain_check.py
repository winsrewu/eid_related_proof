"""Empirical check: chains sharing their last n repeaters.

Claims under test (suffix = last n repeaters, identical across a family):
  OP: output order of family members == order of their suffix activation,
      where suffix activation = enqueue of the first suffix repeater's event.
  CL: at the common output tick T, no chain whose last n repeaters differ
      from the family suffix outputs strictly between two family outputs.

Probe B: with staggered output ticks, cross-tick interleaving must occur
(shows common-T is a necessary hypothesis for clustering).
Probe C: short chains equal to a trailing part of the suffix.
"""
import random
import sys
from basic_redstone_sim import InputNode, OutputNode, Repeater, Observer, World, connect_chain


class RecOutput(OutputNode):
    def __init__(self, world, name, log):
        super().__init__(world, name)
        self.log = log

    def on_neighbor_update(self):
        self.log.append((self.world.tick, self.name))


def build(world, log, name, rep_spec):
    """input -> observer -> reps -> output. rep_spec: list of (delay_gt, priority)."""
    inp = InputNode(world)
    obs = Observer(world)
    reps = [Repeater(world, d // 2, p) for (d, p) in rep_spec]
    out = RecOutput(world, name, log)
    connect_chain([inp, obs] + reps + [out])
    return inp, reps


def run_config(rng):
    n = rng.randint(1, 3)
    suffix = [(rng.choice([2, 4, 6, 8]), rng.choice([-3, -2, -1])) for _ in range(n)]
    T = 60
    world = World()
    log = []
    records = []  # (enqueue_tick, seq, event)
    orig = world.schedule_tick

    def tracking(event):
        records.append((world.tick, len(records), event))
        orig(event)

    world.schedule_tick = tracking

    chains = []  # (name, inp, rep_spec, reps, act_tick, in_family)

    def add(name, rep_spec, in_family):
        total = 2 + sum(d for (d, _) in rep_spec)
        if total > T:
            return
        inp, reps = build(world, log, name, rep_spec)
        chains.append((name, inp, rep_spec, reps, T - total, in_family))

    # family: random prefixes + common suffix
    fam_count = rng.randint(2, 5)
    for i in range(fam_count):
        prefix = [(rng.choice([2, 4, 6, 8]), rng.choice([-3, -2, -1]))
                  for _ in range(rng.randint(0, 3))]
        add("F%d" % i, prefix + suffix, True)

    # non-family chains, also outputting at T
    for j in range(rng.randint(2, 6)):
        spec = [(rng.choice([2, 4, 6, 8]), rng.choice([-3, -2, -1]))
                for _ in range(rng.randint(1, 5))]
        add("N%d" % j, spec, False)

    # probe C: short chains = trailing part of the suffix, output at T
    for m in range(1, n):
        add("S%d" % m, suffix[n - m:], False)

    # activate at tick start, in actOrd order; then drain
    chains.sort(key=lambda c: c[4])
    at_tick = {}
    for c in chains:
        at_tick.setdefault(c[4], [])
        at_tick[c[4]].append(c)
    for act_t, group in at_tick.items():
        rng.shuffle(group)
    by_tick = sorted(at_tick)
    idx = 0
    while world.tick <= T:
        for c in at_tick.get(world.tick, []):
            c[1].set_signal(15)
        world.step_until_next_tick()

    # --- checks ---
    viol = {"op": 0, "cl": 0, "sanity": 0}
    info = {}
    for (name, inp, spec, reps, act, fam) in chains:
        out_entry = [e for e in log if e[1] == name]
        if len(out_entry) != 1:
            viol["sanity"] += 1
            continue
        info[name] = {"tick": out_entry[0][0], "spec": spec, "fam": fam}

    family = [c for c in chains if c[5]]
    # suffix activation of each family member: enqueue of its first suffix rep
    act_order = []
    for (name, inp, spec, reps, act, fam) in family:
        first_suf = reps[len(reps) - n]
        evs = [r for r in records if r[2].node is first_suf]
        if len(evs) != 1:
            viol["sanity"] += 1
            continue
        act_order.append((evs[0][0], evs[0][1], name))
    act_order.sort()

    # OP: family output order == suffix activation order
    fam_out = sorted([e for e in log if e[1] in {c[0] for c in family}],
                     key=lambda e: log.index(e))
    out_order = [e[1] for e in fam_out]
    if any(e[0] != T for e in fam_out):
        viol["sanity"] += 1
    if out_order != [a[2] for a in act_order]:
        viol["op"] += 1

    # CL: between two family outputs at tick T, only same-suffix chains
    tickT = [e for e in log if e[0] == T]
    names = {c[0]: c for c in chains}
    for a in range(len(tickT)):
        for b in range(a + 1, len(tickT)):
            ia, ib = tickT[a][1], tickT[b][1]
            if info.get(ia, {}).get("fam") and info.get(ib, {}).get("fam"):
                for mid in tickT[a + 1:b]:
                    spec = info[mid[1]]["spec"]
                    if len(spec) < n or spec[-n:] != suffix:
                        viol["cl"] += 1
    return viol


def probe_b():
    """Staggered output ticks: cross-tick interleaving of a different chain."""
    world = World()
    log = []
    suffix = [(2, -1), (4, -1)]
    f0 = build(world, log, "F0", [(2, 0)] + suffix)   # total 2+2+2+4=10
    f1 = build(world, log, "F1", [(2, 0)] + suffix)
    nj = build(world, log, "NJ", [(2, 0), (2, 0)])    # total 2+2+2=6
    T = 20
    # family outputs at 10 and 20; NJ outputs at 15 (between the ticks)
    at = {0: [f0], 9: [nj], 10: [f1]}
    while world.tick <= T:
        for inp in at.get(world.tick, []):
            inp[0].set_signal(15)
        world.step_until_next_tick()
    seq = [(t, nm) for (t, nm) in log]
    pos = {nm: i for i, (t, nm) in enumerate(seq)}
    interleaved = pos["F0"] < pos["NJ"] < pos["F1"]
    return seq, interleaved


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    iters = int(sys.argv[2]) if len(sys.argv) > 2 else 2000
    rng = random.Random(seed)
    tot = {"op": 0, "cl": 0, "sanity": 0}
    for _ in range(iters):
        v = run_config(rng)
        for k in tot:
            tot[k] += v[k]
    print("sweep %d configs: OP violations=%d, CL violations=%d, sanity=%d"
          % (iters, tot["op"], tot["cl"], tot["sanity"]))
    seq, interleaved = probe_b()
    print("probe B (staggered ticks): log=%s interleaved=%s" % (seq, interleaved))


if __name__ == "__main__":
    main()
