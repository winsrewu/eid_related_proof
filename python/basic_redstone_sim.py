class Node:
    def __init__(self, world):
        self.inputs = []
        self.outputs = []
        self.world = world
        self.sig_level = 0

    def add_input(self, node):
        self.inputs.append(node)

    def add_output(self, node):
        self.outputs.append(node)

    def get_output_signal(self):
        return self.sig_level

    def get_input_signal(self):
        sig = 0
        for i in self.inputs:
            sig = max(sig, i.get_output_signal())
        return sig

    def on_neighbor_update(self):
        pass

    def on_scheduled_tick(self):
        pass


class Event:
    target_tick: int
    priority: int
    node: Node

    def __init__(self, target_tick, priority, node):
        self.target_tick = target_tick
        self.priority = priority
        self.node = node


class World:
    def __init__(self):
        self.scheduled_ticks = []
        self.tick = 0

    def schedule_tick(self, event):
        self.scheduled_ticks.append(event)

    def _get_event(self):
        events = []
        min_priority = 100
        for e in self.scheduled_ticks:
            if e.target_tick == self.tick:
                events.append(e)
                min_priority = min(min_priority, e.priority)

        event = None
        for e in events:
            if e.priority == min_priority:
                event = e
                break

        if event is None:
            return None
        self.scheduled_ticks.remove(event)
        return event

    def step(self):
        event = self._get_event()
        if event is None:
            return False

        event.node.on_scheduled_tick()
        return True

    def step_until_next_tick(self):
        while self.step():
            pass

        self.tick += 1


class InputNode(Node):
    def set_signal(self, sig_level):
        self.sig_level = sig_level

        for out in self.outputs:
            out.on_neighbor_update()


class OutputNode(Node):
    def __init__(self, world, name):
        super().__init__(world)
        self.name = name

    def on_neighbor_update(self):
        print("{}: {}".format(self.name, self.get_input_signal()))


class Repeater(Node):
    def __init__(self, world, delay, priority):
        super().__init__(world)
        self.delay = delay * 2  # 1 rt = 2 gt
        self.priority = priority

    def on_neighbor_update(self):
        self.world.schedule_tick(
            Event(
                target_tick=self.world.tick + self.delay,
                priority=self.priority,
                node=self,
            )
        )

    def on_scheduled_tick(self):
        self.sig_level = 15 if self.get_input_signal() > 0 else 0
        for out in self.outputs:
            out.on_neighbor_update()


class Observer(Node):
    def on_neighbor_update(self):
        self.world.schedule_tick(
            Event(
                target_tick=self.world.tick + 2,
                priority=0,
                node=self,
            )
        )

    def on_scheduled_tick(self):
        self.sig_level = 15
        for out in self.outputs:
            out.on_neighbor_update()


def connect_chain(chain):
    for i in range(1, len(chain)):
        chain[i].add_input(chain[i - 1])
        chain[i - 1].add_output(chain[i])
    return chain
