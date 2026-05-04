# LAB-B1: Reversible dynamics with barriers (NO external libs)

nodes = ["A", "B", "C"]
barrier = "C"

# Fully reversible transitions
transitions = {(x, y) for x in nodes for y in nodes}

# Find cycles of length 2 and 3
cycles = []

for a in nodes:
    for b in nodes:
        if (a, b) in transitions and (b, a) in transitions and a != b:
            cycles.append([a, b, a])

for a in nodes:
    for b in nodes:
        for c in nodes:
            if len({a, b, c}) == 3:
                if ((a, b) in transitions and
                    (b, c) in transitions and
                    (c, a) in transitions):
                    cycles.append([a, b, c, a])

cycles_crossing_barrier = [c for c in cycles if barrier in c]

print("Barrier:", barrier)
print("All cycles:", cycles)
print("Cycles crossing barrier:", cycles_crossing_barrier)

