# LAB-B3: Non-terminal barriers (NO external libs)

nodes = ["u", "v"]
barrier = "v"

# Transitions allow escape
transitions = {
    ("u", "v"),
    ("v", "u"),
}

def reachable_from(start):
    visited = set()
    stack = [start]

    while stack:
        x = stack.pop()
        for (a, b) in transitions:
            if a == x and b not in visited:
                visited.add(b)
                stack.append(b)
    return visited

print("Transitions:", transitions)
print("Barrier:", barrier)
print("Reachable from barrier:", reachable_from(barrier))

