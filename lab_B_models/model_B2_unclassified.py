# LAB-B2: Unclassified configurations

configs = ["x"]

Stable = set()
Critical = set()
Isolating = set()

def classify(c):
    return (
        c in Stable,
        c in Critical,
        c in Isolating
    )

for c in configs:
    s, cr, i = classify(c)
    print(f"{c}: Stable={s}, Critical={cr}, Isolating={i}")

