from loventre_invariance_c import compute_C, C_invariant

# Due storie diverse, stesso regime
metrics_1 = {
    "potential": 0.48,
    "U_threshold": 0.5,
}

metrics_2 = {
    "potential": 0.47,
    "U_threshold": 0.5,
}

# Cambio di regime
metrics_3 = {
    "potential": 0.62,
    "U_threshold": 0.5,
}

print("C(metrics_1):", compute_C(metrics_1))
print("C(metrics_2):", compute_C(metrics_2))
print("C(metrics_3):", compute_C(metrics_3))

print("Invariant (1,2):", C_invariant(metrics_1, metrics_2))
print("Invariant (1,3):", C_invariant(metrics_1, metrics_3))

