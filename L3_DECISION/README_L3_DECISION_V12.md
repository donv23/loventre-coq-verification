# L3_DECISION — V12
Livello 3 della pipeline Loventre Engine V12.
Trasforma gli output `-ish` del BUS L2 in una decisione operativa più leggibile.

Input:
- bus_label: uno tra SAFE-ish / P_ACC-ish / BLACKHOLE-ish / UNDEFINED-ish
- kappa_l1: valore normalizzato 0.0–1.0 (o None)

Output:
- decision_l3: SAFE / SAFE_ACCESSIBLE / CAUTIOUS / BLACKHOLE / UNKNOWN
- confidence_l3: float grezzo (clampato 0–1)
- note: stringa diagnostica

Questo layer NON modifica il bus e NON esporta JSON.
Ogni modifica deve rispettare la direzione:
    L0 → L1 → L2 → L3 → LAB

