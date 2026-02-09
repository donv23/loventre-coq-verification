# L2_BUS V12 — Core Experimental BUS Layer

Scopo:
- Interpretare le metriche L1 (kappa_l1, status)
- Restituire un bus_state semplice:
    SAFE-ish
    P_ACC-ish (se kappa_l1 > 0.8)
    BLACKHOLE-ish
    UNDEFINED-ish

Input:
- dict L1 con almeno:
    kappa_l1
    status

Output:
- dict con:
    bus_state
    meta_label_v12

Nota:
- Nessuna dipendenza dal LAB
- Nessuna chiamata a L0_CORE dal LAB
- Nessuna scrittura file, solo calcolo

