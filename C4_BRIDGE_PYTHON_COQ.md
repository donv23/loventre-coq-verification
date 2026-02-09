# C4 — Ponte concettuale Python ↔ Coq (Loventre)

## Scopo

Questo documento esplicita il **ponte concettuale**
tra le barriere strutturali del Loventre Engine Python
e i lemmi/invarianti del CANON Coq.

Nessun codice Coq viene generato o modificato.

---

## Mappatura concettuale

### Guard canonico
- Python: `apply_guard_barrier`
- Coq: assiomi di validità dei witness (LMetrics_valid)

### Orizzonte BH
- Python: `apply_horizon_barrier`
- Coq: irreversibilità NP-like / black-hole
  (lemmi di non ritorno)

### Monotonicità del rischio
- Python: `apply_monotonicity_barrier`
- Coq: monotonicità della complessità sotto aumento di pressione

### SAFE compatibility
- Python: `apply_safe_compatibility_barrier`
- Coq: coerenza SAFE ↔ P-like

---

## Vincoli

- Il CANON Coq **non dipende** dal motore Python
- Il motore Python **non prova nulla**
- Il ponte è:
  - esplicativo
  - auditabile
  - opzionale

---

**Fine C4**

