# Referee Walkthrough  
**Loventre Coq Verification – v4 Freeze (2026-01-04)**

Questo documento guida il referee nella lettura, verifica e comprensione del repository  
`loventre-coq-verification`, nello stato **congelato** identificato dal branch:

- `release-2026-01-04-ultimissimo`  
- tag: **`v4-freeze-2026-01-04`**

L’obiettivo è rendere la verifica **lineare, riproducibile e semanticamente trasparente**, senza
richiedere assunzioni esterne né interpretazioni informali.

---

## 1. Scopo del repository

Questo repository contiene **esclusivamente**:

- formalizzazione Coq del **modello logico-astratto Loventre**;
- definizioni di metriche astratte (`LMetrics`);
- predicati di fase (*P-like*, *P-like-accessible*, *NP-like-black-hole*);
- lemmi e teoremi di esistenza;
- audit di correttezza (assenza di `Admitted` non tracciati).

❗ **Non contiene**:
- codice algoritmico,
- implementazioni numeriche,
- motori di calcolo o simulazione,
- rivendicazioni di risultati classici (es. P ≠ NP standard).

---

## 2. Struttura ad alto livello


Documentazione chiave:
- `README.md` — panoramica canonica
- `REFEREE_NOTE.md` — nota epistemica per la valutazione
- `SCOPE_AND_NON_CLAIMS.md` — limiti espliciti e non-claim
- `REFEREE_WALKTHROUGH.md` — questo file

---

## 3. Governance epistemica (A1 / A2 / A3)

Il modello segue una **separazione esplicita dei livelli**:

### A1 — Strutturale (dimostrato)
- definizione di `LMetrics`;
- predicati di fase (`is_P_like`, `is_NP_like_black_hole`);
- esistenza di profili *P-like* e *NP-like-black-hole*.

### A2 — Dinamico (ammissibile)
- proprietà di accessibilità come nozione distinta;
- nessuna riduzione computazionale classica.

### A3 — Assunzione residua (esplicita)
- esistenza di almeno un profilo *P-like-accessible*;
- dichiarata come **assioma localizzato**:
  ```coq
  Axiom exists_P_like_accessible :
    exists m : LMetrics, is_P_like_accessible m.

---

Se vuoi, nel **ciclo 8.2** posso proporti:
- un **CHECKLIST_FOR_REFEREES.md** ultra-sintetico (1 pagina),
- oppure un **MAP_OF_DEPENDENCIES.md** che visualizza i legami tra i file Coq.

