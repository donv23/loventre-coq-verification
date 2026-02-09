# Loventre Project — Governance & Scope

## 1. Stato del progetto

Il progetto Loventre è diviso in tre aree **formalmente separate**:

### A. Coq CANON v3 (FORMALIZZAZIONE)
- Contiene la dimostrazione formale del Teorema di Loventre v3
- È verificabile interamente tramite Coq
- È l’unica parte che costituisce una **dimostrazione matematica**

### B. Python Engine (STRUMENTALE, INTERNO)
- Serve esclusivamente a:
  - generare witness
  - esplorare scenari
  - produrre JSON coerenti con la teoria
- **NON** è necessario alla verifica del teorema
- **NON** è parte della dimostrazione
- **NON** è destinato alla pubblicazione

### C. Axis C / LAB (RICERCA FUTURA)
- Spazio di esplorazione concettuale
- Protetto da firewall
- Non influenza il CANON
- Non contiene claim dimostrativi

---

## 2. Cosa è dimostrato

È dimostrata formalmente, in Coq:

- una separazione strutturale tra classi computazionali
- all’interno del **modello Loventre v3**
- sulla base di assiomi esplicitati

---

## 3. Cosa NON è dimostrato

- Non viene dimostrato P ≠ NP nel senso classico
- Non viene fatta alcuna affermazione sul mondo esterno al modello
- Nessun risultato dipende da simulazioni Python

---

## 4. Ruolo del Python Engine

Il Python Engine:
- è uno strumento sperimentale
- supporta la comprensione e l’esplorazione
- non ha valore probatorio
- è considerato **proprietà intellettuale riservata**

---

## 5. Verifica

La verifica ufficiale del risultato avviene esclusivamente tramite Coq,
usando lo script:

    ./coqc_all_v3.sh

Qualsiasi altra parte del repository è accessoria.

