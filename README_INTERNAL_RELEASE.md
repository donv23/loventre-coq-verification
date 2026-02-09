# Internal Release Package — Progetto Loventre

**Status:** STABLE INTERNAL RELEASE  
**Data:** Dicembre 2025  
**Ambito:** CANON + Axis A (Engine)  
**Pubblicità:** NON pubblico

---

## 1. Scopo del pacchetto

Questo documento definisce il **pacchetto di rilascio interno**
del progetto Loventre nello stato attuale.

Il pacchetto serve a:
- fissare uno snapshot stabile
- consentire backup e replica controllata
- garantire auditabilità futura
- impedire derive semantiche

Non è destinato a:
- pubblicazione
- revisione esterna
- claim teorici

---

## 2. Componenti incluse

### 2.1 CANON (FROZEN)

File e concetti Coq considerati **stabili e intoccabili**:

- `Loventre_Metrics_Bus_Core.v`
- `Loventre_Witness_SAFE_Global.v`
- `SAFE_Barrier_Theory_v5.v`
- Test e witness associati
- `README_CANON_FROZEN.md`

---

### 2.2 Axis A — Engine (FROZEN)

Componenti Python congelate:

- `loventre_pipeline.py`
- `loventre_suggestion_bridge.py`
- `loventre_policy_export.py`
- Pipeline di metrics / lmetrics
- Bridge JSON / Coq

Documenti associati:
- `README_AXIS_A_ENGINE_SCOPE.md`
- `README_AXIS_A_CANON_TERMINOLOGY.md`
- `README_AXIS_A_ENGINE_FROZEN.md`

---

## 3. Stato di integrità

Al momento del rilascio interno:

- CANON è semanticamente chiuso
- Axis A è terminologicamente allineato
- LAB è separato e non fondativo
- Nessun file FROZEN dipende da LAB
- Nessun claim classico è presente

---

## 4. Uso consentito

Questo pacchetto può essere usato per:

- esecuzione locale dell’Engine
- verifica di coerenza interna
- generazione di witness
- backup personale
- confronto storico futuro

---

## 5. Uso vietato (vincolante)

È vietato usare questo pacchetto per:

- affermare P ≠ NP classico
- presentare risultati come dimostrativi
- fondare separazioni esterne
- trasferire risultati LAB al CANON
- promozione accademica automatica

---

## 6. Aggiornamenti futuri

Ogni aggiornamento richiede:

- nuovo documento di release
- nuova data
- nuova fase numerata
- audit completo

In assenza di questi requisiti:
👉 **questo rilascio resta valido e attivo**.

---

## 7. Regola finale

> Questo rilascio non dimostra nulla.  
> Dimostra solo **disciplina strutturale**.

---

