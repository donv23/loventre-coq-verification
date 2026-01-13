# 📐 LOVENTRE Coq v11 — CANVAS PRINCIPALI

**Versione:** v11  
**Manutentore:** Vincenzo Loventre  
**Regime:** CANONICO  
**Stato:** Attivo

---

## CANVAS 0 — Regole Auree (Sempre Valide)

* Rispondere e lavorare solo in italiano  
* Ogni modifica → `cd` alla root + `nano` + incolla **file completo**  
* Nessuna modifica parziale né “cambia riga”  
* Backup sempre: copia automatica in `99_LEGACY/<timestamp>` prima di toccare file canonici  
* Mai indovinare il contenuto dei file: `cat` o `nl -ba` prima  
* Test immediato dopo ogni modifica  
  * Coq → `coqc ...` o `make`  
  * Python (se presente) → regression suite  
* Niente `Admitted` non controllati  
* Mai cancellare file → spostare in `99_LEGACY` se dismesso  

---

## CANVAS 1 — CORE & SEMANTICA

**Contenuto**
* `LMetrics`
* Parametri fondamentali
* Semantica elementare P / Pacc / NPbh
* eventuale Bridge di base

**Obiettivo**
> Mini-universo coerente senza contraddizioni

**Esiti richiesti**
* Nessun assioma nascosto
* Nessuna tautologia “NPbh = non-P”
* Risk e SAFE coerenti

---

## CANVAS 2 — CLASSI & PREDICATI

**File**
* `Loventre_Class_P_v11.v`
* `Loventre_Class_Pacc_v11.v`
* `Loventre_Class_NPbh_v11.v`
* `Loventre_Class_Bridge_v11.v`

**Obiettivi**
* Chiarire inclusioni e non-inclusioni
* Stabilizzare costruttori
* P ⊂ Pacc e NPbh disgiunto provabili da witness

---

## CANVAS 3 — WITNESS & EVIDENZE

**File**
* `Loventre_Witness_v11.v`
* `Loventre_LMetrics_Suite_v11.v`

**Regole**
* Ogni witness prova qualcosa di nuovo
  * `m_P` → P≠∅
  * `m_Pacc_only` → Pacc≠P
  * `m_NPbh` → NPbh≠∅

**Audit**
> Se un witness non tiene → colpa del modello

---

## CANVAS 4 — MAIN & SEPARAZIONE

**File**
* `Loventre_Main_v11.v`
* `Loventre_Separation_v11.v`

**Obiettivo**
> Separazione tra P / Pacc / NPbh

**Condizioni**
* nessuna inversione logica
* bullets corretti per `split`
* nessuna prova “magica”

---

## CANVAS 5 — SAFE, RISK & META

**File**
* `Loventre_SAFE_v11.v`
* `Loventre_RISK_v11.v`
* `Loventre_META_v11.v`

**Significato**
* SAFE → limiti
* RISK → diagnosi
* META → movimento informazionale

---

## CANVAS 6 — LAB STRICT

**Directory**
* `06_LAB_STRICT_v11/`

**Permessi**
* sperimentazione libera

**Divieti**
* Main NON può importare LAB
* nessuna scrittura da LAB verso canonico

---

## CANVAS 7 — PIPELINE

**File**
* `Loventre_Pipeline_v11.v`
* `Loventre_Pipeline_STRICT_v11.v`
* `Loventre_STRICT_Invariants_v11.v`

**Obiettivo**
> Formalizzare metamorfosi e chiusure delle classi

---

## CANVAS 8 — FUTURO (v12+)

**Non eseguito**
* nuovi witness
* JSON-Coq bridge
* Axis C eventuale

**Regola**
> Non iniziare v12 senza build verde completa di v11

---

## CHIUSURA

v11 è:
* ecosistema coerente
* governato da Canvas
* vive solo se tutto è verde

