# Namespace & Warning Policy — Progetto Loventre
📅 Dicembre 2025

Questo documento chiarisce la gestione dei warning Coq
relativi al namespace nel progetto Loventre.

---

## 1. Warning osservato

Il warning ricorrente:

> `Trying to mask the absolute name "X"`

si verifica quando:
- un file `X.v` definisce `Module X.`
- lo stesso file è importato con `Require Import X`

Questo comportamento è **noto** e **documentato** in Coq.

---

## 2. Politica adottata

Nel progetto Loventre:

### ✅ WARNING AMMESSI
Il warning è **esplicitamente ammesso** nei seguenti casi:
- file di **vocabolario**
- file che **definiscono concetti fondamentali**
- file in cui:
  - nome del file = nome del modulo
  - modulo = concetto teorico atomico

Esempi:
- `Loventre_Noise_Regimes.v`
- `Loventre_Complexity_Noise_Classes.v`
- `Loventre_Structural_Sensitivity.v`

In questi casi:
- il warning NON indica errore
- il pattern è intenzionale
- la leggibilità concettuale ha priorità

---

### ❌ WARNING NON AMMESSI
Il warning è **vietato** in:
- teoremi finali
- file di separazione strutturale
- bridge semantici di alto livello

In tali file:
- è vietato ridefinire moduli omonimi
- sono obbligatori alias espliciti (Regola A11)
- ogni dipendenza deve essere visibile e non ambigua

---

## 3. Regola operativa

Prima di eliminare un warning di namespace,
chiedersi:

> “Questo file è vocabolario o teorema?”

- Se è vocabolario → **NON correggere**
- Se è teorema → **correggere strutturalmente**

---

## 4. Stato

Questa policy è **attiva** a partire dal freeze
`FREEZE_STATE_NOISE_SENSITIVITY_v1`.

---

**FINE POLICY**

