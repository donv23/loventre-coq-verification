# LOVENTRE — TRITTICO P/NP v3 (2-SAT, SAT, TSP) — SINTESI (Dicembre 2025)

## 0. Scopo

Questa nota raccoglie in un unico quadro i tre case study:

- 2-SAT (problema in P),
- SAT (NP-completo),
- TSP (NP-completo),

nel contesto del modello Loventre v3, usando:

- le classi interne:
  - `In_P_Lov`, `In_Pacc_Lov`, `In_NP_bh_Lov`,
- le etichette di rischio:
  - SAFE, CRIT, quasi-bh, BH,
- i witness canonici:
  - `m_2SAT_easy_demo`, `m_2SAT_crit_demo`,
  - `m_SATcrit16_cli_demo`,
  - `m_TSPcrit28_cli_demo`,
- e le ipotesi concettuali H1–H3 sul mapping da problemi classici a LMetrics:

  - seed: `LOVENTRE_PNP_HYPOTHESES_H1H2H3_SEED_2025-12.md`.

Obiettivo: avere una **mappa leggibile** P/NP–Loventre v3 da poter citare
in una futura sezione “interpretativa” di un paper sul Teorema v3.

---

## 1. Riepilogo rapido dei tre problemi

### 1.1. 2-SAT

- Problema di soddisfacibilità booleana con clausole di lunghezza ≤ 2.
- **In P**: esistono algoritmi polinomiali noti (grafi di implicazione, SCC).
- Intuizione:
  - problema “trattabile”,
  - ma con istanze easy e istanze più “vicine al bordo”.

### 1.2. SAT

- Problema di soddisfacibilità booleana generale (es. CNF).
- **NP-completo**:
  - prototipo storico di problema NP-completo,
  - cuore del problema P vs NP.

### 1.3. TSP (decisionale)

- TSP decisionale: esiste un tour di costo ≤ B?
- **NP-completo**, altro prototipo classico.
- Intuizione:
  - paesaggio di soluzioni estremamente complesso,
  - molti minimi locali, esplosione combinatoria.

---

## 2. Riepilogo interno Loventre v3 (profili e classi)

### 2.1. 2-SAT: easy vs critico

Profili canonici:

- `m_2SAT_easy_demo`:
  - `phase_guess = P_like`,
  - `risk_class = SAFE`,
  - `time_regime = poly`,
  - `horizon_flag = false`,
  - `risk_index` e `chi_compactness` bassi.

- `m_2SAT_crit_demo`:
  - `phase_guess = P_like_accessible`,
  - `risk_class = CRIT`,
  - `time_regime = poly_critical`,
  - `horizon_flag = false`,
  - `risk_index` e `chi_compactness` alti, ma **non** NP_bh.

Interpretazione:

- entrambi sono nel mondo P_like / Pacc,
- nessuno entra in `In_NP_bh_Lov`.

### 2.2. SAT: profilo NP_like_black_hole

Witness canonico:

- `m_SATcrit16_cli_demo : LMetrics`.

Assioma chiave (via Geometry v3):

- `m_SATcrit16_soddisfa_is_NP_like_black_hole`.

Interpretazione:

- `m_SATcrit16_cli_demo` appartiene a `In_NP_bh_Lov`,
- rappresenta una **istanza critica di SAT** vista come black-hole
  informazionale.

### 2.3. TSP: profilo NP_like_black_hole

Witness canonico:

- `m_TSPcrit28_cli_demo : LMetrics`.

Assioma chiave:

- `m_TSPcrit28_soddisfa_is_NP_like_black_hole`.

Interpretazione:

- `m_TSPcrit28_cli_demo` appartiene a `In_NP_bh_Lov`,
- rappresenta una **istanza critica di TSP** in piena regione NP_bh.

---

## 3. Tabella di sintesi P/NP–Loventre v3

### 3.1. Trittico in una tabella

| Problema       | Stato classico   | Profili Loventre v3             | Classe interna principale    | Rischio / regime        |
|----------------|------------------|---------------------------------|------------------------------|-------------------------|
| 2-SAT (easy)   | P                | `m_2SAT_easy_demo`              | `In_P_Lov`                   | SAFE, poly              |
| 2-SAT (crit)   | P                | `m_2SAT_crit_demo`              | `In_Pacc_Lov`                | CRIT, poly_critical     |
| SAT (critico)  | NP-completo      | `m_SATcrit16_cli_demo`          | `In_NP_bh_Lov`               | CRIT/BH-like            |
| TSP (critico)  | NP-completo      | `m_TSPcrit28_cli_demo`          | `In_NP_bh_Lov`               | CRIT/BH-like            |

Lettura:

- 2-SAT:
  - abita P_like / Pacc,
  - può diventare critico, ma **non** entra in NP_bh.

- SAT e TSP (regimi critici):
  - vengono modellati come NP_like_black_hole,
  - rappresentano il “cuore duro” NP-completo nel paesaggio Loventre.

### 3.2. Contrasto concettuale essenziale

- **2-SAT** (P):
  - profili regolari o critici *ma accessibili*,
  - mai black-hole.

- **SAT/TSP** (NP-completi):
  - profili critici che il modello colloca esplicitamente in NP_bh,
  - regioni dove la curvatura/compattazione è interpretata come
    “singolarità informazionale”.

Questa differenza è il cuore del trittico.

---

## 4. Collegamento con le ipotesi H1–H3

Riprendiamo le ipotesi dal seed HYPOTHESES:

- **H1**: monotonia di difficoltà → problemi più difficili dovrebbero
  avere profili con `risk_index`, `chi_compactness`, ecc. più alti;
- **H2**: stabilità di P → problemi in P non devono generare
  sistematicamente NP_bh;
- **H3**: non-degenerazione di NP_bh → NP_bh non deve contenere
  problemi manifestamente “facili”.

### 4.1. 2-SAT e H2

- 2-SAT è in P:
  - i profili `m_2SAT_easy_demo` e `m_2SAT_crit_demo`:

    - restano in P_like/Pacc,
    - anche quando CRIT, non diventa NP_bh.

- Compatibile con H2:
  - P rimane nel cuscinetto P_like/Pacc anche in regimi critici,
  - nessuna invasione forzata di NP_bh.

### 4.2. SAT/TSP e H1–H3

- SAT e TSP sono NP-completi:
  - i profili `m_SATcrit16_cli_demo` e `m_TSPcrit28_cli_demo`:

    - abitano NP_bh,
    - sono esempi canonici di regioni ad alta curvatura/compattazione.

- Compatibili con:

  - **H1**:
    - problemi “hard” (SAT/TSP critici) → profili in NP_bh;
  - **H3**:
    - NP_bh non contiene 2-SAT,
    - è riservata a problemi con struttura di difficoltà NP-hard.

---

## 5. Come si collega al Teorema Loventre v3

Il Teorema di Loventre v3, nella sua forma citabile:

- è dimostrato in Coq e dice, in sintesi:

  > Sotto T_Loventre_v3_Prop, esiste un profilo NP_like_black_hole
  > non P_like_accessible, e `In_NP_bh_Lov` non è contenuta in
  > `In_Pacc_Lov`.

Il trittico 2-SAT / SAT / TSP offre una **narrazione concreta**:

- 2-SAT:
  - rappresenta ciò che ci si aspetta da un problema in P:
    - P_like / Pacc, SAFE/CRIT, mai NP_bh;

- SATcrit16 e TSPcrit28:
  - incarnano i witness NP_bh,
  - sono esempi naturali di profili “oltre la barriera Pacc”
    nel senso del modello.

Quindi:

> Il Teorema Loventre v3 è un risultato rigoroso **nel modello**;  
> il trittico mostra che esiste una lettura coerente con l’intuizione
> classica P (2-SAT) vs NP-completi (SAT/TSP),  
> a patto di accettare H1–H3 come desiderata per un mapping Φ.

---

## 6. Cosa NON dice questa sintesi (anticorpi finali)

Questa nota **non** afferma che:

1. `In_P_Lov` è uguale a P, o `In_NP_bh_Lov` è uguale a NP o NP-complete.
2. La separazione Loventre v3 dimostra P≠NP classico.
3. SAT/TSP siano “dimostrati difficili” dal modello Loventre:
   la loro difficoltà è un fatto esterno, che il modello
   **assume come intuizione**.

Quello che fa, invece, è:

- fissare una **mappa concettuale** chiara:

  - 2-SAT → P_like/Pacc, SAFE/CRIT;
  - SAT/TSP → NP_bh;

- rendere esplicito che qualunque claim interpretativo verso P/NP
  deve passare:
  - dalle ipotesi H1–H3,
  - e dal riconoscere che il Teorema Loventre v3 resta,
    per ora, un risultato **interno al modello**.

_Fine — LOVENTRE_PNP_TRITTICO_v3_SYNTHESIS_2025-12_


