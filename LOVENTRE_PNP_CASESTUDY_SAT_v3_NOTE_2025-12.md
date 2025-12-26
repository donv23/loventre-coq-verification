# LOVENTRE — CASE STUDY SAT v3 (Dicembre 2025)

## 0. Scopo

Questo case study fa da “specchio” al caso 2-SAT e ha tre obiettivi:

1. Prendere un problema classico **NP-completo** (SAT) e posizionarlo
   nel paesaggio Loventre v3.

2. Mettere in relazione il witness canonico:

   - `m_SATcrit16_cli_demo`

   con la classe interna `In_NP_bh_Lov` (NP_like_black_hole).

3. Mostrare come un mapping concettuale Φ_SAT possa essere compatibile
   con le ipotesi H1–H3 (seed `LOVENTRE_PNP_HYPOTHESES_H1H2H3_SEED_2025-12.md`),
   in modo complementare al caso 2-SAT.

Come per 2-SAT, questa nota non introduce nuovi teoremi; è un
**esercizio di interpretazione** sull’Asse A (P/NP) del programma
Loventre v3.

---

## 1. SAT nel mondo classico (foto rapida)

### 1.1. Definizione classica

- SAT: problema di soddisfacibilità booleana.
- Input: una formula booleana (ad esempio in CNF) su variabili booleane.
- Domanda: esiste un assegnamento di verità che rende la formula vera?

Risultato fondamentale (classico):

- SAT è **NP-completo**:
  - appartiene a NP,
  - ogni problema in NP è riducibile polinomialmente a SAT.

Quindi, a livello classico:

- SAT è il prototipo di problema “NP-difficile”,
- non si conosce un algoritmo polinomiale deterministico,
- è al cuore del problema P vs NP.

### 1.2. Intuizione “regimi easy/critici” per SAT

Anche per SAT è naturale pensare a:

- istanze “facili” (strutturalmente semplici, con molte soluzioni, o
  con pattern trivialmente soddisfacibili);
- istanze “critiche” (vicino a soglie di soddisfacibilità, dense,
  con strutture che “incastrano” rapidamente la ricerca).

La differenza rispetto a 2-SAT è che:

- per 2-SAT sappiamo che TUTTO il problema è in P;
- per SAT, i regimi critici non sono solo “annoying” ma
  **rappresentano effettivamente il cuore NP-difficile**.

---

## 2. SAT nel modello Loventre v3

### 2.1. Il witness canonico SATcrit16

Nel nucleo Geometry v3 c’è un witness importante:

- `m_SATcrit16_cli_demo : LMetrics`

per il quale esiste un assioma (via `Loventre_LMetrics_Existence_Summary.v`):

- `m_SATcrit16_soddisfa_is_NP_like_black_hole`.

In altre parole:

- nel modello Loventre v3,
- `m_SATcrit16_cli_demo` è dichiarato **NP_like_black_hole**.

Concettualmente:

> `m_SATcrit16_cli_demo` è il profilo canonico che rappresenta una
> **istanza critica di SAT** nel paesaggio LMetrics, e viene posto
> esplicitamente nella classe NP_like_black_hole.

### 2.2. Posizione nella classificazione Loventre

In termini delle classi interne:

- `m_SATcrit16_cli_demo` ∈ `In_NP_bh_Lov`,
- NON è in `In_Pacc_Lov` (per definizione di NP_like_black_hole),
- è pensato come profilo con:
  - `chi_compactness` molto alta,
  - `risk_index` molto alto,
  - parametri informazionali in una zona “quasi-singolare”.

Nella tabella qualitativa:

| Profilo                  | Classe Loventre       | Rischio      | Intuizione complessità           |
|--------------------------|-----------------------|--------------|----------------------------------|
| `m_SATcrit16_cli_demo`   | `In_NP_bh_Lov`        | CRIT/BH-like | cuore NP-complete / “black-hole”|

---

## 3. Un mapping concettuale Φ_SAT

### 3.1. Idea generale

Immaginiamo un mapping concettuale:

> Φ_SAT : (istanze di SAT) → LMetrics

che assegna a ciascuna formula SAT un profilo LMetrics, in base a:

- numero di variabili, clausole,
- struttura (ad es. random vs strutturata),
- densità, simmetrie, pattern di vincoli, ecc.

L’idea è che esistano:

- istanze di SAT relativamente “easy” (Φ_SAT(φ_easy) con profilo
  più vicini a P_like/Pacc);  
- istanze di SAT “critiche” (Φ_SAT(φ_crit) con profili catastati
  in regioni NP_like_black_hole, o “quasi-bh” con BH flag attivo).

Il witness `m_SATcrit16_cli_demo` rappresenta esattamente un
profilo di tipo Φ_SAT(φ_crit).

### 3.2. Compatibilità qualitativa con H1–H3

Vediamo come un Φ_SAT del genere può essere compatibile con H1–H3
(vedi `LOVENTRE_PNP_HYPOTHESES_H1H2H3_SEED_2025-12.md`):

- **H1 (Monotonia di difficoltà)**:

  - man mano che consideriamo istanze più “hard” di SAT (più vicine
    al cuore NP-completo, con comportamento di ricerca esplosivo),
    Φ_SAT dovrebbe produrre profili con:

    - `chi_compactness` crescente,
    - `risk_index` crescente,
    - eventuale `horizon_flag` che si accende,

    fino a collocare tali istanze nella classe NP_like_black_hole
    (o strettamente al suo bordo).

  - il witness `m_SATcrit16_cli_demo` è precisamente un esempio
    “canonico” di questo comportamento.

- **H2 (Stabilità di P)**:

  - H2 riguarda soprattutto problemi in P (come 2-SAT);
  - qui SAT è NP-completo, quindi NON richiediamo che tutte le sue
    istanze restino lontane da NP_bh;
  - al contrario, è plausibile che per famiglie di istanze “hard”
    di SAT, Φ_SAT porti il profilo dentro NP_bh.

  In altre parole: SAT, essendo NP-completo, è esattamente il tipo
  di problema per cui un modello come Loventre **deve** permettersi
  di usare la regione NP_bh.

- **H3 (Non-degenerazione di NP_bh)**:

  - il fatto che `m_SATcrit16_cli_demo` sia NP_bh è un segnale che
    NP_bh non è una classe “vuota” o artificiale;
  - combinato col case 2-SAT (dove i profili restano P_like/Pacc),
    suggerisce che NP_bh è riservata a problemi per cui riconosciamo
    una difficoltà strutturalmente diversa da P.

---

## 4. Confronto diretto: 2-SAT vs SAT

Mettiamo a confronto i case study:

| Problema     | Stato classico | Profili Loventre v3          | Classe Loventre chiave      |
|--------------|----------------|------------------------------|-----------------------------|
| 2-SAT        | in P           | `m_2SAT_easy`, `m_2SAT_crit` | P_like / Pacc, SAFE/CRIT    |
| SAT          | NP-completo    | `m_SATcrit16_cli_demo`       | NP_like_black_hole          |

In termini di narrativa:

- 2-SAT:
  - resta nel “cuscinetto” P_like/Pacc,
  - può diventare critico, ma non collassa in NP_bh;

- SAT:
  - ha istanze che il modello colloca in NP_bh,
  - rappresenta il cuore “black-hole” della difficoltà NP.

Questo è esattamente il tipo di contrasto che rende interessante
l’Asse A del programma Loventre v3:

> **indicizzare problemi classici non solo per classe (P/NP),  
> ma per posizione geometrica nel paesaggio LMetrics.**

---

## 5. Che cosa NON stiamo facendo

È importante ricordare che:

1. Non stiamo dicendo che:

   - `In_P_Lov` = P,  
   - `In_NP_bh_Lov` = NP o NP-complete.

2. Non stiamo dimostrando nulla del tipo:

   - “SAT non è in P perché il suo profilo è NP_bh”.

   SAT è già noto NP-completo; il modello Loventre usa questa
   intuizione per collocarlo in NP_bh, NON viceversa.

3. Non stiamo usando SAT per affermare P≠NP.

Ciò che stiamo facendo è:

- prendere un problema NP-completo canonico (SAT),
- vedere come il modello Loventre lo tratta (NP_bh),
- confrontarlo con il modo in cui tratta 2-SAT (P_like/Pacc),
- e usare questo contrasto come materiale concettuale per:

  - eventuali futuri teoremi condizionali (sotto H1–H3),
  - una lettura geometrica delle classi di difficoltà.

---

## 6. Possibili passi successivi

A partire da questo case study SAT, i prossimi passi naturali sono:

1. Aggiungere un case study TSP, con:

   - `m_TSPcrit28_cli_demo` come witness canonico NP_bh,
   - un’analisi parallela a quella di SAT.

2. Scrivere una nota che raccolga:

   - case 2-SAT (P, P_like/Pacc),
   - case SAT (NP-completo, NP_bh),
   - case TSP (NP-completo, NP_bh),

   e proponga una **prima bozza di “mappa**

