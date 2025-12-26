# LOVENTRE — CASE STUDY TSP v3 (Dicembre 2025)

## 0. Scopo

Questo case study completa la “tripletta”:

- 2-SAT (P, P_like/Pacc),
- SAT (NP-completo, NP_bh),
- TSP (NP-completo, NP_bh),

nel contesto del modello Loventre v3.

Obiettivi principali:

1. Posizionare TSP (versione decisionale/critica) nel paesaggio LMetrics.
2. Chiarire il ruolo del witness:
   - `m_TSPcrit28_cli_demo`.
3. Verificare la coerenza concettuale con le ipotesi H1–H3 del seed:
   - `LOVENTRE_PNP_HYPOTHESES_H1H2H3_SEED_2025-12.md`.

Come per 2-SAT e SAT, questa nota è un pezzo del **programma P/NP-Loventre**,
non un nuovo teorema.

---

## 1. TSP nel mondo classico (foto rapida)

### 1.1. Definizione (versione decisionale)

- TSP decisionale: dato un grafo pesato (o una matrice di distanze)
  e una soglia B, chiedere se esiste un tour Hamiltoniano di costo
  ≤ B.

- TSP decisionale è **NP-completo**:
  - appartiene a NP (un tour candidato è verificabile in tempo polinomiale),
  - ogni problema in NP è riducibile polinomialmente a TSP.

In termini classici:

- TSP è uno dei prototipi storici di NP-completo,
- è intrinsecamente difficile (in assenza di una prova P=NP).

### 1.2. Intuizione “regimi easy/critici” per TSP

Come per SAT, è naturale distinguere:

- istanze “easy” (piccoli grafi, strutture particolari, distanze “gentili”),
- istanze “critiche” (grafi complessi, metriche “cattive”, vicino a soglie,
  con molte quasi-soluzioni ma pochissime veramente buone, ecc.).

Nel contesto TSP, le istanze critiche sono spesso quelle dove:

- il paesaggio delle soluzioni ha tantissimi minimi locali,
- i metodi di ricerca locale / branch-and-bound esplodono in tempi.

---

## 2. TSP nel modello Loventre v3

### 2.1. Il witness canonico TSPcrit28

Nel nucleo Geometry v3 esiste il witness:

- `m_TSPcrit28_cli_demo : LMetrics`

con un assioma (via `Loventre_LMetrics_Existence_Summary.v`):

- `m_TSPcrit28_soddisfa_is_NP_like_black_hole`.

Questo significa che:

- nel modello Loventre v3,
- `m_TSPcrit28_cli_demo` è dichiarato **NP_like_black_hole**.

Interpretazione concettuale:

> `m_TSPcrit28_cli_demo` è il profilo canonico che rappresenta
> una **istanza critica di TSP** in zona black-hole informazionale,
> dove la curvatura/compattazione del paesaggio è altissima.

### 2.2. Posizione nella classificazione Loventre

In termini di classi:

- `m_TSPcrit28_cli_demo` ∈ `In_NP_bh_Lov`,
- non appartiene a `In_Pacc_Lov`,
- è un rappresentante esplicito della regione NP_like_black_hole.

Nella tabella “tripla” (2-SAT / SAT / TSP):

| Problema / profilo         | Stato classico | Classe Loventre chiave      |
|----------------------------|----------------|-----------------------------|
| 2-SAT easy/crit            | in P           | P_like / Pacc, SAFE/CRIT    |
| SATcrit16                  | NP-completo    | NP_like_black_hole          |
| TSPcrit28                  | NP-completo    | NP_like_black_hole          |

Quindi:

- SATcrit16 e TSPcrit28 sono i due pilastri NP_bh nel modello;
- 2-SAT rimane l’esempio “P ma con regimi interni” (no NP_bh).

---

## 3. Un mapping concettuale Φ_TSP

### 3.1. Idea generale

Immaginiamo un mapping concettuale:

> Φ_TSP : (istanze di TSP) → LMetrics

che prende in input:

- dimensione del grafo,
- distribuzione dei pesi,
- struttura (completo, sparso, metric, non-metric, ecc.),
- eventuali parametri di “difficoltà empirica”

e produce un profilo LMetrics, con:

- `kappa_eff`, `entropy_eff` (curvatura/entropia del paesaggio),
- `chi_compactness`, `risk_index` (compattazione / rischio),
- informazioni su regimi SAFE/CRIT/BH, ecc.

L’idea, allineata al resto del programma, è:

- istanze TSP piccole o molto strutturate → profili non troppo
  estremi (magari P_like-like o moderatamente critici);
- istanze TSP critiche (TSPcrit28-style) → profili NP_like_black_hole,
  con indicatori vicini a “singolarità informazionale”.

### 3.2. Compatibilità qualitativa con H1–H3

Riprendiamo H1–H3 dal seed HYPOTHESES:

- **H1 (Monotonia di difficoltà)**:

  - per TSP, le istanze considerate “hard” dalla comunità
    (branch-and-bound esplode, euristiche in difficoltà) dovrebbero
    avere Φ_TSP(istanza_hard) in regioni ad alta `chi_compactness`,
    `risk_index` e potenzialmente NP_bh;
  - `m_TSPcrit28_cli_demo` è precisamente un “marker” per questo tipo
    di comportamento.

- **H2 (Stabilità di P)**:

  - H2 dice che problemi in P non devono generare profili NP_bh
    in modo sistematico;
  - TSP NON è noto essere in P (è NP-completo), quindi non c’è
    nessun vincolo da H2 che impedisca a Φ_TSP di produrre NP_bh:
    anzi, è atteso.

- **H3 (Non-degenerazione di NP_bh)**:

  - il fatto che TSPcrit28 sia NP_bh e 2-SAT no, suggerisce una
    buona non-degenerazione: NP_bh non è una classe che inghiotte
    indistintamente tutti i problemi;
  - è plausibile pensare che NP_bh sia “riservata” a problemi con
    strutture di difficoltà tipiche di NP-hard/NP-completi.

---

## 4. Allineamento SAT / TSP nel paesaggio NP_bh

Con i due case study SAT e TSP, il modello Loventre v3:

- colloca SATcrit16 e TSPcrit28 nella stessa regione concettuale:

  - NP_like_black_hole,
  - profili altamente compattati,
  - regioni “collassate” del paesaggio.

- li distingue invece da:

  - 2-SAT easy/crit (P_like/Pacc, SAFE/CRIT),
  - eventuali problemi P-like stabili.

Questo è coerente con l’idea che:

> NP_bh_Lov è una regione in cui vivono i profili associati a problemi
> che, nel mondo classico, riconosciamo come “intrinsecamente difficili”
> (NP-completi), mentre Pacc è riservata a problemi/istanze P-like
> con buona accessibilità.

---

## 5. Potenziali sviluppi sul trittico 2-SAT / SAT / TSP

Con 2-SAT, SAT e TSP hai una base concettuale per una nota successiva:

- una **“mappa P/NP-Loventre v3 – Trittico canonico”**, che:

  1. mette in una sola tabella:
     - 2-SAT easy/crit,
     - SATcrit16,
     - TSPcrit28;

  2. esplicita:

     - quali obiettivi soddisfano H1–H3,
     - dove si colloca ogni witness sul continuum:
       - P_like SAFE → Pacc CRIT → quasi-bh → NP_bh.

  3. permette frasi del tipo:

     > “Nel modello Loventre v3, 2-SAT abita la regione P_like/Pacc,
     > mentre SAT critico e TSP critico abitano NP_like_black_hole.
     > Questo è coerente con il fatto che 2-SAT è in P, mentre SAT e
     > TSP sono NP-completi. Tuttavia la connessione con P/NP classico
     > resta un programma condizionale (H1–H3).”

---

## 6. Conclusione del case study TSP

Questo case study consolida l’idea che:

- NP_bh_Lov non è un deflettore generico,
- ma una regione del modello pensata per catturare la “difficoltà
  strutturale” di problemi NP-completi “hard” (SAT, TSP),
- mentre problemi in P (come 2-SAT) possono avere regimi critici
  senza mai uscire da P_like/Pacc.

Questo non prova nulla su P vs NP, ma fornisce una **metafora
geometrica consistente** con l’intuizione classica:

- P ≈ regioni P_like/Pacc (SAFE / CRIT ma senza collasso),
- NP-hard ≈ regioni NP_bh (black-hole informazionali).

_Fine — LOVENTRE_PNP_CASESTUDY_TSP_v3_NOTE_2025-12_

