# LOVENTRE — CASE STUDY 2-SAT v3 (Dicembre 2025)

## 0. Scopo

Questo case study ha tre obiettivi:

1. Prendere un problema classico **in P** (2-SAT) e posizionarlo nel
   paesaggio Loventre v3.

2. Mettere in relazione i profili:
   - `m_2SAT_easy_demo`,
   - `m_2SAT_crit_demo`

   con le classi interne (`In_P_Lov`, `In_Pacc_Lov`, SAFE/CRIT/quasi-bh).

3. Mostrare come un mapping concettuale Φ_2SAT possa essere compatibile
   con le ipotesi H1–H3 del seed:

   - `LOVENTRE_PNP_HYPOTHESES_H1H2H3_SEED_2025-12.md`.

Non è un risultato formale, ma un **esempio di lavoro** sull’Asse A
(P/NP) del programma Loventre v3.

---

## 1. 2-SAT nel mondo classico (foto rapida)

### 1.1. Definizione classica

- 2-SAT: formule CNF dove ogni clausola ha al massimo 2 letterali.

- È noto che 2-SAT è **in P**: esistono algoritmi polinomiali
  (es. tramite grafi di implicazione e componenti fortemente connesse).

Quindi, a livello classico:

- 2-SAT non è NP-completo;
- è considerato un problema “trattabile”, anche se può avere
  istanze più o meno delicate (vicine a soglie di soddisfacibilità).

### 1.2. Intuizione “regimi easy/critici” per 2-SAT

Senza entrare in dettagli tecnici, è naturale pensare che:

- istanze “facili” (es. sparse, con molte soluzioni) siano molto più
  regolari;

- istanze “critiche” (strutturalmente dense, vicino al “confine” fra
  soddisfacibile/insoddisfacibile) siano più instabili, pur rimanendo
  nel regime P dal punto di vista della complessità.

Questa distinzione “easy vs critico” è precisamente il tipo di cosa
che il modello Loventre v3 può esprimere come **differenza di profilo**
nel paesaggio LMetrics, anche se la classe P classica non la vede.

---

## 2. 2-SAT nel modello Loventre v3 (easy / crit)

### 2.1. I due profili canonici

Nel layer v3+ hai due witness JSON canonici:

- `m_2SAT_easy_demo`
- `m_2SAT_crit_demo`

che, secondo il MINI SEED JSON_IO → Coq, hanno (schematicamente):

- **m_2SAT_easy_demo**:
  - `phase_guess = P_like`
  - `risk_class = SAFE`
  - `time_regime = poly`
  - `horizon_flag = false`
  - `risk_index ≈ 0.18`
  - `chi_compactness ≈ 0.25`

- **m_2SAT_crit_demo**:
  - `phase_guess = P_like_accessible`
  - `risk_class = CRIT`
  - `time_regime = poly_critical`
  - `horizon_flag = false`
  - `risk_index ≈ 0.81`
  - `chi_compactness ≈ 0.86`

In termini Loventre v3:

- entrambi sono nel “mondo P_like”,
- ma con ruoli diversi:

  - easy_demo: P_like + SAFE,
  - crit_demo: P_like_accessible + CRIT, quasi-bh ma non NP_bh.

### 2.2. Posizione nelle classi Loventre

Tabellina interna:

| Profilo              | Classe Loventre        | Rischio     | Regime tempo        | BH?        |
|----------------------|------------------------|-------------|---------------------|-----------|
| `m_2SAT_easy_demo`   | in `In_P_Lov`          | SAFE        | poly                | no bh     |
| `m_2SAT_crit_demo`   | in `In_Pacc_Lov`       | CRIT        | poly_critical       | quasi-bh  |

A livello concettuale:

- `m_2SAT_easy_demo` rappresenta “un 2-SAT che il modello vede come facile”;
- `m_2SAT_crit_demo` rappresenta “un 2-SAT che il modello vede come
  *ancora P_like_accessible*, ma in una zona molto critica del paesaggio”.

---

## 3. Un mapping concettuale Φ_2SAT

### 3.1. Idea generale

Pensiamo a un mapping concettuale:

> Φ_2SAT : (istanze di 2-SAT) → LMetrics

che, per una data formula 2-SAT (più eventuali parametri), produca
un profilo LMetrics.

Ovviamente nel motore Python esiste già una dinamica specifica, ma qui
ci interessa solo una possibile **descrizione concettuale**:

- variabili: dimensione `n`, numero clausole `m`,
- struttura: densità del grafo di implicazione, presenza di pattern
  altamente vincolanti, ecc.

L’idea di base:

> man mano che l’istanza si avvicina a una regione “critica” (poche
> soluzioni, grafo molto vincolato, transizioni brusche), i parametri:

- `chi_compactness`,
- `risk_index`,
- `gamma_dilation`,
- altri indicatori di “curvatura”,

devono crescere, spingendo il profilo verso la zona CRIT / quasi-bh.

### 3.2. Compatibilità qualitativa con H1–H3

Vediamo come un Φ_2SAT di questo tipo si incolla alle ipotesi H1–H3:

- **H1 (Monotonia di difficoltà)**:
  - istanze “molto easy” → Φ_2SAT(φ) ≈ `m_2SAT_easy_demo`:
    - P_like, SAFE, risk_index basso;
  - istanze “critiche” → Φ_2SAT(φ) ≈ `m_2SAT_crit_demo`:
    - P_like_accessible, CRIT, risk_index alto.

- **H2 (Stabilità di P)**:
  - 2-SAT è in P:
    - anche per istanze critiche, Φ_2SAT non deve portare il profilo
      in NP_like_black_hole;
    - infatti `m_2SAT_crit_demo` resta P_like_accessible, non NP_bh,
      con horizon_flag = false.

- **H3 (Non-degenerazione NP_bh)**:
  - 2-SAT non deve occupare “a caso” la regione NP_bh:
    - i due profili canonici 2-SAT restano in P_like / Pacc,
      anche quando CRIT e quasi-bh;
    - NP_bh è riservato a profili stile TSPcrit/SATcrit.

Quindi 2-SAT, nel paesaggio v3:

- popola bene la parte **P_like / Pacc** (con SAFE e CRIT),
- non invade NP_bh,
- illustra come un problema in P possa avere **regimi interni** molto diversi
  dal punto di vista informazionale.

---

## 4. Che cosa offre questo case study al programma P/NP

Questo case study di 2-SAT dimostra che:

1. È possibile avere un problema in P che, nel modello Loventre,
   generi:

   - profili P_like+SAFE (easy),
   - profili P_like_accessible+CRIT (critici),
   - ma **non** profili NP_like_black_hole.

2. Il modello è in grado di:
   - distinguere fra “facilità” puramente definita (appartenenza a P),
   - e “facilità”/“stabilità” geometrica (SAFE vs CRIT vs quasi-bh).

3. Questo tipo di distinzione è un ingrediente importante
   per qualunque tentativo di leggere:

   - `In_P_Lov` / `In_Pacc_Lov` / `In_NP_bh_Lov`

   come analoghi geometrici delle classi P / NP-hard, in modo
   **non banale**.

---

## 5. Possibili sviluppi futuri (sempre come programma)

A partire da questo caso studio, i passi naturali sono:

1. Ripetere l’analisi concettuale per:

   - SAT (3-SAT),
   - TSP (decisionale),
   - altri problemi classici “toy”,

   costruendo per ciascuno:
   - 1–2 profili canonici (easy / crit),
   - un pezzo di narrativa “Φ_problema” compatibile con H1–H3.

2. Valutare se esistono enunciati **condizionali** del tipo:

   > Se Φ_problema soddisfa H1–H3 e alcune condizioni strutturali,
   > allora i profili TSPcrit/SATcrit “si comportano” come NP_bh
   > nel senso Loventre, mentre 2-SAT rimane Pacc.

3. Mantenere chiara la distinzione fra:

   - risultati rigorosi nel modello (già formalizzati in Coq),
   - e programmi di ricerca che collegano il modello a P/NP classico.

_Fine — LOVENTRE_PNP_CASESTUDY_2SAT_v3_NOTE_2025-12_

