# FREEZE STATE — Noise & Structural Sensitivity Layer (v1)
📅 Dicembre 2025

Questo documento dichiara **formalmente congelato** il layer
di **Regimi di Rumore, Sensibilità Strutturale e Soglie di Classe**
del modello Loventre.

---

## 1. Ambito del congelamento

Il freeze copre **esclusivamente** i seguenti concetti:

### 🔹 Regimi di Rumore (Noise Regimes)
- tassonomia qualitativa
- ordine strutturale
- esclusività dei regimi

### 🔹 Sensibilità Strutturale (PSS)
- definizione logica
- relazione con robustezza
- implicazioni strutturali
- collegamento a perturbazioni e rumore

### 🔹 Classi di Complessità (astratte)
- P_STR, P_ACC, BH_NP
- soglie di rumore ammissibile
- esclusioni strutturali canoniche

---

## 2. File congelati (CANON)

I seguenti file sono **CANONICI** e NON DEVONO essere modificati
senza una nuova versione di freeze.

### Noise
- `Loventre_Noise_Regimes.v`
- `Loventre_Noise_Regimes_Order.v`
- `Loventre_Noise_Regimes_Exclusivity.v`

### Structural Sensitivity
- `Loventre_Structural_Sensitivity.v`
- `Loventre_Structural_Sensitivity_Lemmas.v`
- `Loventre_Sensitivity_Induces_Critical_Noise.v`
- `Loventre_Sensitivity_Coherence.v`

### Class Thresholds
- `Loventre_Complexity_Noise_Classes.v`
- `Loventre_Sensitivity_Exceeds_PACC.v`
- `Loventre_Sensitivity_Excludes_PACC.v`
- `Loventre_Sensitivity_Excludes_PSTR.v`
- `Loventre_Sensitivity_Excludes_PSTR_Class.v`

---

## 3. Regole post-freeze

Dopo questo freeze:

- ❌ Vietato modificare definizioni, assiomi o parametri in questi file
- ❌ Vietato introdurre nuovi significati semantici retroattivi
- ✅ Ammesso SOLO:
  - dipendere da questi file
  - usarli come ipotesi strutturali
  - costruire teoremi sopra di essi

Ogni cambiamento richiede:
- nuovo file
- nuovo namespace
- nuovo documento di freeze

---

## 4. Stato di compilazione

Tutti i file elencati:
- compilano con `coqc`
- non introducono inconsistenze
- non richiedono Import impliciti
- rispettano le Regole Auree del progetto Loventre

---

## 5. Nota metodologica

Questo freeze **non è una chiusura teorica**,
ma una **stabilizzazione del vocabolario**.

Serve a:
- ridurre attrito cognitivo
- impedire regressioni
- rendere possibile la separazione strutturale delle classi
  nei layer successivi.

---

**FINE FREEZE — v1**

