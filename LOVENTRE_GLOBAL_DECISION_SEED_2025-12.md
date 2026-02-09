# LOVENTRE_GLOBAL_DECISION_SEED_2025-12.md

## 0. Scopo di questo seed

Questo documento definisce il **ruolo concettuale** del livello di *Global Decision* nel Loventre Engine, in dialogo con:

- il **bus di metriche** (LMetrics) lato Python/Coq,
- il **Loventre Policy Bridge** lato motore,
- il **Loventre_Conjecture_Package** lato Coq.

Obiettivi:

1. Fissare un vocabolario stabile per parlare di **decisioni globali** prese dal motore a partire da stati metrici critici / quasi-critici.
2. Rendere chiaro, per un referee, come le decisioni del motore possono essere viste come una realizzazione concreta (ma non rivelata) delle congetture modulari in Coq.
3. Mantenere **protetta** la mappa interna `metriche → decisione`, rendendo visibili solo proprietà astratte.

---

## 1. Posizione del Global Decision nella pipeline Loventre

Schema concettuale (molto semplificato):

1. **Einstein–Loventre layer / Metric Engine**  
   - Il motore genera una famiglia di stati `LMetrics` (uno per istanza / configurazione / seed).
   - Ogni `LMetrics` contiene, fra gli altri:
     - `kappa_eff`, `entropy_eff`, `V0`, `a_min`,
     - `p_tunnel`, `P_success`,
     - `gamma_dilation`, `time_regime`,
     - `mass_eff`, `inertial_idx`,
     - `risk_index`, `risk_class`,
     - `chi_compactness`, `horizon_flag`, ecc.

2. **Criticality / SAT_TSP layer**  
   - Alcuni stati LMetrics sono marcati come **critici** (SAT_crit, TSP_crit) lato Coq,
     corrispondenti a regimi di:
     - **alta classe di rischio** (High_risk_class),
     - **vicinanza all’orizzonte** e/o **alta probabilità di tunneling**.

3. **Loventre Policy Bridge (Global Decision)**  
   - A valle del bus di metriche, il Policy Bridge produce una o più decisioni globali:
     - lato Python: oggetti / stringhe / enums interne,
     - lato Coq: un tipo astratto `GlobalDecision : Type` nel modulo `Loventre_Metrics_Bus`.
   - Le decisioni globali NON sono tutte fissate ora; esempi concettuali:
     - `Dec_Allow` / `Dec_Block` / `Dec_Investigate` / `Dec_Deflect` / `Dec_Abort`.
   - Il Global Decision layer è il punto in cui il motore “agisce” sul mondo: sceglie una policy a partire da un regime metrico critico o quasi-critico.

---

## 2. Interfaccia concettuale con il bus di metriche (LMetrics)

Lato Coq, nel modulo `Loventre_Metrics_Bus`, esistono:

- un tipo:
  - `LMetrics : Type`,
- tipi ausiliari:
  - `RiskClass : Type`,
  - `GlobalDecision : Type`,
  - `TimeRegime`, `MetaLabel`, ecc.,
- un record con campi:
  - `kappa_eff`, `entropy_eff`, `V0`, `a_min`,
  - `p_tunnel`, `P_success`,
  - `gamma_dilation`, `time_regime`,
  - `mass_eff`, `inertial_idx`,
  - `risk_index`, `risk_class`,
  - `chi_compactness`, `horizon_flag`, …

In questo seed assumiamo la seguente filosofia:

1. **Il bus di metriche è il “linguaggio comune”** tra:
   - la fisica/numerica del motore Loventre (Python),
   - la formalizzazione matematica (Coq).

2. **GlobalDecision dipende solo da LMetrics**  
   - concettualmente, il Policy Bridge implementa una mappa:
     \[
       \text{LMetrics} \longrightarrow \text{GlobalDecision}
     \]
   - ma questa mappa rimane **non esplicitata** in Coq e nei paper: Coq vede solo proprietà astratte
     del tipo "se un certo regime è critico, allora esiste una decisione globale con proprietà X".

3. **RiskClass e GlobalDecision sono “views” del bus**  
   - `risk_class` è una compressione dello stato metrico in una “classe di rischio” qualitativa.
   - `GlobalDecision` è una compressione delle azioni possibili in risposta a quello stato.

---

## 3. Collegamento con le congetture modulari in Coq

Nel file `03_Main/Loventre_Main_Theorem.v` abbiamo introdotto:

- `Conjecture_SAT_Critical_Family : Prop`
- `Conjecture_TSP_Critical_Family : Prop`
- `Conjecture_TM_Bridge : Prop`
- `Conjecture_Metrics_to_Dynamics : Prop`
- il record:
  ```coq
  Record Loventre_Conjecture_Package : Prop := {
    hyp_SAT  : Conjecture_SAT_Critical_Family;
    hyp_TSP  : Conjecture_TSP_Critical_Family;
    hyp_TM   : Conjecture_TM_Bridge;
    hyp_METR : Conjecture_Metrics_to_Dynamics
  }.

