# LOVENTRE — STATO COQ v3 (09/12/2025)

Questo file fotografa lo **stato stabile v3** dello stack Coq del progetto Loventre, lato `Loventre_Coq_Clean`.

---

## 1. Moduli che compilano correttamente (v3)

Lanciando i comandi (con `cd` dentro `Loventre_Coq_Clean`):

```bash
coqc -Q 01_Core Loventre_Core \
     -Q 02_Advanced Loventre_Advanced \
     -Q 02_Advanced/Geometry Loventre_Advanced.Geometry \
     02_Advanced/Geometry/Loventre_LMetrics_Existence_Summary.v

coqc -Q 01_Core Loventre_Core \
     -Q 02_Advanced Loventre_Advanced \
     -Q 02_Advanced/Geometry Loventre_Advanced.Geometry \
     -Q 03_Main Loventre_Main \
     03_Main/Loventre_Main_Theorem_v3.v

coqc -Q 01_Core Loventre_Core \
     -Q 02_Advanced Loventre_Advanced \
     -Q 02_Advanced/Geometry Loventre_Advanced.Geometry \
     -Q 03_Main Loventre_Main \
     03_Main/Loventre_Main_Theorem_v3_Bridge.v

coqc -Q 01_Core Loventre_Core \
     -Q 02_Advanced Loventre_Advanced \
     -Q 02_Advanced/Geometry Loventre_Advanced.Geometry \
     -Q 03_Main Loventre_Main \
     03_Main/Test_Loventre_Theorem_v3_All.v
```

lo stack v3 che **compila senza errori** è:

* `01_Core/Loventre_Kernel.v`
* `02_Advanced/Loventre_Metrics_Bus.v`
* `02_Advanced/Geometry/Loventre_LMetrics_Phase_Predicates.v`
* `02_Advanced/Geometry/Loventre_LMetrics_JSON_Witness.v`
* `02_Advanced/Geometry/Loventre_LMetrics_Existence_Summary.v`
* `03_Main/Loventre_Main_Theorem_v3.v`
* `03_Main/Loventre_Main_Theorem_v3_Bridge.v`
* `03_Main/Test_Loventre_Theorem_v3_All.v`

---

## 2. Tipo LMetrics e classificazione P / NP_like-black-hole

Il tipo centrale è il **bus delle metriche**:

```coq
Record LMetrics := {
  kappa_eff            : R;
  entropy_eff          : R;
  V0                   : R;
  a_min                : R;
  p_tunnel             : R;
  P_success            : R;
  gamma_dilation       : R;
  time_regime          : TimeRegime;
  mass_eff             : R;
  inertial_idx         : R;
  risk_index           : R;
  risk_class           : string;
  chi_compactness      : R;
  horizon_flag         : bool;
  meta_label           : string;
  loventre_global_decision : option string;
  loventre_global_color    : option string
}.
```

La classificazione di fase è implementata in:

* `Loventre_LMetrics_Phase_Predicates.v`, con predicati:

```coq
Definition is_P_like (m : LMetrics) : Prop := (* alias P-like SAFE/LOW *) ...
Definition is_NP_like_black_hole (m : LMetrics) : Prop := (* alias NP-like BH *) ...
```

(Internamente `is_P_like` e `is_NP_like_black_hole` sono definiti usando `chi_compactness`, `horizon_flag` e/o `risk_index`, coerenti con la semantica P / NP_like_black_hole.)

---

## 3. Witness JSON ↔ LMetrics (bridge Python → Coq)

Il file:

* `02_Advanced/Geometry/Loventre_LMetrics_JSON_Witness.v`

contiene le **definizioni Coq** corrispondenti ai 4 witness JSON esportati dal motore Python:

* `m_seed11_cli_demo`      : witness P_like (SAFE/LOW)
* `m_seed_grid_demo`       : witness P_like_accessible borderline
* `m_TSPcrit28_cli_demo`   : witness NP_like_black_hole_TSP
* `m_SATcrit16_cli_demo`   : witness NP_like_black_hole_SAT (già pronto lato JSON; lato teorema v3 è ancora opzionale)

Questi record sono definiti come istanze di `LMetrics` con i valori presi dai JSON generati da:

* `loventre_export_witness_json.py`
* `loventre_coq_snippet_gen.py`

---

## 4. Enunciato del Main Theorem v3

In `03_Main/Loventre_Main_Theorem_v3.v` il **tipo** del teorema è:

```coq
Theorem Loventre_Main_Theorem_v3_Prop :
  exists m_P m_NP : LMetrics,
    is_P_like m_P /\ is_NP_like_black_hole m_NP.
```

La **prova concreta** (che Coq ci mostra in output quando compiliamo `Test_Loventre_Theorem_v3_All.v`) è:

```coq
Loventre_Main_Theorem_v3_Prop =
ex_intro
  (fun m_P : LMetrics =>
     exists m_NP : LMetrics,
       is_P_like m_P /\ is_NP_like_black_hole m_NP)
  m_seed11_cli_demo
  (ex_intro
     (fun m_NP : LMetrics =>
        is_P_like m_seed11_cli_demo /\ is_NP_like_black_hole m_NP)
     m_TSPcrit28_cli_demo
     (conj m_seed11_soddisfa_is_P_like
           m_TSPcrit28_soddisfa_is_NP_like_black_hole))
  : exists m_P m_NP : LMetrics,
      is_P_like m_P /\ is_NP_like_black_hole m_NP.
```

Quindi, a parole:

> Il teorema v3 afferma che **esistono** due metriche Loventre `m_P` e `m_NP` tali che:
>
> * `is_P_like m_P`
> * `is_NP_like_black_hole m_NP`
>
> e i witness scelti sono:
>
> * `m_P := m_seed11_cli_demo`
> * `m_NP := m_TSPcrit28_cli_demo`

con i lemmi:

```coq
Lemma m_seed11_soddisfa_is_P_like :
  is_P_like m_seed11_cli_demo.

Lemma m_TSPcrit28_soddisfa_is_NP_like_black_hole :
  is_NP_like_black_hole m_TSPcrit28_cli_demo.
```

---

## 5. Bridge logico `Loventre_Main_Theorem_v3_Bridge`

Il file:

* `03_Main/Loventre_Main_Theorem_v3_Bridge.v`

introduce un tipo *pulito*:

```coq
Definition Loventre_Main_Theorem_v3_statement : Prop :=
  exists m_P m_NP : LMetrics,
    is_P_like m_P /\ is_NP_like_black_hole m_NP.
```

e il **bridge**:

```coq
Theorem Loventre_Main_Theorem_v3_Bridge :
  Loventre_Main_Theorem_v3_statement.
Proof.
  unfold Loventre_Main_Theorem_v3_statement.
  exact Loventre_Main_Theorem_v3_Prop.
Qed.
```

(con compilazione effettiva implementata tramite `let e := Loventre_Main_Theorem_v3_Prop in match e with ... end`, ma logicamente equivalente a `exact`).

Risultato:

* `Loventre_Main_Theorem_v3_Prop` = versione “di lavoro” della prova
* `Loventre_Main_Theorem_v3_statement` = formula pulita
* `Loventre_Main_Theorem_v3_Bridge` = collegamento fra le due

---

## 6. File di test `Test_Loventre_Theorem_v3_All.v`

Questo file:

* importa `Loventre_Main_Theorem_v3` e `Loventre_Main_Theorem_v3_Bridge`
* compila senza errori
* fa emergere in output la forma esplicita della prova (con `ex_intro`, `conj`, ecc.), utile per debugging e documentazione.

---

## 7. Prossimi passi naturali (TODO v3.x)

1. **Integrare anche `m_SATcrit16_cli_demo`** in una versione `v3.1` del teorema, ad esempio come lemma separato:

   ```coq
   Lemma Loventre_SATcrit16_is_NP_like_black_hole :
     is_NP_like_black_hole m_SATcrit16_cli_demo.
   ```

2. Preparare una versione `v3_safe` dove:

   * la distinzione SAFE / NON-SAFE è esplicitata (es. via `risk_class` e `horizon_flag`)
   * si introduce una forma più vicina al futuro Teorema v5/v6 (P_SAFE vs NP_like_black_hole_nonSAFE).

3. Tenere **questo file** come riferimento stabile:

   * se in futuro cambiamo i nomi dei predicati (`is_P_like`, `is_NP_like_black_hole`) o la struttura di `LMetrics`,
   * dovremo sempre assicurarci che i comandi di compilazione di cui sopra continuino a funzionare.

---

*Fine snapshot v3 — Loventre_Coq_Clean — 09 dicembre 2025.*

