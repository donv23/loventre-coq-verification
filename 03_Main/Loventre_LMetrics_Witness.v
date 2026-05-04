(* =============================================== *)
(* LOVENTRE PROJECT - LMetrics Witness Seed        *)
(* Module: Loventre_LMetrics_Witness               *)
(* Date: December 2025                             *)
(* =============================================== *)

(** 
  Loventre LMetrics Witness Seed – Dicembre 2025
  =============================================

  Questo seed fissa quattro regimi "canonici" del bus metrico LMetrics,
  concettualmente costruiti lato Python e referenziati qui:

    - m_seed11_safe_json            : caso SAFE / P_like_like / subcritico
    - m_TSPcrit12_borderline_json   : caso BORDERLINE / NP_like_critico / near-horizon
    - m_TSPcrit28_json              : caso CRITICO / NP_like_black_hole (famiglia TSP_crit_n)
    - m_SATcrit16_json              : caso CRITICO / NP_like_black_hole (famiglia SAT_crit_n)

  L’idea è: 
    metrics (Python) -> Policy Bridge -> LMetrics JSON -> nome Coq.

  In questo modo il record LMetrics in Coq ha una controparte operativa 
  diretta nel motore Loventre in Python (anche se qui li trattiamo in modo
  astratto, via [Parameter], per non legarci subito ai numeri specifici).
*)

Require Import Loventre_Metrics_Bus.
Require Import Loventre_SAT_TSP_Critical_Metrics.

(* ------------------------------------------------- *)
(* 1. Parametri astratti che rappresentano i JSON    *)
(* ------------------------------------------------- *)

(** 
  In futuro questi potranno essere definiti come

      Definition ... : LMetrics := {| ... |}.

  auto-generati da loventre_lmetrics_to_coq_snippet.py.

  Per ora li trattiamo come elementi astratti di LMetrics
  che rappresentano i quattro stati canonici.
*)

Parameter m_seed11_safe_json          : LMetrics.
Parameter m_TSPcrit12_borderline_json : LMetrics.
Parameter m_TSPcrit28_json            : LMetrics.
Parameter m_SATcrit16_json            : LMetrics.

(** Alias brevi per i quattro witness principali. *)

Definition m_safe       : LMetrics := m_seed11_safe_json.
Definition m_borderline : LMetrics := m_TSPcrit12_borderline_json.
Definition m_crit_TSP   : LMetrics := m_TSPcrit28_json.
Definition m_crit_SAT   : LMetrics := m_SATcrit16_json.

(* ------------------------------------------------- *)
(* 2. Regimi qualitativi di GlobalDecision attesi    *)
(* ------------------------------------------------- *)

(** 
  Vista qualitativa (allineata al Policy Bridge Python):

    - m_safe       -> GD_safe / GC_green
    - m_borderline -> GD_borderline / GC_amber
    - m_crit_*     -> GD_critical / GC_red
*)

Conjecture GlobalDecision_safe :
  loventre_global_decision m_safe = GD_safe.

Conjecture GlobalDecision_borderline :
  loventre_global_decision m_borderline = GD_borderline.

Conjecture GlobalDecision_critical_TSP :
  loventre_global_decision m_crit_TSP = GD_critical.

Conjecture GlobalDecision_critical_SAT :
  loventre_global_decision m_crit_SAT = GD_critical.

(* ------------------------------------------------- *)
(* 3. Collegamento con SAT_crit, TSP_crit, witness   *)
(* ------------------------------------------------- *)

(** 
  Collegamento con le famiglie critiche SAT/TSP e con Metrics_witness.

  L'idea è:

    - m_crit_TSP, m_crit_SAT sono testimoni concreti delle famiglie 
      NP_like-critiche TSP_crit_n e SAT_crit_n,
    - per questi witness vale Metrics_witness, quindi ci aspettiamo una 
      GlobalDecision "almeno borderline", di fatto critical.
*)

Axiom Metrics_witness_TSPcrit28 :
  TSP_crit m_crit_TSP /\ Metrics_witness m_crit_TSP.

Axiom Metrics_witness_SATcrit16 :
  SAT_crit m_crit_SAT /\ Metrics_witness m_crit_SAT.

(* Piccoli lemmi di proiezione, comodi in seguito. *)

Lemma m_crit_TSP_TSP_crit : TSP_crit m_crit_TSP.
Proof.
  destruct Metrics_witness_TSPcrit28 as [Hcrit _].
  exact Hcrit.
Qed.

Lemma m_crit_TSP_Metrics_witness : Metrics_witness m_crit_TSP.
Proof.
  destruct Metrics_witness_TSPcrit28 as [_ Hwit].
  exact Hwit.
Qed.

Lemma m_crit_SAT_SAT_crit : SAT_crit m_crit_SAT.
Proof.
  destruct Metrics_witness_SATcrit16 as [Hcrit _].
  exact Hcrit.
Qed.

Lemma m_crit_SAT_Metrics_witness : Metrics_witness m_crit_SAT.
Proof.
  destruct Metrics_witness_SATcrit16 as [_ Hwit].
  exact Hwit.
Qed.

(* ------------------------------------------------- *)
(* 4. Congetture strutturali sul layer globale       *)
(* ------------------------------------------------- *)

(** 
  Congettura strutturale (versione locale):

    - ogni witness metrico NP_like (SAT_crit o TSP_crit), una volta visto
      dal Global Decision Layer, non può risultare "safe".
*)

Conjecture witness_are_not_safe :
  forall m : LMetrics,
    Metrics_witness m ->
    loventre_global_decision m <> GD_safe.

(** 
  Variante più forte (bozza):

    un witness metrico NP_like-critico è globalmente borderline o critical.

  (La versione formale generale potrebbe usare un predicato NP_like_critico m.)
*)

Conjecture witness_are_borderline_or_critical :
  forall m : LMetrics,
    Metrics_witness m ->
      loventre_global_decision m = GD_borderline \/
      loventre_global_decision m = GD_critical.

(* ------------------------------------------------- *)
(* 5. Conseguenze immediate sui quattro witness      *)
(* ------------------------------------------------- *)

Section Consequences_for_Witnesses.

  Hypothesis H_borderline_or_critical :
    forall m : LMetrics,
      Metrics_witness m ->
        loventre_global_decision m = GD_borderline \/
        loventre_global_decision m = GD_critical.

  Lemma m_crit_TSP_global_borderline_or_critical :
    loventre_global_decision m_crit_TSP = GD_borderline \/
    loventre_global_decision m_crit_TSP = GD_critical.
  Proof.
    apply H_borderline_or_critical.
    apply m_crit_TSP_Metrics_witness.
  Qed.

  Lemma m_crit_SAT_global_borderline_or_critical :
    loventre_global_decision m_crit_SAT = GD_borderline \/
    loventre_global_decision m_crit_SAT = GD_critical.
  Proof.
    apply H_borderline_or_critical.
    apply m_crit_SAT_Metrics_witness.
  Qed.

End Consequences_for_Witnesses.

(* =============================================== *)
(* End of Loventre_LMetrics_Witness.v              *)
(* =============================================== *)

