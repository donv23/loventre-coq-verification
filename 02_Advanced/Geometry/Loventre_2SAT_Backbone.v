(** 
  Loventre_2SAT_Backbone.v
  V84.6 — Spina dorsale 2-SAT

  Aggrega e re-esporta:
    JSON {easy,critico}
    decode & compute
    compare easy/crit
    monotonicità Pacc
    lemma easy sovradominante
    lemma critico non SAFE

  Nessuna prova nuova: è colla architetturale
*)

From Loventre_Core Require Import Loventre_Core_Prelude.
From Loventre_Advanced Require Import
     Loventre_LMetrics_Core
     Loventre_Metrics_Bus
     Loventre_Risk_Level
     Loventre_SAFE_Model
     Loventre_Class_Model
     Loventre_LMetrics_JSON_Witness.

From Loventre_Advanced.Geometry Require Import
     Loventre_2SAT_LMetrics_Crit_JSON
     Loventre_2SAT_LMetrics_From_JSON
     Loventre_2SAT_Decode_Compute
     Loventre_2SAT_EasyCrit_Compare
     Loventre_2SAT_Pacc_Monotonicity
     Loventre_2SAT_Pacc_Axiom
     Loventre_2SAT_Crit_NotSafe.
     
Open Scope R_scope.

(**
  Grande lemma di riepilogo:
  easy ⇒ Pacc & SAFE
  critico ⇒ ¬SAFE
  easy domina critico
*)

Lemma two_sat_backbone_summary :
  (SAFE_pass m2sat_easy_json = true)
/\ (SAFE_fail m2sat_crit_json = true)
/\ easy_dominates_crit.
/\ critical_not_pacc_or_safe.
Proof.
  split.
  - exact easy_is_safe.
  split.
  - exact crit_2sat_not_safe.
  split.
  - exact easy_dominates_crit.
  - exact critical_not_pacc.
Qed.

(** Fine modulo: questo file diventa il "motore di contesto"
    per la futura riscrittura di Phase_Separation in V85 *)

