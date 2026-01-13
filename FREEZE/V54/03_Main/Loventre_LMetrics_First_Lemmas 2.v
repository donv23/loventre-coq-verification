(** Loventre_LMetrics_First_Lemmas.v

    Main-level lemmi su LMetrics e witness critici.
    Seed dicembre 2025 – ponte tra Geometry e JSON witness.
*)

From Loventre_Geometry Require Import Loventre_Metrics_Bus.
From Loventre_Geometry Require Import Loventre_SAT_TSP_Critical_Metrics.
From Loventre_Geometry Require Import Loventre_LMetrics_Witness_CLI.
From Loventre_Geometry Require Import Loventre_LMetrics_Witness_Lemmas.
From Loventre_Geometry Require Import Loventre_LMetrics_JSON_Witness.

Module MB      := Loventre_Metrics_Bus.
Module Crit    := Loventre_SAT_TSP_Critical_Metrics.
Module CLI     := Loventre_LMetrics_Witness_CLI.
Module WLemmas := Loventre_LMetrics_Witness_Lemmas.
Module JSONW   := Loventre_LMetrics_JSON_Witness.

(**
  Idea: qui raccogliamo lemmi "di livello Main" che
  riusano risultati geometrici e JSON-based.

  Primo passo: formalizzare che i due witness canonici
  JSON (TSPcrit28, SATcrit16) sono entrambi globalmente
  classificati come "critical" e "red".
*)

Theorem main_json_witnesses_are_critical_and_red :
  JSONW.loventre_global_decision JSONW.m_TSPcrit28_json = JSONW.GD_critical /\
  JSONW.loventre_global_color    JSONW.m_TSPcrit28_json = JSONW.GC_red /\
  JSONW.loventre_global_decision JSONW.m_SATcrit16_json = JSONW.GD_critical /\
  JSONW.loventre_global_color    JSONW.m_SATcrit16_json = JSONW.GC_red.
Proof.
  (* Usiamo direttamente i lemmi del modulo JSON witness. *)
  destruct JSONW.GD_TSPcrit28_json_critical as [Htsp_dec Htsp_col].
  destruct JSONW.GD_SATcrit16_json_critical as [Hsat_dec Hsat_col].
  repeat split; assumption.
Qed.

