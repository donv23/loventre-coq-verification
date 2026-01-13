(* ========================================================== *)
(*  LOVENTRE PROJECT — Loventre_LMetrics_JSON_Link.v           *)
(*  Dicembre 2025 — Ponte documentale Coq ↔ JSON witness       *)
(* ========================================================== *)

From Stdlib Require Import String List.
Import ListNotations.
Local Open Scope string_scope.

(** ========================================================= *)
(** * Scopo del modulo                                         *)
(**                                                            *)
(**  Questo file non aggiunge logica matematica.               *)
(**  Serve come documento di collegamento tra i witness JSON   *)
(**  generati dal motore Python e le entità Coq (LMetrics).    *)
(**                                                            *)
(**  Ogni voce indica:                                         *)
(**   - lm_id (nome Coq del witness)                           *)
(**   - path del file JSON corrispondente                      *)
(** ========================================================= *)

Record LMetrics_JSON_Link := {
  lm_id_link : string;
  lm_json_path : string;
}.

Definition loventre_json_links : list LMetrics_JSON_Link :=
  [ {|
      lm_id_link := "m_seed11_cli_demo";
      lm_json_path := "witness_json/m_seed11_cli_demo.json";
    |};
    {|
      lm_id_link := "m_seed_grid_demo";
      lm_json_path := "witness_json/m_seed_grid_demo.json";
    |};
    {|
      lm_id_link := "m_TSPcrit28_cli_demo";
      lm_json_path := "witness_json/m_TSPcrit28_cli_demo.json";
    |};
    {|
      lm_id_link := "m_SATcrit16_cli_demo";
      lm_json_path := "witness_json/m_SATcrit16_cli_demo.json";
    |};
    (* ====================================================== *)
    (*  Nuovi witness 2-SAT – Dicembre 2025                  *)
    (* ====================================================== *)
    {|
      lm_id_link := "m_2SAT_easy_demo";
      lm_json_path := "witness_json/metrics_2SAT_easy_demo.json";
    |};
    {|
      lm_id_link := "m_2SAT_crit_demo";
      lm_json_path := "witness_json/metrics_2SAT_crit_demo.json";
    |}
  ].

(** ========================================================= *)
(** * Nota finale                                              *)
(**                                                            *)
(**  Questo elenco è sincronizzato con la regression suite     *)
(**  Python LOVENTRE_ENGINE_STATUS_2025-12-08.md               *)
(**  e deve essere aggiornato solo quando si aggiungono nuovi  *)
(**  witness JSON riconosciuti dal motore.                     *)
(** ========================================================= *)

