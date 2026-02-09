(*
  Loventre_V32_Witness_From_JSON.v
  Genera witness LMetrics per Coq dalla cartella JSON_IO/LMetrics_v3_for_Coq
  V31/V32 Canon — GENNAIO 2026
*)

From Stdlib Require Import String Bool List.
Require Import Loventre_v3_JSON_Bridge.
Require Import Loventre_LMetrics_Structure.
Require Import Loventre_Class_Membership.

Open Scope string_scope.

(* === JSON SOURCE PATHS === *)
Definition path_grid : string :=
  "JSON_IO/LMetrics_v3_for_Coq/lmetrics_seed_grid_demo.json".

Definition path_2sat_easy : string :=
  "JSON_IO/LMetrics_v3_for_Coq/lmetrics_2sat_easy_demo.json".

Definition path_2sat_crit : string :=
  "JSON_IO/LMetrics_v3_for_Coq/lmetrics_2sat_crit_demo.json".

(* === LOAD WITNESSES === *)
Definition w_grid : option LMetrics := load_lmetrics_from_json_file path_grid.
Definition w_2sat_easy : option LMetrics := load_lmetrics_from_json_file path_2sat_easy.
Definition w_2sat_crit : option LMetrics := load_lmetrics_from_json_file path_2sat_crit.

(* === ASSERT they loaded === *)
Definition grid_loaded : bool :=
  match w_grid with Some _ => true | None => false end.

Definition easy_loaded : bool :=
  match w_2sat_easy with Some _ => true | None => false end.

Definition crit_loaded : bool :=
  match w_2sat_crit with Some _ => true | None => false end.

(* === CLASSIFICATION CHECKS === *)

Definition grid_P_like : bool :=
  match w_grid with
  | Some m => is_P_like m
  | None => false
  end.

Definition easy_Pacc_like : bool :=
  match w_2sat_easy with
  | Some m => is_Pacc_like m
  | None => false
  end.

Definition crit_NPbh_like : bool :=
  match w_2sat_crit with
  | Some m => is_NP_blackhole m
  | None => false
  end.

(* === SUMMARY RECORD === *)

Record WitnessSummary := {
  loaded_grid : bool;
  loaded_easy  : bool;
  loaded_crit  : bool;
  label_grid_Pstr : bool;
  label_easy_Pacc : bool;
  label_crit_NPbh : bool
}.

Definition summary : WitnessSummary :=
  {| loaded_grid := grid_loaded;
     loaded_easy := easy_loaded;
     loaded_crit := crit_loaded;
     label_grid_Pstr := grid_P_like;
     label_easy_Pacc := easy_Pacc_like;
     label_crit_NPbh := crit_NPbh_like
  |}.

