(**
  Loventre_Witness_Loader.v
  -------------------------
  Pone a disposizione LMetrics per test/witness V32
*)

From Stdlib Require Import Reals.
Require Import Loventre_v32_JSON_Types.
Require Import Loventre_v32_JSON_Loader.
Require Import Loventre_v32_JSON_To_LMetrics.

Definition witness_v32_metrics :=
  load_lmetrics_from_json.

