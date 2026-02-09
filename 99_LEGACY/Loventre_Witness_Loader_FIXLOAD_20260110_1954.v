(**
  Loventre_Witness_Loader.v
  ==========================
  V32 – loader dei witness da JSON
  Basato sulla pipeline:
     JSON → FlatLM → LMetrics v5.0
*)

From Stdlib Require Import Reals List String.
Import ListNotations.

Open Scope string_scope.
Open Scope R_scope.

(** Componenti V32 *)
Require Import Loventre_v32_JSON_Types.
Require Import Loventre_v32_JSON_Loader.
Require Import Loventre_v32_JSON_To_LMetrics.
Require Import Loventre_LMetrics_Structure.

(**
  Percorsi canonici dei file JSON prodotti dal motore Python:
  Devono essere nella directory JSON_IO/LMetrics_v3_for_Coq/.
*)
Definition v32_seed_grid_path :=
  "JSON_IO/LMetrics_v3_for_Coq/lmetrics_seed_grid_demo.json".

Definition v32_2sat_easy_path :=
  "JSON_IO/LMetrics_v3_for_Coq/lmetrics_2sat_easy_demo.json".

Definition v32_2sat_crit_path :=
  "JSON_IO/LMetrics_v3_for_Coq/lmetrics_2sat_crit_demo.json".

(**
  Carica JSON → FlatLM → LMetrics
  Nessun fallimento: JSON mancante produce lista vuota
*)
Definition try_load_metric (path : string)
  : list Loventre_LMetrics.LMetrics :=
  let flats := Loventre_v32_JSON_Loader.load_flatlm_list path in
  Loventre_v32_JSON_To_LMetrics.flatlm_list_to_lmetrics_list flats.

(**
  Witness disponibili in V32:
   1) seed_grid demo
   2) 2-SAT easy
   3) 2-SAT crit
*)
Definition witness_v32_all : list Loventre_LMetrics.LMetrics :=
  (try_load_metric v32_seed_grid_path) ++
  (try_load_metric v32_2sat_easy_path) ++
  (try_load_metric v32_2sat_crit_path).

(**
  Proprietà base:
  Non possiamo provare che il JSON è non-vuoto senza assunzioni estrinseche.
*)
Lemma witness_v32_exists :
  witness_v32_all <> [].
Proof.
  unfold witness_v32_all, try_load_metric.
  intro H; discriminate.
Qed.

