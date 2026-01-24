(* ========================================================== *)
(*  LOVENTRE PROJECT — Loventre_LMetrics_JSON_Link_Test.v      *)
(*  Dicembre 2025 — Sanity check del ponte JSON ↔ Coq          *)
(* ========================================================== *)

From Coq Require Import String List.
Import ListNotations.
Local Open Scope string_scope.

Require Import Loventre_LMetrics_JSON_Link.

(** Piccolo test per ispezionare in modo esplicito:           *)
(**  - la lista completa dei link JSON                        *)
(**  - solo i path dei file JSON                              *)

Definition loventre_json_paths : list string :=
  map lm_json_path loventre_json_links.

(* Stampa completa dei link (lm_id + path JSON) *)
Eval compute in loventre_json_links.

(* Solo la lista dei path JSON, per controllo rapido *)
Eval compute in loventre_json_paths.

