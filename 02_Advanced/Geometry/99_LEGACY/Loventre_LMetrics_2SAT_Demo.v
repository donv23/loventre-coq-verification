(* ========================================================== *)
(*  LOVENTRE PROJECT — Loventre_LMetrics_2SAT_Demo.v          *)
(*  Dicembre 2025 — Demo di collegamento LMetrics ↔ 2-SAT     *)
(* ========================================================== *)

From Coq Require Import String List.
Import ListNotations.
Local Open Scope string_scope.

Require Import Loventre_LMetrics_JSON_Link.

(** Scopo:
    Verificare che i witness 2-SAT (easy / crit) siano accessibili
    dal ponte LMetrics_JSON_Link e utilizzabili come riferimento Coq. *)

Definition lm_2SAT_easy_path : string :=
  "witness_json/metrics_2SAT_easy_demo.json".

Definition lm_2SAT_crit_path : string :=
  "witness_json/metrics_2SAT_crit_demo.json".

(** Entrambe le definizioni seguenti sono placeholder simbolici
    che in futuro verranno sostituiti da record LMetrics reali. *)

Parameter m_2SAT_easy_demo : Type.
Parameter m_2SAT_crit_demo : Type.

(** Sanity check: Coq conferma la presenza dei due path nei link globali. *)

Definition check_2SAT_links :=
  filter
    (fun link =>
       let id := lm_id_link link in
       orb (String.eqb id "m_2SAT_easy_demo")
           (String.eqb id "m_2SAT_crit_demo"))
    loventre_json_links.

Eval compute in check_2SAT_links.

