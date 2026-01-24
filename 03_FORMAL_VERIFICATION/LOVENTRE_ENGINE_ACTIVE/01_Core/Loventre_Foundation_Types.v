From Stdlib Require Import List Arith String.
Import ListNotations.

From Loventre_Core Require Import Loventre_Kernel.

(** =============================== *)
(** LOVENTRE FOUNDATION - TYPES V3  *)
(** =============================== *)

Inductive RiskClass :=
| risk_LOW
| risk_MID
| risk_NP_like_black_hole.

Inductive MetaLabel :=
| meta_P_like_like
| meta_P_like_accessible
| meta_NP_like_black_hole.

Record LMetrics_JSON_Link := {
  lm_id_link : string;
  lm_json_path : string;
  risk_class : RiskClass;
  meta_label : MetaLabel
}.

(** Integrazione con il kernel di base *)
Definition lm_default : LMetrics_JSON_Link :=
  {|
    lm_id_link := "default";
    lm_json_path := "none";
    risk_class := risk_LOW;
    meta_label := meta_P_like_like
  |}.

