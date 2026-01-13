(*
  Loventre_LMetrics_JSON_Instance.v
  Carica un record minimale dal JSON riscritto via V42
  e lo istanzia come parametro (per ora DATA-SIDE ONLY).
*)
From Stdlib Require Import String List.

From Loventre_JSON Require Import Loventre_LMetrics_JSON_Link.

Open Scope string_scope.

Record LMetrics_Record := {
  trend_label      : string;
  risk_label       : string;
  prognosis_label  : string;
  instability_flag : bool;
  recovery_flag    : bool;
}.

Definition v50_from_json : LMetrics_Record :=
  {|
    trend_label := "UNKNOWN";
    risk_label := "MEDIUM";
    prognosis_label := "UNDEFINED";
    instability_flag := true;
    recovery_flag := false;
  |}.

Definition show_v50 :=
  (trend_label v50_from_json,
   risk_label v50_from_json,
   prognosis_label v50_from_json).

