(*
  Loventre_LMetrics_JSON_Instance.v
  CANONICO — V50 JSON Bridge

  Questo modulo definisce una struttura di esempio LMetrics caricata da JSON.
*)

From Stdlib Require Import String.
Local Open Scope string_scope.

(* IMPORT CORRETTO — forma piena, nessun "From" *)
Require Import Loventre_JSON.Loventre_LMetrics_JSON_Link.

(* Stub di valori di esempio — saranno poi sostituiti dal loader *)
Definition demo_policy : string := "STABILIZE".
Definition demo_trend  : string := "UNKNOWN".
Definition demo_risk   : string := "MEDIUM".
Definition demo_prog   : string := "UNDEFINED".

Record LMetrics_json_instance := {
  lm_policy_label : string;
  lm_trend_label  : string;
  lm_risk_label   : string;
  lm_prognosis_label : string;
}.

(* istanza iniziale *)
Definition lmetrics_from_json_stub : LMetrics_json_instance :=
  {| lm_policy_label := demo_policy;
     lm_trend_label  := demo_trend;
     lm_risk_label   := demo_risk;
     lm_prognosis_label := demo_prog;
  |}.

(* micro prova *)
Definition stub_trend := lm_trend_label lmetrics_from_json_stub.

