(**
  ------------------------------------------------------------------
  Loventre_LMetrics_v8_Policy.v
  Strato Policy Bridge nominale — Canvas 9 (Gennaio 2026)
  ------------------------------------------------------------------
*)

From Stdlib Require Import Reals.
Open Scope R_scope.

From Loventre_Main
     Require Import
       Loventre_Main_Theorem_v8_Prelude
       Loventre_LMetrics_v8_Aliases.

From Loventre_Advanced Require Import Loventre_Metrics_Bus.
Import Loventre_Metrics_Bus.

Set Implicit Arguments.
Unset Strict Implicit.

(**
  Policy locale — classificazione per witness
*)
Definition loventre_local_decision (m : LMetrics) : GlobalDecision :=
  if (Rlt_dec (entropy_eff m) (kappa_eff m)) then INSISTI else VALUTA.

(**
  Policy macro — interpretazione astratta della scelta
*)
Definition loventre_macro_policy (m : LMetrics) : GlobalColor :=
  match loventre_local_decision m with
  | INSISTI => GREEN
  | VALUTA  => AMBER
  | RITIRA  => RED
  end.

(**
  Mapping policy → rischio aggregato
*)
Definition loventre_risk_eval (m : LMetrics) : RiskClass :=
  match loventre_macro_policy m with
  | GREEN => RISK_LOW
  | AMBER => RISK_MEDIUM
  | RED   => RISK_HIGH
  end.

(* Fine file Policy nominale V8 *)

