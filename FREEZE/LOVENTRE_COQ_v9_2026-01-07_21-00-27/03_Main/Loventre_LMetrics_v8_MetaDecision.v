(**
  ------------------------------------------------------------------
  Loventre_LMetrics_v8_MetaDecision.v
  Meta decision layer — Canvas 10 (Gennaio 2026)
  Combina SAFE + POLICY + RISK in un unico ritorno aggregato
  ------------------------------------------------------------------
*)

From Stdlib Require Import Reals.
Open Scope R_scope.

From Loventre_Main
     Require Import
       Loventre_Main_Theorem_v8_Prelude
       Loventre_LMetrics_v8_Aliases
       Loventre_LMetrics_v8_SAFE
       Loventre_LMetrics_v8_Policy
       Loventre_LMetrics_v8_Risk.

From Loventre_Advanced Require Import Loventre_Metrics_Bus.
Import Loventre_Metrics_Bus.

Set Implicit Arguments.
Unset Strict Implicit.

(**
  Meta-Decision: tripla aggregata
  (decisione locale * colore macro * classe di rischio)
*)
Definition loventre_global_decision_v8 (m : LMetrics)
  : GlobalDecision * GlobalColor * RiskClass :=
  let dec := loventre_local_decision m in
  let col := loventre_macro_policy m in
  let ris := loventre_risk_eval m in
  (dec, col, ris).

(* Fine file MetaDecision V8 *)

