(**
  ------------------------------------------------------------------
  Loventre_Main_Theorem_v8_Citable.v
  Canvas 11 — wrapper "citabile"
  Gennaio 2026
  Espone una vista compatta del Teorema V8:
  JSON/Bus v7 → SAFE → POLICY → RISK → META → AGGREGATORE.
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
       Loventre_LMetrics_v8_Risk
       Loventre_LMetrics_v8_MetaDecision
       Loventre_Main_Theorem_v8_All_In_One.

From Loventre_Advanced Require Import Loventre_Metrics_Bus.
Import Loventre_Metrics_Bus.

Set Implicit Arguments.
Unset Strict Implicit.

(**
  Dichiarazione compatta:
  La tripla aggregata V8 è sempre definita per ogni `LMetrics`.
*)
Theorem Loventre_Main_Theorem_v8_Citable :
  forall (m : LMetrics),
    exists (d : GlobalDecision) (c : GlobalColor) (r : RiskClass),
      loventre_global_decision_v8 m = (d, c, r).
Proof.
  intros m.
  unfold loventre_global_decision_v8.
  remember (loventre_local_decision m) as d.
  remember (loventre_macro_policy m) as c.
  remember (loventre_risk_eval m) as r.
  exists d, c, r.
  reflexivity.
Qed.

(**
  Punto di uscita pubblico V8
  (versione citabile/sintetica)
*)

