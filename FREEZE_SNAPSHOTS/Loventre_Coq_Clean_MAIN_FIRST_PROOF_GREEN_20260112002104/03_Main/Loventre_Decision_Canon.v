(**
  Loventre_Decision_Canon.v
  Punto di accesso canonico alla decisione Loventre
  FASE 1.5 — dicembre 2025
*)

From Loventre_Advanced.Geometry Require Import
  Loventre_LMetrics_Structure
  Loventre_LMetrics_Decision.

(* ===================================================== *)
(* === Alias canonici esportati verso il Main Stack   === *)
(* ===================================================== *)

Definition LoventreDecision := Loventre_LMetrics_Decision.LoventreDecision.

Definition decision_of_LMetrics :=
  Loventre_LMetrics_Decision.decision_of_metrics.

