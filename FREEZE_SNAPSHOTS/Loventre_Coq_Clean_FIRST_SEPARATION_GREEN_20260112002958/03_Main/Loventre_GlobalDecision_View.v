(*
  ---------------------------------------------------------
  Loventre_GlobalDecision_View.v
  Stub V9 — Vista minimale su GlobalDecision e GlobalColor
  ---------------------------------------------------------
*)

From Stdlib Require Import Reals Bool String.
Open Scope R_scope.

From Loventre_Advanced Require Import Loventre_Metrics_Bus.
Import Loventre_Metrics_Bus.

(*
  ---------------------------------------------------------
  Vista su GlobalDecision
  ---------------------------------------------------------
*)

Definition loventre_decision (m : LMetrics) : GlobalDecision :=
  loventre_global_decision m.

(*
  ---------------------------------------------------------
  Vista su GlobalColor
  ---------------------------------------------------------
*)

Definition loventre_color (m : LMetrics) : GlobalColor :=
  loventre_global_color m.

(*
  ---------------------------------------------------------
  Vista su score globale
  ---------------------------------------------------------
*)

Definition loventre_score (m : LMetrics) : R :=
  loventre_global_score m.

(*
  ---------------------------------------------------------
  Fine file — Stub minimale
  ---------------------------------------------------------
*)

