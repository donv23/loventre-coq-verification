(**
  Loventre_LMetrics_Structure.v
  gennaio 2026 — V84.2.3
  Unificazione struttura LMetrics senza duplicazioni.
*)

From Stdlib Require Import Reals.Rdefinitions Reals.Raxioms.

(* ================================ *)
(* === Re-export LMetrics Core  === *)
(* ================================ *)

From Loventre_Advanced Require Export Loventre_LMetrics_Core.

(* --------------------------------------------------------------- *)
(* Proprietà aggiuntive NON strutturali                            *)
(* --------------------------------------------------------------- *)

(* In v5.0 la proprietà informazionale diagnostica non è più un campo
   del record. Manteniamo un placeholder debole e coerente. *)

Definition MetricNonneg (M : LMetrics) : Prop :=
  Rge (kappa_eff M) 0%R /\ Rge (entropy_eff M) 0%R.

Axiom metric_nonneg_axiom :
  forall M : LMetrics, MetricNonneg M.

