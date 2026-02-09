(* ======================================================= *)
(* LOVENTRE ENGINE v7 — PREDICATES (test minimo)            *)
(* ======================================================= *)

From Stdlib Require Import ZArith Lia.
Local Open Scope Z_scope.

From LMetrics_v7 Require Import
     LMetrics_v7_types
     LMetrics_v7_import
     LMetrics_v7_SAFE_BH.

(* ------------------------------------------------------- *)
(* PREDICATI MINIMALI DI TEST — STESSA API, CORPO BANALIZZATO *)
(* ------------------------------------------------------- *)

Definition is_SAFE_pred (m : LMetricsV7) : Prop :=
  is_SAFE m.

Definition is_BH_pred (m : LMetricsV7) : Prop :=
  is_BH m.

(* Lemma che non crea unfolding perversi *)
Lemma SAFE_or_BH_or_other_minimal :
  forall m, is_SAFE_pred m \/ is_BH_pred m \/ True.
Proof. intros; auto. Qed.

(* Fine file predicati minimale *)

