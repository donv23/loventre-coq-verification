(* ************************************************************** *)
(* Loventre_SAT_TSP_Critical_Metrics.v                            *)
(* Seed dicembre 2025 – versione coerente con Phase_Predicates   *)
(* ************************************************************** *)

From Coq Require Import Reals.
From Loventre_Geometry Require Import Loventre_Metrics_Bus.

Module MB := Loventre_Metrics_Bus.

Definition LMetrics := MB.LMetrics.

(* ------------------------------------------------------------- *)
(*   Witness SAT/TSP 16                                          *)
(* ------------------------------------------------------------- *)

Definition SAT_TSPcrit16_witness (m:LMetrics) : Prop :=
  (Rgt m.(MB.gamma_dilation) m.(MB.kappa_eff)) /\
  (m.(MB.horizon_flag) = true).

Theorem SAT_TSPcrit16_has_horizon :
  forall m, SAT_TSPcrit16_witness m -> m.(MB.horizon_flag) = true.
Proof.
  intros m H. unfold SAT_TSPcrit16_witness in H. tauto.
Qed.

(* ------------------------------------------------------------- *)
(*   Witness SAT/TSP 28                                          *)
(* ------------------------------------------------------------- *)

Definition SAT_TSPcrit28_witness (m:LMetrics) : Prop :=
  (m.(MB.horizon_flag) = true) /\
  (Rlt m.(MB.P_success) m.(MB.p_tunnel)).

Theorem SAT_TSPcrit28_has_horizon :
  forall m, SAT_TSPcrit28_witness m -> m.(MB.horizon_flag) = true.
Proof.
  intros m H. unfold SAT_TSPcrit28_witness in H. tauto.
Qed.

