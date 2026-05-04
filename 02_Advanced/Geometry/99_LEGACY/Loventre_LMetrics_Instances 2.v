(* *************************************************************** *)
(* Loventre_LMetrics_Instances.v                                   *)
(* *************************************************************** *)

From Coq Require Import Reals.

From Loventre_Geometry Require Import Loventre_Metrics_Bus.
Module MB := Loventre_Metrics_Bus.

From Loventre_Geometry Require Import Loventre_LMetrics_Phase_Predicates.
Module PP := Loventre_LMetrics_Phase_Predicates.

(* Alias locale per il record metriche *)
Definition LMetrics := MB.LMetrics.

(* Witness CLI (dummy) *)
Definition witness_cli : LMetrics :=
  {| MB.kappa_eff       := 1%R;
     MB.entropy_eff     := 0.5%R;
     MB.V0              := 0.1%R;
     MB.a_min           := 1%R;
     MB.p_tunnel        := 0.2%R;
     MB.P_success       := 0.9%R;
     MB.gamma_dilation  := 1.0%R;
     MB.chi_compactness := 0.0%R;
     MB.horizon_flag    := false
  |}.

(* Stub minimo: esistenza di almeno una metrica *)
Lemma instance_exists : exists m: LMetrics, True.
Proof.
  exists witness_cli. trivial.
Qed.

