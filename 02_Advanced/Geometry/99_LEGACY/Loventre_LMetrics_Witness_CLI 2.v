(* ******************************************************************* *)
(* Loventre_LMetrics_Witness_CLI.v                                     *)
(* ******************************************************************* *)

From Coq Require Import Reals.
From Loventre_Geometry Require Import Loventre_Metrics_Bus.
From Loventre_Geometry Require Import Loventre_LMetrics_Complexity_Witness.

Module MB := Loventre_Metrics_Bus.
Module W  := Loventre_LMetrics_Complexity_Witness.

Definition LMetrics := MB.LMetrics.

(* ------------------------------------------------------------------ *)
(* SAFE witness concrete                                              *)
(* ------------------------------------------------------------------ *)

Definition cli_safe : LMetrics :=
  {| MB.kappa_eff       := 0%R;
     MB.entropy_eff     := 0%R;
     MB.V0              := 0%R;
     MB.a_min           := 0%R;
     MB.p_tunnel        := 0%R;
     MB.P_success       := 1%R;
     MB.gamma_dilation  := 0%R;
     MB.chi_compactness := 0%R;
     MB.horizon_flag    := false |}.

(* ------------------------------------------------------------------ *)
(* BLACK witness concrete                                             *)
(* ------------------------------------------------------------------ *)

Definition cli_black : LMetrics :=
  {| MB.kappa_eff       := 100%R;
     MB.entropy_eff     := 50%R;
     MB.V0              := 10%R;
     MB.a_min           := 1%R;
     MB.p_tunnel        := 1%R;
     MB.P_success       := 0%R;
     MB.gamma_dilation  := 10%R;
     MB.chi_compactness := 1%R;
     MB.horizon_flag    := true |}.


