(* ******************************************************************* *)
(*  Loventre_LMetrics_Witness_CLI.v                                    *)
(*  Witness CLI minimale coerente con il Metrics Bus                   *)
(* ******************************************************************* *)

From Coq Require Import Reals.

From Loventre_Geometry Require Import Loventre_Metrics_Bus.
Module MB := Loventre_Metrics_Bus.

(* Un witness CLI statico, coerente con il Metrics Bus *)
Definition witness_cli : MB.LMetrics :=
  {|
    MB.kappa_eff := 1%R;
    MB.entropy_eff := 1%R;
    MB.V0 := 0%R;
    MB.a_min := 0%R;
    MB.p_tunnel := 0%R;
    MB.P_success := 1%R;
    MB.gamma_dilation := 0%R;
    MB.chi_compactness := 0%R;
    MB.horizon_flag := false
  |}.

Lemma Loventre_LMetrics_Witness_CLI_dummy : True.
Proof. exact I. Qed.

