(**
  Loventre_Test_LMetrics_Raw_Import_v1.v
  Gennaio 2026 — V60c minimal test
*)

From Loventre_Core Require Import Loventre_LMetrics_Core.
From Loventre_Advanced.Geometry Require Import
     Loventre_LMetrics_Phase_Predicates.

Open Scope bool_scope.

(* LMetrics test sample, manually lifted from ACCESS witness *)

Definition sample_lmetrics : LMetrics :=
  {|
    kappa_eff := 0.52 ;
    entropy_eff := 0.38 ;
    V0 := 0.49 ;
    p_tunnel := 0.55 ;

    time_regime := Normal ;
    horizon_flag := false ;
    chi_compactness := 0 ;
    risk_index := 0 ;
  |}.

Goal is_P_like sample_lmetrics = false.
Proof. reflexivity. Qed.

Goal is_accessible_like sample_lmetrics = true.
Proof. reflexivity. Qed.

Goal is_NP_blackhole_like sample_lmetrics = false.
Proof. reflexivity. Qed.

Print sample_lmetrics.

