(** 
   Loventre_Test_LMetrics_v9_All.v
   Test minimo per validare compilazione e uso del bus v9
*)

From Stdlib Require Import Reals Bool.Bool.

From Loventre_Advanced Require Import Loventre_Metrics_Bus.
From Loventre_Main Require Import 
     Loventre_LMetrics_v9_SAFE
     Loventre_LMetrics_v9_Aliases
     Loventre_LMetrics_v9_Risk
     Loventre_GlobalDecision_Core
     Loventre_GlobalDecision_View
     Loventre_LMetrics_v9_Policy
     Loventre_LMetrics_v9_MetaDecision
     Loventre_LMetrics_v9_OneShot
.

Import Loventre_Metrics_Bus.

Open Scope R_scope.

(** Dummy instance: tutte le metriche a zero / flag safe.
    Questo è legale, perché LMetrics è un record completamente esplicito.
 *)

Definition m0 : LMetrics :=
  {|
    kappa_eff := 0;
    entropy_eff := 0;
    V0 := 0;
    a_min := 0;

    p_tunnel := 0;
    P_success := 0;

    gamma_dilation := 0;
    time_regime := time_euclidean;  (* costruttore valido v9 *)

    mass_eff := 0;
    inertial_idx := 0;

    risk_index := 0;
    risk_class := risk_low;

    meta_label := meta_unknown;

    chi_compactness := 0;
    horizon_flag := false;

    loventre_global_decision := GD_safe;
    loventre_global_color := GC_green;
    loventre_global_score := 0
  |}.

Lemma test_safe_m0 :
  loventre_is_safe m0 = true.
Proof. reflexivity. Qed.

Lemma test_policy_noop :
  apply_policy_to_metrics m0 = m0.
Proof. reflexivity. Qed.

Lemma test_meta_noop :
  apply_meta_decision_to_metrics m0 = m0.
Proof. reflexivity. Qed.

Lemma test_oneshot_noop :
  loventre_lmetrics_v9_oneshot m0 = m0.
Proof. reflexivity. Qed.

