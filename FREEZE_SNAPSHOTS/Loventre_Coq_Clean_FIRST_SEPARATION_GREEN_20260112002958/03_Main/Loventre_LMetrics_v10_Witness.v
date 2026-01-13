(*
  ---------------------------------------------------------
  Loventre_LMetrics_v10_Witness.v
  Tre witness v10 dal motore Python (seed22, seed33, TSPcrit80)
  ---------------------------------------------------------
*)

From Stdlib Require Import Reals Bool String.
Open Scope R_scope.

From Loventre_Advanced Require Import Loventre_Metrics_Bus.
Import Loventre_Metrics_Bus.

Set Implicit Arguments.
Unset Strict Implicit.

Definition m_seed22_v10 : LMetrics :=
  {|
    kappa_eff := 0.2;
    entropy_eff := 0.4;
    V0 := 0.1;
    a_min := 0.0;
    p_tunnel := 0.0;
    P_success := 1.0;
    gamma_dilation := 0.0;
    time_regime := time_euclidean;
    mass_eff := 1.0;
    inertial_idx := 0.2;
    risk_index := 0.2;
    risk_class := risk_low;
    meta_label := meta_P_like_like;
    chi_compactness := 0.0;
    horizon_flag := false;
    loventre_global_decision := GD_safe;
    loventre_global_color := GC_green;
    loventre_global_score := 1.0
  |}.

Definition m_seed33_v10 : LMetrics :=
  {|
    kappa_eff := 0.3;
    entropy_eff := 0.9;
    V0 := 0.2;
    a_min := 0.0;
    p_tunnel := 0.0;
    P_success := 1.0;
    gamma_dilation := 0.0;
    time_regime := time_euclidean;
    mass_eff := 1.0;
    inertial_idx := 0.3;
    risk_index := 0.3;
    risk_class := risk_low;
    meta_label := meta_P_like_like;
    chi_compactness := 0.0;
    horizon_flag := false;
    loventre_global_decision := GD_safe;
    loventre_global_color := GC_green;
    loventre_global_score := 1.0
  |}.

Definition m_TSPcrit80_v10 : LMetrics :=
  {|
    kappa_eff := -0.8;
    entropy_eff := 0.0;
    V0 := 1.0;
    a_min := 0.0;
    p_tunnel := 0.0;
    P_success := 0.0;
    gamma_dilation := 0.0;
    time_regime := time_threshold;
    mass_eff := 1.0;
    inertial_idx := 0.8;
    risk_index := 0.8;
    risk_class := risk_np_like_black_hole;
    meta_label := meta_NP_like_black_hole;
    chi_compactness := 0.0;
    horizon_flag := true;
    loventre_global_decision := GD_invalid;
    loventre_global_color := GC_red;
    loventre_global_score := 0.0
  |}.

Lemma v10_seed22_is_safe :
  loventre_global_decision m_seed22_v10 = GD_safe.
Proof. reflexivity. Qed.

Lemma v10_seed33_is_safe :
  loventre_global_decision m_seed33_v10 = GD_safe.
Proof. reflexivity. Qed.

Lemma v10_tspcrit80_is_blackhole :
  loventre_global_decision m_TSPcrit80_v10 = GD_invalid.
Proof. reflexivity. Qed.

