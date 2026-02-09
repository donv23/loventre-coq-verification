(*
  Axis F — 3SAT Witnesses (LAB)
  =============================

  Purpose:
  --------
  Provide Coq-side witnesses corresponding to existing JSON metrics:

    - m_3SAT_crit_demo.json
    - m_3SAT_easy_demo.json

  IMPORTANT:
  ----------
  - LAB ONLY
  - No lemmas
  - No claims about P vs NP
  - No dependency on CANON proofs
  - These definitions exist ONLY to align JSON ↔ Coq identifiers
*)

From Loventre_Advanced.Geometry Require Import Loventre_LMetrics_Types.

(* ------------------------------------------------------------ *)
(* 3SAT — critical instance (structural black hole)             *)
(* ------------------------------------------------------------ *)

Definition m_3SAT_crit_demo : LMetrics :=
  {|
    kappa_eff := -0.92;
    entropy_eff := 0.91;
    V0 := 1.25;
    a_min := 0.02;
    p_tunnel := 1.0e-8;
    P_success := 0.0;
    gamma_dilation := 3.5;
    time_regime := time_hyperbolic;
    mass_eff := 9.8;
    inertial_idx := 9.5;
    risk_index := 9.7;
    risk_class := risk_NP_like_black_hole;
    meta_label := meta_NP_like_black_hole;
    chi_compactness := 0.96;
    horizon_flag := true;
    loventre_global_decision := GD_invalid;
    loventre_global_color := GC_red;
    loventre_global_score := 1.0;
  |}.

(* ------------------------------------------------------------ *)
(* 3SAT — easy instance (locally accessible)                    *)
(* ------------------------------------------------------------ *)

Definition m_3SAT_easy_demo : LMetrics :=
  {|
    kappa_eff := 0.15;
    entropy_eff := 0.42;
    V0 := 0.18;
    a_min := 0.6;
    p_tunnel := 0.65;
    P_success := 1.0;
    gamma_dilation := 1.0;
    time_regime := time_euclidean;
    mass_eff := 1.1;
    inertial_idx := 1.0;
    risk_index := 1.2;
    risk_class := risk_LOW;
    meta_label := meta_P_like_like;
    chi_compactness := 0.18;
    horizon_flag := false;
    loventre_global_decision := GD_invalid;
    loventre_global_color := GC_green;
    loventre_global_score := 0.9;
  |}.

(*
  Design notes:
  -------------
  - Both witnesses are descriptive only.
  - The coexistence of easy / hard instances for NP-classical problems
    is intentional and supports Axis F.
  - No implication is asserted or proven here.
*)

