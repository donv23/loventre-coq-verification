(*
  Loventre_LMetrics_v7_JSON_Seeds.v
  Seed JSON → LMetrics_v7 (CLI bridge minimo + 4 seeds)
  Congelamento: Gennaio 2026
*)

From Stdlib Require Import Reals String Bool.
Open Scope R_scope.

From Loventre_Advanced.Geometry
     Require Import Loventre_LMetrics_v7_Structure.

From Loventre_Advanced.Geometry
     Require Import Loventre_LMetrics_v7_JSON_Importer.

Import Loventre_LMetrics_V7_Structure.

(*
  -----------------------------------------------------------
  Seed JSON minimali generati dal motore Python
  Valori placeholder coerenti con LM_JSON_V7
  -----------------------------------------------------------
*)

Definition json_seed11_v7 : LM_JSON_V7 :=
  {|
    j_kappa_eff       := 1%R;
    j_entropy_eff     := 1%R;
    j_V0              := 1%R;
    j_a_min           := 1%R;
    j_p_tunnel        := 1%R;
    j_P_success       := 1%R;
    j_gamma_dilation  := 1%R;
    j_time_regime     := "SAFE";
    j_mass_eff        := 1%R;
    j_inertial_idx    := 1%R;
    j_risk_index      := 1%R;
    j_risk_class      := "LOW";
    j_chi_compactness := 1%R;
    j_horizon_flag    := false;
    j_meta_label      := "seed11";
    j_global_decision := "GO";
    j_global_color    := "GREEN";
    j_global_score    := 1%R
  |}.

Definition json_TSPcrit28_v7 : LM_JSON_V7 :=
  {|
    j_kappa_eff       := 2%R;
    j_entropy_eff     := 2%R;
    j_V0              := 2%R;
    j_a_min           := 2%R;
    j_p_tunnel        := 2%R;
    j_P_success       := 2%R;
    j_gamma_dilation  := 2%R;
    j_time_regime     := "BH";
    j_mass_eff        := 2%R;
    j_inertial_idx    := 2%R;
    j_risk_index      := 2%R;
    j_risk_class      := "HIGH";
    j_chi_compactness := 2%R;
    j_horizon_flag    := true;
    j_meta_label      := "tsp28";
    j_global_decision := "DROP";
    j_global_color    := "RED";
    j_global_score    := 2%R
  |}.

Definition json_2SAT_easy_v7 : LM_JSON_V7 :=
  {|
    j_kappa_eff       := 0.5%R;
    j_entropy_eff     := 0.5%R;
    j_V0              := 0.5%R;
    j_a_min           := 0.5%R;
    j_p_tunnel        := 0.5%R;
    j_P_success       := 0.5%R;
    j_gamma_dilation  := 0.5%R;
    j_time_regime     := "SAFE";
    j_mass_eff        := 0.5%R;
    j_inertial_idx    := 0.5%R;
    j_risk_index      := 0.5%R;
    j_risk_class      := "LOW";
    j_chi_compactness := 0.5%R;
    j_horizon_flag    := false;
    j_meta_label      := "2sat_easy";
    j_global_decision := "GO";
    j_global_color    := "GREEN";
    j_global_score    := 0.5%R
  |}.

Definition json_2SAT_crit_v7 : LM_JSON_V7 :=
  {|
    j_kappa_eff       := 4%R;
    j_entropy_eff     := 4%R;
    j_V0              := 4%R;
    j_a_min           := 4%R;
    j_p_tunnel        := 4%R;
    j_P_success       := 4%R;
    j_gamma_dilation  := 4%R;
    j_time_regime     := "BH";
    j_mass_eff        := 4%R;
    j_inertial_idx    := 4%R;
    j_risk_index      := 4%R;
    j_risk_class      := "HIGH";
    j_chi_compactness := 4%R;
    j_horizon_flag    := true;
    j_meta_label      := "2sat_crit";
    j_global_decision := "DROP";
    j_global_color    := "RED";
    j_global_score    := 4%R
  |}.

(*
  -----------------------------------------------------------
  Conversione JSON → LMetrics_v7
  -----------------------------------------------------------
*)
Definition m_seed11_v7       : LMetrics_v7 := json_to_v7 json_seed11_v7.
Definition m_TSPcrit28_v7   : LMetrics_v7 := json_to_v7 json_TSPcrit28_v7.
Definition m_2SAT_easy_v7   : LMetrics_v7 := json_to_v7 json_2SAT_easy_v7.
Definition m_2SAT_crit_v7   : LMetrics_v7 := json_to_v7 json_2SAT_crit_v7.

(*
  -----------------------------------------------------------
  Lemma di comprensione: esistenza seed canonici
  -----------------------------------------------------------
*)
Lemma seeds_v7_exist :
  exists s11 tsp28 e2sat c2sat : LMetrics_v7,
    s11 = m_seed11_v7 /\
    tsp28 = m_TSPcrit28_v7 /\
    e2sat = m_2SAT_easy_v7 /\
    c2sat = m_2SAT_crit_v7.
Proof. repeat eexists; repeat split; reflexivity. Qed.

