(**
  Loventre_v32_JSON_To_LMetrics.v
  ===============================
  Conversione FlatLM → LMetrics (record ricco).
*)

From Stdlib Require Import Reals.
Open Scope R_scope.

Require Import Loventre_v32_JSON_Types.
Require Import Loventre_v32_JSON_Loader.
Require Import Loventre_LMetrics_Structure.

Module JT := Loventre_v32_JSON_Types.
Module JL := Loventre_v32_JSON_Loader.
Module LM := Loventre_LMetrics.

(**
  Converte un singolo FlatLM nel record LMetrics ricco.
*)
Definition flatlm_to_lmetrics (f : JT.FlatLM) : LM.LMetrics :=
  LM.Build_LMetrics
    (JT.fl_kappa_eff f)
    (JT.fl_entropy_eff f)
    (JT.fl_V0 f)
    (JT.fl_a_min f)
    (JT.fl_p_tunnel f)
    (JT.fl_P_success f)
    (JT.fl_gamma_dilation f)
    (JT.fl_time_regime f)
    (JT.fl_mass_eff f)
    (JT.fl_inertial_idx f)
    (JT.fl_risk_index f)
    (JT.fl_chi_compactness f)
    (JT.fl_horizon_flag f)
    (JT.fl_information_potential f).

