(**
  Loventre_v32_JSON_To_LMetrics.v
  -------------------------------
  Conversione FlatLM → LMetrics (mappaggio parziale v32)
*)

From Stdlib Require Import Reals.
Require Import Loventre_v32_JSON_Types.
Require Import Loventre_v32_JSON_Loader.
Require Import Loventre_LMetrics_Structure.

Open Scope R_scope.

(**
  Mappa FlatLM in LMetrics
  I campi non presenti in FlatLM vengono valorizzati con placeholder 0.0
*)
Definition flatlm_to_lmetrics (F : JT.FlatLM) : Loventre_LMetrics.LMetrics :=
  {|
    Loventre_LMetrics.kappa_eff        := JT.fl_kappa_eff F;
    Loventre_LMetrics.entropy_eff      := JT.fl_entropy_eff F;
    Loventre_LMetrics.V0               := JT.fl_V0 F;
    Loventre_LMetrics.a_min            := 0.0;
    Loventre_LMetrics.p_tunnel         := JT.fl_p_tunnel F;
    Loventre_LMetrics.P_success        := JT.fl_P_success F;
    Loventre_LMetrics.gamma_dilation   := 0.0;
    Loventre_LMetrics.time_regime      := 0.0;
    Loventre_LMetrics.mass_eff         := 0.0;
    Loventre_LMetrics.inertial_idx     := 0.0;
    Loventre_LMetrics.risk_index       := 0.0;
    Loventre_LMetrics.chi_compactness  := 0.0;
    Loventre_LMetrics.horizon_flag     := 0.0;
    Loventre_LMetrics.informational_potential := 0.0
  |}.

Definition load_lmetrics_from_json : Loventre_LMetrics.LMetrics :=
  flatlm_to_lmetrics load_flat_json.

