(**
  Loventre_v32_JSON_Types.v
  =========================
  V32 — Definizione del tipo FlatLM letto da JSON.
  Corrisponde ai campi JSON V31, senza semantica.
*)

From Stdlib Require Import Reals String.
Open Scope R_scope.
Open Scope string_scope.

Module Loventre_v32_JSON_Types.

  Record FlatLM := {
    fl_kappa_eff        : R;
    fl_entropy_eff      : R;
    fl_V0               : R;
    fl_a_min            : R;
    fl_p_tunnel         : R;
    fl_P_success        : R;
    fl_gamma_dilation   : R;
    fl_time_regime      : R;
    fl_mass_eff         : R;
    fl_inertial_idx     : R;
    fl_risk_index       : R;
    fl_chi_compactness  : R;
    fl_horizon_flag     : R;
    fl_information_potential : R
  }.

End Loventre_v32_JSON_Types.

