(**
  Loventre_v32_JSON_To_LMetrics.v
  Convertitore JSON→FlatLM→LMetrics usando il record canonico v5
*)

From Stdlib Require Import Reals String.
Local Open Scope R_scope.
Open Scope string_scope.

Require Import Loventre_v32_JSON_Types.
Require Import Loventre_v32_JSON_Loader.
Require Import Loventre_LMetrics_Structure.

Import Loventre_LMetrics.

(**
  Convertitore FlatLM → LMetrics
*)
Definition flatlm_to_lmetrics (fl : JT.FlatLM) : LMetrics :=
  {|
    kappa_eff            := fl.(JT.fl_kappa_eff);
    entropy_eff          := fl.(JT.fl_entropy_eff);
    V0                   := fl.(JT.fl_V0);
    a_min                := 0%R;
    p_tunnel             := fl.(JT.fl_p_tunnel);
    P_success            := fl.(JT.fl_P_success);
    gamma_dilation       := 0%R;
    time_regime          := 0%R;
    mass_eff             := 0%R;
    inertial_idx         := 0%R;
    risk_index           := 0%R;
    chi_compactness      := 0%R;
    horizon_flag         := 0%R;
    informational_potential := fl.(JT.fl_kappa_eff) + fl.(JT.fl_entropy_eff)
  |}.

(**
  Wrapper JSON→LMetrics
*)
Definition load_lmetrics_from_json (s : string) : option LMetrics :=
  match load_flatlm_from_json s with
  | Some fl => Some (flatlm_to_lmetrics fl)
  | None => None
  end.

