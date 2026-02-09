(**
  Loventre_LMetrics_Structure.v
  dicembre 2025 — modulo strutturale LMetrics v5.0
*)

From Stdlib Require Import Reals.
Local Open Scope R_scope.

Module Loventre_LMetrics.

  Record LMetrics := {
    kappa_eff        : R;
    entropy_eff      : R;
    V0               : R;
    a_min            : R;
    p_tunnel         : R;
    P_success        : R;
    gamma_dilation   : R;
    time_regime      : R;
    mass_eff         : R;
    inertial_idx     : R;
    risk_index       : R;
    chi_compactness  : R;
    horizon_flag     : R;

    (* ============================================= *)
    (* v5.0 — informational potential (diagnostic)   *)
    (* ============================================= *)
    informational_potential : R
  }.

  (* ====================================================== *)
  (* v5.0 — Axiom diagnostico locale (non fisico)          *)
  (* ====================================================== *)

  Axiom informational_potential_nonneg :
    forall M : LMetrics, informational_potential M >= 0.

End Loventre_LMetrics.

