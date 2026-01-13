(*
  Loventre_LMetrics_v6_Structure.v
  Struttura LMetrics versione V6 — FULL
  Congelamento: Gennaio 2026
*)

From Stdlib Require Import ZArith String List.
Import ListNotations.

Module Loventre_LMetrics_V6_Structure.

Record LMetrics_v6 : Type :=
{
  (* curvature & entropy *)
  kappa_eff              : option Z;
  entropy_eff            : option Z;

  (* physical synthesis *)
  mass_eff               : Z;
  inertial_idx           : option Z;

  (* risk + classification *)
  risk_index             : option Z;
  risk_class             : string;

  (* global policy output *)
  loventre_global_decision : string;
  loventre_global_color     : string;
  loventre_global_score     : Z;

  (* barrier / potential layer *)
  V0                     : option Z;
  a_min                  : option Z;
  p_tunnel               : option Z;
  P_success              : option Z;

  (* dilation & temporal regime *)
  gamma_dilation         : option Z;
  time_regime            : option string;

  (* meta/tracking *)
  meta_label             : string;
  chi_compactness        : option Z;
  horizon_flag           : option bool;
}.

End Loventre_LMetrics_V6_Structure.

