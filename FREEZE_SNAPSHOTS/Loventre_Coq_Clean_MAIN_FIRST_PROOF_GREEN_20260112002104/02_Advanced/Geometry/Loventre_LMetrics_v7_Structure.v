(*
  Loventre_LMetrics_v7_Structure.v
  Struttura LMetrics versione V7 — coerente con Sanity e Bridge
  Congelamento: Gennaio 2026
*)

From Stdlib Require Import Reals String.
Open Scope R_scope.

Module Loventre_LMetrics_V7_Structure.

(*
  Versione V7 del bus LMetrics.
  Tutti i campi numerici sono reali (R),
  per compatibilità con lra e la fase di Sanity.
*)

Record LMetrics_v7 : Type := {
  (* Curvatura / entropia / barriera *)
  v7_kappa_eff       : R;
  v7_entropy_eff     : R;
  v7_V0              : R;
  v7_a_min           : R;

  (* Tunneling *)
  v7_p_tunnel        : R;
  v7_P_success       : R;

  (* Regime temporale *)
  v7_gamma_dilation  : R;
  v7_time_regime     : string;

  (* Massa / inerzia *)
  v7_mass_eff        : R;
  v7_inertial_idx    : R;

  (* Rischio aggregato *)
  v7_risk_index      : R;
  v7_risk_class      : string;

  (* Compattezza e orizzonte *)
  v7_chi_compactness : R;
  v7_horizon_flag    : bool;

  (* Metadati e policy *)
  v7_meta_label      : string;
  v7_global_decision : string;
  v7_global_color    : string;
  v7_global_score    : R
}.

End Loventre_LMetrics_V7_Structure.

