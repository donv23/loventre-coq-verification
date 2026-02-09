(**
  Loventre_v32_JSON_Types.v
  -------------------------
  Strutture dati piatte per JSON V32
*)

From Stdlib Require Import Reals String List.
Import ListNotations.
Open Scope string_scope.
Open Scope R_scope.

Module Loventre_v32_JSON_Types.

  (** Flat record proveniente dal JSON
      zero semantica: tutti campi R *)
  Record FlatLM := {
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
    informational_potential : R
  }.

End Loventre_v32_JSON_Types.

