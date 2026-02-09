(**
  Loventre_v32_JSON_Types.v
  --------------------------
  Patch MINIMA per V32
  - Reintroduce un tipo "FlatLM" compatibile con V31
  - Fornito come placeholder per caricare test JSON
*)

From Stdlib Require Import Reals String List.
Import ListNotations.
Open Scope string_scope.
Open Scope R_scope.

Module Loventre_v32_JSON_Types.

  (**
    Record FLAT — versione ridotta, compatibile con JSON
    Corrisponde ai campi principali usati dai loader V31/V32
    NOTA: Questo NON è LMetrics. È solo un tipo ponte.
  *)
  Record FlatLM := {
    fl_kappa_eff   : R;
    fl_entropy_eff : R;
    fl_V0          : R;
    fl_p_tunnel    : R;
    fl_P_success   : R
  }.

End Loventre_v32_JSON_Types.

Export Loventre_v32_JSON_Types.

