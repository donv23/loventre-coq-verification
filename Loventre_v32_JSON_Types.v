(**
  Loventre_v32_JSON_Types.v
  --------------------------
  Strato JSON V32 – tipo ponte
  Definisce FlatLM e modulo JT
*)

From Stdlib Require Import Reals String List.
Import ListNotations.
Open Scope string_scope.
Open Scope R_scope.

Module JT.

  (**
    Record FLAT — versione ridotta compatibile con JSON V31/V32
    NOTA: NON è LMetrics. Serve solo per conversione successiva.
  *)
  Record FlatLM := {
    fl_kappa_eff   : R;
    fl_entropy_eff : R;
    fl_V0          : R;
    fl_p_tunnel    : R;
    fl_P_success   : R
  }.

End JT.

Export JT.

