(**
  Loventre_v32_JSON_Loader.v
  --------------------------
  Loader dummy V32
  Produce FlatLM da placeholder numerici.
*)

From Stdlib Require Import Reals.
Require Import Loventre_v32_JSON_Types.

Open Scope R_scope.

(**
  load_flat_json
  Per ora: stub deterministico (nessuna IO reale)
*)
Definition load_flat_json : JT.FlatLM :=
  {|
    fl_kappa_eff   := 0.10;
    fl_entropy_eff := 0.20;
    fl_V0          := 0.30;
    fl_p_tunnel    := 0.40;
    fl_P_success   := 0.50
  |}.

