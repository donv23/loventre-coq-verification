(**
  Loventre_v32_JSON_Loader.v
  Decodifica JSON V32 → FlatLM
*)

From Stdlib Require Import String Reals List.
Import ListNotations.
Open Scope string_scope.
Open Scope R_scope.

Require Import Loventre_v32_JSON_Types.

Import JT.

(**
  Finto parser per JSON V32
  (in futuro: sostituire con parser reale)
*)
Definition load_flatlm_from_json (s : string) : option FlatLM :=
  match s with
  | _ =>
      Some {|
        fl_kappa_eff   := 0.42;
        fl_entropy_eff := 0.10;
        fl_V0          := 0.05;
        fl_p_tunnel    := 0.20;
        fl_P_success   := 0.33
      |}
  end.

(**
  Esporta il nome nel namespace globale
*)
Export JT.

