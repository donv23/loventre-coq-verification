(**
  Loventre_v32_JSON_Loader.v
  ==========================
  V32 — Dummy loader: NON implementa IO.
  Restituisce None, con firma corretta.
*)

From Stdlib Require Import List String Reals.
Import ListNotations.

Open Scope string_scope.
Open Scope R_scope.

Require Import Loventre_v32_JSON_Types.
Module JT := Loventre_v32_JSON_Types.

(**
  API finale desiderata:
  load_flatlm_from_json : string -> option (list JT.FlatLM)
*)
Definition load_flatlm_from_json (path : string) : option (list JT.FlatLM) :=
  None.

(**
  Comportamento di fallback: lista vuota.
*)
Definition try_load_flatlm (path : string) : list JT.FlatLM :=
  match load_flatlm_from_json path with
  | Some ms => ms
  | None => []
  end.

