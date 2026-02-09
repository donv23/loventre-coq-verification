(**
  Loventre_v32_JSON_To_LMetrics.v
  --------------------------------
  Passo 3: conversione FlatLM -> LMetrics
  Nessuna logica di classe, nessun SAFE.
*)

From Stdlib Require Import Reals List String.
Import ListNotations.
Open Scope string_scope.
Open Scope R_scope.

Require Import Loventre_v32_JSON_Types.
Require Import Loventre_v32_JSON_Loader.
Require Import Loventre_LMetrics_Structure.

Module Loventre_v32_JSON_To_LMetrics.

  Module LM := Loventre_LMetrics.
  Module JT := Loventre_v32_JSON_Types.
  Module JL := Loventre_v32_JSON_Loader.

  (** Conversione FlatLM -> LMetrics *)
  Definition flatlm_to_lm (f : JT.FlatLM) : LM.LMetrics :=
    {|
      LM.kappa_eff        := JT.kappa_eff f ;
      LM.entropy_eff      := JT.entropy_eff f ;
      LM.V0               := JT.V0 f ;
      LM.a_min            := JT.a_min f ;
      LM.p_tunnel         := JT.p_tunnel f ;
      LM.P_success        := JT.P_success f ;
      LM.gamma_dilation   := JT.gamma_dilation f ;
      LM.time_regime      := JT.time_regime f ;
      LM.mass_eff         := JT.mass_eff f ;
      LM.inertial_idx     := JT.inertial_idx f ;
      LM.risk_index       := JT.risk_index f ;
      LM.chi_compactness  := JT.chi_compactness f ;
      LM.horizon_flag     := JT.horizon_flag f ;
      LM.informational_potential :=
        JT.informational_potential f   (* Se manca nei JSON rimane 0 *)
    |}.

  (** Converte lista option FlatLM -> lista LMetrics *)
  Definition map_flatlm_to_lm (opt_f : option (list JT.FlatLM))
    : list LM.LMetrics :=
    match opt_f with
    | None => []
    | Some xs => map flatlm_to_lm xs
    end.

  (** Nuovo entrypoint V32 — type LMetrics *)
  Definition load_lmetrics_from_json (path : string)
    : list LM.LMetrics :=
    map_flatlm_to_lm (JL.load_flatlm_from_json path).

End Loventre_v32_JSON_To_LMetrics.

