(*
  Loventre_LMetrics_v7_to_Bus.v
  Ponte V7 → Metrics_Bus (record ridotto LMetrics)
  Congelamento: Gennaio 2026
*)

From Stdlib Require Import String Reals.
Open Scope R_scope.

(* Record LMetrics_v7 già normalizzato a R/string/bool *)
From Loventre_Advanced.Geometry
     Require Import Loventre_LMetrics_v7_Structure.
Import Loventre_LMetrics_V7_Structure.

(* Record LMetrics ridotto del Bus globale *)
From Loventre_Advanced
     Require Import Loventre_Metrics_Bus.
Import Loventre_Metrics_Bus.

(* ------------------------------------------------------- *)
(* STRING → TimeRegime mapping (fallback EUCLIDEAN)        *)
(* ------------------------------------------------------- *)

Definition decode_time_regime (s : string) : TimeRegime :=
  if String.eqb s "EUCLIDEAN"
  then time_euclidean
  else if String.eqb s "THRESHOLD"
  then time_threshold
  else if String.eqb s "HYPERBOLIC"
  then time_hyperbolic
  else time_euclidean.

(* ------------------------------------------------------- *)
(* STRING → RiskClass mapping (fallback BLACK_HOLE)        *)
(* ------------------------------------------------------- *)

Definition decode_risk_class (s : string) : RiskClass :=
  if String.eqb s "LOW"
  then RISK_LOW
  else if String.eqb s "MEDIUM"
  then RISK_MEDIUM
  else if String.eqb s "HIGH"
  then RISK_HIGH
  else RISK_BLACK_HOLE.

(* ------------------------------------------------------- *)
(* V7 → Bus (R record)                                     *)
(* ------------------------------------------------------- *)

Definition translate_LMetrics_v7_to_bus (m : LMetrics_v7)
  : LMetrics :=
  {|
    (* Curvatura / entropia / barriera *)
    kappa_eff       := m.(v7_kappa_eff);
    entropy_eff     := m.(v7_entropy_eff);
    V0              := m.(v7_V0);
    a_min           := m.(v7_a_min);

    (* Tunneling *)
    p_tunnel        := m.(v7_p_tunnel);
    P_success       := m.(v7_P_success);

    (* Regime temporale *)
    gamma_dilation  := m.(v7_gamma_dilation);
    time_regime     := decode_time_regime m.(v7_time_regime);

    (* Massa *)
    mass_eff        := m.(v7_mass_eff);
    inertial_idx    := m.(v7_inertial_idx);

    (* Rischio *)
    risk_index      := m.(v7_risk_index);
    risk_class      := decode_risk_class m.(v7_risk_class);

    (* Compattezza / Orizzonte *)
    chi_compactness := m.(v7_chi_compactness);
    horizon_flag    := m.(v7_horizon_flag)
  |}.

(* ------------------------------------------------------- *)
(* Esistenza triviale                                       *)
(* ------------------------------------------------------- *)

Lemma translate_v7_exists :
  forall m : LMetrics_v7,
    exists b : LMetrics, b = translate_LMetrics_v7_to_bus m.
Proof. intros m; eauto. Qed.

