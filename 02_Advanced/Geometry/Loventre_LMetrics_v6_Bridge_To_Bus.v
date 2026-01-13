(*
  Loventre_LMetrics_v6_Bridge_To_Bus.v
  Ponte V6 → Metrics_Bus (R record)
  Rocq/Coq 9.1 — Congelamento: Gennaio 2026
*)

From Stdlib Require Import ZArith String Reals.
Open Scope Z_scope.
Open Scope R_scope.

(* Record LMetrics_v6 (intero bus da Python) *)
From Loventre_Advanced.Geometry
     Require Import Loventre_LMetrics_v6_Structure.
Import Loventre_LMetrics_V6_Structure.

(* Record LMetrics (bus formale Ridotto) *)
From Loventre_Advanced
     Require Import Loventre_Metrics_Bus.
Import Loventre_Metrics_Bus.

(* -------------------------------------- *)
(* Conversioni Z -> R                     *)
(* -------------------------------------- *)

Definition z_to_r (z: Z) : R := IZR z.

Definition opt_z_to_r (o: option Z) : R :=
  match o with
  | None => 0%R
  | Some z => IZR z
  end.

(* -------------------------------------- *)
(* Mapping stringhe -> enum               *)
(* -------------------------------------- *)

Definition infer_risk_class (rc: string) : RiskClass :=
  if String.eqb rc "LOW" then RISK_LOW else
  if String.eqb rc "MEDIUM" then RISK_MEDIUM else
  if String.eqb rc "HIGH" then RISK_HIGH else
    RISK_BLACK_HOLE.

(* -------------------------------------- *)
(* V6 --> Bus (R record)                  *)
(* ORDINE CAMPI come nel record LMetrics  *)
(* -------------------------------------- *)

Definition translate_LMetrics_v6 (m: LMetrics_v6) : LMetrics :=
  {|
    (* Curvatura / entropia / barriera *)
    kappa_eff       := opt_z_to_r m.(kappa_eff);
    entropy_eff     := opt_z_to_r m.(entropy_eff);
    V0              := opt_z_to_r m.(V0);
    a_min           := opt_z_to_r m.(a_min);

    (* Tunneling *)
    p_tunnel        := opt_z_to_r m.(p_tunnel);
    P_success       := opt_z_to_r m.(P_success);

    (* Regime temporale — default minimale *)
    gamma_dilation  := opt_z_to_r m.(gamma_dilation);
    time_regime     := time_euclidean;

    (* Massa *)
    mass_eff        := z_to_r m.(mass_eff);
    inertial_idx    := opt_z_to_r m.(inertial_idx);

    (* Rischio *)
    risk_index      := opt_z_to_r m.(risk_index);
    risk_class      := infer_risk_class m.(risk_class);

    (* Compattezza + orizzonte *)
    chi_compactness := opt_z_to_r m.(chi_compactness);
    horizon_flag    := match m.(horizon_flag) with
                       | None => false
                       | Some b => b
                       end
  |}.

Lemma translate_exists :
  forall m: LMetrics_v6,
    exists b: LMetrics, b = translate_LMetrics_v6 m.
Proof. intros m; eauto. Qed.

