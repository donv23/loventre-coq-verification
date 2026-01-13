(*
  Loventre_LMetrics_v6_to_v7.v
  Normalizzazione completa LMetrics_v6 → LMetrics_v7
  Stato: Gennaio 2026
*)

From Stdlib Require Import ZArith String Reals Bool.
Open Scope Z_scope.
Open Scope R_scope.

(* ===================================== *)
(* Strutture V6 e V7                     *)
(* ===================================== *)
From Loventre_Advanced.Geometry
     Require Import Loventre_LMetrics_v6_Structure
                    Loventre_LMetrics_v7_Structure.
Import Loventre_LMetrics_V6_Structure.
Import Loventre_LMetrics_V7_Structure.

(* ===================================== *)
(* Bus v3 (usiamo solo prefissi)         *)
(* ===================================== *)
From Loventre_Advanced
     Require Import Loventre_Metrics_Bus.
(* NOTA: NON facciamo Import Loventre_Metrics_Bus. *)

(* ===================================== *)
(* Conversioni                          *)
(* ===================================== *)

Definition z_to_r (z: Z) : R := IZR z.

Definition opt_z_to_r (o: option Z) : R :=
  match o with
  | None => 0%R
  | Some z => IZR z
  end.

(* String -> RiskClass *)
Definition infer_risk_class (rc: string) : Loventre_Metrics_Bus.RiskClass :=
  if String.eqb rc "LOW" then Loventre_Metrics_Bus.RISK_LOW else
  if String.eqb rc "MEDIUM" then Loventre_Metrics_Bus.RISK_MEDIUM else
  if String.eqb rc "HIGH" then Loventre_Metrics_Bus.RISK_HIGH else
    Loventre_Metrics_Bus.RISK_BLACK_HOLE.

(* String -> GlobalDecision *)
Definition infer_global_decision (s: string) : Loventre_Metrics_Bus.GlobalDecision :=
  if String.eqb s "INSISTI" then Loventre_Metrics_Bus.INSISTI else
  if String.eqb s "VALUTA" then Loventre_Metrics_Bus.VALUTA else
    Loventre_Metrics_Bus.RITIRA.

(* String -> GlobalColor *)
Definition infer_global_color (s: string) : Loventre_Metrics_Bus.GlobalColor :=
  if String.eqb s "GREEN" then Loventre_Metrics_Bus.GREEN else
  if String.eqb s "AMBER" then Loventre_Metrics_Bus.AMBER else
    Loventre_Metrics_Bus.RED.

(* MetaLabel – placeholder *)
Definition infer_meta_label (_s: string) : Loventre_Metrics_Bus.MetaLabel :=
  Loventre_Metrics_Bus.P_like_accessibile.

(* time_regime da option string robusto *)
Definition infer_time_regime (sopt: option string) : Loventre_Metrics_Bus.TimeRegime :=
  match sopt with
  | Some s =>
      if String.eqb s "hyperbolic" then Loventre_Metrics_Bus.time_hyperbolic else
      if String.eqb s "threshold" then Loventre_Metrics_Bus.time_threshold else
        Loventre_Metrics_Bus.time_euclidean
  | None => Loventre_Metrics_Bus.time_euclidean
  end.

(* ===================================== *)
(* Normalizzazione V6 → V7               *)
(* ===================================== *)

Definition translate_LMetrics_v6_to_v7 (m: LMetrics_v6) : LMetrics_v7 :=
  {|
    v7_kappa_eff          := opt_z_to_r (kappa_eff m);
    v7_entropy_eff        := opt_z_to_r (entropy_eff m);
    v7_V0                 := opt_z_to_r (V0 m);
    v7_a_min              := opt_z_to_r (a_min m);

    v7_p_tunnel           := opt_z_to_r (p_tunnel m);
    v7_P_success          := opt_z_to_r (P_success m);

    v7_gamma_dilation     := opt_z_to_r (gamma_dilation m);
    v7_time_regime        := infer_time_regime (time_regime m);

    v7_mass_eff           := z_to_r (mass_eff m);
    v7_inertial_idx       := opt_z_to_r (inertial_idx m);

    v7_risk_index         := opt_z_to_r (risk_index m);
    v7_risk_class         := infer_risk_class (risk_class m);

    v7_chi_compactness    := opt_z_to_r (chi_compactness m);
    v7_horizon_flag       :=
      match (horizon_flag m) with
      | None => false
      | Some b => b
      end;

    v7_loventre_global_decision :=
      infer_global_decision (loventre_global_decision m);
    v7_loventre_global_color :=
      infer_global_color (loventre_global_color m);
    v7_loventre_global_score :=
      z_to_r (loventre_global_score m);

    v7_meta_label :=
      infer_meta_label (meta_label m)
  |}.

Lemma translate_v6_v7_exists :
  forall m: LMetrics_v6,
    exists b: LMetrics_v7, b = translate_LMetrics_v6_to_v7 m.
Proof. intros m; eauto. Qed.

