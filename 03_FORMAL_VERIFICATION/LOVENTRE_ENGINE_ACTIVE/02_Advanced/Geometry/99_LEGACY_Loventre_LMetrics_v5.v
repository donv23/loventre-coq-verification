(**
  Loventre LMetrics — Versione v5.0
  Extended structure con Informational Potential / Flag / Inertia
  (Non modifica la semantica v4, aggiunge solo 3 campi)
*)

From Stdlib Require Import Reals.
Require Import SAFE_Barrier_Structure.

(********************************************************************)
(** Tipi addizionali per Informational Flag                        **)
(********************************************************************)

Inductive InformationalFlag :=
  | info_LOW
  | info_MED
  | info_HIGH.

(********************************************************************)
(** Struttura LMetrics v5                                          **)
(********************************************************************)

Record LMetrics := {
  kappa_eff : R;
  entropy_eff : R;
  V0 : R;
  a_min : R;
  p_tunnel : R;
  P_success : R;
  gamma_dilation : R;

  time_regime : TimeRegime;
  mass_eff : R;
  inertial_idx : R;
  risk_index : R;
  risk_class : RiskClass;
  meta_label : MetaLabel;

  chi_compactness : R;
  horizon_flag : bool;

  loventre_global_decision : GlobalDecision;
  loventre_global_color : GlobalColor;
  loventre_global_score : R;

  (** Nuovi campi v5.0 — Python ↔ Coq Sync **)
  informational_potential : R;
  informational_flag : InformationalFlag;
  informational_inertia : R
}.

(********************************************************************)
(** Lemma diagnostico (non strutturale, solo sanity check)         **)
(********************************************************************)

Lemma informational_flag_is_well_formed :
  forall (M : LMetrics),
    match informational_flag M with
    | info_LOW => True
    | info_MED => True
    | info_HIGH => True
    end.
Proof.
  intro M.
  destruct (informational_flag M); trivial.
Qed.

