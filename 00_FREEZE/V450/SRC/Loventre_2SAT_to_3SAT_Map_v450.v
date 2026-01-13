(***************************************************************************)
(* Loventre 2SAT → 3SAT Mapping - V450                                     *)
(* Autore: Vincenzo Loventre                                               *)
(* Scopo: ponte concettuale, non riduzione completa                        *)
(***************************************************************************)

From Loventre_Core Require Import Loventre_Core_Prelude.
From Loventre_Advanced Require Import
  Loventre_LMetrics_Core
  Loventre_Metrics_Bus
  Loventre_SAFE_Model
  Loventre_Class_Model
  Loventre_Phase_Assembly
.
From Loventre_Advanced.Geometry Require Import
  Loventre_LMetrics_Phase_Predicates
  Loventre_LMetrics_Structure
.

(***************************************************************************)
(* Definizione: mapping astratto 2SAT→3SAT                                 *)
(* Nel modello Loventre: sempice identity con “penalità minima”            *)
(* Possibile estensione con curva/entropia in futuro                       *)
(***************************************************************************)

Definition Map_2SAT_to_3SAT (M : LMetrics) : LMetrics :=
  {| kappa_eff      := kappa_eff M + 0;   (* placeholder *)
     entropy_eff    := entropy_eff M + 0; (* placeholder *)
     V0             := V0 M;
     p_tunnel       := p_tunnel M;
     P_success      := P_success M;
     gamma_dilation := gamma_dilation M;
     time_regime    := time_regime M;
     mass_eff       := mass_eff M;
     inertial_idx   := inertial_idx M;
     risk_index     := risk_index M;
     risk_class     := risk_class M;
     chi_compactness := chi_compactness M;
     horizon_flag   := horizon_flag M
  |}.

(***************************************************************************)
(* Lemma: SAFE preservato                                                  *)
(***************************************************************************)

Lemma map_preserves_SAFE :
  forall M,
    In_Safe_Loventre M ->
    In_Safe_Loventre (Map_2SAT_to_3SAT M).
Proof.
  intros M Hs.
  exact Hs.
Qed.

(***************************************************************************)
(* Lemma: P_like preservato                                                *)
(***************************************************************************)

Lemma map_preserves_P_like :
  forall M,
    In_P_like_Loventre M ->
    In_P_like_Loventre (Map_2SAT_to_3SAT M).
Proof.
  intros M Hp.
  exact Hp.
Qed.

(***************************************************************************)
(* Mini-teorema composito                                                  *)
(***************************************************************************)

Theorem twoSAT_to_threeSAT_safety_backbone :
  forall M,
    In_P_like_Loventre M ->
    In_Safe_Loventre M ->
    In_P_like_Loventre (Map_2SAT_to_3SAT M)
    /\ In_Safe_Loventre (Map_2SAT_to_3SAT M).
Proof.
  intros M Hp Hs.
  split.
  - apply map_preserves_P_like; exact Hp.
  - apply map_preserves_SAFE; exact Hs.
Qed.

