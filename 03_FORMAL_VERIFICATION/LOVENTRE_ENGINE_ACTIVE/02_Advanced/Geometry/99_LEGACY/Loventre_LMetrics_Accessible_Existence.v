(* Loventre_LMetrics_Accessible_Existence.v
   Track 2 – Fase P_like_accessible "scaricata" su m_seed_grid_demo.

   Dicembre 2025: esistenza P_like_accessible NON più assioma puro,
   ma realizzata da un witness concreto m_seed_grid_demo (JSON/metrics).
*)

From Coq Require Import Reals.

From Loventre_Geometry Require Import
  Loventre_LMetrics_JSON_Witness
  Loventre_LMetrics_Existence_Summary
  Loventre_LMetrics_Phase_Predicates.

Set Implicit Arguments.
Set Strict Implicit.
Unset Printing Implicit Defensive.

Module JSONW := Loventre_LMetrics_JSON_Witness.
Module Ex    := Loventre_LMetrics_Existence_Summary.
Module Phase := Loventre_LMetrics_Phase_Predicates.

Import JSONW Phase.

(** ------------------------------------------------------------------------ *)
(** 1. Witness concreto P_like_accessible: m_seed_grid_demo                  *)
(** ------------------------------------------------------------------------ *)

(**
  Ricordiamo la definizione concettuale:

    Definition is_P_like_accessible (m : LMetrics) : Prop :=
      is_low_risk m /\
      is_non_black_hole m /\
      loventre_global_decision m = GD_borderline /\
      loventre_global_color m = GC_green.

  dove:

    is_low_risk m      := risk_class m = risk_LOW
    is_non_black_hole m := horizon_flag m = false

  Dal lato JSON/metrics sappiamo che m_seed_grid_demo è:
    - low risk,
    - non-black-hole (horizon_flag = false),
    - GD_borderline,
    - GC_green.

  Qui formalizziamo direttamente queste uguaglianze usando la definizione
  di m_seed_grid_demo in Loventre_LMetrics_JSON_Witness.v.
 *)

Lemma m_seed_grid_demo_is_P_like_accessible :
  is_P_like_accessible m_seed_grid_demo.
Proof.
  unfold is_P_like_accessible, is_low_risk, is_non_black_hole.
  simpl.
  repeat split; reflexivity.
Qed.

(** Esistenza P_like_accessible "scaricata" su m_seed_grid_demo *)

Lemma exists_P_like_accessible :
  exists m : LMetrics, is_P_like_accessible m.
Proof.
  exists m_seed_grid_demo.
  apply m_seed_grid_demo_is_P_like_accessible.
Qed.

(** ------------------------------------------------------------------------ *)
(** 2. Teorema di tripla esistenza P / P_accessible / NP_like-black-hole     *)
(** ------------------------------------------------------------------------ *)

Theorem Loventre_P_Paccessible_NP_like_triple_exist :
  (exists m : LMetrics, is_P_like m)
  /\
  (exists m : LMetrics, is_P_like_accessible m)
  /\
  (exists m : LMetrics, is_NP_like_black_hole m).
Proof.
  (* Dal file Existence_Summary abbiamo già:
       Loventre_P_vs_NP_like_black_hole_exist_predicative :
         (exists m : LMetrics, is_P_like m)
         /\
         (exists m : LMetrics, is_NP_like_black_hole m).
   *)
  destruct Ex.Loventre_P_vs_NP_like_black_hole_exist_predicative
    as [HexP HexNP].
  split.
  - (* esistenza P_like *)
    exact HexP.
  - split.
    + (* esistenza P_like_accessible, ora realizzata da m_seed_grid_demo *)
      apply exists_P_like_accessible.
    + (* esistenza NP_like-black-hole *)
      exact HexNP.
Qed.

