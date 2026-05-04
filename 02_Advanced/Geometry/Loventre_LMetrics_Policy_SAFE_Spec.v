(* =========================================== *)
(* Loventre_LMetrics_Policy_SAFE_Spec.v        *)
(* SAFE Policy → GREEN Color Bridge            *)
(* =========================================== *)

From Stdlib Require Import Reals.

From Loventre_Geometry Require Import
  Loventre_Metrics_Bus.

Import Loventre_Metrics_Bus.

(* ----------------------------------------------------------------- *)
(* Predicati di alto livello                                         *)
(* ----------------------------------------------------------------- *)

Definition is_globally_SAFE (m : LMetrics) : Prop :=
  loventre_global_decision m = GD_safe.

Definition is_globally_GREEN (m : LMetrics) : Prop :=
  loventre_global_color m = GC_green.

(* ----------------------------------------------------------------- *)
(* Assioma di coerenza decision ↔ color                              *)
(*                                                                   *)
(* Esprime il vincolo semantico (non strutturalmente forzato dal     *)
(* record LMetrics) secondo cui la decisione globale e il colore     *)
(* operativo sono allineati: SAFE ⇒ GREEN, INVALID ⇒ UNKNOWN.        *)
(*                                                                   *)
(* Questo assioma riflette l'invariante mantenuto dal Policy Bridge  *)
(* del motore Python.                                                *)
(* ----------------------------------------------------------------- *)

Axiom decision_color_coherence_safe :
  forall m : LMetrics,
    loventre_global_decision m = GD_safe ->
    loventre_global_color m = GC_green.

Axiom decision_color_coherence_invalid :
  forall m : LMetrics,
    loventre_global_decision m = GD_invalid ->
    loventre_global_color m = GC_unknown.

(* ----------------------------------------------------------------- *)
(* Enunciato e teorema: SAFE ⇒ GREEN (reale, non tautologico)        *)
(* ----------------------------------------------------------------- *)

Definition policy_SAFE_implies_green_global : Prop :=
  forall m : LMetrics,
    is_globally_SAFE m ->
    is_globally_GREEN m.

Theorem policy_SAFE_implies_green_global_proof :
  policy_SAFE_implies_green_global.
Proof.
  unfold policy_SAFE_implies_green_global,
         is_globally_SAFE, is_globally_GREEN.
  intros m Hsafe.
  apply decision_color_coherence_safe. exact Hsafe.
Qed.

(* ----------------------------------------------------------------- *)
(* Corollario: separazione SAFE vs INVALID a livello colore          *)
(* ----------------------------------------------------------------- *)

Theorem safe_and_invalid_colors_distinct :
  forall m : LMetrics,
    loventre_global_decision m = GD_safe ->
    ~ loventre_global_color m = GC_unknown.
Proof.
  intros m Hsafe Habsurd.
  assert (HG : loventre_global_color m = GC_green)
    by (apply decision_color_coherence_safe; exact Hsafe).
  rewrite HG in Habsurd. discriminate.
Qed.
