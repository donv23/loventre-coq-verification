(* Loventre_LMetrics_Policy_Theorem.v
   Versione minimal: teorema SAFE-separation su LMetrics.
*)

From Stdlib Require Import Reals.

From Loventre_Geometry Require Import
  Loventre_LMetrics_JSON_Witness
  Loventre_LMetrics_Existence_Summary
  Loventre_LMetrics_Phase_Predicates
  Loventre_LMetrics_Policy_Spec
  Loventre_LMetrics_Policy_SAFE_Spec.

From Loventre_Main Require Import
  Loventre_LMetrics_Policy_Specs.

Set Implicit Arguments.
Set Strict Implicit.
Unset Printing Implicit Defensive.

Module JSONW    := Loventre_LMetrics_JSON_Witness.
Module Ex       := Loventre_LMetrics_Existence_Summary.
Module Phase    := Loventre_LMetrics_Phase_Predicates.
Module PolSpec  := Loventre_LMetrics_Policy_Spec.
Module SafeSpec := Loventre_LMetrics_Policy_SAFE_Spec.
Module Core     := Loventre_LMetrics_Policy_Specs.

Import JSONW Phase.

(** Assioma di collegamento: NP_like-black-hole ⇒ black-hole *)

Axiom NP_like_black_hole_implies_black_hole :
  forall m : LMetrics,
    is_NP_like_black_hole m ->
    is_black_hole m.

(** ------------------------------------------------------------------------ *)
(** Teorema decisionale: NP_like-black-hole ⇒ NON SAFE                       *)
(** ------------------------------------------------------------------------ *)

Definition Loventre_SAFE_separation_prop : Prop :=
  forall m : LMetrics,
    is_NP_like_black_hole m ->
    loventre_global_decision m <> GD_safe.

Theorem Loventre_SAFE_separation_from_core_and_SAFE_spec :
  Core.Loventre_Policy_Core_Program ->
  SafeSpec.policy_SAFE_implies_green_global ->
  Loventre_SAFE_separation_prop.
Proof.
  intros Hcore Hsafe.
  unfold Loventre_SAFE_separation_prop.
  intros m Hnp Hsafe_dec.

  (* Decomponiamo il Core Program per ottenere la regola "mai verde su black-hole" *)
  destruct Hcore as [Hexist Hideal].
  destruct Hideal as [Hnever [Hgreen Hborder]].

  (* SAFE ⇒ GC_green (spec SAFE) *)
  unfold SafeSpec.policy_SAFE_implies_green_global in Hsafe.
  specialize (Hsafe m).
  pose proof (Hsafe Hsafe_dec) as Hcolor_green.

  (* NP_like-black-hole ⇒ black-hole (assioma di fase) *)
  assert (Hbh : is_black_hole m).
  { apply NP_like_black_hole_implies_black_hole; assumption. }

  (* Regola di Policy: mai GC_green su black-hole *)
  unfold PolSpec.policy_never_green_on_black_hole_global in Hnever.
  specialize (Hnever m).
  unfold PolSpec.policy_never_green_on_black_hole_pointwise in Hnever.
  specialize (Hnever Hbh).

  (* Contraddizione tra:
       - Hnever : loventre_global_color m <> GC_green
       - Hcolor_green : loventre_global_color m = GC_green
     che chiude il goal. *)
  apply (Hnever Hcolor_green).
Qed.

