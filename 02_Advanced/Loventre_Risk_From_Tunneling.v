(** Loventre_Risk_From_Tunneling.v
    Rischio indotto dal tunneling nel modello Loventre.
    LIVELLO: Advanced — CANON
*)

From Stdlib Require Import Arith ZArith.
From Stdlib Require Import Logic.Classical_Prop.

From Loventre_Core Require Import
  Loventre_Kernel
  Loventre_Foundation_Types
  Loventre_Foundation_Params.

From Loventre_Advanced Require Import
  Loventre_Tunneling_Model.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Loventre_Geometry.

Open Scope Z_scope.

(** ================================================================ *)
(** Predicato canonico SAFE                                          *)
(** ================================================================ *)

Parameter SAFE : M -> Prop.

(** ================================================================ *)
(** Classificazione di rischio (LOGICA, non computazionale)          *)
(** ================================================================ *)

Definition risk_LOW_P (x : M) : Prop :=
  ~ eventual_tunneling x.

Definition risk_MID_P (x : M) : Prop :=
  eventual_tunneling x.

(** ================================================================ *)
(** Lemmi di coerenza SAFE / rischio                                 *)
(** ================================================================ *)

Lemma SAFE_implies_no_tunneling :
  forall x : M,
    SAFE x ->
    ~ eventual_tunneling x.
Admitted.
(* CANON: questo lemma verrà collegato a SAFE_Barrier_Theory *)

Lemma SAFE_is_low_risk :
  forall x : M,
    SAFE x ->
    risk_LOW_P x.
Proof.
  intros x Hsafe.
  unfold risk_LOW_P.
  apply SAFE_implies_no_tunneling.
  exact Hsafe.
Qed.

