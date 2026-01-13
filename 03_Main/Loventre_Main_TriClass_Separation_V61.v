(** Loventre_Main_TriClass_Separation_V61.v
    Tri-separazione tra P-like, P-accessible-like e BH-like (V61-04)
 *)

From Stdlib Require Import Bool.

From Loventre_Main Require Import
  Loventre_Main_Prelude
  Loventre_Main_Predicates
  Loventre_Main_Classes
  Loventre_Main_Consistency_V61
  Loventre_Main_Separation_V61
  Loventre_Main_Theorem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** 1. Esiste BH-like che NON e' P-like *)
Theorem Loventre_BH_not_P :
  exists m,
       In_NP_blackhole_like m
    /\ ~ In_P_like m.
Proof.
  apply Loventre_Core_Separation.
Qed.

(** 2. Esiste P-accessible-like NON BH-like *)
Theorem Loventre_Pacc_not_BH :
  exists m,
       In_P_accessible_like m
    /\ ~ In_NP_blackhole_like m.
Proof.
  apply Loventre_Pacc_not_BH.
Qed.

(** 3. Esiste P-like (banale, per definizione del modello) *)
Theorem Loventre_exists_P_like :
  exists m, In_P_like m.
Proof.
  apply Existence_P_like_Witness.
Qed.

(** 4. Nessuna inclusione collassa le tre classi *)

Theorem Loventre_P_not_Pacc :
  exists m,
       In_P_like m
    /\ ~ In_P_accessible_like m.
Proof.
  apply P_vs_Paccessible_Separated.
Qed.

(** 5. Tri-separazione finale internalizzata *)
Theorem Loventre_TriClass_Separation :
     (exists m, In_P_like m)
  /\ (exists m, In_P_accessible_like m /\ ~ In_P_like m)
  /\ (exists m, In_NP_blackhole_like m /\ ~ In_P_accessible_like m).
Proof.
  split.
  - apply Loventre_exists_P_like.
  split.
  - apply P_vs_Paccessible_Separated.
  - apply BH_vs_Paccessible_Separated.
Qed.

