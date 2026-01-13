(** Loventre_Main_Separation_V61.v
    Separazione conclusiva delle classi Loventre (V61-03)
 *)

From Stdlib Require Import Bool.

From Loventre_Main Require Import
  Loventre_Main_Prelude
  Loventre_Main_Predicates
  Loventre_Main_Classes
  Loventre_Main_Consistency_V61
  Loventre_Main_Theorem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Riaffermiamo la separazione essenziale:
    Esiste un modello black-hole-like che non è P-like *)

Theorem Loventre_Core_Separation :
  exists m,
        In_NP_blackhole_like m
     /\ ~ In_P_like m.
Proof.
  apply Loventre_Class_Separation_Minimal.
Qed.

(** E la accessibilità non coincide con BH *)

Theorem Loventre_Pacc_not_BH :
  exists m,
        In_P_accessible_like m
     /\ ~ In_NP_blackhole_like m.
Proof.
  (** witness P_acc già garantito dal sistema *)
  apply Existence_P_accessible_Witness.
Qed.

