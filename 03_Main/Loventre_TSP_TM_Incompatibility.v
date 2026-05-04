(** Loventre_TSP_TM_Incompatibility.v
    Incompatibilità tra:
      - la realizzazione TM1 della famiglia TSP_crit, e
      - la Congettura Loventre + proprietà NP-like critica di TSP_crit_family.

    Risultato:
      - Se assumiamo la Congettura Loventre e le proprietà di TSP_crit_family
        (come in Loventre_TSP_Critical_Family),
        allora TM1 NON può realizzare TSP_crit_family.
 *)

From Coq Require Import Arith.

Require Import Loventre_Conjecture.
Require Import Loventre_TM_Family_Bridge.
Require Import Loventre_TSP_Critical_Family.
Require Import Loventre_TM_Base.
Require Import Loventre_TM_1.
Require Import Loventre_TM_TSP_Critical_Realization.
Require Import Loventre_TSP_Critical_Conjecture_View.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Loventre_TSP_TM_Incompatibility.

  Module Conj    := Loventre_Conjecture.Loventre_Conjecture.
  Module Bridge  := Loventre_TM_Family_Bridge.Loventre_TM_Family_Bridge.
  Module TMBase  := Loventre_TM_Base.Loventre_TM_Base.
  Module TM1     := Loventre_TM_1.Loventre_TM_1.
  Module TSPCrit := Loventre_TSP_Critical_Family.Loventre_TSP_Critical_Family.
  Module Real    := Loventre_TM_TSP_Critical_Realization.Loventre_TM_TSP_Critical_Realization.
  Module View    := Loventre_TSP_Critical_Conjecture_View.Loventre_TSP_Critical_Conjecture_View.

  (* ----------------------------------------------------------- *)
  (* 1. Teorema: TM1 non può realizzare TSP_crit_family          *)
  (* ----------------------------------------------------------- *)

  Theorem TM1_cannot_realize_TSP_crit_family :
    ~ Bridge.Realizes_Family TM1.tm1_init TSPCrit.TSP_crit_family.
  Proof.
    unfold not.
    intro Hreal.
    (* Dal teorema TM otteniamo che TSP_crit_family sarebbe polytime. *)
    pose proof (Real.TSP_crit_family_polytime_if_TM1_realizes Hreal)
      as Hpoly.
    (* Dalla Congettura specializzata otteniamo che non può esserlo. *)
    pose proof View.TSP_crit_family_not_polytime_from_conjecture
      as Hnotpoly.
    (* Contraddizione. *)
    apply Hnotpoly; exact Hpoly.
  Qed.

End Loventre_TSP_TM_Incompatibility.

