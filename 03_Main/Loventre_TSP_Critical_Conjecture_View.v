(** Loventre_TSP_Critical_Conjecture_View.v
    Vista della famiglia TSP_crit dal punto di vista della
    Congettura Loventre.

    Obiettivo:
      - Specializzare la Congettura Loventre_NP_like_critical_not_Polytime
        alla famiglia TSP_crit_family.
      - Usare l'assioma TSP_crit_family_is_NP_like_critical per ottenere
        che TSP_crit_family non è polytime nel senso Loventre.
 *)

From Coq Require Import Arith.

Require Import Loventre_Conjecture.
Require Import Loventre_TSP_Critical_Family.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Loventre_TSP_Critical_Conjecture_View.

  Module Conj    := Loventre_Conjecture.Loventre_Conjecture.
  Module TSPCrit := Loventre_TSP_Critical_Family.Loventre_TSP_Critical_Family.

  (* ----------------------------------------------------------- *)
  (* 1. Conseguenza della Congettura per TSP_crit_family         *)
  (* ----------------------------------------------------------- *)

  Theorem TSP_crit_family_not_polytime_from_conjecture :
    ~ Conj.Loventre_polytime_family TSPCrit.TSP_crit_family.
  Proof.
    unfold not.
    intro Hpoly.
    pose proof TSPCrit.TSP_crit_family_is_NP_like_critical as Hcrit.
    pose proof (Conj.Loventre_NP_like_critical_not_Polytime
                  TSPCrit.TSP_crit_family Hcrit) as Hnot.
    apply Hnot; exact Hpoly.
  Qed.

End Loventre_TSP_Critical_Conjecture_View.

