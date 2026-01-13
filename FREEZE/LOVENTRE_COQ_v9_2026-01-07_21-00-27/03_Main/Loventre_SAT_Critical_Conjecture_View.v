(** Loventre_SAT_Critical_Conjecture_View.v
    Vista della famiglia SAT_crit dal punto di vista della
    Congettura Loventre.

    Obiettivo:
      - Specializzare la Congettura Loventre_NP_like_critical_not_Polytime
        alla famiglia SAT_crit_family.
      - Usare l'assioma SAT_crit_family_is_NP_like_critical per ottenere
        che SAT_crit_family non è polytime nel senso Loventre.
 *)

From Stdlib Require Import Arith.

Require Import Loventre_Conjecture.
Require Import Loventre_SAT_Critical_Family.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Loventre_SAT_Critical_Conjecture_View.

  Module Conj    := Loventre_Conjecture.Loventre_Conjecture.
  Module SATCrit := Loventre_SAT_Critical_Family.Loventre_SAT_Critical_Family.

  (* ----------------------------------------------------------- *)
  (* 1. Conseguenza della Congettura per SAT_crit_family         *)
  (* ----------------------------------------------------------- *)

  Theorem SAT_crit_family_not_polytime_from_conjecture :
    ~ Conj.Loventre_polytime_family SATCrit.SAT_crit_family.
  Proof.
    unfold not.
    intro Hpoly.
    pose proof SATCrit.SAT_crit_family_is_NP_like_critical as Hcrit.
    pose proof (Conj.Loventre_NP_like_critical_not_Polytime
                  SATCrit.SAT_crit_family Hcrit) as Hnot.
    apply Hnot; exact Hpoly.
  Qed.

End Loventre_SAT_Critical_Conjecture_View.

