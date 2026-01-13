(** Loventre_TM_SAT_Critical_Realization.v
    Realizzazione TM della famiglia SAT_crit nel quadro Loventre.

    Obiettivo:
      - Collegare una TM concreta (tm1_init in Loventre_TM_1)
        alla famiglia SAT_crit_family definita in
        Loventre_SAT_Critical_Family.
      - Usare il bridge astratto Loventre_TM_Family_Bridge per
        dedurre che la famiglia è polytime nel senso di
        Loventre_Conjecture.Loventre_polytime_family,
        MA SOLO sotto l'ipotesi che tm1_init realizzi davvero la famiglia.
 *)

From Stdlib Require Import Arith.

Require Import Loventre_Conjecture.
Require Import Loventre_TM_Family_Bridge.
Require Import Loventre_SAT_Critical_Family.
Require Import Loventre_TM_Base.
Require Import Loventre_TM_1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Loventre_TM_SAT_Critical_Realization.

  Module Conj    := Loventre_Conjecture.Loventre_Conjecture.
  Module Bridge  := Loventre_TM_Family_Bridge.Loventre_TM_Family_Bridge.
  Module TMBase  := Loventre_TM_Base.Loventre_TM_Base.
  Module SATCrit := Loventre_SAT_Critical_Family.Loventre_SAT_Critical_Family.
  Module TM1     := Loventre_TM_1.Loventre_TM_1.

  (* ----------------------------------------------------------- *)
  (* 1. Teorema condizionale: se tm1 realizza SAT_crit_family    *)
  (*    allora SAT_crit_family è polytime (nel senso Loventre)   *)
  (* ----------------------------------------------------------- *)

  Theorem SAT_crit_family_polytime_if_TM1_realizes :
    Bridge.Realizes_Family TM1.tm1_init SATCrit.SAT_crit_family ->
    Conj.Loventre_polytime_family SATCrit.SAT_crit_family.
  Proof.
    intro Hreal.
    eapply Bridge.TM_polytime_realization_implies_Loventre_polytime_family.
    - exact Hreal.
    - exact TM1.tm1_polytime.
  Qed.

End Loventre_TM_SAT_Critical_Realization.

