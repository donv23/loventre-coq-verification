(** Loventre_Lemmas.v
    Lemmi / assiomi di supporto per i moduli avanzati Loventre.

    Nota:
      - Questo file raccoglie assiomi e lemmi generali utilizzati
        da moduli come Loventre_Regimes_Properties, ecc.
      - In questa fase alcuni risultati sono lasciati come [Axiom],
        per concentrarsi sulla struttura globale del progetto.
 *)

From Coq Require Import Arith ZArith Lia List.
Import ListNotations.

Require Import Loventre_Foundation_Types.
Require Import Loventre_Foundation_Time.
Require Import Loventre_Foundation_History_Structure.
Require Import Loventre_Time_Regimes.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* --------------------------------------------------------------- *)
(* 1. Separazione tra regime subcritico e supercritico nel tempo   *)
(* --------------------------------------------------------------- *)

(** Intuizione:
    - [time_subcritical s n] e [time_supercritical s n] rappresentano
      due regimi mutuamente esclusivi per lo stato [s] al tempo [n].
    - Assumiamo che non possano valere entrambi sullo stesso
      stato e istante temporale.
 *)

Axiom subcritical_not_supercritical :
  forall (s : State) (n : nat),
    time_subcritical s n ->
    ~ time_supercritical s n.

