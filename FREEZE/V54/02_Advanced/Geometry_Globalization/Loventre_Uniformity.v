(*
  Loventre_Uniformity.v

  FASE A — Uniformità astratta
  ----------------------------

  Questo modulo introduce famiglie di strategie locali
  e una nozione astratta di uniformità.

  Vincoli:
  - Nessuna globalizzazione
  - Nessuna coerenza globale
  - Nessuna GCT
  - Nessun riferimento computazionale o temporale
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import
  Loventre_Advanced.Geometry_Globalization.Loventre_Local_Strategy.

Section Uniformity.

  (* Un insieme (astratto) di indici *)
  Parameter Index : Type.

  (*
    Una famiglia di strategie locali è una funzione
    che assegna a ogni indice una strategia locale.
  *)
  Definition StrategyFamily : Type :=
    Index -> LocalStrategy.

  (*
    Uniformità astratta:
    tutte le strategie della famiglia sono
    localmente equivalenti tra loro.
  *)
  Definition uniform_family (F : StrategyFamily) : Prop :=
    forall i j : Index,
      locally_equivalent (F i) (F j).

  (*
    Lemma base:
    una famiglia costante è uniforme.
  *)
  Lemma uniform_family_constant :
    forall (s : LocalStrategy),
      uniform_family (fun _ => s).
  Proof.
    intros s i j c.
    reflexivity.
  Qed.

End Uniformity.

