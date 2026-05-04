(*
  LAB-13.1 — Core_Global_Path.v

  Obiettivo:
  Definire una nozione di RIGIDITÀ GLOBALE
  che NON sia riducibile a proprietà pairwise.

  Strategia:
  - introdurre cammini finiti (paths)
  - definire rigidità come assenza di ritorni globali
    lungo cammini non banali
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* === Configurazioni astratte === *)

Parameter Config : Type.

(* === Relazione di transizione elementare === *)

Parameter trans : Config -> Config -> Prop.

(* === Cammini finiti === *)

Inductive path : Config -> Config -> Prop :=
| path_refl :
    forall x : Config,
      path x x
| path_step :
    forall x y z : Config,
      trans x y ->
      path y z ->
      path x z.

(* === Cammino non banale === *)

Definition nontrivial_path (x y : Config) : Prop :=
  path x y /\ x <> y.

(* === Rigidità globale (versione PATH) === *)

(*
  Intuizione:
  se esiste un cammino non banale da x a y,
  allora NON deve esistere alcun cammino (nemmeno lungo)
  che riporti da y a x.
*)

Definition GlobalRigid_Path : Prop :=
  forall x y : Config,
    nontrivial_path x y ->
    ~ path y x.

(* === Osservazione chiave === *)

(*
  Questa definizione:
  - NON è pairwise
  - NON parla di singole transizioni inverse
  - parla di struttura globale dei cammini
*)

