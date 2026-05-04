(*
  LAB-14.3 — Core_Internal_Path_Rigidity.v

  Internal Path Rigidity:
  studiamo una forma rafforzata di rigidità parziale in cui
  i cammini rilevanti devono rimanere INTERAMENTE all’interno
  di un sottoinsieme S di configurazioni.

  Questo è il primo criterio strutturalmente stabile
  dopo il fallimento della rigidità globale (LAB-13)
  e della rigidità parziale ingenua (LAB-14.1 / 14.2).
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* === Configurazioni astratte === *)

Parameter Config : Type.

(* === Relazione di transizione === *)

Parameter trans : Config -> Config -> Prop.

(* === Sottoinsieme osservabile / accessibile === *)

Parameter S : Config -> Prop.

(* === Cammini === *)

Inductive path : Config -> Config -> Prop :=
| path_refl :
    forall x, path x x
| path_step :
    forall x y z,
      trans x y ->
      path y z ->
      path x z.

(* === Cammini interni a S === *)

Inductive internal_path : Config -> Config -> Prop :=
| ip_refl :
    forall x,
      S x ->
      internal_path x x
| ip_step :
    forall x y z,
      S x ->
      trans x y ->
      internal_path y z ->
      internal_path x z.

(* === Cammino non banale === *)

Definition nontrivial (x y : Config) : Prop :=
  x <> y.

(* === Rigidità interna sui cammini === *)

Definition InternalPathRigid : Prop :=
  forall x y,
    S x ->
    S y ->
    nontrivial x y ->
    internal_path x y ->
    ~ internal_path y x.

(*
  Intuizione:
  - la rigidità NON è richiesta globalmente
  - NON riguarda tutti i cammini
  - ma SOLO quelli che:
      • partono in S
      • restano in S
      • sono non banali
*)

(* === Relazione con i LAB precedenti === *)

(*
  - LAB-13:
      la rigidità globale fallisce anche con vincoli forti
  - LAB-14.1 / 14.2:
      la rigidità parziale fallisce se i cammini possono uscire da S
  - LAB-14.3:
      la rigidità diventa plausibile solo se il cammino è interno a S
*)


