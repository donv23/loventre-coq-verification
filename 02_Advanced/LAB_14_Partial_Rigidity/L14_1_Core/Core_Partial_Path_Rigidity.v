(*
  LAB-14.1 — Core_Partial_Path_Rigidity.v

  Obiettivo:
  formalizzare una nozione di "rigidità" a livello di CAMMINI (path),
  e una versione PARZIALE rispetto ad un sottoinsieme S : Config -> Prop.

  Idea:
  - path trans x y = esiste un cammino (multi-step) da x a y.
  - nontrivial_path trans x y = x <> y /\ path trans x y.
  - GlobalPathRigid trans: nessuna mutua raggiungibilità non banale.
  - PartialPathRigid trans S: la rigidità vale solo per x,y che stanno in S.
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Core.

Context {Config : Type}.
Context (trans : Config -> Config -> Prop).

(* Chiusura riflessiva-transitiva "costruita a mano" *)
Inductive path : Config -> Config -> Prop :=
| path_refl : forall x, path x x
| path_step : forall x y z, trans x y -> path y z -> path x z.

Definition nontrivial_path (x y : Config) : Prop :=
  x <> y /\ path x y.

Definition GlobalPathRigid : Prop :=
  forall x y : Config,
    nontrivial_path x y -> ~ path y x.

Definition PartialPathRigid (S : Config -> Prop) : Prop :=
  forall x y : Config,
    S x -> S y ->
    nontrivial_path x y ->
    ~ path y x.

Lemma GlobalPathRigid_implies_Partial :
  GlobalPathRigid -> forall S, PartialPathRigid S.
Proof.
  intros H S x y Hx Hy Hnt.
  exact (H x y Hnt).
Qed.

End Core.

