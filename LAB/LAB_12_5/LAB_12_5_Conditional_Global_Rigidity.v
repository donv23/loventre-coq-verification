(*
  LAB-12.5 — Conditional Global Rigidity
  Autore: Vincenzo Loventre
  Data: Gennaio 2026

  Scopo:
  Testare se una rigidità globale via reachability
  diventa non-tautologica quando si assume
  l'esistenza di struttura (bacini non banali).
*)

Parameter Config : Type.
Parameter trans : Config -> Config -> Prop.

(* Reachability globale *)
Inductive reach : Config -> Config -> Prop :=
| reach_refl : forall x, reach x x
| reach_step : forall x y z,
    trans x y ->
    reach y z ->
    reach x z.

(* Un bacino: insieme non vuoto chiuso per reachability interna *)
Definition Basin (B : Config -> Prop) : Prop :=
  (exists x, B x) /\
  (forall x y, B x -> reach x y -> B y).

(* Esistenza di due bacini distinti e disgiunti *)
Definition Two_Disjoint_Basins : Prop :=
  exists B1 B2 : Config -> Prop,
    Basin B1 /\
    Basin B2 /\
    (forall x, ~(B1 x /\ B2 x)).

(* Decomposizione della reachability compatibile coi bacini *)
Definition Reach_Decomposable_cond : Prop :=
  exists B1 B2 : Config -> Prop,
    Basin B1 /\
    Basin B2 /\
    (forall x, ~(B1 x /\ B2 x)) /\
    (forall x y, B1 x -> B2 y -> ~ reach x y) /\
    (forall x y, B2 x -> B1 y -> ~ reach x y).

(* Rigidità globale CONDIZIONATA *)
Definition GlobalRigid_reach_cond : Prop :=
  Two_Disjoint_Basins -> ~ Reach_Decomposable_cond.

