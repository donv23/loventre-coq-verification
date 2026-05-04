(*
  LAB-12.4 — Global Rigidity via Reachability
  Autore: Vincenzo Loventre
  Data: Gennaio 2026

  Scopo:
  Definire una nozione di rigidità globale NON pairwise,
  NON equivalente a IrrevLocal, basata su reachability globale.

  Questo file è un LAB:
  - nessun teorema
  - nessun assioma nuovo
  - solo definizioni strutturali
*)

Parameter Config : Type.
Parameter trans : Config -> Config -> Prop.

(*
  Reachability globale: chiusura riflessiva e transitiva di trans
*)
Inductive reach : Config -> Config -> Prop :=
| reach_refl : forall x, reach x x
| reach_step : forall x y z,
    trans x y ->
    reach y z ->
    reach x z.

(*
  Partizione NON banale dello spazio degli stati
*)
Definition Partition (P Q : Config -> Prop) : Prop :=
  (exists x, P x) /\
  (exists y, Q y) /\
  (forall x, ~(P x /\ Q x)).

(*
  La reachability è decomponibile se esiste
  una partizione non banale senza cammini incrociati
*)
Definition Reach_Decomposable : Prop :=
  exists P Q : Config -> Prop,
    Partition P Q /\
    (forall x y, P x -> Q y -> ~ reach x y) /\
    (forall x y, Q x -> P y -> ~ reach x y).

(*
  Rigidità globale (versione LAB):
  assenza di decomposizioni della reachability
*)
Definition GlobalRigid_reach : Prop :=
  ~ Reach_Decomposable.

