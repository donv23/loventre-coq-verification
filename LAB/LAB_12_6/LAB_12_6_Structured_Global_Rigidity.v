(*
  LAB-12.6 — Structured Global Rigidity
  Autore: Vincenzo Loventre
  Data: Gennaio 2026

  Versione stabile:
  - reach è campo del sistema
  - nessuna dipendenza esterna ambigua
*)

(* Sistema concreto *)
Record System := {
  Config : Type;
  trans : Config -> Config -> Prop;
  reach : Config -> Config -> Prop;

  reach_refl :
    forall x, reach x x;

  reach_step :
    forall x y z,
      trans x y ->
      reach y z ->
      reach x z
}.

(* Bacino concreto *)
Record Basin (S : System) := {
  basin_pred : S.(Config) -> Prop;
  basin_nonempty : exists x, basin_pred x;
  basin_closed :
    forall x y,
      basin_pred x ->
      S.(reach) x y ->
      basin_pred y
}.

(* Due bacini concreti *)
Record TwoBasins (S : System) := {
  basin1 : Basin S;
  basin2 : Basin S
}.

(* Bacini disgiunti *)
Definition Basins_Disjoint (S : System) (TB : TwoBasins S) : Prop :=
  let B1 := basin_pred (basin1 TB) in
  let B2 := basin_pred (basin2 TB) in
    forall x, ~(B1 x /\ B2 x).

(* Decomposizione concreta *)
Definition Reach_Decomposable_struct (S : System) (TB : TwoBasins S) : Prop :=
  let B1 := basin_pred (basin1 TB) in
  let B2 := basin_pred (basin2 TB) in
    (forall x y, B1 x -> B2 y -> ~ S.(reach) x y) /\
    (forall x y, B2 x -> B1 y -> ~ S.(reach) x y).

(* Rigidità globale strutturata *)
Definition GlobalRigid_struct (S : System) (TB : TwoBasins S) : Prop :=
  Basins_Disjoint S TB ->
  ~ Reach_Decomposable_struct S TB.

