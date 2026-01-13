From Stdlib Require Import Reals ZArith Zfloor.
Open Scope R_scope.

(* 1) Cerchiamo qualunque lemma che contenga Zfloor *)
Search Zfloor.

(* 2) Cerchiamo le proprietà che usano IZR e floor *)
Search IZR (Zfloor _).

(* 3) Cerchiamo i lemmi con "spec" nel nome *)
Search spec Zfloor.

(* 4) Cerchiamo lemmi con floor e bound *)
Search (_ <= _ < _)%R.

(* 5) Controlliamo se Zfloor_has_spec esiste *)
Fail Check Zfloor_spec.

(* 6) Testiamo definizione di default *)
Check Zfloor.

