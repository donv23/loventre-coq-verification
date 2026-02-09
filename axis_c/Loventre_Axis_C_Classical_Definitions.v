(* =============================================== *)
(* Axis C — Classical Definitions (LAB)             *)
(* =============================================== *)

From Stdlib Require Import Bool.

Module Axis_C.

(* ----------------------------------------------- *)
(* Dominio astratto dei problemi classici           *)
(* ----------------------------------------------- *)

Parameter ClassicalProblem : Type.

(* ----------------------------------------------- *)
(* Predicati classici (non computazionali)          *)
(* ----------------------------------------------- *)

Parameter In_P  : ClassicalProblem -> Prop.
Parameter In_NP : ClassicalProblem -> Prop.

(* ----------------------------------------------- *)
(* Separabilità classica (ASSUNTA, LAB)             *)
(* ----------------------------------------------- *)

Definition Axis_C_Separability : Prop :=
  exists p : ClassicalProblem, In_NP p /\ ~ In_P p.

End Axis_C.

