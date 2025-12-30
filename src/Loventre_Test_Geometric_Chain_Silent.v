(*
  Loventre_Test_Geometric_Chain_Silent.v

  Smoke test SILENZIOSO (no Check/Compute che stampano output):
  core -> corollari -> witness interpretation.

  Obiettivo: compilazione pulita + catena verificabile senza rumore.
*)

From Stdlib Require Import Reals Lra.
Open Scope R_scope.

Require Import Loventre_Geometric_Separation.
Require Import Loventre_Geometric_Separation_Corollary.
Require Import Loventre_Witness_Interpretation.

(* =============================== *)
(* 1) Core ok                      *)
(* =============================== *)

Lemma core_chain_ok :
  exists x y : Inst, P_like x /\ NP_like y.
Proof.
  exact Loventre_geometric_separation.
Qed.

Lemma geometric_separation_distinct :
  exists x y : Inst, V0 x < V0 y /\ x <> y.
Proof.
  destruct exists_geometric_separation as [x [y Hxy]].
  exists x, y.
  split.
  - exact Hxy.
  - intro Heq. subst.
    lra.
Qed.

(* =============================== *)
(* 2) Corollari ok                 *)
(* =============================== *)

Lemma corollary1_ok :
  exists y : Inst, NP_like y.
Proof.
  exact exists_non_P_like.
Qed.

Lemma corollary2_ok :
  forall x : Inst, P_like x -> ~ NP_like x.
Proof.
  exact P_like_not_NP_like.
Qed.

Lemma corollary3_ok :
  ~ (forall x : Inst, P_like x).
Proof.
  exact not_all_P_like.
Qed.

(* =============================== *)
(* 3) Witness interpretation ok    *)
(* =============================== *)

Lemma witness_layer_ok :
  exists x y : Inst,
    ExperimentalWitness x /\
    ExperimentalWitness y /\
    P_like x /\
    NP_like y.
Proof.
  exact exists_experimental_separation.
Qed.

