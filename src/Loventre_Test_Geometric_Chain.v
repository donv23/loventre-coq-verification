(*
  Loventre_Test_Geometric_Chain.v

  Test di compilazione unitaria della catena geometrica Loventre:
    - Loventre_Geometric_Separation.v
    - Loventre_Geometric_Separation_Corollary.v
    - Loventre_Witness_Interpretation.v

  Obiettivo: un solo punto di compilazione ("smoke test") che conferma:
    - core: esistenza separazione P-like / NP-like (nel modello)
    - corollari: coerenza minima
    - layer witness: interpretazione sperimentale (assiomi espliciti)
*)

From Stdlib Require Import Reals Lra.

Require Import Loventre_Geometric_Separation.
Require Import Loventre_Geometric_Separation_Corollary.
Require Import Loventre_Witness_Interpretation.

Open Scope R_scope.

(* ====================================================== *)
(* 1) Core: separazione P-like / NP-like                  *)
(* ====================================================== *)

Lemma core_chain_ok :
  exists x y : Inst, P_like x /\ NP_like y.
Proof.
  exact Loventre_geometric_separation.
Qed.

(* Distinzione x<>y ottenuta dalla separazione geometrica V0 x < V0 y *)
Lemma geometric_separation_distinct :
  exists x y : Inst, V0 x < V0 y /\ x <> y.
Proof.
  destruct exists_geometric_separation as [x [y Hxy]].
  exists x, y.
  split.
  - exact Hxy.
  - intro Heq. subst y.
    lra.
Qed.

(* ====================================================== *)
(* 2) Corollari: coerenza minima                          *)
(* ====================================================== *)

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

(* ====================================================== *)
(* 3) Witness interpretation layer                         *)
(* ====================================================== *)

Lemma witness_layer_ok :
  exists x y : Inst,
    ExperimentalWitness x /\
    ExperimentalWitness y /\
    P_like x /\
    NP_like y.
Proof.
  exact exists_experimental_separation.
Qed.

(* Se compila, la catena è OK. *)
Print core_chain_ok.
Print geometric_separation_distinct.
Print corollary1_ok.
Print corollary2_ok.
Print corollary3_ok.
Print witness_layer_ok.

