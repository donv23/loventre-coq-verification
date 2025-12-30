(*
  Loventre_Witness_Interpretation.v

  Interpretazione formale dei witness sperimentali
  osservati nel Loventre Engine.

  Nessun Admitted.
  Le assunzioni sperimentali sono esplicitate come assiomi.
*)

From Stdlib Require Import Reals Lra.
Open Scope R_scope.

Require Import Loventre_Geometric_Separation.

(* ========================================================= *)
(* 1. Witness sperimentali                                   *)
(* ========================================================= *)

Definition ExperimentalWitness (x : Inst) : Prop := True.

(* ========================================================= *)
(* 2. Assiomi sperimentali (interpretazione)                 *)
(* ========================================================= *)

Axiom experimental_high_barrier_implies_NP_like :
  forall x : Inst,
    ExperimentalWitness x ->
    V0 x > 0 ->
    NP_like x.

Axiom experimental_minimal_barrier_implies_P_like :
  forall x : Inst,
    ExperimentalWitness x ->
    V0 x = 0 ->
    P_like x.

(* Esistenza di un witness “a barriera minima” (ancoraggio sperimentale) *)
Axiom exists_experimental_minimal_barrier :
  exists x0 : Inst,
    ExperimentalWitness x0 /\ V0 x0 = 0.

(* ========================================================= *)
(* 3. Teorema di interpretazione                             *)
(* ========================================================= *)

Theorem exists_experimental_separation :
  exists x y : Inst,
    ExperimentalWitness x /\
    ExperimentalWitness y /\
    P_like x /\
    NP_like y.
Proof.
  destruct exists_experimental_minimal_barrier as [x0 [Hx0 Hx0V]].
  destruct exists_geometric_separation as [x1 [y1 Hxy]].

  exists x0, y1.

  refine (conj Hx0 (conj I (conj _ _))).

  (* P_like x0 dal witness a barriera minima *)
  apply experimental_minimal_barrier_implies_P_like.
  exact Hx0.
  exact Hx0V.

  (* NP_like y1: dalla separazione geometrica otteniamo V0 y1 > 0
     usando anche V0_nonneg su x1 *)
  apply experimental_high_barrier_implies_NP_like.
  exact I.
  assert (0 <= V0 x1) as Hx1_nonneg.
  { apply V0_nonneg. }
  lra.
Qed.

