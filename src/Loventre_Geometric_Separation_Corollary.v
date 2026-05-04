(*
  Loventre_Geometric_Separation_Corollary.v

  Corollari formali derivati dal nucleo geometrico Loventre,
  SENZA introdurre nuovi assiomi.

  Questo file dipende unicamente da:
    - Loventre_Geometric_Separation.v
*)

From Stdlib Require Import Reals Lra.
Require Import Loventre_Geometric_Separation.

Open Scope R_scope.

(* ========================================================= *)
(* Corollario 1: esistono istanze non tutte P-like            *)
(* ========================================================= *)

Corollary exists_non_P_like :
  exists y : Inst, NP_like y.
Proof.
  destruct Loventre_geometric_separation as [x [y [_ Hy]]].
  exists y.
  exact Hy.
Qed.

(* ========================================================= *)
(* Corollario 2: P-like e NP-like sono disgiunti               *)
(* ========================================================= *)

Corollary P_like_not_NP_like :
  forall x : Inst, P_like x -> ~ NP_like x.
Proof.
  intros x HP HNP.
  unfold P_like in HP.
  unfold NP_like in HNP.
  lra.
Qed.

(* ========================================================= *)
(* Corollario 3: non tutte le istanze sono P-like              *)
(* ========================================================= *)

Corollary not_all_P_like :
  ~ (forall x : Inst, P_like x).
Proof.
  intro Hall.
  destruct exists_non_P_like as [y Hy].
  specialize (Hall y).
  unfold P_like in Hall.
  unfold NP_like in Hy.
  lra.
Qed.

