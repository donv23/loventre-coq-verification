(* ============================================================= *)
(*                                                               *)
(*   Loventre_PN_Geometric_Separation.v                          *)
(*                                                               *)
(*   Separazione geometrica P-like / NP-like                     *)
(*   nel modello Loventre                                       *)
(*                                                               *)
(* ============================================================= *)

From Stdlib Require Import Reals.

Require Import Loventre_Metrics_Bus.
Require Import Loventre_Safe_Bridge.

Open Scope R_scope.

Section Geometric_Separation.

  (*
     Definizioni strutturali:
     - P-like  ⇔ SAFE
     - NP-like ⇔ UNSAFE
   *)

  Definition P_like (w : LMetrics) : Prop :=
    safe_bridge w = SAFE.

  Definition NP_like (w : LMetrics) : Prop :=
    safe_bridge w = UNSAFE.

  (*
     Lemma centrale di incompatibilità geometrica:
     nessun oggetto globale può essere sia P-like che NP-like.
   *)
  Theorem P_like_NP_like_incompatible :
    forall (w : LMetrics),
      ~ (P_like w /\ NP_like w).
  Proof.
    intros w [HP HNP].
    unfold P_like, NP_like in *.
    rewrite HP in HNP.
    discriminate.
  Qed.

End Geometric_Separation.

(* ============================================================= *)
(*   FINE FILE                                                   *)
(* ============================================================= *)

