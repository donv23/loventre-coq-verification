(* ============================================================= *)
(* LAB18_Minimal_Plike_Accessibility.v                           *)
(*                                                               *)
(* LAB-18.3 — Necessità dell’accessibilità globale               *)
(*                                                               *)
(* Formalizzazione minimale e isolata del fatto che              *)
(* qualunque nozione ragionevole di P-like richiede              *)
(* accessibilità globale.                                        *)
(*                                                               *)
(* Nessun uso di SAFE, path, dinamiche o policy.                 *)
(* Nessuna modifica al CANON.                                    *)
(* ============================================================= *)

From Stdlib Require Import Reals.
Require Import Coq.micromega.Lra.

Open Scope R_scope.

(* ------------------------------------------------------------- *)
(* Parametri astratti                                            *)
(* ------------------------------------------------------------- *)

Parameter Structure : Type.

(* Quantità informazionale globale *)
Parameter entropy : Structure -> R.

(* Nozione minimale (astratta) di P-like *)
Parameter P_like_min : Structure -> Prop.

(* ------------------------------------------------------------- *)
(* Accessibilità globale (forma minimale)                         *)
(* ------------------------------------------------------------- *)

Definition globally_accessible (w : Structure) : Prop :=
  exists r : R, r > 0 /\ entropy w = r.

(* ------------------------------------------------------------- *)
(* Assunzione strutturale esplicita                               *)
(* ------------------------------------------------------------- *)

(*
  Assunzione minimale:
  Se una struttura è P-like, allora ammette almeno
  un canale informazionale globale non nullo.

  NOTA:
  - Questa NON è una definizione di P-like.
  - È un vincolo strutturale dichiarato esplicitamente.
*)
Axiom P_like_has_global_channel :
  forall w : Structure,
    P_like_min w ->
    exists r : R, r > 0 /\ entropy w = r.

(* ------------------------------------------------------------- *)
(* Lemma principale (necessità)                                  *)
(* ------------------------------------------------------------- *)

Lemma P_like_requires_global_accessibility :
  forall w : Structure,
    P_like_min w ->
    globally_accessible w.
Proof.
  intros w HP.
  unfold globally_accessible.
  apply (P_like_has_global_channel w HP).
Qed.

(* ------------------------------------------------------------- *)
(* Stato epistemico                                              *)
(* ------------------------------------------------------------- *)

(*
  Questo lemma stabilisce SOLO una necessità strutturale:

      P-like ⇒ accessibilità globale

  Non vale il viceversa.
  Non introduce SAFE.
  Non introduce dinamiche.
  Non produce separazioni forti.

  È un ponte minimale, isolato e controllato,
  pronto per essere usato (o rifiutato) nei LAB successivi.
*)

Lemma LAB18_3_ok : True.
Proof. exact I. Qed.

(* ============================================================= *)
(* END OF FILE                                                   *)
(* ============================================================= *)

