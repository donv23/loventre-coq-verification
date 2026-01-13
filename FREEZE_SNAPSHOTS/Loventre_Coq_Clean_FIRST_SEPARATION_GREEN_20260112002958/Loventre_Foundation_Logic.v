(** Loventre_Foundation_Logic.v
    Modulo di utilità logica di base per il progetto Loventre.
    Contiene solo lemmi generali su /\ , \/ , -> , <->, ecc.
*)

From Stdlib Require Import Init.Prelude.

Module Loventre_Logic.

  (** Lemma: commutatività della congiunzione *)
  Lemma and_comm : forall (P Q : Prop),
    P /\ Q -> Q /\ P.
  Proof.
    intros P Q [HP HQ].
    split; assumption.
  Qed.

  (** Lemma: associatività della congiunzione *)
  Lemma and_assoc : forall (P Q R : Prop),
    (P /\ Q) /\ R -> P /\ (Q /\ R).
  Proof.
    intros P Q R [[HP HQ] HR].
    split; [assumption | split; assumption].
  Qed.

  (** Lemma: commutatività della disgiunzione *)
  Lemma or_comm : forall (P Q : Prop),
    P \/ Q -> Q \/ P.
  Proof.
    intros P Q H.
    destruct H as [HP | HQ].
    - right; exact HP.
    - left; exact HQ.
  Qed.

  (** Lemma: modus ponens esplicito *)
  Lemma modus_ponens : forall (P Q : Prop),
    P -> (P -> Q) -> Q.
  Proof.
    intros P Q HP HPQ.
    apply HPQ; exact HP.
  Qed.

  (** Lemma: equivalenza simmetrica *)
  Lemma iff_sym : forall (P Q : Prop),
    (P <-> Q) -> (Q <-> P).
  Proof.
    intros P Q [HPQ HQP].
    split; assumption.
  Qed.

  (** Lemma: equivalenza transitiva *)
  Lemma iff_trans : forall (P Q R : Prop),
    (P <-> Q) -> (Q <-> R) -> (P <-> R).
  Proof.
    intros P Q R [HPQ HQP] [HQR HRQ].
    split; intro H.
    - apply HQR, HPQ, H.
    - apply HQP, HRQ, H.
  Qed.

End Loventre_Logic.
