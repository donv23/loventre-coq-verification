(**
  Loventre_Noise_Regimes_Order.v
  dicembre 2025

  Canvas XVI-A

  Ordine strutturale dei regimi di rumore.

  Nessuna dinamica.
  Nessuna probabilità.
*)

From Stdlib Require Import Relations.

Require Import Loventre_Noise_Regimes.

Module Loventre_Noise_Regimes_Order.

  Import Loventre_Noise_Regimes.

  (**
    Relazione di precedenza strutturale.
  *)
  Inductive noise_precedes : Noise_Regime -> Noise_Regime -> Prop :=
  | inert_precedes_critical :
      noise_precedes Inert_Noise Critical_Noise
  | critical_precedes_horizon :
      noise_precedes Critical_Noise Horizon_Opening_Noise
  | inert_precedes_horizon :
      noise_precedes Inert_Noise Horizon_Opening_Noise.

  (**
    Irreflexività.
  *)
  Lemma noise_precedes_irreflexive :
    forall r : Noise_Regime,
      ~ noise_precedes r r.
  Proof.
    intros r H.
    inversion H.
  Qed.

  (**
    Transitività (analisi completa dei casi).
  *)
  Lemma noise_precedes_transitive :
    forall r1 r2 r3 : Noise_Regime,
      noise_precedes r1 r2 ->
      noise_precedes r2 r3 ->
      noise_precedes r1 r3.
  Proof.
    intros r1 r2 r3 H12 H23.
    inversion H12; inversion H23; subst;
      try inversion H0;  (* elimina casi impossibili *)
      try inversion H1.
    - (* Inert -> Critical -> Horizon *)
      exact inert_precedes_horizon.
  Qed.

  (**
    Ordine strutturale stretto sui regimi di rumore.
  *)
  Definition noise_strict_order :=
    noise_precedes.

End Loventre_Noise_Regimes_Order.

