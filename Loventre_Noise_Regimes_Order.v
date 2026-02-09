(**
  Loventre_Noise_Regimes_Order.v
  gennaio 2026

  Mini ordine parziale tra regimi di rumore.
  Nessun significato dinamico, struttura minimale.
*)

From Stdlib Require Import Reals.

Require Import Loventre_Noise_Regimes.

Module Loventre_Noise_Regimes_Order.

  Import Loventre_Noise_Regimes.

  (**
    Ordine qualitativo canonico:
      Inert < Critical < Horizon
  *)

  Definition le_noise (r1 r2 : Noise_Regime) : Prop :=
    match r1, r2 with
    | Inert_Noise, _ => True
    | Critical_Noise, Critical_Noise => True
    | Critical_Noise, Horizon_Opening_Noise => True
    | Horizon_Opening_Noise, Horizon_Opening_Noise => True
    | _, _ => False
    end.

  (**
    Proprietà essenziali — placeholder
    (nessun teorema per ora)
  *)

  Parameter le_noise_reflexive :
    forall r, le_noise r r.

  Parameter le_noise_transitive :
    forall r1 r2 r3,
      le_noise r1 r2 ->
      le_noise r2 r3 ->
      le_noise r1 r3.

End Loventre_Noise_Regimes_Order.

