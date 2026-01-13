(** Loventre_LMetrics_Core.v
    Core astratto delle metriche v3
    Gennaio 2026 — CANON V50
 *)

From Stdlib Require Import Reals ZArith.
From Loventre_Core Require Import Loventre_Kernel.
From Loventre_Core Require Import Loventre_Foundation_Types.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope R_scope.

(** ===========================
      Struttura del bus metrico
    =========================== *)

Record LMetrics := {
  kappa_eff      : R;   (** Curvatura effettiva *)
  entropy_eff    : R;   (** Entropia effettiva *)
  V0             : R;   (** Potenziale/barriera informazionale *)
  horizon_flag   : bool (** TRUE = regime black hole *)
}.

(** ===========================
         Interpretazioni
    =========================== *)

Definition SAFE (m : LMetrics) : Prop :=
  horizon_flag m = false.

Definition BlackHole (m : LMetrics) : Prop :=
  horizon_flag m = true.

(** ===========================
   Lemmi banali per non rompere
    =========================== *)

Lemma SAFE_not_BH :
  forall m, SAFE m -> ~ BlackHole m.
Proof.
  intros m Hs Hc.
  unfold SAFE, BlackHole in *.
  rewrite Hs in Hc.
  discriminate.
Qed.

Lemma BH_not_SAFE :
  forall m, BlackHole m -> ~ SAFE m.
Proof.
  intros m Hbh Hs.
  unfold SAFE, BlackHole in *.
  rewrite Hbh in Hs.
  discriminate.
Qed.

Close Scope R_scope.

