(** Loventre_Main_Predicates.v
    V57 — Allineato al bus metrico canonico
    Rimuove duplicati SAFE/BlackHole
 *)

From Stdlib Require Import Bool.
From Loventre_Main Require Import Loventre_Main_Prelude.
From Loventre_Advanced Require Export Loventre_LMetrics_Core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ===============================
      Predicati derivati e lemmi
    =============================== *)

(** SAFE e BlackHole sono già definiti in Loventre_LMetrics_Core *)

Lemma SAFE_not_BlackHole_main : forall m, SAFE m -> ~ BlackHole m.
Proof.
  intros m Hs Hc.
  unfold SAFE, BlackHole in *.
  rewrite Hs in Hc; discriminate.
Qed.

Lemma BlackHole_not_SAFE_main : forall m, BlackHole m -> ~ SAFE m.
Proof.
  intros m Hbh Hs.
  unfold SAFE, BlackHole in *.
  rewrite Hbh in Hs; discriminate.
Qed.

