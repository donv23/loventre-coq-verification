(** Loventre_Main_Theorem.v
    Prima separazione logica nel modello v50
    Gennaio 2026 — CANON BASE
 *)

From Stdlib Require Import Reals Bool.
From Loventre_Advanced Require Import Loventre_LMetrics_Core.
From Loventre_Main Require Import Loventre_Main_Witness.
From Loventre_Main Require Import Loventre_Main_Classes.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope R_scope.

(** =========================================
     Mini-separazione SAFE vs BlackHole (Prop)
   ========================================= *)

Lemma minimal_is_SAFE :
  SAFE m_seed_minimal.
Proof.
  reflexivity.
Qed.

Lemma critico_not_SAFE :
  ~ SAFE m_seed_critico.
Proof.
  unfold SAFE, BlackHole in *.
  simpl. discriminate.
Qed.

Lemma first_separation :
  SAFE m_seed_minimal /\ ~ SAFE m_seed_critico.
Proof.
  split.
  - apply minimal_is_SAFE.
  - apply critico_not_SAFE.
Qed.

Close Scope R_scope.

