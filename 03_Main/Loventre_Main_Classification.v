(** Loventre_Main_Classification.v
    V59 — Classificazione universale delle famiglie nel modello Loventre
 *)

From Stdlib Require Import Bool.

From Loventre_Main Require Import
  Loventre_Main_Prelude
  Loventre_Main_Predicates
  Loventre_Main_Witness
  Loventre_Main_2SAT_Classes
  Loventre_Main_Classes.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Definizione: Classifies — m deve cadere in una delle tre famiglie *)
Definition Classifies (m : LMetrics) : Prop :=
  In_P_like m \/ In_P_accessible_like m \/ In_NP_blackhole_like m.

(** Lemma 1 — ogni witness P_like semplice è classificabile *)
Lemma Classifies_seed_minimal :
  Classifies m_seed_minimal.
Proof.
  unfold Classifies.
  left.
  unfold In_P_like, SAFE.
  exact SAFE_seed_minimal.
Qed.

(** Lemma 2 — ogni witness P_accessible è classificabile *)
Lemma Classifies_seed_grid :
  Classifies m_seed_grid.
Proof.
  unfold Classifies.
  right; left.
  unfold In_P_accessible_like.
  split.
  - apply SAFE_seed_grid.
  - apply not_blackhole_seed_grid.
Qed.

(** Lemma 3 — ogni witness 2SAT_easy è classificabile *)
Lemma Classifies_2SAT_easy :
  Classifies m_2SAT_easy.
Proof.
  unfold Classifies.
  right; left.
  unfold In_P_accessible_like.
  split.
  - apply SAFE_2SAT_easy.
  - apply not_blackhole_2SAT_easy.
Qed.

(** Lemma 4 — ogni witness 2SAT_crit cade nella BH *)
Lemma Classifies_2SAT_crit :
  Classifies m_2SAT_crit.
Proof.
  unfold Classifies.
  right; right.
  apply BlackHole_2SAT_crit.
Qed.

(** Lemma 5 — almeno una istanza in ciascuna classe *)
Lemma NonEmpty_P_like   : exists m, In_P_like m.
Proof. exists m_seed_minimal; now unfold In_P_like, SAFE. Qed.

Lemma NonEmpty_P_acc    : exists m, In_P_accessible_like m.
Proof.
  exists m_seed_grid.
  unfold In_P_accessible_like.
  split; [apply SAFE_seed_grid | apply not_blackhole_seed_grid].
Qed.

Lemma NonEmpty_BH       : exists m, In_NP_blackhole_like m.
Proof. exists m_2SAT_crit; apply BlackHole_2SAT_crit. Qed.

