(* =============================================================== *)
(* Loventre_Main_2SAT_Global_Structural_Theorem.v                  *)
(* Prima separazione completa di famiglie 2SAT nel modello Loventre *)
(* GENNAIO 2026 – V95                                              *)
(* =============================================================== *)

From Loventre_Core        Require Import Loventre_Core_Prelude.
From Loventre_Advanced    Require Import
     Loventre_Class_Model
     Loventre_Class_Properties
     Loventre_Phase_Assembly
     Loventre_Metrics_Bus.
From Loventre_Advanced.Geometry Require Import
     Loventre_2SAT_EasyCrit_Compare
     Loventre_2SAT_Local_Family
     Loventre_2SAT_Mini_Theorem_Extended
     Loventre_2SAT_Pacc_Class_Bridge
     Loventre_2SAT_SAFE_Bridge.

(* --------------------------------------------------------------- *)
(* Mini risultato di appoggio: estraiamo direttamente le famiglie *)
(* --------------------------------------------------------------- *)

Definition fam_easy : list LMetrics :=
  easy_lovelocal_family.

Definition fam_crit : list LMetrics :=
  crit_lovelocal_family.

Lemma fam_easy_nonempty :
  fam_easy <> [].
Proof.
  unfold fam_easy, easy_lovelocal_family.
  exact easy_family_is_nonempty.
Qed.

Lemma fam_crit_nonempty :
  fam_crit <> [].
Proof.
  unfold fam_crit, crit_lovelocal_family.
  exact crit_family_is_nonempty.
Qed.

(* --------------------------------------------------------------- *)
(* Passo 2: tutte le istanze easy cadono nella classe Pacc Loventre *)
(* --------------------------------------------------------------- *)

Lemma fam_easy_is_Pacc :
  forall m, In m fam_easy -> In_Pacc_Lov m.
Proof.
  intros m Hm.
  apply easy_family_all_in_Pacc.
  exact Hm.
Qed.

(* --------------------------------------------------------------- *)
(* Passo 3: tutte le istanze crit cadono nella classe NPbh Loventre *)
(* --------------------------------------------------------------- *)

Lemma fam_crit_in_NPbh :
  forall m, In m fam_crit -> In_NP_BlackHole_Lov m.
Proof.
  intros m Hm.
  apply crit_family_all_in_NPbh.
  exact Hm.
Qed.

(* --------------------------------------------------------------- *)
(* Passo Finale: SEPARAZIONE STRUTTURALE SU FAMIGLIE               *)
(* --------------------------------------------------------------- *)

Theorem Loventre_2SAT_Global_Structural_Separation :
  (exists m1, In m1 fam_easy  /\ In_Pacc_Lov m1)
  /\
  (exists m2, In m2 fam_crit /\ In_NP_BlackHole_Lov m2).
Proof.
  split.
  - destruct (easy_family_witness_exists) as [m Hm].
    exists m. split; try exact Hm.
    apply fam_easy_is_Pacc. exact Hm.
  - destruct (crit_family_witness_exists) as [m Hm].
    exists m. split; try exact Hm.
    apply fam_crit_in_NPbh. exact Hm.
Qed.

(* =============================================================== *)
(* FINE – Nessun Axiom, tutto derivato da Geometry + Class Model   *)
(* =============================================================== *)

