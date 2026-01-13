(**
  Loventre_Main_2SAT3SAT_Family_Aggregator_v300.v
  ------------------------------------------------
  Aggregatore globale per 2-SAT / 3-SAT nel modello Loventre (v3 CANON)

  Obiettivo:
    - Ricevere un profilo metrico LMetrics generico
    - Classificare automaticamente in:
        P_like_accessible oppure NP_like_blackhole
    - Valido per:
        * 2SAT easy
        * 2SAT critico
        * 3SAT easy
        * 3SAT critico
    - Nessun nuovo assioma
*)

From Loventre_Core Require Import Loventre_Core_Prelude.
From Loventre_Advanced Require Import
     Loventre_LMetrics_Core
     Loventre_Metrics_Bus
     Loventre_Class_Model
     Loventre_Class_Properties
     Loventre_Phase_Assembly.
From Loventre_Advanced.Geometry Require Import
     Loventre_LMetrics_Phase_Predicates
     Loventre_LMetrics_Structure.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
  Classificazione globale di un singolo profilo LMetrics.
  Condizione:
    - se è NP-like-black-hole → NP_blackhole_Lov
    - altrimenti → P_like_accessible_Lov

  NB:
    Non distinguiamo qui fra 2SAT/3SAT;
    ci affidiamo ai predicati già stabiliti dal modello Loventre.
*)

Definition loventre_family_classifier (m : LMetrics) : Loventre_Class :=
  if is_NP_like_blackhole m
  then NP_blackhole_Lov
  else P_like_accessible_Lov.

(**
  Teorema aggregatore:
    Qualunque sia il profilo metrico m,
    la classificazione globale coincide con le proprietà interne
    (is_NP_like_blackhole / is_P_like_accessible).

  Questa proposizione è semicostruttiva: non crea nuova inferenza.
*)

Theorem loventre_family_classifier_sound (m : LMetrics) :
  (is_NP_like_blackhole m = true -> loventre_family_classifier m = NP_blackhole_Lov)
/\
  (is_NP_like_blackhole m = false -> loventre_family_classifier m = P_like_accessible_Lov).
Proof.
  unfold loventre_family_classifier.
  destruct (is_NP_like_blackhole m); intros; auto.
Qed.

(**
  Citable corollary:
    Ogni test 2SAT o 3SAT che rispetta il Bus Loventre
    cade esattamente in P_accessible oppure NP_blackhole.
*)
Corollary loventre_family_two_way_total (m : LMetrics) :
  loventre_family_classifier m = NP_blackhole_Lov
  \/
  loventre_family_classifier m = P_like_accessible_Lov.
Proof.
  unfold loventre_family_classifier.
  destruct (is_NP_like_blackhole m); auto.
Qed.

