(**
   Loventre_Main_3SAT_to_BH_v460.v
   --------------------------------
   Entry-point che dimostra l'esistenza di una mappa
   3SAT → BH nel modello Loventre.
*)

From Loventre_Core Require Import Loventre_Core_Prelude.
From Loventre_Advanced Require Import Loventre_LMetrics_Core Loventre_Metrics_Bus.
From Loventre_Advanced.Geometry Require Import
  Loventre_LMetrics_Phase_Predicates
  Loventre_3SAT_to_BH_Map_v460.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
  Main lemma:
  Ogni witness 3SAT-like può essere mappato in uno stormo BH-like.
*)

Lemma exists_3SAT_to_BH_map :
  forall (m : LMetrics),
    exists mbh : Mapped3SATBH,
      mapped_BH mbh = map_3SAT_to_BH m
      /\ is_NP_blackhole_like (mapped_BH mbh) = true.
Proof.
  intros m.
  exists (mk_mapped_pair m).
  split; simpl; auto.
Qed.

(**
  Conclusione filosofica controllata: Il ponte è parziale,
  non tocca P ≠ NP classico, solo il modello Loventre.
*)


