From Loventre_Main Require Import Loventre_Main_Theorem_v3.

(* Prova 1: nome non qualificato *)
Fail Check Loventre_Main_Theorem_v3_Prop.

(* Prova 2: nome qualificato col modulo *)
Fail Check Loventre_Main_Theorem_v3.Loventre_Main_Theorem_v3_Prop.

Goal True. exact I. Qed.

