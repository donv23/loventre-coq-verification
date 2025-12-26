(* ====================================================================== *)
(* Test_Loventre_Theorem_v3_All.v                                        *)
(*                                                                       *)
(* Smoke-test canonico: verifica che la catena v3 sia importabile.        *)
(* Nessun assioma aggiunto.                                              *)
(* ====================================================================== *)

From Loventre_Main Require Import
  Loventre_Theorem_v3_P_vs_NP_like
  Loventre_Theorem_v3_Citable_Prop.

Goal True.
  Check Loventre_Theorem_v3_P_vs_NP_like.
  Check Loventre_Citable_P_vs_NP_like_black_hole.
  exact I.
Qed.

