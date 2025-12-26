(* ====================================================================== *)
(* Loventre_Theorem_v3_Citable_Prop.v                                    *)
(*                                                                       *)
(* Facade "citable" del teorema v3 già dimostrato.                       *)
(* Nessun nuovo witness, nessuna nuova assunzione.                       *)
(*                                                                       *)
(* Idea: il contenuto formale resta in:                                  *)
(*   03_Main/Loventre_Theorem_v3_P_vs_NP_like.v                           *)
(* Qui facciamo solo re-export / alias stabile.                          *)
(* ====================================================================== *)

From Loventre_Main Require Import
  Loventre_Theorem_v3_P_vs_NP_like.

(* Alias citabile: stesso statement del teorema canonico. *)
Theorem Loventre_Citable_P_vs_NP_like_black_hole :=
  Loventre_Theorem_v3_P_vs_NP_like.

