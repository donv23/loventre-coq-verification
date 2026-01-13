(* ====================================================================== *)
(* Loventre_Theorem_v3_Citable_Prop.v                                     *)
(*                                                                       *)
(* Facade "citable" del teorema v3 gia' dimostrato.                       *)
(* Nessun nuovo witness. Nessuna costruzione manuale di LMetrics.         *)
(* ====================================================================== *)

From Loventre_Main Require Import
  Loventre_Theorem_v3_P_vs_NP_like.

(* Alias citabile: stesso contenuto del teorema canonico.
   Usando Definition, Coq eredita automaticamente il tipo. *)
Definition Loventre_Citable_P_vs_NP_like_black_hole :=
  Loventre_Theorem_v3_P_vs_NP_like.

