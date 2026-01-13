(* ============================================================= *)
(*                                                               *)
(*   Loventre_Geometric_Separation_SAFE.v                        *)
(*                                                               *)
(*   Separazione geometrica P-like / NP-like                     *)
(*   secondo i predicati canonici di fase                        *)
(*                                                               *)
(*   Layer: Geometry                                             *)
(*                                                               *)
(* ============================================================= *)

From Stdlib Require Import Reals.

From Loventre_Advanced.Geometry Require Import Loventre_LMetrics_Structure.
From Loventre_Advanced.Geometry Require Import Loventre_LMetrics_Phase_Predicates.

(* ------------------------------------------------------------- *)
(* Separazione geometrica canonica                               *)
(* ------------------------------------------------------------- *)

Section Geometric_Separation_P_vs_NP.

  Theorem P_like_NP_like_incompatible :
    forall (m : Loventre_Metrics_Bus.LMetrics),
      ~ (
        Loventre_LMetrics_Phase_Predicates.P_like m /\
        Loventre_LMetrics_Phase_Predicates.NP_like m
      ).
  Proof.
    intros m [HP HNP].
    unfold Loventre_LMetrics_Phase_Predicates.P_like in HP.
    unfold Loventre_LMetrics_Phase_Predicates.NP_like in HNP.
    destruct HP as [Hnot_compact Hno_horizon].
    destruct HNP as [Hcompact Hhorizon].
    contradiction.
  Qed.

End Geometric_Separation_P_vs_NP.

(* ============================================================= *)
(*   FINE FILE                                                   *)
(* ============================================================= *)

