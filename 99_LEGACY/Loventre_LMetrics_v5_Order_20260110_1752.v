(**
  Loventre_LMetrics_v5_Order.v
  dicembre 2025 — proprietà strutturale v5.1
*)

(* ==== Import di base su R ==== *)
From Coq Require Import Reals.
From Coq Require Import Rtotal_order.  (* <-- per Rle_total *)

(* namespace corretto *)
From Loventre_Geom Require Import Loventre_LMetrics_Structure.

(* IMPORTANTE: usa disuguaglianza su R, NON nat *)
Local Open Scope R_scope.

Module LMetrics_Order_v5.

  (**
    Teorema strutturale:
    Ogni coppia di metriche ha potenzialità confrontabili.
  *)

  Theorem informational_potential_total_order :
    forall (M1 M2 : LMetrics),
      M1.(informational_potential) <= M2.(informational_potential)
      \/ M2.(informational_potential) <= M1.(informational_potential).
  Proof.
    intros M1 M2.
    apply Rle_total.
  Qed.

End LMetrics_Order_v5.

