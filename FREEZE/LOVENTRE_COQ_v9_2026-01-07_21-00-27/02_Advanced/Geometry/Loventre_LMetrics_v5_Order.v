(**
  Loventre_LMetrics_v5_Order.v
  dicembre 2025 — proprietà strutturale v5.1
*)

Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.    (* uso corretto di lra *)
Local Open Scope R_scope.

From Loventre_Geom Require Import Loventre_LMetrics_Structure.

Module LMetrics_Order_v5.

  (**
    Proprietà di ordinabilità del potenziale informazionale.
    Usando Rtotal_order per Rocq 9.1.
  *)

  Theorem informational_potential_total_order :
    forall (M1 M2 : LMetrics),
        M1.(informational_potential) <= M2.(informational_potential)
     \/ M2.(informational_potential) <= M1.(informational_potential).
  Proof.
    intros M1 M2.
    destruct (Rtotal_order (informational_potential M1)
                           (informational_potential M2))
      as [Hlt | [Heq | Hgt]].
    - (* caso M1 < M2 *)
      left; lra.
    - (* caso M1 = M2 *)
      left; lra.
    - (* caso M1 > M2 *)
      right; lra.
  Qed.

End LMetrics_Order_v5.

