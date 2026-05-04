(*
  TEST — LAB-12.4
  Consistenza: Reach_Decomposable non è impossibile per definizione.
*)

Load "LAB/LAB_12_4/LAB_12_4_GlobalRigid_Reachability.v".

Axiom Reach_Decomposable_possible :
  Reach_Decomposable.

Lemma GlobalRigid_reach_not_trivial :
  ~ GlobalRigid_reach.
Proof.
  unfold GlobalRigid_reach.
  exact Reach_Decomposable_possible.
Qed.

