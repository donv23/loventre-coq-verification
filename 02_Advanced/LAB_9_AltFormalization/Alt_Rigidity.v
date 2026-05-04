(*
  Alt_Rigidity.v
  Structural rigidity in the alternative formulation.
  (No Barrier primitive; intrinsic irreversibility only.)
*)

Require Import Loventre_Advanced.LAB_9_AltFormalization.Alt_Core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma no_global_symmetry_alt :
  (exists x y : Config, trans x y /\ irreversible y) ->
  ~ (forall a b : Config, trans a b -> trans b a).
Proof.
  intros [x [y [Hxy Hy]]] Hsym.
  (* From irreversibility we get ~ trans y x *)
  pose proof (@intrinsic_irreversibility x y Hxy Hy) as Hnot.
  (* Global symmetry gives trans y x *)
  pose proof (@Hsym x y Hxy) as Hyx.
  exact (Hnot Hyx).
Qed.

