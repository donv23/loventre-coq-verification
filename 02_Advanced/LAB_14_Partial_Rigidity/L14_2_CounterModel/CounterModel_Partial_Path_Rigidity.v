(*
  LAB-14.2 — CounterModel_Partial_Path_Rigidity.v

  Contromodello:
  - irreversibilità locale
  - ma rigidità parzialeIGIDA fallisce
    se i cammini possono uscire da S
*)

Require Import
  Loventre_Advanced.LAB_14_Partial_Rigidity.L14_1_Core.Core_Partial_Path_Rigidity.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* === Configurazioni concrete === *)

Inductive Config : Type :=
| a | b | c | d.

(* === Relazione di transizione === *)

Inductive trans : Config -> Config -> Prop :=
| Hac : trans a c
| Hcb : trans c b
| Hbd : trans b d
| Hda : trans d a.

(* === Sottoinsieme protetto === *)

Definition S (x : Config) : Prop :=
  x = a \/ x = b.

(* === Irreversibilità locale === *)

Lemma IrrevLocal_holds :
  forall x y : Config,
    trans x y -> ~ trans y x.
Proof.
  intros x y Hxy Hyx.
  inversion Hxy; subst; inversion Hyx.
Qed.

(* === Cammini corretti (ordine giusto di path_step) === *)

Lemma path_a_b : path trans a b.
Proof.
  eapply path_step.
  - exact Hac.
  - eapply path_step.
    + exact Hcb.
    + apply path_refl.
Qed.

Lemma path_b_a : path trans b a.
Proof.
  eapply path_step.
  - exact Hbd.
  - eapply path_step.
    + exact Hda.
    + apply path_refl.
Qed.

(* === Fallimento della rigidità parziale === *)

Lemma not_PartialPathRigid_S :
  ~ PartialPathRigid trans S.
Proof.
  unfold PartialPathRigid, nontrivial_path.
  intro H.

  assert (Sa : S a).
  { left; reflexivity. }

  assert (Sb : S b).
  { right; reflexivity. }

  assert (Hnt : a <> b /\ path trans a b).
  { split.
    - discriminate.
    - exact path_a_b.
  }

  specialize (H a b Sa Sb Hnt).
  apply H.
  exact path_b_a.
Qed.

