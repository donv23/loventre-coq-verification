from pathlib import Path

TARGET = Path(
    "02_Advanced/LAB_12_Minimal_Rigidity/"
    "L12_2_Pairwise/CounterModel_Pairwise.v"
)

CONTENT = r'''
(*
  LAB-12.2 — CounterModel_Pairwise.v
  Versione canonica pulita (v11, gennaio 2026)

  Contromodello che mostra:
  Irreversibilità locale pairwise
  NON implica rigidità globale.
*)

Require Import
  Loventre_Advanced.LAB_12_Minimal_Rigidity.L12_2_Pairwise.Core_Pairwise.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* === Configurazioni concrete === *)

Inductive Config : Type :=
| a
| b
| c.

(* === Relazione di transizione === *)

Inductive trans : Config -> Config -> Prop :=
| Hab : trans a b
| Hbc : trans b c
| Hca : trans c a.

(* === Irreversibilità locale (pairwise) === *)

Lemma IrrevLocal_holds :
  forall x y : Config,
    trans x y -> ~ trans y x.
Proof.
  intros x y Hxy Hyx.
  destruct Hxy; destruct Hyx; discriminate.
Qed.

(* === Fallimento della rigidità globale === *)

Lemma not_GlobalRigid : ~ GlobalRigid.
Proof.
  unfold GlobalRigid.
  intro H.
  specialize (H a b).
  apply (H Hab).
  exact Hca.
Qed.
'''

TARGET.write_text(CONTENT.strip() + "\n")
print("OK: CounterModel_Pairwise.v riscritto (v11, senza terminal_isolated).")

