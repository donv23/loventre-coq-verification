(*
  Loventre_Local_Strategy.v

  FASE A — Oggetti astratti
  ------------------------

  Questo modulo definisce il concetto astratto di "strategia locale".

  Vincoli:
  - Nessun riferimento a computazione, tempo, TM
  - Nessuna globalità
  - Nessuna uniformità
  - Nessuna GCT

  Scopo:
  Fornire un oggetto primitivo riutilizzabile per la fase di globalizzazione.
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section LocalStrategy.

  (* Un contesto locale astratto *)
  Parameter LocalContext : Type.

  (* Un'azione o decisione locale astratta *)
  Parameter LocalAction : Type.

  (*
    Una strategia locale è una funzione che,
    dato un contesto locale,
    produce un'azione locale.
  *)
  Definition LocalStrategy : Type :=
    LocalContext -> LocalAction.

  (*
    Proprietà minimale: due strategie sono localmente equivalenti
    se producono la stessa azione su ogni contesto.
  *)
  Definition locally_equivalent
             (s1 s2 : LocalStrategy) : Prop :=
    forall c : LocalContext, s1 c = s2 c.

  (*
    Riflessività della equivalenza locale.
    (Lemma banale, ma utile come sanity check.)
  *)
  Lemma locally_equivalent_refl :
    forall s : LocalStrategy,
      locally_equivalent s s.
  Proof.
    intros s c.
    reflexivity.
  Qed.

End LocalStrategy.

