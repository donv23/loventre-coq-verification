(** * Loventre_Mini_Theorem_Stack
    Mini Teorema & Policy Stack (dicembre 2025)

    Questo file fornisce un punto di ingresso compatto
    al "Mini Teorema di Loventre" così come descritto
    nello stack LMetrics + Policy + SAFE + Profili di complessità.

    L'idea è di non aggiungere nuova logica,
    ma solo di dare un nome stabile e leggibile
    al blocco centrale di proprietà già raccolte
    in Loventre_Theorem_v2_Statement.
 *)

From Loventre_Geometry Require Import
  Loventre_LMetrics_Policy_SAFE_Spec
  Loventre_LMetrics_Complexity_Profiles.

From Loventre_Main Require Import
  Loventre_LMetrics_Policy_Specs
  Loventre_Theorem_v1
  Loventre_Theorem_v2_Sketch.

Set Implicit Arguments.
Set Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Statement compatto dello stack

    Per ora identifichiamo direttamente
    lo "stack mini-teorema" con lo statement
    già definito in Loventre_Theorem_v2_Sketch:

      - tripla esistenza P / P_accessible / NP_like-black-hole,
      - programma di Policy (Core + SAFE),
      - separazione di complessità tra i profili
        P_like_complexity_profile e NP_like_crit_complexity_profile.

    In futuro, se servirà una decomposizione più narrativa
    (per esempio una versione "v3" del Teorema),
    potremo cambiare la definizione seguente
    senza toccare i file più interni.
 *)

Definition Loventre_Mini_Theorem_Stack_Statement : Prop :=
  Loventre_Theorem_v2_Statement.

(** ** Teorema: dallo stesso contratto a Mini_Theorem_Stack

    Questo teorema dice soltanto:
    "Sotto lo stesso contratto già usato per Theorem_v1/v2,
     lo stack Mini è soddisfatto".

    È deliberatamente un wrapper molto sottile.
 *)

Theorem Loventre_Mini_Theorem_Stack_from_contract :
  Loventre_Policy_Core_Program ->
  policy_SAFE_implies_green_global ->
  Loventre_Mini_Theorem_Stack_Statement.
Proof.
  intros Hcore Hsafe.
  unfold Loventre_Mini_Theorem_Stack_Statement.
  apply Loventre_Theorem_v2_from_contract; assumption.
Qed.

(** ** Proiezione: separazione di complessità

    Come piccolo bonus, estraiamo esplicitamente
    la parte di separazione di complessità dal teorema v2.

    Questo rende comodo usare direttamente
    la separazione tra i profili P_like_complexity_profile
    e NP_like_crit_complexity_profile
    senza dover "navigare" a mano dentro Loventre_Theorem_v2_Statement.
 *)

Lemma Loventre_Mini_Theorem_Stack_complexity_separation :
  Loventre_Policy_Core_Program ->
  policy_SAFE_implies_green_global ->
  Loventre_Complexity_Separation_Statement.
Proof.
  intros Hcore Hsafe.
  pose proof (Loventre_Theorem_v2_from_contract Hcore Hsafe) as H.
  (* Per definizione, Loventre_Theorem_v2_Statement è
     una congiunzione:
       Loventre_Theorem_v1_Statement
       /\
       Loventre_Complexity_Separation_Statement.
   *)
  destruct H as [_ Hsep].
  exact Hsep.
Qed.

