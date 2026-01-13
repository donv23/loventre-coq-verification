(*
  Loventre_TimeNoReturn_Ext_V830.v
  Versione: V830 (Canvas 2 — Dinamica Informazionale Estesa)
  Obiettivo:
    - estendere la no-return region a un basin dinamico
    - mostrare chiusura del basin sotto evolve_once ed evolve_n
  Stato: CANON — nessun witness/JSON, nessun assioma
*)

From Coq Require Import Reals.
From Coq Require Import Lia.

From Loventre_Core Require Import Loventre_Prelude.
From Loventre_Core Require Import Loventre_LMetrics_Core.
From Loventre_Advanced Require Import Loventre_TimeEvolution_V800.
From Loventre_Advanced Require Import Loventre_TimeChain_V810.
From Loventre_Advanced Require Import Loventre_TimeNoReturn_V820.

Open Scope R_scope.

Module Loventre_TimeNoReturn_Ext_V830.

  (**
     DEFINIZIONE BASIN (bacino di non ritorno)
     m appartiene al basin se può essere evoluto fino a raggiungere no_return_state
  *)
  Definition basin_of_no_return (m : LMetrics) : Prop :=
    exists n, no_return_state (evolve_n n m).

  (**
     Lemma 1: se uno stato è già no_return_state, è triviale nel basin
  *)
  Lemma no_return_in_basin :
    forall m,
      no_return_state m ->
      basin_of_no_return m.
  Proof.
    intros m Hnr.
    unfold basin_of_no_return.
    exists 0%nat.
    simpl; assumption.
  Qed.

  (**
     Lemma 2: se m è nel basin, evolve_once(m) resta nel basin
     Intuizione: se evolve_n n m ∈ no_return_state,
                 allora evolve_n n (evolve_once m)
                 = evolve_{n+1} m, che è no_return.
  *)
  Lemma basin_stable_once :
    forall m,
      basin_of_no_return m ->
      basin_of_no_return (evolve_once m).
  Proof.
    intros m [n Hnr].
    unfold basin_of_no_return.
    exists (n + 1)%nat.
    rewrite evolve_n_semigroup.
    simpl.
    apply evolve_once_preserves_no_return.
    exact Hnr.
  Qed.

  (**
     Lemma 3: stabilità su evolve_n
     Chiusura naturale: evolve_n non esce dal basin
  *)
  Lemma basin_stable_many :
    forall k m,
      basin_of_no_return m ->
      basin_of_no_return (evolve_n k m).
  Proof.
    intros k m Hb.
    induction k.
    - assumption.
    - simpl.
      apply IHk.
      apply basin_stable_once.
      assumption.
  Qed.

  (**
     Lemma finale V830:
     Se m ∈ basin, allora ∀k, evolve_n(k,m) ∈ basin
     (il basin è forward-invariant)
  *)
  Lemma basin_forward_closure :
    forall m k,
      basin_of_no_return m ->
      basin_of_no_return (evolve_n k m).
  Proof.
    intros m k Hb.
    apply basin_stable_many; assumption.
  Qed.

  (**
     NOTE TECNICHE
     - V800: evolve_once
     - V810: evolve_n semigruppo
     - V820: no_return_state irreversibile
     - V830: bacino dinamico forward-invariante
     In V850 introdurremo collegamento con classi e SAFE/NPbh.
  *)

End Loventre_TimeNoReturn_Ext_V830.

