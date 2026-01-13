(*
  Loventre_TimeNoReturn_V820.v
  Versione: V820 (Canvas 2 — Dinamica Informazionale)
  Obiettivo:
    - introdurre condizione di non ritorno usando V0 (barriera informazionale)
    - dimostrare che evolve_n non può far "salire" di nuovo sopra la soglia
    - primo passo verso irreversibilità strutturale (NP_blackhole roadmap)
  Stato: CANON — nessun witness, nessun JSON, nessun assioma aggiunto
*)

From Coq Require Import Reals.
From Coq Require Import Lia.

From Loventre_Core Require Import Loventre_Prelude.
From Loventre_Core Require Import Loventre_LMetrics_Core.
From Loventre_Advanced Require Import Loventre_TimeEvolution_V800.
From Loventre_Advanced Require Import Loventre_TimeChain_V810.

Open Scope R_scope.

Module Loventre_TimeNoReturn_V820.

  (**
     Definizione soglia critica della barriera
     Nota: V800 definisce decay di V0 in evolve_once.
     Ora formalizziamo soglia per irreversibilità.
  *)
  Definition V0_threshold : R := 0.50.

  (**
     Predicato di No Return
     Uno stato è nel dominio di non ritorno
     se la sua barriera informazionale è già al di sotto della soglia.
  *)
  Definition no_return_state (m : LMetrics) : Prop :=
    m.(V0) <= V0_threshold.

  (**
     Lemma fondamentale:
     evolve_once NON aumenta V0,
     quindi non può riportare V0 sopra la soglia.
  *)
  Lemma evolve_once_preserves_no_return :
    forall m,
      no_return_state m ->
      no_return_state (evolve_once m).
  Proof.
    intros m Hnr.
    unfold no_return_state, evolve_once in *; simpl.
    (* V0_new = V0 * (1 - 0.005) <= V0 <= threshold *)
    assert (m.(V0) * (1 - 0.005) <= m.(V0)).
    { apply Rmult_le_reg_l.
      - apply Rlt_le, Rlt_trans with (r2:=0); lra.
      - replace (1 - 0.005) with 0.995 by lra; lra.
    }
    apply Rle_trans with (r2 := m.(V0)); assumption.
  Qed.

  (**
     Estensione naturale su evolve_n
     Una volta sotto la soglia, ogni passo mantiene il vincolo
  *)
  Lemma evolve_n_preserves_no_return :
    forall n m,
      no_return_state m ->
      no_return_state (evolve_n n m).
  Proof.
    intros n m Hnr; induction n.
    - simpl; assumption.
    - simpl. apply evolve_once_preserves_no_return, IHn, Hnr.
  Qed.

  (**
     Lemma simbolico chiave:
     Se m entra in no_return_state dopo n passi,
     allora nessun k successivo lo riporta fuori
     (semantica debole "irreversibilità locale").
  *)
  Lemma no_return_irreversible :
    forall n k m,
      no_return_state (evolve_n n m) ->
      no_return_state (evolve_n (n + k) m).
  Proof.
    intros n k m Hnr.
    rewrite evolve_n_semigroup.
    apply evolve_n_preserves_no_return.
    exact Hnr.
  Qed.

  (**
     Commento:
     - V820 formalizza “assenza di via di ritorno”
     - nessun richiamo a classi o witness
     - fondamento logico per Canvas 3 e 5
     - passo minimo verso attrattore NP_blackhole
  *)

End Loventre_TimeNoReturn_V820.

