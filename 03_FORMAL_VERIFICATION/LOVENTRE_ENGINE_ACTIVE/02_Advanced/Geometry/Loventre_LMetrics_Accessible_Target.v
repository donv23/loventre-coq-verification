(** * Loventre_LMetrics_Accessible_Target
    Bersaglio per scaricare exists_P_like_accessible

    Scopo di questo file:
      - Fissare esplicitamente l'idea di un candidato concreto
        P_like_accessible proveniente dal mondo JSON/metrics
        (concettualmente: seed_grid).
      - Formulare il lemma-obiettivo
          m_seed_grid_is_P_like_accessible
        che in futuro dovrà sostituire l'assioma
          exists_P_like_accessible.

    Per ora NON tocchiamo l'assioma originale, dichiarato altrove:
      Axiom exists_P_like_accessible :
        exists m : LMetrics, is_P_like_accessible m.

    Questo file serve solo come "bersaglio dichiarato" per la fase
    in cui il bridge JSON → LMetrics sarà abbastanza maturo
    da supportare una prova concreta e da identificare esplicitamente
    il witness seed_grid lato Coq.
 *)

From Loventre_Geometry Require Import
  Loventre_LMetrics_JSON_Witness
  Loventre_LMetrics_Phase_Predicates
  Loventre_LMetrics_Accessible_Existence.

Set Implicit Arguments.
Set Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Candidato astratto P_like_accessible

    Nota importante:
      - Qui introduciamo un candidato astratto
          m_P_like_accessible_candidate : LMetrics.
      - Concettualmente, in futuro, questo candidato dovrà essere
        identificato con il witness seed_grid costruito a partire
        dal JSON metrics_seed_grid_demo_global.json e proiettato
        in LMetrics (modulo JSON_Witness).

    Per ora non forziamo alcun legame sintattico con i witness JSON,
    per evitare dipendenze fragili finché non avremo il nome esatto
    del witness e il bridge completato.
 *)

Parameter m_P_like_accessible_candidate : LMetrics.

Definition m_P_like_accessible_candidate_prop : Prop :=
  is_P_like_accessible m_P_like_accessible_candidate.

(** ** Lemma-obiettivo: in futuro, sostituto dell'assioma

    Enunciato desiderato:
      "il candidato P_like_accessible astratto soddisfa
       is_P_like_accessible".

    Piano concettuale per una futura prova (non implementato qui):
      - identificare m_P_like_accessible_candidate con il witness
        seed_grid proveniente dal JSON (via Loventre_LMetrics_JSON_Witness),
      - usare il bridge JSON → LMetrics per seed_grid,
      - caratterizzare in Coq le condizioni:
          * low risk,
          * non-black-hole,
          * GD_borderline + GC_green,
        che definiscono is_P_like_accessible,
      - combinare questi fatti per concludere il lemma.

    Per ora lasciamo il lemma come Admitted,
    in modo da avere un bersaglio preciso su cui convergere.
 *)

Lemma m_seed_grid_is_P_like_accessible :
  is_P_like_accessible m_P_like_accessible_candidate.
Admitted.

(** ** Lemma di ponte: dal candidato accessibile all'esistenza globale

    Qui formalizziamo la frase:
      "Se (per qualche ragione) abbiamo una prova che il candidato
       è P_like_accessible, allora esiste almeno una metrica
       P_like_accessible".

    Nota tecnica:
      - L'ipotesi del lemma è la PROPOSIZIONE
          is_P_like_accessible m_P_like_accessible_candidate
        (non il nome del lemma m_seed_grid_is_P_like_accessible,
        che è invece un TERMINE/prova di quella proposizione).
 *)

Definition exists_P_like_accessible_target : Prop :=
  exists m : LMetrics, is_P_like_accessible m.

Lemma exists_P_like_accessible_from_candidate :
  is_P_like_accessible m_P_like_accessible_candidate ->
  exists_P_like_accessible_target.
Proof.
  intros H.
  exists m_P_like_accessible_candidate.
  exact H.
Qed.

