(** Loventre_TM_Family_Bridge.v
    Bridge concettuale tra:
      - il modello di macchina di Turing (Loventre_TM_Base),
      - le famiglie astratte di istanze (Loventre_Conjecture)
      - il predicato Loventre_polytime_family.

    ATTENZIONE:
      Questo file e' volutamente astratto: non fissiamo ancora
      una codifica concreta delle istanze su nastro TM.
      Introduciamo solo:
        - un predicato [Realizes_Family] che collega una TM a una family,
        - un assioma di equivalenza con [Loventre_polytime_family].
*)

From Coq Require Import Arith.

Require Import Loventre_TM_Base Loventre_Conjecture.

Module Loventre_TM_Family_Bridge.

  (** Alias dei moduli coinvolti. *)
  Module TMBase := Loventre_TM_Base.Loventre_TM_Base.
  Module Conj   := Loventre_Conjecture.Loventre_Conjecture.

  (** Riprendiamo i nomi chiave dal modulo Conj per comodita'. *)
  Definition instance := Conj.instance.
  Definition family   := Conj.family.

  (** Predicato astratto:
      [Realizes_Family c F] significa che la configurazione TM concreta [c]
      realizza (risolve) la family di istanze [F].

      Intuizione (da istanziare in seguito):
        - F : nat -> instance  e' una famiglia di problemi,
        - c : TMBase.Config  e' una TM inizializzata,
        - per ogni n, l'esecuzione di c su una codifica di [F n]
          termina con risposta corretta (accetta/rifiuta).

      Non fissiamo qui:
        - la codifica [instance -> TMBase.Word],
        - il criterio di accettazione/rifiuto.
   *)
  Parameter Realizes_Family : TMBase.Config -> family -> Prop.

  (** Assioma chiave di collegamento:

      Una family e' Loventre-polynomial se e solo se
      esiste una configurazione TM concreta che la realizza
      in tempo polinomiale nel senso di TMBase.polytime_config.

      In altre parole:
        [Loventre_polytime_family F] <-> esiste una TM polinomiale
        (nel modello TMBase) che risolve la family F.
   *)
  Axiom Loventre_polytime_family_iff_TM_realization :
    forall (F : family),
      Conj.Loventre_polytime_family F <->
      exists c : TMBase.Config,
        Realizes_Family c F /\ TMBase.polytime_config c.

  (** Direzione utile: se possediamo esplicitamente una TM concreta [c]
      che realizza F e che e' polinomiale nel senso TMBase, allora
      possiamo concludere che [F] e' una family Loventre-polynomial. *)
  Theorem TM_polytime_realization_implies_Loventre_polytime_family :
    forall (c : TMBase.Config) (F : family),
      Realizes_Family c F ->
      TMBase.polytime_config c ->
      Conj.Loventre_polytime_family F.
  Proof.
    intros c F Hreal Hpoly.
    destruct (Loventre_polytime_family_iff_TM_realization F)
      as [H_from_Loventre H_to_Loventre].
    (* Ci serve la direzione:
         (exists c, Realizes_Family c F /\ TMBase.polytime_config c)
         -> Loventre_polytime_family F. *)
    apply H_to_Loventre.
    exists c; split; assumption.
  Qed.

End Loventre_TM_Family_Bridge.

