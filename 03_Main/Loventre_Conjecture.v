(** * Loventre_Conjecture

   Seed concettuale per la Congettura di Loventre:
   collega la geometria Loventre (famiglie NP_like-critiche / supercritiche)
   con l'impossibilita' di una famiglia deterministicamente polinomiale.

   ATTENZIONE:
   - Questo file e' volutamente astratto.
   - I predicati [Loventre_NP_like_critical_family],
     [Loventre_supercritical_family] e [Loventre_polytime_family]
     verranno istanziati in seguito usando:
       * i moduli di Kernel/Geometria (NP_like, tempo iperbolico, barriere),
       * il modulo di modello algoritmico (famiglie di istanze e tempo di calcolo).
*)

From Coq Require Import Arith.

Module Loventre_Conjecture.

  (** Tipo astratto di istanze di problema.

      In seguito potra' essere:
        - una codifica di formule SAT,
        - tour TSP,
        - descrizioni di macchine di Turing, ecc.
   *)
  Parameter instance : Type.

  (** Taglia dell'istanza (numero di variabili, lunghezza dell'input, ecc.). *)
  Parameter size : instance -> nat.

  (** Classificazione Loventre "locale": istanze NP_like nel senso geometrico.

      Intuitivamente:
        [NP_like_Loventre x] significa che l'istanza x, nel modello
        interno di curvatura/tempo, cade in una regione critica:
          - Pattern C fully_critical,
          - tempo interno iperbolico,
          - barriera di complessita' con p_tunnel molto piccolo, ecc.
   *)
  Parameter NP_like_Loventre : instance -> Prop.

  (** Famiglia di problemi parametrizzata da n: [F n] e' l'istanza di taglia n. *)
  Definition family := nat -> instance.

  (** Predicato astratto:
      [Loventre_supercritical_family F] significa che la famiglia F
      e' "NP_like-critica/supercritica" in senso Loventre.

      In seguito questo sara' definito usando, ad esempio:
        - funzioni [V0_F : nat -> nat], [a_min_F : nat -> nat],
          [gamma_F : nat -> nat] o versioni reali,
        - condizioni del tipo:
              [NP_like_Loventre (F n)] per infiniti n,
              crescita sufficiente di V0_F, a_min_F, gamma_F,
              p_tunnel_F(n; E_poly(n)) estremamente piccolo
              per ogni energia polinomiale E_poly.
   *)
  Parameter Loventre_supercritical_family : family -> Prop.

  (** Predicato astratto di esistenza di una famiglia deterministicamente
      polinomiale che risolve F.

      Idee da istanziare nel modello algoritmico:
        [Loventre_polytime_family F] ~
          "esiste un algoritmo deterministico A
           e un polinomio P tale che, per ogni n,
           il tempo di A su [F n] e' <= P (size (F n)))."
   *)
  Parameter Loventre_polytime_family : family -> Prop.

  (** *** Enunciato base della Congettura di Loventre

      Versione qualitativa:

        "Ogni famiglia Loventre-supercritica (NP_like-critica nel senso della
         curvatura e della dilatazione del tempo interno) NON e' risolvibile
         da alcuna famiglia deterministicamente polinomiale."

      Questa e' la forma astratta del ponte:
        geometria Loventre  -->  limite sulle famiglie polytime.
   *)

  Conjecture Loventre_Supercritical_not_Polytime :
    forall (F : family),
      Loventre_supercritical_family F ->
      ~ Loventre_polytime_family F.

  (** Variante piu' forte: richiediamo esplicitamente che, per infiniti n,
      le istanze [F n] siano NP_like nel senso geometrico Loventre.

      NOTA:
        - [Loventre_supercritical_family] potra' gia' includere questa condizione.
        - Manteniamo comunque una seconda congettura separata per chiarezza.
   *)
  Parameter Loventre_NP_like_critical_family : family -> Prop.

  Conjecture Loventre_NP_like_critical_not_Polytime :
    forall (F : family),
      Loventre_NP_like_critical_family F ->
      ~ Loventre_polytime_family F.

End Loventre_Conjecture.
