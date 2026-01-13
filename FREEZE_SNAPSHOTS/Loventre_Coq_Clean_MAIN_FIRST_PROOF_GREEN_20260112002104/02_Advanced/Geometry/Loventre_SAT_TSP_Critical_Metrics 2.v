(** * Loventre_SAT_TSP_Critical_Metrics.v
    Stato: seed 2025-12

    Questo modulo collega il bus di metriche tipato (LMetrics)
    alle famiglie critiche SAT/TSP e al concetto di "witness metrico".

    - BusState       := LMetrics (alias per lo stato del bus)
    - SAT_crit       : BusState -> Prop
    - TSP_crit       : BusState -> Prop
    - Metrics_witness: BusState -> Prop

    In più, enunciamo (come Conjecture) alcune proprietà desiderate che
    collegano Metrics_witness e GlobalDecision:

      - un witness metrico dovrebbe essere almeno globalmente borderline
        o critical;
      - uno stato globalmente critical è un candidato naturale per la
        regione NP_like-critica / near-horizon.

    Le prove di queste congetture saranno obiettivo di lavoro futuro.
 *)

Require Import Reals.
Require Import Loventre_Geometry.Loventre_Metrics_Bus.

Open Scope R_scope.

(** ** Alias per lo stato del bus *)

Definition BusState := LMetrics.



(** ** Predicati critici per SAT e TSP

    A questo livello fissiamo solo la *firma*:

      SAT_crit : BusState -> Prop
      TSP_crit : BusState -> Prop

    L'idea è che:

      - SAT_crit m    esprima che m è lo stato metrico di una istanza
                      SAT_crit_n (famiglia critica SAT del motore);
      - TSP_crit m    esprima che m è lo stato metrico di una istanza
                      TSP_crit_n (famiglia critica TSP del motore).

    La definizione concreta (in termini di crescita di V0, a_min, collasso
    di p_tunnel e P_success, ecc.) verrà aggiunta in futuro.
 *)

Parameter SAT_crit : BusState -> Prop.
Parameter TSP_crit : BusState -> Prop.



(** ** Witness metrico *)

Definition Metrics_witness (m : BusState) : Prop :=
  SAT_crit m \/ TSP_crit m.



(** ** Collegamenti concettuali con GlobalDecision

    Lato Python, il Policy Bridge produce un'etichetta qualitativa:

      "safe" | "borderline" | "critical" | "invalid"

    che qui modelliamo come:

      GD_safe | GD_borderline | GD_critical | GD_invalid

    L'idea concettuale (non ancora formalmente provata) è:

      - se Metrics_witness m allora m è, dinamicamente, almeno borderline
        o critical (in termini di loventre_global_decision);
      - se loventre_global_decision m = GD_critical allora m è un candidato
        naturale per essere un witness metrico di una famiglia NP_like-critica
        (SAT_crit o TSP_crit).
 *)

Conjecture witness_globally_borderline_or_critical :
  forall (m : BusState),
    Metrics_witness m ->
      loventre_global_decision m = GD_borderline \/
      loventre_global_decision m = GD_critical.

Conjecture globally_critical_is_witness_like :
  forall (m : BusState),
    loventre_global_decision m = GD_critical ->
    exists m',
      Metrics_witness m' /\
      (* m e m' sono "equivalenti" come stato metrico, in un senso da precisare. *)
      True.

(** Nota:
    - La seconda congettura usa un "exists m'" per tenere la definizione
      aperta: in futuro potremo raffinare cosa significa "stato metrico
      equivalente" (ad es. up to isomorfismo di features o fino a certe
      distorsioni controllate delle metriche).

    Queste congetture non fissano alcuna formula numerica: esprimono
    soltanto la struttura logica che ci aspettiamo dalle famiglie critiche
    SAT/TSP nel contesto del Loventre Metrics Bus.
 *)

