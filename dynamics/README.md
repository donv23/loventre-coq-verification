# dynamics

## Cosa fa

Il layer `dynamics/` implementa i **processi evolutivi** del Loventre Engine.

Contiene:
- orchestrazione dei flussi
- evoluzione temporale delle istanze
- applicazione iterativa di trasformazioni
- propagazione di segnali e stati
- meta-engine e pipeline di esecuzione

Questo layer risponde alla domanda:
> “Come evolve una configurazione nel tempo o lungo un processo?”

---

## Cosa NON fa

Il layer `dynamics/` **NON** deve:
- definire metriche di base
- introdurre nuove grandezze quantitative
- stabilire soglie concettuali
- definire classi astratte
- decidere policy finali
- imporre giudizi normativi (“accettabile”, “SAFE”, “critico”)

Se un file in `dynamics/`:
- ridefinisce una metrica
- decide una classe finale
- introduce semantica normativa autonoma

👉 **sta oltrepassando il proprio ruolo.**

---

## Dipendenze consentite

Il layer `dynamics/` può importare:
- `core/`
- `metrics/`
- `regimes/`
- `barriers/`

Può interagire con:
- `policy/` **solo come chiamata finale**, mai come dipendenza strutturale

Non può importare:
- `experiments/`
- `bridges/`
- `utils/infra/` (salvo logging minimale)

---

## Ruolo architetturale

Il `dynamics/` è:
- il cuore operativo del motore
- intrinsecamente instabile
- destinato a evolvere

Il suo compito è **portare informazione fino al punto di decisione**,  
non **prendere la decisione**.

Se la dynamics fosse rimossa,
resterebbero:
- struttura (`core/`)
- misura (`metrics/`)
- classificazione (`regimes/`)

ma **nessun processo**.

