# core

## Cosa fa

Il layer `core/` definisce la **struttura astratta** del Loventre Engine.

Contiene esclusivamente:
- predicati strutturali
- classificazioni concettuali
- invarianti logici
- nozioni di appartenenza a classi (es. decisione, stabilità, sicurezza)

È il **fratello concettuale** del CANON Coq:
- ne rispetta il vocabolario
- ne riflette l’intenzione
- **non lo reimplementa**
- **non lo estende**

Il core non esegue calcoli, non simula processi, non prende decisioni operative.

---

## Cosa NON fa

Il layer `core/` **NON** deve contenere:
- numeri empirici
- soglie quantitative
- metriche
- simulazioni
- dinamiche temporali
- policy operative
- codice di orchestrazione
- I/O, logging, CLI, JSON, bridge

Se un file in `core/`:
- dipende dal tempo
- dipende dai dati
- dipende da esperimenti
- prende decisioni operative

👉 **è nel posto sbagliato.**

---

## Dipendenze consentite

Il layer `core/`:
- **non importa** alcun altro layer del Loventre Engine
- può usare solo:
  - standard library Python
  - definizioni locali interne a `core/`

Qualsiasi dipendenza verso:
- `metrics/`
- `regimes/`
- `barriers/`
- `dynamics/`
- `policy/`
- `bridges/`
- `experiments/`

è **vietata**.

---

## Ruolo architetturale

Il `core/` è:
- stabile
- lento a cambiare
- concettualmente minimale

Ogni altro layer **dipende semanticamente** dal core,  
ma il core **non dipende da nessuno**.

Se il Loventre Engine fosse distrutto,
il `core/` dovrebbe restare **intelligibile da solo**.

