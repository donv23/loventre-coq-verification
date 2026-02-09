# bridges

## Cosa fa

Il layer `bridges/` implementa **connessioni esplicite** tra il Loventre Engine Python e sistemi esterni.

Contiene:
- mapping dichiarati verso Coq
- esportazioni JSON
- loader e serializer
- generatori di snippet o witness

Risponde alla domanda:
> “Come viene rappresentato questo modello fuori dal motore?”

---

## Cosa NON fa

Il layer `bridges/` **NON** deve:
- introdurre nuova semantica
- correggere risultati
- prendere decisioni
- modificare metriche o dinamiche
- interpretare il significato dei dati

Se un bridge:
- decide cosa è corretto
- filtra risultati
- impone criteri

👉 **sta violando il contratto.**

---

## Dipendenze consentite

Il layer `bridges/` può importare:
- `core/`
- `metrics/`
- `regimes/`
- `barriers/`
- `dynamics/`
- `policy/` (solo per esportazione finale)

Non può importare:
- `experiments/`
- `utils/infra/`

---

## Ruolo architetturale

Il `bridges/` è:
- dichiarativo
- trasparente
- auditabile

Serve a **mostrare** il modello, non a cambiarlo.

