# regimes

## Cosa fa

Il layer `regimes/` definisce **stati informazionali discreti** e le loro relazioni.

Contiene:
- definizioni di regimi
- ordini parziali o totali tra stati
- transizioni concettuali (non temporali)
- esclusività e compatibilità tra regimi

Risponde alla domanda:
> “In che tipo di stato informazionale si trova il sistema?”

---

## Cosa NON fa

Il layer `regimes/` **NON** deve:
- calcolare metriche
- simulare dinamiche temporali
- prendere decisioni normative
- introdurre soglie numeriche operative
- orchestrare processi

Se un file in `regimes/`:
- calcola numeri
- evolve nel tempo
- decide un esito finale

👉 **è nel posto sbagliato.**

---

## Dipendenze consentite

Il layer `regimes/` può importare:
- `core/`
- (eventualmente) tipizzazioni da `metrics/` **senza calcolo**

Non può importare:
- `dynamics/`
- `policy/`
- `experiments/`
- `bridges/`

---

## Ruolo architetturale

Il `regimes/` fornisce **struttura discreta** ai segnali continui.

È un layer di **interpretazione formale**, non di azione.

