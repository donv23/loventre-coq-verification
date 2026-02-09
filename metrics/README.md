# metrics

## Cosa fa

Il layer `metrics/` implementa **strumenti di misura quantitativa**.

Contiene esclusivamente:
- metriche numeriche
- indicatori continui o discreti
- stime, curve, profili
- trasformazioni quantitative dei dati

Le metriche producono **segnali**, non interpretazioni.

Questo layer risponde alla domanda:
> “Quali grandezze osservabili posso estrarre da una configurazione?”

Non risponde a:
> “Cosa significa questa configurazione?”

---

## Cosa NON fa

Il layer `metrics/` **NON** deve:
- classificare istanze
- definire regimi
- imporre soglie decisionali finali
- prendere decisioni operative
- contenere policy
- orchestrare flussi
- assumere semantica normativa (“buono”, “cattivo”, “sicuro”)

Se un file in `metrics/`:
- decide una classe
- etichetta un risultato
- forza una soglia come verità

👉 **sta violando il contratto.**

---

## Dipendenze consentite

Il layer `metrics/` può importare:
- `core/`
- standard library Python
- librerie numeriche (se presenti)

Non può importare:
- `policy/`
- `dynamics/`
- `experiments/`
- `bridges/`
- `regimes/` (se non come pura tipizzazione)

Le metriche **non devono sapere** come verranno usate.

---

## Ruolo architetturale

Il `metrics/` è:
- instabile (può evolvere)
- sperimentabile
- sostituibile

Se una metrica cambia,
il significato concettuale **non deve cambiare**.

Il layer `metrics/` è una **sonda**,  
non un giudice.

