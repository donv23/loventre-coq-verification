# Loventre Engine – Architettura Fase 1–2

## 1. Visione d’insieme

In questa fase il Loventre Engine è costituito da **due algoritmi principali**:

* **Primo Algoritmo (Flow Engine 1D)**: genera e trasforma un flusso scalare nel tempo, mantenendo la memoria del percorso (history) e calcolando metriche informazionali di base.
* **Secondo Algoritmo (Trajectory Analyzer)**: osserva il flusso generato dal Primo Algoritmo, legge history + metriche e classifica il comportamento del sistema in diversi **regimi dinamici**.

Il tutto è orchestrato tramite uno script principale di esecuzione:

* `pipeline_test.py` → **run ufficiale** in un regime critico di riferimento.
* `pipeline_regimes_lab.py` → **laboratorio dei regimi**, per esplorare come cambiano stato finale e regime al variare dei parametri.

---

## 2. Primo Algoritmo – Motore di flusso 1D

### 2.1. Stato

Lo stato del sistema è rappresentato dalla classe `State`, che contiene un dizionario `data`. Nella Fase 1–2, la forma logica dello stato è:

```python
State({
  "value": <numero>,
  "history": [<sequenza di value>]
})
```

* `value`: valore scalare corrente del flusso.
* `history`: lista dei valori che il flusso ha assunto nel tempo (in questa versione: solo 3 passi: iniziale, dopo AlgorithmA, dopo AlgorithmB).

### 2.2. Pipeline dei transitions

La pipeline del Primo Algoritmo è costruita tramite `FlowPipeline`:

```python
pipeline = FlowPipeline(
    transitions=[
        apply_algorithm_a(param=CRITICAL_PARAM),
        apply_algorithm_b(factor=CRITICAL_FACTOR),
    ]
)
```

I due step principali sono:

1. **AlgorithmA** (via `apply_algorithm_a`) – primo stadio di trasformazione del flusso.
2. **AlgorithmB** (via `apply_algorithm_b`) – secondo stadio, tipicamente di amplificazione/scalatura.

Entrambi i transitions, dopo aver modificato `value`, invocano una funzione interna `_append_history(state)` che:

* garantisce l’esistenza di `data["history"]`,
* aggiunge il `value` corrente in coda alla history.

### 2.3. Metriche informazionali

Le metriche sono implementate in `flow_analyzer/core/metrics.py` e sono pensate come una **prima approssimazione informazionale**:

* **Curvature**:

  ```python
  curvature = value**2
  ```

  Interpretabile come intensità del flusso.

* **Entropy** (versione history-based):

  * calcolata come **media delle differenze assolute** tra valori consecutivi nella history;
  * se la history non è disponibile o troppo corta, si ricade su `abs(value)`.

* **Criticality**:

  ```python
  criticality = 1.0 se |value| > 1 else 0.0
  ```

  Rappresenta un semplice indicatore binario di “stato critico” del sistema.

La funzione `compute_all_metrics(state)` restituisce un dizionario:

```python
{
  "curvature": ...,
  "entropy": ...,
  "criticality": ...,
}
```

che viene propagato come parte del risultato della pipeline.

---

## 3. Secondo Algoritmo – Analizzatore di traiettoria

Il Secondo Algoritmo è definito in:

* `flow_analyzer/multiscale/trajectory_analyzer.py`

ed è concettualmente **esterno** al motore di flusso: non modifica lo stato, ma lo osserva.

### 3.1. Input e output

La funzione principale è:

```python
def analyze_trajectory(state, metrics) -> dict:
    ...
```

Input:

* `state`: lo `State` finale prodotto dal Primo Algoritmo, con almeno `value` e `history`.
* `metrics`: il dizionario con `curvature`, `entropy`, `criticality`.

Output: un dizionario `profile` che riassume il comportamento del flusso, ad esempio:

```python
{
  "regime": "critical_high_entropy",
  "length": 3,
  "avg_step": 3.0,
  "curvature": 36.0,
  "entropy": 3.0,
  "criticality": 1.0,
  "history_tail": [0, 2, 6],
  "notes": "Flusso accelerato e critico su scala breve.",
}
```

### 3.2. Uso di history e metriche

`analyze_trajectory`:

1. Estrae la `history` dallo stato, se presente, e ne misura la lunghezza.
2. Legge `curvature`, `entropy`, `criticality` dalle metriche.
3. Applica una serie di **regole soglia** per classificare il regime del flusso.
4. Costruisce un profilo con:

   * regime,
   * dimensione della history,
   * ampiezza media del passo (approssimata con entropy),
   * coda della history (`history_tail`),
   * una nota descrittiva.

---

## 4. Regimi dinamici del flusso

Il Secondo Algoritmo classifica il flusso in tre regimi principali:

### 4.1. Regime `stable_low_variation`

* **Condizioni (soglie attuali)**:

  * entropy ≤ 1.0
  * curvature ≤ 4.0

Interpretazione:

* il flusso ha intensità e variazioni piccole;
* il sistema è stabile e non critico;
* la history mostra cambiamenti modesti.

### 4.2. Regime `critical_high_entropy`

* **Condizioni (soglie attuali)**:

  * criticality ≥ 1.0
  * entropy ≥ 2.5
  * curvature ≥ 20.0

Interpretazione:

* il flusso è intenso e variabile;
* il sistema è in regime critico su scala breve;
* la history mostra salti significativi tra uno step e l’altro.

### 4.3. Regime `intermediate`

Tutti i casi che non rientrano nelle due categorie precedenti vengono classificati come `intermediate`.

Interpretazione:

* zona di transizione tra stabilità e regime critico;
* utile come “buffer” per future raffinazioni delle soglie o per introdurre sottoclassi più sofisticate.

---

## 5. Script di esecuzione

### 5.1. `pipeline_test.py` – Run ufficiale

Questo file esegue il **run ufficiale** del Loventre Engine nel regime critico di riferimento.

* Definisce costanti:

  ```python
  CRITICAL_PARAM = 2
  CRITICAL_FACTOR = 3
  ```

* Inizializza lo stato:

  ```python
  initial_state = State(data={"value": 0, "history": [0]})
  ```

* Costruisce la pipeline con AlgorithmA e AlgorithmB.

* Esegue la pipeline → ottiene `final_state, metrics`.

* Passa `final_state` e `metrics` al Secondo Algoritmo (`analyze_trajectory`).

* Stampa:

  * stato finale,
  * metriche finali,
  * profilo del flusso.

### 5.2. `pipeline_regimes_lab.py` – Laboratorio dei regimi

Questo file esplora una griglia di parametri `(param, factor)` (ad es. [1,2,3] × [1,2,3]) e, per ciascuna combinazione, esegue:

* la pipeline del Primo Algoritmo,
* il Secondo Algoritmo di analisi,
* la stampa sintetica di:

  * `value` finale,
  * metriche,
  * regime,
  * coda della history,
  * nota descrittiva.

Serve come **strumento di esplorazione** per capire come le scelte dei parametri influenzano il comportamento globale del motore.

---

## 6. Stato del progetto e prossimi passi

### 6.1. Cosa è stato completato

* Definizione di un **motore di flusso 1D** con memoria (history) e metriche informazionali di base.
* Implementazione di un **analizzatore di traiettoria** che classifica il comportamento del flusso in regimi dinamici.
* Creazione di uno script di **run ufficiale** (regime critico di riferimento).
* Creazione di un **laboratorio dei regimi** per esplorare sistematicamente lo spazio dei parametri.

### 6.2. Idee per il Terzo Algoritmo (Fase successiva)

La Fase 3 è orientata ad estendere il motore in direzione di maggiore struttura e “geometria”:

* passare da un singolo `value` a **più canali** (es. `value_x`, `value_y`, …) organizzati in una struttura (`channels`);
* definire una `history` per canale o una struttura di history più ricca;
* introdurre metriche che catturino non solo l’andamento di un singolo flusso, ma le **relazioni** tra flussi (interazioni, coerenza, divergenza);
* progettare un eventuale **Terzo Algoritmo** che lavori a livello più alto (ad esempio: riconoscimento di pattern multicanale, rilevazione di “configurazioni critiche” nello spazio dei canali, ecc.).

Questa architettura Fase 1–2 fornisce una base stabile su cui costruire livelli successivi di complessità, mantenendo chiara la separazione tra:

* generazione del flusso (Primo Algoritmo),
* analisi qualitativa del comportamento (Secondo Algoritmo),
* future estensioni geometriche e multiscala (Terzo Algoritmo e oltre).
