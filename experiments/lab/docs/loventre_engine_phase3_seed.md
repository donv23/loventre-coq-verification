# Loventre Engine – Architettura Fase 3 (Seed)

## 1. Obiettivo della Fase 3

Nelle fasi 1–2 il motore lavora su uno stato scalare:

- `value` come ampiezza corrente del flusso,
- `history` come lista 1D dei valori generati da Algorithm A → Algorithm B,
- un secondo algoritmo (`trajectory_analyzer`) che classifica la traiettoria in tre regimi:
  - `stable_low_variation`,
  - `intermediate`,
  - `critical_high_entropy`.

La Fase 3 introduce un **terzo livello di analisi**, che non guarda più solo a:

- un singolo valore (`value`),
- o alla sola entropia della history,

ma alla **configurazione multicanale** che si ottiene dalla history stessa, vista come una piccola geometria 1D a finestre.

Questo livello è implementato in:

- `multichannel_patterns.py`

e comunica con il resto del motore senza modificare l’architettura esistente (Fase 1–2 rimane valida).

## 2. Geometria a finestre sulla history

Dato:

```python
state.data["history"] = [x0, x1, x2, x3, ...]
## 7. Laboratorio di validazione dei regimi multicanale

Il file:

- `multichannel_patterns_lab.py`

contiene tre scenari sintetici che permettono di osservare in modo controllato
i regimi del terzo algoritmo:

- `slow_monotone`  
  history = [0, 1, 2, ..., 9]  
  → `regime_multichannel = synchronized_low_spread`, non critico.

- `runaway_monotone`  
  history = [0, 2, 4, 8, 16, 32, 64, 128]  
  → `regime_multichannel = synchronized_high_spread`, critico.

- `oscillatory_desync`  
  history = [0, 5, -5, 5, -5, 5, -5, 5, -5]  
  → `regime_multichannel = desynchronized_high_spread`, critico con sincronia ~0.

Questo laboratorio non modifica il motore, ma fornisce esempi “canonici” per
tutti i regimi multicanale definiti da `multichannel_patterns.py`.
## 8. Possibili evoluzioni (Fase 4 – design preliminare)

La Fase 3 (seed) introduce un terzo algoritmo di analisi geometrico-multicanale,
ma lo stato principale del motore rimane scalare:

```python
State(data={"value": ..., "history": [...]})
## 9. Estensione dello stato – Fase 4 (Modello B, seed)

A valle della Fase 3 (terzo algoritmo multicanale), è stata introdotta
una prima estensione "reale" dello stato del motore (Modello B).

Lo stato `State.data` non è più solo:

```python
{"value": ..., "history": [...]}
## 4.3 Run ufficiale: regime critico di riferimento (A + B + C)

Lo script `pipeline_test.py` definisce un *run ufficiale* del Loventre Engine
nel regime critico di riferimento:

- `CRITICAL_PARAM = 2`
- `CRITICAL_FACTOR = 3`

Lo stato iniziale è:

```python
State(data={"value": 0, "history": [0]})

## 4. Firma critica seed (param = 2, factor = 3)

In questa sezione fissiamo una convenzione operativa: scegliamo una specifica coppia di parametri
\((\text{param}, \text{factor}) = (2, 3)\) come **seed critico di riferimento** del Loventre Engine
per la Fase 3.

Questa scelta non è arbitraria: è giustificata dalla “firma” combinata che emerge dai test
numerici sui tre livelli di analisi implementati:

1. **Flusso 1D (history corta, 3 step)**  
   Per \((\text{param}, \text{factor}) = (2,3)\) il flusso 1D soddisfa:
   - valore finale: `value = 6`  
   - history finale: `history = [0, 2, 6]`
   - metriche 1D:
     - `curvature = 36.0`
     - `entropy = 3.0`
     - `criticality = 1.0`
   - regime 1D: `critical_high_entropy`  
   - note: “Flusso accelerato e critico su scala breve.”

   Questo descrive un flusso **fortemente accelerato** su orizzonte corto, con entropia elevata
   e marcatura di **criticità locale** (short-scale).

2. **Geometria multicanale (history corta, Pattern C)**  
   Sul vettore dei canali finali `channels = [0, 2, 6]` otteniamo:
   - `channels_spread = 6`
   - regime multicanale (short): `desynchronized_high_spread`
   - classificazione Pattern C:
     - `configuration_label = fully_critical_configuration`
     - `is_fully_critical = True`
     - `has_geometric_precritical = False`
     - `is_regular = False`

   Quindi la configurazione multicanale a 3 canali generata dal seed \((2,3)\) è:
   - **non regolare**,  
   - **non semplicemente pre-critica**,  
   - ma direttamente marcata come **fully_critical_configuration**.

   In altre parole, su scala corta, il seed \((2,3)\) rappresenta una **configurazione C‐critica piena**:
   la geometria discreta a 3 canali porta immediatamente in un regime di ampia diffusione (spread)
   e desincronizzazione, con etichetta critica forte.

3. **History lunga (21 step) e multicanale a finestre**

   Sullo stesso seed osserviamo anche il comportamento su una history più lunga (21 punti):

   - regime 1D lungo: `critical_high_entropy`
   - regime multicanale lungo: `synchronized_high_spread`
   - `channels_spread_long = 118098`
   - `is_multichannel_critical (long) = True`

   Qui compare un fenomeno fondamentale per la lettura teorica:

   - su **scala corta** la configurazione è **desynchronized_high_spread**  
     (molte vie esplorative locali, forte apertura dello spazio degli stati);
   - su **scala lunga** la stessa dinamica converge in un regime  
     **synchronized_high_spread** multicanale (alta ampiezza ma sincronizzata).

   Questo pattern è interpretabile come:
   - apertura esplosiva dello spazio computazionale a breve termine,
   - seguita da una **ricomposizione coerente** su scala più ampia.

### 4.1. Confronto con gli altri parametri (griglia 1–3 × 1–3)

La tabella `critical_signature_lab.py` mostra che, nella griglia
\(\text{param}, \text{factor} \in \{1,2,3\}\), compaiono tre coppie con
Pattern C marcato come `fully_critical_configuration` su history corta:

- \((\text{param}, \text{factor}) = (2,3)\)
- \((\text{param}, \text{factor}) = (3,2)\)
- \((\text{param}, \text{factor}) = (3,3)\)

Tutte e tre sono **configurazioni C pienamente critiche** su orizzonte corto. Tuttavia:

- le coppie con \(\text{param} = 1\) non raggiungono mai una configuration C pienamente critica,
  ma restano in regimi `regular_configuration` o `mixed_configuration`;
- il seed \((2,3)\) è il primo (per complessità combinatoria minima) che:
  - è **critical_high_entropy** in 1D su history corta,
  - è C-critico pieno (`fully_critical_configuration`) su 3 canali,
  - resta **critical_high_entropy** anche su history lunga,
  - e diventa **multicanale critico e sincronizzato** su scala lunga (`synchronized_high_spread`,
    `is_multichannel_critical = True`).

Per questo, convenzionalmente, adottiamo:

> **Definizione (Seed critico C del Loventre Engine).**  
> Si chiama *seed critico C* il pair \((\text{param}, \text{factor}) = (2,3)\), considerato come
> configurazione canonica del Loventre Engine in Fase 3, in quanto:
> - genera su history corta una configurazione `fully_critical_configuration` nel senso di Pattern C;
> - realizza un flusso `critical_high_entropy` sia su scala corta che lunga;
> - mostra il passaggio da una geometria **desynchronized_high_spread** (locale)
>   a una geometria **synchronized_high_spread** (globale) in versione multicanale.

Questa definizione fornisce un **testimone costruttivo** (un “esempio concreto”) di una dinamica
che presenta contemporaneamente:

- **criticità locale** (apertura esplosiva dello spazio degli stati),
- **coerenza globale** (ricomposizione sincronizzata a lungo raggio),
- e una struttura geometrica discreta chiaramente distinguibile rispetto ai regimi regolari
  e pre-critici.

Nella dimostrazione teorica della Teoria di Loventre, il seed \((2,3)\) potrà essere usato
come prototipo esplicito di “configurazione C‐critica” per ancorare la parte formale del
risultato a un modello dinamico finito e verificabile algoritmicamente.

### 4.2 Lemma – Seed critico C del Loventre Engine

**Lemma 4.2 (Seed critico C).**  
Nel modello discreto implementato dal Loventre Engine (Fase 3), fissata la griglia
\(\text{param}, \text{factor} \in \{1,2,3\}\), il pair
\[
(\text{param}, \text{factor}) = (2,3)
\]
costituisce un **seed critico C canonico** nel seguente senso:

1. (Criticità 1D su scala corta)  
   La dinamica 1D generata da \((2,3)\) su history corta (3 step) soddisfa:
   - `regime_1D_short = critical_high_entropy`,
   - `criticality = 1.0`,
   - history finale `history_short = [0, 2, 6]`.

2. (Configurazione C pienamente critica su 3 canali)  
   Il vettore dei canali finali `channels = [0, 2, 6]` associato allo stesso seed è classificato da
   `Pattern C` come:
   - `configuration_label = fully_critical_configuration`,
   - `is_fully_critical = True`,
   - `has_geometric_precritical = False`,
   - `is_regular = False`.

3. (Persistenza della criticità su history lunga)  
   Estendendo la history a 21 step con lo stesso seed \((2,3)\), si ha:
   - `regime_1D_long = critical_high_entropy`,
   - `is_multichannel_critical_long = True`,
   - regime multicanale lungo `multi_long = synchronized_high_spread`,
   - `channels_spread_long = 118098` (spread elevato ma sincronizzato).

4. (Minima complessità combinatoria nella griglia considerata)  
   Nella griglia \(\text{param}, \text{factor} \in \{1,2,3\}\) solo i tre pair
   \((2,3)\), \((3,2)\), \((3,3)\) realizzano una `fully_critical_configuration` su
   history corta. Tra questi, \((2,3)\) è quello con:
   - parametri più bassi in modulo,
   - e firma completa: criticità 1D corta + criticità 1D lunga + criticità multicanale
     sia corta (Pattern C fully critical) sia lunga (multicanale critico sincronizzato).

In virtù di queste proprietà, \((2,3)\) viene assunto come **seed critico C di riferimento**
per la fase 3 del Loventre Engine.

---

**Dimostrazione (computazionale).**  
Il lemma è verificato eseguendo i moduli:

- `pipeline_test.py`
- `pipeline_regimes_lab.py`
- `pipeline_multichannel_long_history.py`
- `multichannel_patterns_lab.py`
- `critical_signature_lab.py`

e leggendo, per \((\text{param}, \text{factor}) = (2,3)\), le seguenti uscite:

- da `pipeline_test.py`:
  - `history = [0, 2, 6]`, `regime_1D = critical_high_entropy`,
  - `channels = [0, 2, 6]`, `channels_spread = 6`,
  - Pattern C: `configuration_label = fully_critical_configuration`.

- da `pipeline_regimes_lab.py`:
  - conferma del regime `critical_high_entropy` 1D per \((2,3)\),
  - conferma di Pattern C `fully_critical_configuration` su history corta.

- da `pipeline_multichannel_long_history.py`:
  - regime lungo: `regime_1D_long = critical_high_entropy`,
  - regime multicanale lungo: `multi_long = synchronized_high_spread`,
  - `is_multichannel_critical = True`,
  - `channels_spread_long = 118098`.

- da `critical_signature_lab.py`:
  - tabella che mostra, nella griglia \(\{1,2,3\} \times \{1,2,3\}\), solo tre seed
    con `PatternC = fully_critical_configuration`, e identifica \((2,3)\) come
    “seed critico di riferimento”.

Questi output fissano in modo algoritmico (e riproducibile) le proprietà elencate nei punti (1)–(4),
da cui segue la tesi del lemma.

## Seed discreto delle regioni critiche (param, factor)

In questa fase fissiamo un *seed discreto* del comportamento dell’engine sul piano dei parametri \((param, factor)\) con valori in \{1, 2, 3\}.

Per ogni coppia \((param, factor)\) abbiamo estratto, dai moduli di laboratorio

- `pipeline_regimes_lab.py`              (history corta)
- `pipeline_multichannel_long_history.py` (history lunga)
- `pattern_classifier.py`
- `critical_signature_lab.py`

una firma qualitativa composta da:

- regime 1D su history corta e lunga;
- regime multicanale su history corta e lunga;
- classificazione Pattern C su history corta;
- ampiezza di canale `channels_spread` su history corta e lunga;
- informazione se il regime multicanale lungo è critico (`multi_critical=True/False`).

A partire da questa firma, il modulo `critical_regions_seed.py` assegna ad ogni coppia \((param, factor)\) una etichetta di *regione*:

- `regular_region`  
  comportamento regolare, senza struttura precritica sul Pattern C.
- `precritical_region`  
  comportamento che mostra elementi precritici (Pattern C misto o geometric_precritical).
- `critical_region`  
  comportamento pienamente critico sul Pattern C.

### Tabella delle regioni per (param, factor) ∈ {1,2,3} × {1,2,3}

La tabella seguente riassume il seed discreto che abbiamo fissato:

| param | factor | region_type        | Pattern C (short)                    | multi_critical (long) | spread short | spread long |
|-------|--------|--------------------|--------------------------------------|------------------------|--------------|-------------|
| 1     | 1      | regular_region     | regular_configuration                | False                  | 1            | 1           |
| 1     | 2      | regular_region     | regular_configuration                | True                   | 2            | 1024        |
| 1     | 3      | precritical_region | mixed_configuration                  | True                   | 3            | 59049       |
| 2     | 1      | regular_region     | regular_configuration                | False                  | 2            | 2           |
| 2     | 2      | precritical_region | geometric_precritical_configuration  | True                   | 4            | 2048        |
| 2     | 3      | critical_region    | fully_critical_configuration         | True                   | 6            | 118098      |
| 3     | 1      | precritical_region | geometric_precritical_configuration  | True                   | 3            | 3           |
| 3     | 2      | critical_region    | fully_critical_configuration         | True                   | 6            | 3072        |
| 3     | 3      | critical_region    | fully_critical_configuration         | True                   | 9            | 177147      |

Qui:

- “Pattern C (short)” è la classificazione di configurazione ottenuta dal Pattern C sulla history corta;
- “multi_critical (long)” indica se, sulla history lunga, il regime multicanale è critico;
- “spread short” è `channels_spread` sulla history corta;
- “spread long” è `channels_spread` sulla history lunga.

### Seed critico canonico

All’interno di questo seed discreto, assumiamo come *seed critico canonico* la coppia

- \((param, factor) = (2, 3)\),

che soddisfa contemporaneamente:

- Pattern C pienamente critico su history corta  
  (`fully_critical_configuration`);
- regime 1D critico ad alta entropia;
- regime multicanale critico ad alta diffusione su history lunga (`synchronized_high_spread`, `multi_critical=True`);
- crescita dello spread su history lunga pari a `118098`, che realizza una esplosione controllata ma non comprimibile in una regione regolare o precritica.

Questa coppia svolge il ruolo di *firma minima* della regione critica: è il punto da cui estendere la caratterizzazione delle regioni critiche in senso continuo e, nella teoria, il candidato naturale a modellare una dinamica intrinsecamente non riducibile ai comportamenti regolari e precritici.

## Seed discreto delle regioni critiche del Loventre Engine

In questa fase fissiamo un **seed discreto** di configurazioni del Loventre Engine,
parametrizzate da una coppia di interi positivi \((\mathrm{param}, \mathrm{factor}) \in \{1,2,3\} \times \{1,2,3\}\).

Per ciascuna coppia \((\mathrm{param}, \mathrm{factor})\), l’engine è stato eseguito in due regimi temporali:

- **history corta**: traiettoria ridotta su cui si misura il Pattern C e lo spread finale dei canali;
- **history lunga**: traiettoria iterata (ad es. 10 iterazioni) su cui si misura la diffusione multicanale a lungo termine e la presenza di regime critico multicanale.

Su questa base abbiamo fissato, per ogni coppia \((\mathrm{param}, \mathrm{factor})\), i seguenti oggetti discreti:

- `region_type`  
  - `regular_region`  
  - `precritical_region`  
  - `critical_region`
- `pattern_label_short` (Pattern C su history corta)  
  - `regular_configuration`  
  - `mixed_configuration`  
  - `geometric_precritical_configuration`  
  - `fully_critical_configuration`
- `multi_critical_long`  
  - Booleano che indica se, su history lunga, il regime multicanale è critico ad alta diffusione.
- `spread_short`  
  - Valore discreto dello spread finale dei canali su history corta.
- `spread_long`  
  - Valore discreto dello spread multicanale su history lunga.

Questi dati sono codificati nel modulo Python `critical_regions_api.py` come mappa

\[
(\mathrm{param}, \mathrm{factor}) \longmapsto
\{\texttt{region\_type}, \texttt{pattern\_label\_short},
\texttt{multi\_critical\_long}, \texttt{spread\_short},
\texttt{spread\_long}\}.
\]

### Tabella del seed discreto (param, factor)

Riassumiamo il contenuto della mappa discreta:

- \((1,1)\):  
  - `region_type` = `regular_region`  
  - `pattern_label_short` = `regular_configuration`  
  - `multi_critical_long` = False  
  - `spread_short` = 1  
  - `spread_long` = 1  

- \((1,2)\):  
  - `region_type` = `regular_region`  
  - `pattern_label_short` = `regular_configuration`  
  - `multi_critical_long` = True  
  - `spread_short` = 2  
  - `spread_long` = 1024  

- \((1,3)\):  
  - `region_type` = `precritical_region`  
  - `pattern_label_short` = `mixed_configuration`  
  - `multi_critical_long` = True  
  - `spread_short` = 3  
  - `spread_long` = 59049  

- \((2,1)\):  
  - `region_type` = `regular_region`  
  - `pattern_label_short` = `regular_configuration`  
  - `multi_critical_long` = False  
  - `spread_short` = 2  
  - `spread_long` = 2  

- \((2,2)\):  
  - `region_type` = `precritical_region`  
  - `pattern_label_short` = `geometric_precritical_configuration`  
  - `multi_critical_long` = True  
  - `spread_short` = 4  
  - `spread_long` = 2048  

- \((2,3)\):  
  - `region_type` = `critical_region`  
  - `pattern_label_short` = `fully_critical_configuration`  
  - `multi_critical_long` = True  
  - `spread_short` = 6  
  - `spread_long` = 118098  

- \((3,1)\):  
  - `region_type` = `precritical_region`  
  - `pattern_label_short` = `geometric_precritical_configuration`  
  - `multi_critical_long` = True  
  - `spread_short` = 3  
  - `spread_long` = 3  

- \((3,2)\):  
  - `region_type` = `critical_region`  
  - `pattern_label_short` = `fully_critical_configuration`  
  - `multi_critical_long` = True  
  - `spread_short` = 6  
  - `spread_long` = 3072  

- \((3,3)\):  
  - `region_type` = `critical_region`  
  - `pattern_label_short` = `fully_critical_configuration`  
  - `multi_critical_long` = True  
  - `spread_short` = 9  
  - `spread_long` = 177147  

### Seed critico canonico

Definiamo il **seed critico canonico** come la coppia

\[
(\mathrm{param}^\*, \mathrm{factor}^\*) = (2,3),
\]

caratterizzata da:

- `region_type` = `critical_region`;
- `pattern_label_short` = `fully_critical_configuration` su history corta;
- regime 1D di tipo `critical_high_entropy`;
- regime multicanale critico ad alta diffusione su history lunga
  (`multi_critical_long` = True con `spread_long` = 118098).

Nel codice, questa scelta è implementata dalla funzione

```python
is_seed_canonico(param, factor)

## 7. Bridge concettuale verso la Teoria di Loventre

Questa Fase 3 del Loventre Engine non è solo un “giocattolo numerico”, ma un **modello discreto minimale** che realizza, in piccolo, la struttura concettuale usata nella Teoria di Loventre per distinguere:

- **regimi regolari** (non critici, P-like),
- **regimi pre-critici** (di soglia),
- **regimi critici** (NP-like nel senso informazionale).

L’idea è: ogni algoritmo iterativo (param, factor) genera un flusso che può essere visto come una **geometria discreta**; la classificazione in *regular / precritical / critical region* è la versione “seed” della separazione strutturale che poi, nella dimostrazione formale, viene trasportata su varietà informazionali continue.

### 7.1 Oggetti dinamici centrali

La Fase 3 introduce quattro livelli di osservazione del flusso:

1. **Flusso 1D breve**  
   - History corta: ad esempio `[0, 2, 6]`.  
   - Metriche associate: `curvature`, `entropy`, `criticality`.  
   - Regime 1D: `stable_low_variation`, `intermediate`, `critical_high_entropy`, ecc.

2. **Flusso multicanale (finestre)**  
   - La history viene “spacchettata” in finestre sovrapposte; ogni finestra è vista come un piccolo vettore (canale).  
   - Metriche multicanale:
     - `average_channel_variance`
     - `average_spatial_spread`
     - `synchrony_ratio`
   - Regime multicanale: `synchronized_low_spread`, `synchronized_high_spread`, `desynchronized_high_spread`, `mixed_intermediate`.

3. **Pattern C sulla history corta**  
   - Si applica un classificatore sui tre valori finali `[a, b, c] = [value_{t-2}, value_{t-1}, value_t]`.  
   - Questo pattern viene etichettato come:
     - `regular_configuration`
     - `mixed_configuration`
     - `geometric_precritical_configuration`
     - `fully_critical_configuration`  
   - Output logico:  
     - `configuration_label` (una delle quattro)  
     - `is_fully_critical` (boolean)  
     - `has_geometric_precritical` (boolean)  
     - `is_regular` (boolean)

4. **Regione critica (Critical Region)**  
   - Dal combinato di:
     - pattern C sulla history corta,
     - comportamento multicanale su history lunga,
     - spread dei canali (short/long),
   - si ottiene una classificazione discreta:
     - `regular_region`
     - `precritical_region`
     - `critical_region`

Questa classificazione è implementata nei moduli:

- `critical_signature_lab.py`
- `critical_regions_seed.py`
- `critical_regions_api.py`

### 7.2 Tripla firma discreta di un algoritmo (param, factor)

Per ogni coppia discreta `(param, factor)` definiamo tre livelli di firma:

1. **Firma breve (short seed)**  
   Dati:
   - `regime_1d_short`
   - `regime_multichannel_short`
   - `pattern_configuration_short` (Pattern C)
   - `spread_short` (ampiezza dei canali finali, e.g. `6` per `[0, 2, 6]`)

2. **Firma lunga (long seed)**  
   Dati:
   - `regime_1d_long`
   - `regime_multichannel_long`
   - `spread_long`
   - `is_multichannel_critical_long` (boolean)

3. **Tipo di regione**  
   Dato:
   - `region_type ∈ {regular_region, precritical_region, critical_region}`

Operativamente, la Fase 3 costruisce queste firme partendo dalle tabelle generate da:

- `pipeline_regimes_lab.py`
- `pipeline_multichannel_long_history.py`
- `multichannel_patterns_lab.py`
- `critical_signature_lab.py`
- `critical_regions_seed.py`
- `critical_regions_api.py`

### 7.3 Seed canonico critico

Dalle tabelle ottenute in laboratorio, il motore individua un **seed canonico critico**:

- `(param = 2, factor = 3)`

Per questo seed abbiamo:

- **History corta finale**: `[0, 2, 6]`
- **Pattern C**:
  - `configuration_label = fully_critical_configuration`
  - `is_fully_critical = True`
- **Regime 1D breve**:
  - `regime_1d_short = critical_high_entropy`
  - `criticality = 1.0`
- **Regime multicanale breve**:
  - `regime_multichannel_short = desynchronized_high_spread`
  - `spread_short = 6`
- **Regime su history lunga**:
  - `regime_1d_long = critical_high_entropy`
  - `regime_multichannel_long = synchronized_high_spread`
  - `is_multichannel_critical_long = True`
  - `spread_long = 118098` (esplosione combinatoria della dispersione)

La regione corrispondente risulta:

- `region_type = critical_region`
- `is_seed_canonico = True` (nel mapping definito in `critical_regions_api.py`)

Questo seed `(2, 3)` è il **prototipo discreto di una dinamica “fortemente critica”**: corto raggio altamente entropico, pattern completamente critico, e divergenza multicanale a lungo raggio.

### 7.4 Mapping informale verso “classi P-like / NP-like”

Nel contesto della Teoria di Loventre, la distinzione fra regioni può essere letta come una **metafora dinamica** di differenti classi di complessità:

- **regular_region**  
  - Flussi stabili o poco varianti, senza pattern critici robusti.  
  - Lettura qualitativa: **regime P-like**, dove la geometria informazionale rimane quasi piatta e controllata.

- **precritical_region**  
  - Presenza di pattern geometrici che anticipano la criticità (`geometric_precritical_configuration`), ma senza ancora una piena esplosione su scala lunga.  
  - Lettura qualitativa: **regime di soglia**, dove il sistema inizia ad accumulare “tensione geometrica” ma non ha ancora una criticità completa.

- **critical_region**  
  - Pattern completamente critici su history corta (`fully_critical_configuration`), combinati con criticità multicanale su history lunga.  
  - Lettura qualitativa: **regime NP-like**, dove la geometria informazionale mostra curvature elevate, configurazioni altamente sparse, e sincronizzazione critica su molte scale.

Questa interpretazione non pretende di identificare esattamente le classi P e NP della complessità tradizionale, ma fornisce un **modello dinamico-geometrico** in cui:

- certi algoritmi restano confinati in regioni regolari;
- altri possono accedere a regioni critiche dotate di proprietà strutturali molto più “pesanti” (spread esplosivo, pattern pienamente critici, ecc.).

### 7.5 Schema informale del Teorema di Loventre (versione seed)

In versione “seed discreto”, il nucleo concettuale del Teorema di Loventre può essere schematizzato così:

1. Ogni algoritmo iterativo del motore (param, factor) induce una **tripla firma discreta**:
   - firma breve (1D + multicanale + Pattern C),
   - firma lunga,
   - tipo di regione (`regular / precritical / critical`).

2. Esiste almeno un **seed canonico critico** (qui `(param=2, factor=3)`) tale che:
   - la sua firma breve è pienamente critica (`fully_critical_configuration` + `critical_high_entropy`);
   - la sua firma lunga mostra criticità multicanale persistente e spread esplosivo;
   - la regione associata è `critical_region`.

3. Le regioni regolari, precritiche e critiche sono **separate in modo strutturale**:  
   la dinamica di un algoritmo che rimane confinato in `regular_region` non può, senza cambiare struttura, riprodurre le proprietà geometriche e di dispersione del seed canonico in `critical_region`.

4. Questo schema discreto fornisce un **modello minimalista** di separazione fra:
   - algoritmi che abitano regioni “P-like” (regolari),
   - e algoritmi che attivano regioni “NP-like” (critiche),
   entro la geometria informazionale generata dal Loventre Engine.

Nella dimostrazione formale (in Coq e nel quadro continuo), questa struttura seed viene sollevata a:

- manifolds informazionali con curvature non banali,
- funzioni di energia/entropia,
- e una nozione di separazione strutturale fra classi di flussi (P-like / NP-like) che non è meramente misuristica, ma **geometrica**.

## 3. Bridge del seed tra simulazione e teoria

In questa fase considero il Loventre Engine confinato al reticolo finito
param, factor ∈ {1,2,3}. Per ogni coppia (param, factor) il codice
`loventre_theory_bridge_seed.py` definisce una firma discreta:

SeedTheorySignature(param, factor) =
  (region_type,
   pattern_short,
   regime_1d_short, regime_1d_long,
   regime_multi_short, regime_multi_long,
   spread_short, spread_long,
   multi_critical_long,
   is_canonical_seed,
   complexity_flavour).

In questo schema:

- region_type ∈ {regular_region, precritical_region, critical_region}
  descrive la natura geometrico-dinamica del seed.
- pattern_short cattura la configurazione Pattern C su history corta
  (regular_configuration, mixed_configuration,
   geometric_precritical_configuration, fully_critical_configuration).
- regime_1d_short, regime_1d_long descrivono il comportamento del flusso
  1D (stable_low_variation, intermediate, critical_high_entropy).
- regime_multi_short, regime_multi_long descrivono il comportamento
  multicanale a finestra mobile (mixed_intermediate,
  desynchronized_high_spread, synchronized_low_spread,
  synchronized_high_spread).
- spread_short, spread_long misurano lo spread globale dei canali
  su history corta e lunga.
- multi_critical_long indica se, su history lunga, il profilo
  multicanale è effettivamente critico.
- is_canonical_seed indica se il seed è scelto come riferimento
  canonico all’interno della sua regione.
- complexity_flavour ∈ {P_like, threshold_precritical, NP_like}
  è l’etichetta di “complessità fenomenologica” associata alla regione.

### 3.1 Classificazione discreta delle regioni

La funzione di bridge assegna ad ogni seed (param, factor) una
flavour di complessità:

- P_like se region_type = regular_region.
- NP_like se region_type = critical_region.
- threshold_precritical se region_type = precritical_region.

Per il reticolo param, factor ∈ {1,2,3} ottengo quindi:

- Semi P_like:
  (1,1), (1,2), (2,1) con region_type = regular_region
  e complexity_flavour = P_like.

- Semi threshold_precritical:
  (1,3), (2,2), (3,1) con region_type = precritical_region
  e complexity_flavour = threshold_precritical.

- Semi NP_like:
  (2,3), (3,2), (3,3) con region_type = critical_region
  e complexity_flavour = NP_like.

Questa classificazione è coerente con l’analisi precedente delle
firme critiche (Pattern C) e delle traiettorie multicanale su history
corta e lunga.

### 3.2 Seed critico canonico

Definisco seed critico canonico il seed (param, factor) che soddisfa
contemporaneamente:

1. region_type = critical_region;
2. pattern_short = fully_critical_configuration;
3. regime_1d_short = regime_1d_long = critical_high_entropy;
4. regime_multi_long = synchronized_high_spread;
5. multi_critical_long = True;
6. is_canonical_seed = True;
7. complexity_flavour = NP_like.

Sulla griglia {1,2,3}×{1,2,3} il codice identifica come unico seed
critico canonico la coppia:

(param, factor) = (2,3).

In altre parole, (2,3) è il seed che massimizza in modo strutturato
la curvatura informazionale, l’entropia e la diffusione multicanale,
costituendo così il prototipo NP_like nel modello finito del Loventre
Engine.

## 8. Classificazione di complessità: P_like, threshold_precritical, NP_like

L’output combinato dei moduli

- `critical_signature_lab.py`,
- `critical_regions_seed.py`,
- `critical_regions_api.py`,
- `loventre_theory_bridge_seed.py`

permette di associare ad ogni coppia \((param, factor) \in \{1,2,3\} \times \{1,2,3\}\) una
**firma dinamica completa**:

- un tipo di regione:  
  `regular_region`, `precritical_region`, `critical_region`;
- un pattern geometrico corto (Pattern C):  
  `regular_configuration`, `mixed_configuration`,  
  `geometric_precritical_configuration`, `fully_critical_configuration`;
- un regime 1D corto/lungo:  
  `stable_low_variation`, `intermediate`, `critical_high_entropy`;
- un regime multicanale corto/lungo:  
  `mixed_intermediate`, `synchronized_low_spread`,  
  `synchronized_high_spread`, `desynchronized_high_spread`;
- due misure di diffusione:  
  `spread_short`, `spread_long`;
- un flag di multicanalità critica a lungo termine:  
  `multi_critical_long ∈ {True, False}`.

Su questa base, il modulo `loventre_theory_bridge_seed.py` definisce una mappa

\[
\mathrm{complexity\_flavour} : \{1,2,3\} \times \{1,2,3\}
\longrightarrow \{\texttt{P\_like},\ \texttt{threshold\_precritical},\ \texttt{NP\_like}\},
\]

cioè assegna ad ogni seed un **“flavour di complessità”** che è un’analogia
strutturale con le classi di complessità (P, frontiera di soglia, NP) nel
quadro finito del Loventre Engine.

### 8.1. Definizione (flavour di complessità locale)

Sia \((param, factor)\) un seed della griglia \(\{1,2,3\}^2\).
Indichiamo con:

- `region_type(param, factor)` ∈ {`regular_region`, `precritical_region`, `critical_region`};
- `pattern_short(param, factor)` ∈ {`regular_configuration`, `mixed_configuration`,  
  `geometric_precritical_configuration`, `fully_critical_configuration`};
- `regime_1d_long(param, factor)` ∈ {`stable_low_variation`, `intermediate`, `critical_high_entropy`};
- `regime_multi_long(param, factor)` ∈ {`synchronized_low_spread`, `synchronized_high_spread`,
  `desynchronized_high_spread`, `mixed_intermediate`};
- `spread_short(param, factor)`, `spread_long(param, factor)` ∈ ℕ;
- `multi_critical_long(param, factor)` ∈ {True, False}.

Definiamo il **flavour di complessità** di \((param, factor)\),
denotato `complexity_flavour(param, factor)`, secondo le seguenti regole:

1. **Caso P_like (regime regolare controllato)**  
   Diciamo che \((param, factor)\) è di tipo `P_like` se:

   - `region_type = regular_region`,  
   - `multi_critical_long = False`,  
   - la diffusione multicanale a lungo termine rimane controllata
     (cioè `spread_long` non esplode combinatorialmente rispetto a `spread_short`).

   Intuitivamente, questi seed corrispondono a dinamiche in cui
   il flusso informazionale rimane “polinomialmente controllato”:
   le perturbazioni locali non generano un runaway combinatorio
   nello spazio dei canali.

2. **Caso threshold_precritical (regime di soglia strutturale)**  
   Diciamo che \((param, factor)\) è di tipo `threshold_precritical` se:

   - `region_type = precritical_region`,  
   - `pattern_short` è di tipo `mixed_configuration` o
     `geometric_precritical_configuration`,  
   - `multi_critical_long = True`,  
   - la diffusione `spread_long` è già molto più ampia di `spread_short`,
     ma la firma non soddisfa ancora tutte le condizioni del caso critico canonico.

   Questi seed rappresentano la **frontiera strutturale di soglia**:
   dinamiche che non sono più pienamente regolari, ma neanche ancora
   “massimamente critiche” nel senso del seed canonico. Sono i punti
   in cui piccole variazioni parametriche possono spingere il sistema
   verso un comportamento fortemente critico.

3. **Caso NP_like (regime critico pienamente sviluppato)**  
   Diciamo che \((param, factor)\) è di tipo `NP_like` se:

   - `region_type = critical_region`,  
   - `pattern_short = fully_critical_configuration`,  
   - `regime_1d_long = critical_high_entropy`,  
   - `regime_multi_long = synchronized_high_spread`,  
   - `multi_critical_long = True`,  
   - la diffusione multicanale a lungo termine è
     **combinatorialmente più ampia** di quella a breve termine:

     \[
       spread\_long \gg spread\_short
     \]

     in modo strutturato (come mostrato dai casi, ad esempio,
     \((2,3), (3,2), (3,3)\), dove `spread_long` assume valori
     come 118098, 3072, 177147, a fronte di spread corti 6, 6, 9).

   In questi seed, una configurazione localmente critica (Pattern C fully_critical)
   viene amplificata da una dinamica che rimane critica anche su history lunga
   e che sincronizza una diffusione spaziale molto ampia. In termini analogici,
   questi seed si comportano come **prototipi NP_like**: una piccola struttura
   critica locale genera un’espansione combinatoria della configurazione globale.

### 8.2. Interpretazione informazionale

Nel modello finito del Loventre Engine, il flavour di complessità non è una
classe di complessità nel senso classico (Turing), ma un’etichetta
**morfologica** assegnata allo stato di flusso:

- I seed `P_like` corrispondono a dinamiche dove la curvatura informazionale
  e l’entropia crescono in modo controllato, e la struttura multicanale non
  entra in regime di runaway sincronizzato. Sono analoghi a processi che
  richiedono risorse “polinomiali” rispetto alla scala del problema.

- I seed `threshold_precritical` descrivono la frontiera, in cui la combinazione
  di pattern precritici (Pattern C) e multicanalità critica a lungo termine
  indica che il sistema è vicino a un cambiamento di fase informazionale.
  Sono i candidati naturali per definire condizioni di soglia (threshold)
  in cui la distinzione P_like / NP_like viene preparata geometricamente.

- I seed `NP_like` rappresentano regimi in cui:
  - la curvatura informazionale e l’entropia sono elevate,
  - la configurazione locale è già pienamente critica (Pattern C fully_critical),
  - la dinamica a lungo termine è multicanale, sincronizzata e ad ampia diffusione.
  
  Questo combina **criticità locale** e **diffusione globale sincronizzata**:
  la struttura locale “semina” una complessità globale che non è comprimibile
  in termini di un seed P_like con la stessa geometria.

### 8.3. Il seed critico canonico (2,3) come prototipo NP_like

Nel modello finito corrente, la griglia \(\{1,2,3\} \times \{1,2,3\}\)
mostra che:

- \((2,3)\) è l’unico seed che soddisfa contemporaneamente:
  - `region_type = critical_region`,
  - `pattern_short = fully_critical_configuration`,
  - `regime_1d_short = critical_high_entropy`,
  - `regime_1d_long = critical_high_entropy`,
  - `regime_multi_short = desynchronized_high_spread`,
  - `regime_multi_long = synchronized_high_spread`,
  - `multi_critical_long = True`,
  - diffusione multicanale lunga `spread_long = 118098`,
    a fronte di uno spread corto `spread_short = 6`.

Per questo motivo il modulo `critical_regions_api.py` lo etichetta come
`is_seed_canonico = True`, e il bridge teorico gli assegna

\[
\mathrm{complexity\_flavour}(2,3) = \texttt{NP\_like}.
\]

In altre parole, \((param, factor) = (2,3)\) è il seed che massimizza in modo
strutturato la curvatura informazionale, l’entropia e la diffusione multicanale,
costituendo il **prototipo NP_like** nel modello finito del Loventre Engine.

Nei capitoli successivi, questo seed verrà utilizzato come **testimone concreto**
nella strategia di separazione tra comportamenti P_like e NP_like nel senso del
Teorema di Loventre: nessun seed P_like, a parità di vincoli strutturali, è in
grado di riprodurre la firma informazionale completa del seed critico canonico
\((2,3)\).

## 9. Separazione locale P_like / NP_like nel modello finito

In questa sezione formalizziamo la separazione, nel modello finito del
Loventre Engine, tra i seed di tipo `P_like` e il seed critico canonico
di tipo `NP_like`, identificato dalla coppia:

\[
(param, factor) = (2,3).
\]

L’idea è la seguente: il seed \((2,3)\) realizza una combinazione
di proprietà (regione critica, Pattern C pienamente critico, dinamica
1D ad alta entropia, diffusione multicanale sincronizzata ad ampia
spread, multicanalità critica a lungo termine) che **nessun seed
P_like** è in grado di riprodurre simultaneamente.

### 9.1. Firma strutturale dei seed

Per ogni seed \((param, factor) \in \{1,2,3\} \times \{1,2,3\}\)
consideriamo il vettore di attributi:

\[
\Sigma(param, factor) =
\Big(
  region\_type,\ pattern\_short,\ regime\_1d\_short,\ regime\_1d\_long,\ 
  regime\_multi\_short,\ regime\_multi\_long,\ 
  spread\_short,\ spread\_long,\ multi\_critical\_long
\Big),
\]

dove:

- `region_type` ∈ {`regular_region`, `precritical_region`, `critical_region`};
- `pattern_short` ∈ {`regular_configuration`, `mixed_configuration`,
  `geometric_precritical_configuration`, `fully_critical_configuration`};
- `regime_1d_short`, `regime_1d_long` ∈
  {`stable_low_variation`, `intermediate`, `critical_high_entropy`};
- `regime_multi_short`, `regime_multi_long` ∈
  {`mixed_intermediate`, `synchronized_low_spread`,  
   `synchronized_high_spread`, `desynchronized_high_spread`};
- `spread_short`, `spread_long` ∈ ℕ misurano l’ampiezza della diffusione
  sui canali (history corta / lunga);
- `multi_critical_long` ∈ {True, False} indica se il regime multicanale
  lungo è critico.

Dai moduli di laboratorio abbiamo estratto che, per il seed canonico:

- `region_type(2,3) = critical_region`;
- `pattern_short(2,3) = fully_critical_configuration`;
- `regime_1d_short(2,3) = critical_high_entropy`;
- `regime_1d_long(2,3) = critical_high_entropy`;
- `regime_multi_short(2,3) = desynchronized_high_spread`;
- `regime_multi_long(2,3) = synchronized_high_spread`;
- `spread_short(2,3) = 6`;
- `spread_long(2,3) = 118098`;
- `multi_critical_long(2,3) = True`;
- `complexity_flavour(2,3) = NP_like`;
- `is_seed_canonico(2,3) = True`.

Questa è la **firma strutturale critica canonica** del modello finito.

### 9.2. Proprietà caratterizzante il seed canonico

Definiamo una formula puramente strutturale \(\varphi\) sui seed:

\[
\varphi(param, factor) \iff
\begin{cases}
region\_type = critical\_region, \\
pattern\_short = fully\_critical\_configuration, \\
regime\_1d\_long = critical\_high\_entropy, \\
regime\_multi\_long = synchronized\_high\_spread, \\
multi\_critical\_long = True.
\end{cases}
\]

Osserviamo che:

- tutti i seed `P_like` hanno `region_type = regular_region`,  
  quindi **non** possono soddisfare \(\varphi\);
- tutti i seed `precritical_region` (`threshold_precritical`) non
  hanno `pattern_short = fully_critical_configuration`, quindi
  non soddisfano \(\varphi\);
- i seed di tipo `critical_region` con `pattern_short = fully_critical_configuration`
  (come \((2,3), (3,2), (3,3)\)) soddisfano \(\varphi\) e sono etichettati
  come `NP_like` dal bridge di teoria.

Inoltre, il modulo `critical_regions_api.py` introduce un’ulteriore
etichetta booleana `is_seed_canonico`, che vale True **solo** per
\((param, factor) = (2,3)\). Possiamo quindi raffinare la proprietà:

\[
\psi(param, factor) \iff \varphi(param, factor) \ \wedge\ is\_seed\_canonico = True.
\]

Per costruzione, \(\psi\) è soddisfatta **esattamente** dal seed \((2,3)\).

### 9.3. Teorema (Separazione locale P_like / NP_like nel modello finito)

**Teorema 9.1 (Separazione locale nel modello finito).**  
Nel modello finito del Loventre Engine definito sulla griglia
\(\{1,2,3\} \times \{1,2,3\}\), la proprietà strutturale \(\varphi\)
non è realizzabile da alcun seed `P_like`, mentre è realizzata da
seed di tipo `NP_like` (in particolare dal seed canonico \((2,3)\)).
Ancora più forte, la proprietà \(\psi\) è realizzata **unicamente**
dal seed canonico \((2,3)\) e da nessun seed `P_like`.

In formule:

1. Per ogni seed \((p,f)\) tale che `complexity_flavour(p,f) = P_like`,
   si ha:

   \[
   \neg \varphi(p,f)
   \quad\text{e in particolare}\quad
   \neg \psi(p,f).
   \]

2. Esiste almeno un seed \((p,f)\) con `complexity_flavour(p,f) = NP_like`
   tale che \(\varphi(p,f)\) è vera (e precisamente \((2,3)\) soddisfa \(\psi\)):

   \[
   \varphi(2,3) \ \wedge\ \psi(2,3) \ \wedge\ \bigl(complexity\_flavour(2,3) = NP\_like\bigr).
   \]

*Dimostrazione (schema).*  
La dimostrazione è puramente finita e si basa sui risultati dei moduli
di laboratorio:

- `critical_signature_lab.py` fornisce le firme dinamiche 1D e multicanale
  (short/long) per tutti i seed;
- `critical_regions_seed.py` e `critical_regions_api.py` etichettano
  ogni seed come `regular_region`, `precritical_region` o `critical_region`,
  e identificano il seed canonico con `is_seed_canonico = True`;
- `loventre_theory_bridge_seed.py` associa ad ogni seed il flavour
  `P_like`, `threshold_precritical` o `NP_like`.

Dai log sperimentali si verifica che:

1. Per tutti i seed con `complexity_flavour = P_like`  
   (cioè \((1,1), (1,2), (2,1)\)), si ha sempre
   `region_type = regular_region`, quindi la prima congiunzione
   in \(\varphi\) (che richiede `critical_region`) è falsificata:  
   \(\neg \varphi(p,f)\) per ogni P_like.

2. Per il seed canonico \((2,3)\):

   - `region_type = critical_region`,
   - `pattern_short = fully_critical_configuration`,
   - `regime_1d_long = critical_high_entropy`,
   - `regime_multi_long = synchronized_high_spread`,
   - `multi_critical_long = True`,
   - `is_seed_canonico = True`,
   - `complexity_flavour = NP_like`.

   Quindi \(\varphi(2,3)\) e \(\psi(2,3)\) sono entrambe vere.

3. Il flag `is_seed_canonico` è, per costruzione, False per tutti gli
   altri seed; quindi nessun altro seed può soddisfare \(\psi\).

Ne segue che esiste una proprietà strutturale \(\psi\), esprimibile in
termini di curvatura, entropia, configurazione geometrica e diffusione
multicanale, che separa il seed canonico NP_like da tutti i seed P_like
nel modello finito.

\(\square\)

### 9.4. Ruolo del seed canonico nella strategia del Teorema di Loventre

Il Teorema 9.1 è una **versione finita e locale** della separazione tra
regimi `P_like` e `NP_like`. In particolare:

- mostra che, anche su una griglia finita di parametri, esiste un seed
  la cui firma informazionale **non è riproducibile** da alcun seed
  P_like sotto gli stessi vincoli geometrici e dinamici;

- fornisce un **testimone concreto**, \((param,factor) = (2,3)\),
  che verrà utilizzato come prototipo NP_like nei passaggi successivi
  (estensioni a famiglie infinite di seed, formalizzazione in Coq,
  enunciato globale del Teorema di Loventre).

Nei capitoli seguenti, l’idea è di:

1. Estendere il quadro da una griglia finita \(\{1,2,3\}^2\) ad una
   famiglia più ampia di seed (o di parametri strutturali), mantenendo
   la distinzione P_like / threshold_precritical / NP_like;

2. Trasportare la proprietà \(\psi\) in una formulazione astratta,
   indipendente dai numeri specifici, ma fondata sulla combinazione
   di:
   - criticità locale (Pattern C fully_critical),
   - persistenza della critica 1D (critical_high_entropy short/long),
   - sincronizzazione multicanale ad ampia diffusione;

3. Dimostrare, nel formalismo del Teorema di Loventre, che nessuna
   dinamica P_like può simulare una dinamica NP_like che soddisfa
   l’analogo astratto di \(\psi\), caricando così il seed canonico
   \((2,3)\) del ruolo di “archetipo informazionale” della classe NP_like.

