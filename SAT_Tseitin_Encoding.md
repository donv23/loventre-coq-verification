# SAT_Tseitin_Encoding.md

Tab: SPERIMENTALE_FINALE_PvsNP  
Canvas: 3 — BRIDGE-B  
Status: encoding esplicito (nessun claim)  
Scopo: stress test della Support Monotonicity su una riduzione concreta Tseitin → SAT  
Dipendenze: D1 (robustezza locale), Support_Monotonicity_Def.md

---

## 0. Scopo del documento

Questo documento fissa **una singola codifica CNF esplicita**
di istanze Tseitin su grafi espansori,
al solo scopo di verificare se la riduzione
può essere **support-monotona** nel senso definito in
`Support_Monotonicity_Def.md`.

Non contiene teoremi né affermazioni di separazione.

---

## 1. Istanza di partenza: Tseitin su espansore

### 1.1 Grafo

Sia \( G = (V,E) \) una famiglia esplicita di grafi:
- d-regolari con \( d \ge 3 \),
- espansione costante,
- \( |V| = n \), \( |E| = m = \Theta(n) \).

Il grafo è fissato e noto.

---

### 1.2 Variabili

Per ogni arco \( e \in E \), introduciamo una variabile booleana:
\[
x_e \in \{0,1\}
\]

---

### 1.3 Vincoli di parità locali

Per ogni vertice \( v \in V \), imponiamo il vincolo:
\[
\bigoplus_{e \ni v} x_e = b_v
\]
dove:
- \( b_v \in \{0,1\} \),
- la somma è modulo 2.

---

### 1.4 Invariante globale

È noto che:
- la soddisfacibilità dell’istanza dipende dalla **parità globale**
  \[
  \bigoplus_{v \in V} b_v
  \]
- se la parità globale è 0 → istanza soddisfacibile,
- se è 1 → istanza insoddisfacibile.

Per grafi espansori, vale D1:
la parità globale è **robusta localmente**.

---

## 2. Codifica CNF dei vincoli di parità

### 2.1 Encoding di un vincolo di parità

Ogni vincolo:
\[
x_{e_1} \oplus x_{e_2} \oplus \dots \oplus x_{e_d} = b
\]
viene codificato in CNF con una famiglia standard di clausole:

- si introduce un encoding locale (eventualmente con variabili ausiliarie),
- il numero di clausole per vertice è \( O(2^{d}) \),
- per \( d \) costante, questo è \( O(1) \).

**Nessuna clausola singola codifica l’intero vincolo.**

---

### 2.2 Dimensione dell’istanza SAT

L’istanza SAT risultante ha:
- \( \Theta(n) \) variabili (incluse ausiliarie),
- \( \Theta(n) \) clausole,
- struttura locale: ogni clausola coinvolge solo variabili
  associate a un singolo vertice o ai suoi archi incidenti.

---

## 3. Mappa tra Tseitin e SAT

### 3.1 Riduzione

La riduzione \( R \) mappa:
- un’istanza Tseitin \( (G, \{b_v\}) \)
- in una CNF \( \varphi_{G,b} \)

tale che:
- \( \varphi_{G,b} \) è soddisfacibile
  se e solo se la parità globale è 0.

---

### 3.2 Località della codifica

Proprietà chiave:
- ogni clausola dipende solo da un singolo vertice
  (o da costantemente pochi archi),
- non esiste una clausola o gadget
  che “veda” più di \( O(1) \) vincoli locali.

---

## 4. Punto critico: test di supporto

### 4.1 Vista sublineare

Consideriamo una procedura \( \mathcal{A}_{SAT} \)
che decide la soddisfacibilità di \( \varphi_{G,b} \)
ispezionando solo un sottoinsieme \( S \) di clausole
con:
\[
|S| = o(n)
\]

---

### 4.2 Domanda centrale

Domanda (cruciale per Support Monotonicity):

> Esistono due istanze \( \varphi_{G,b} \), \( \varphi_{G,b'} \)
> tali che:
> - coincidono su tutte le clausole in \( S \),
> - ma una è soddisfacibile e l’altra no?

Per D1 (robustezza locale di Tseitin),
la risposta è **sì**, se \( |S| = o(n) \).

---

### 4.3 Conseguenza informazionale

Quindi:
- nessuna procedura che usa solo \( o(n) \) clausole
  può distinguere le due parità globali,
- decidere SAT su \( \varphi_{G,b} \)
  richiede supporto \( \Omega(n) \).

---

## 5. Applicazione della Support Monotonicity

Usando la definizione in `Support_Monotonicity_Def.md`:

- una procedura per SAT∘R con supporto sublineare
  indurrebbe una procedura per Tseitin
  con supporto sublineare,
- ciò viola NC per Tseitin-robusto.

Questa riduzione è quindi **plausibilmente support-monotona**,
salvo l’esistenza di gadget nascosti
o codifiche non locali non considerate qui.

---

## 6. Punti di rischio (espliciti)

Questo encoding **fallisce** la Support Monotonicity se:

- esiste una clausola o un insieme \( O(1) \) di clausole
  che codifica implicitamente la parità globale;
- l’encoding introduce una variabile ausiliaria
  che “accumula” informazione globale;
- un algoritmo può sfruttare una proprietà sintattica
  non modellata come supporto.

Questi casi comportano **STOP immediato** del programma BRIDGE-B.

---

## 7. Stato del documento

Questo documento:
- serve solo come stress test,
- non dimostra ML5,
- non implica alcuna separazione.

Il suo unico scopo è verificare
se la definizione di Support Monotonicity
è compatibile con una riduzione reale.

