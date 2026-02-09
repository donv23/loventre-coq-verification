# CHECKPOINT — Teoria strutturale P vs NP
## Stato del progetto (baseline stabile)

Data: checkpoint post D2 + S3 + Bridge  
Stato Coq: TUTTO COMPILA (solo warning di masking innocui)

---

## 1. Scopo del progetto

Costruire una teoria **strutturale** del problema P vs NP,
in cui la difficoltà NP non è modellata come limite quantitativo di tempo,
ma come **instabilità locale → globale** e **assenza di uniformizzazione legittima**.

Il progetto non pretende (a questo stadio) una dimostrazione classica di P ≠ NP,
ma mira a:
- chiarire *cosa* dovrebbe essere dimostrato,
- isolare il principio mancante,
- costruire un linguaggio matematico adeguato.

---

## 2. Struttura a strati (attuale)

### D2 — Teoria astratta (Formal_Core)

File:
- Formal_Core_Sig.v
- Formal_Core_Abstract.v

Contenuto:
- nozione astratta di Order Property (OP),
- principio strutturale:
  
  OP ⇒ non esistenza di sezioni naturali (uniformizzazione).

Status:
- OP è un concetto astratto,
- nessuna istanza concreta,
- nessuna identificazione con modelli computazionali.

---

### S3 — Istanza concreta minimale

File:
- CSP_Instance.v

Contenuto:
- modello concreto minimale,
- definizione di OP_local,
- dimostrazione che OP_local è realizzabile.

Caratteristiche:
- modello artificiale ma coerente,
- assunzioni locali **esplicite**,
- serve solo a dimostrare **non-vacuità**.

Status:
- compila,
- stabile,
- non pretende realismo computazionale.

---

### Bridge — Collegamento minimo e onesto

File:
- Bridge_OP_Local.v

Contenuto:
- assunzione esplicita di esistenza:

  esiste un oggetto astratto che soddisfa OP.

Nota fondamentale:
- NON esiste identificazione tipologica tra oggetti concreti e astratti,
- il bridge è dichiarativo, non costruttivo,
- nessuna forzatura o abuso di Coq.

Status:
- compila,
- ponte minimo,
- auditabile.

---

## 3. Cosa è stato dimostrato

- La teoria astratta è **formalmente consistente**.
- Esiste almeno un modello concreto in cui una OP “locale” è realizzabile.
- È lecito assumere (esplicitamente) l’esistenza di OP a livello astratto.

---

## 4. Cosa NON è stato dimostrato (e perché)

- Nessun collegamento naturale tra OP_local e OP:
  → richiede teoria ulteriore (riduzioni, morfismi, stabilità).
- Nessuna istanza realistica di CSP / SAT / TSP:
  → fuori dallo scopo di S3.
- Nessuna affermazione su P ≠ NP classico:
  → non ancora, e non implicitamente.

---

## 5. Principi metodologici rispettati

- Separazione netta:
  - teoria / modello / ponte.
- Nessuna assunzione nascosta.
- Ogni assioma è dichiarato.
- Ogni file compila.
- Nessuna “correzione manuale” non tracciata.

---

## 6. Prossime direzioni possibili

Da questo checkpoint, le direzioni legittime sono:

1. **S4 — Raffinamento del modello**
   Rendere OP_local meno artificiale, più CSP-like.

2. **D3 — Raffinamento del bridge**
   Ridurre l’assioma di esistenza a un lemma strutturale
   (es. tramite nozioni di morfismo / riduzione legittima).

3. **Documento teorico**
   Esplicitare il principio mancante (PNUC) in forma matematica
   indipendente da Coq.

Qualunque passo successivo deve preservare questo stato come baseline.

---

## Freeze finale — Sensibilità & Rumore (XV)

**Data:** dicembre 2025  
**Stato:** FROZEN

### Layer coinvolti
- Loventre_Noise_Regimes.v
- Loventre_Structural_Sensitivity.v
- Loventre_Structural_Sensitivity_Lemmas.v
- Loventre_Sensitivity_Induces_Critical_Noise.v

### Contenuto strutturale
- Definizione del **Principio di Sensibilità Strutturale (PSS)**
- Tassonomia qualitativa dei **regimi di rumore** (inerte / critico / apertura orizzonte)
- Bridge concettuale:  
  *sensibilità strutturale ⇒ esistenza di rumore non inerte*
- Nessuna dinamica esplicita
- Nessuna probabilità
- Nessuna statistica

### Stato logico
- Nessun `Admitted`
- Nessun nuovo assioma globale
- Uso controllato di `Parameter` come ipotesi strutturali locali
- Tutti i file compilano (`coqc`) senza errori

### Backup
- Snapshot salvato in `99_LEGACY/FREEZE3_*`

### Nota metodologica
Questo freeze chiude il capitolo XV del trattato.
Il modello resta **puramente strutturale**:
prima struttura → poi dinamica → poi misura.

Prossimi step ammessi:
- dinamica del rumore (layer esplicito)
- metriche quantitative di sensibilità
- integrazione con capitoli successivi del trattato

Nessuna estensione attiva in questo checkpoint.

