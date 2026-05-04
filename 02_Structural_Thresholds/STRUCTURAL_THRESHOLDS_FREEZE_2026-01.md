# STRUCTURAL THRESHOLDS — FREEZE v1.0 (2026-01)

## Status
**FROZEN · AUTONOMOUS · NON-NUMERICAL**

Questo documento congela il layer `02_Structural_Thresholds`
come parte stabile della teoria strutturale autonoma.

---

## 1. Scopo del layer

Il layer **Structural Thresholds** formalizza:

- soglie strutturali astratte;
- separazione stabile / critica / isolante;
- asimmetrie direzionali;
- tricotomia globale.

Il layer **non** introduce:
- numeri;
- ordini su ℝ;
- metriche quantitative;
- funzioni di costo o energia.

---

## 2. Dipendenze

Dipende **solo** da:

- `01_Structural_Core/LMetrics_Base.v`
- `01_Structural_Core/Structural_Invariants_Abstract.v`

Non dipende da:
- dinamiche temporali;
- attrattori;
- interpretazioni computazionali;
- CANON v4.

---

## 3. File congelati

I seguenti file sono parte integrante del freeze:

- `Thresholds_Abstract.v`
- `Threshold_Constraints.v`
- `Threshold_Asymmetry.v`
- `Threshold_Trichotomy.v`

Ogni file:
- compila senza `Admitted`;
- usa solo logica proposizionale;
- introduce solo predicati astratti.

---

## 4. Assiomi introdotti (espliciti)

Il layer assume esclusivamente:

- separazione stabile / isolante;
- esclusione reciproca delle soglie estreme;
- caratterizzazione del dominio critico come “intermedio”.

Nessun assioma numerico.
Nessuna comparazione quantitativa.

---

## 5. Teoremi garantiti

Dal layer seguono formalmente:

- assenza di sovrapposizione tripla;
- asimmetria direzionale delle soglie;
- tricotomia strutturale globale.

Questi risultati sono **interni** alla teoria strutturale.

---

## 6. Clausola di stabilità

Dopo questo freeze:

- ❌ nessuna modifica ai file del layer
- ❌ nessuna estensione implicita delle soglie
- ❌ nessuna reinterpretazione numerica

Ogni evoluzione futura avverrà **sopra** questo layer.

---

## 7. Ruolo nella teoria complessiva

Questo layer fornisce:

- la base formale per attrattori e bacini;
- la giustificazione strutturale dell’asimmetria dinamica;
- un’alternativa autonoma alle soglie computazionali classiche.

---

## 8. Data e versione

- **Versione:** v1.0
- **Data freeze:** 2026-01
- **Stato:** definitivo

---

*Fine documento di freeze*

