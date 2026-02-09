# Loventre Python Engine

Engine Python per testare teorie matematiche avanzate, integrazione con Coq.

## Struttura
```
loventre_engine_clean_seed/
├── src/
│   ├── python_engine/     # Codice Python principale
│   └── coq_modules/       # Moduli Coq
├── tests/                 # Test unitari
├── data/                  # Dati e risultati
├── config/                # File configurazione
└── scripts/               # Script di utilità
```

## Installazione
```bash
./run_engine.sh
```

## Test
```bash
./run_tests.sh
```

## Uso
```python
from src.python_engine.theory_tester import LoventreTheoremTester

tester = LoventreTheoremTester()
result = tester.test_p_vs_np_separation()
print(f"Result: {result.status.value}")
```

## Requisiti
- Python 3.8+
- Coq 8.18+ (opzionale)
- NumPy, SymPy, Plotly
