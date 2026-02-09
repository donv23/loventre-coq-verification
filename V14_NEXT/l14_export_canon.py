"""
L14_EXPORT_CANON — V14
======================

Questo modulo introduce il concetto di:
    * esportazione canonica
    * schema fisso di campi
    * hash/versione dei JSON

NB:
Non implementa ancora nessuna logica di export.
Definisce soltanto la struttura *obbligatoria*
che tutti gli export V14 dovranno rispettare.

Regole:
- Nessuna modifica dei file V13
- Tutto ciò che accade in V14 è additivo
- Compatibilità retroattiva garantita
"""

VERSION_TAG = "V14_ALPHA_1"

# Schema canonico minimo per V14
EXPORT_SCHEMA_V14 = {
    "version": VERSION_TAG,
    "timestamp": None,         # verrà riempito al momento della scrittura
    "state": None,             # SAFE / SAFE_ACCESSIBLE / BLACKHOLE / WAIT
    "kappa_l1": None,          # raw→[0,1] normalizzato (ereditato da L1)
    "policy": None,            # DO_NOTHING / STEADY / EXPLORE_MORE
    "router_target": None,     # LOCAL / GLOBAL / LAB
    "consistency_flag": None,  # OK / PROBLEM
}

def get_export_template():
    """
    Restituisce una copia del template canonico.
    Non scrive su disco, non decide policy,
    non valida input: è puro.
    """
    return dict(EXPORT_SCHEMA_V14)

