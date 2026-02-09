"""
test_loventre_full_integrity_with_dump.py
Super test + stampa integrale del Loventre Engine — Terminal Regime
Gennaio 2026
"""
import unittest
from pprint import pprint

from loventre_global_entrypoint import loventre_global_decide_with_policy


REQUIRED_BUS_KEYS = [
    'kappa_eff',
    'entropy_eff',
    'V0',
    'a_min',
    'p_tunnel',
    'P_success',
    'gamma_dilation',
    'time_regime',
    'mass_eff',
    'inertial_idx',
    'risk_index',
    'risk_class',
    'meta_label',
    'chi_compactness',
    'horizon_flag',
    'loventre_global_decision',
    'C_regime',
    'gct_barrier',
]


class TestLoventreFullIntegrityWithDump(unittest.TestCase):
    """
    Identico al test integrato, con STAMPA completa di tutto l'output
    al termine del run dei singoli scenari.
    """

    def assert_bus_keys(self, metrics):
        for key in REQUIRED_BUS_KEYS:
            self.assertIn(
                key,
                metrics,
                f"Chiave mancante nel bus: '{key}'"
            )

    def test_dump_all(self):
        """
        Esegue 4 scenari e stampa TUTTI i risultati:
        - default SAFE
        - SAFE forzato
        - BLACKHOLE forzato
        - valori misti/partial
        """
        print("\n======= LOVENTRE ENGINE FULL DUMP =======")

        scenarios = [
            ("default", {}),
            ("SAFE +1.1", dict(kappa_eff=+1.1)),
            ("BLACKHOLE -1.3", dict(kappa_eff=-1.3)),
            ("PARTIAL entropy only", dict(entropy_eff=5.0)),
        ]

        for name, kwargs in scenarios:
            out = loventre_global_decide_with_policy(**kwargs)
            print(f"\n--- Scenario: {name} ---")
            pprint(out)
            self.assert_bus_keys(out)

        print("\n======= END LOVENTRE ENGINE FULL DUMP =======")

