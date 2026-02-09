"""
test_global_integrity_terminal_regime.py
Test end-to-end per Terminal Regime AUREO
Gennaio 2026
"""
import unittest

from loventre_global_entrypoint import loventre_global_decide_with_policy

class TestLoventreGlobalIntegrity(unittest.TestCase):
    """
    Verifica che il terminal regime rispetti la regola ORO:

        kappa_eff < 0   → BLACKHOLE
        kappa_eff >= 0  → SAFE

    Tutti i layer devono essere trasparenti rispetto alla decisione.
    """

    def test_safe_and_blackhole_integrity(self):
        # Caso SAFE
        safe_metrics = dict(kappa_eff=+0.8)
        out_safe = loventre_global_decide_with_policy(**safe_metrics)
        decision_safe = out_safe["loventre_global"]["global_decision"]
        self.assertEqual(decision_safe, "SAFE")

        # Caso BLACKHOLE
        bh_metrics = dict(kappa_eff=-0.8)
        out_bh = loventre_global_decide_with_policy(**bh_metrics)
        decision_bh = out_bh["loventre_global"]["global_decision"]
        self.assertEqual(decision_bh, "BLACKHOLE")

if __name__ == "__main__":
    unittest.main()

