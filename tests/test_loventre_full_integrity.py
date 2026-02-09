"""
test_loventre_full_integrity.py
Super test integrato del Loventre Engine — Terminal Regime
Gennaio 2026
"""
import unittest

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


class TestLoventreFullIntegrity(unittest.TestCase):
    """
    Verifica end-to-end che il motore rispetti:
    - decisione globale minima irreversibile
    - analisi locale non distruttiva
    - bus normalizzato
    - policy bridge annotativo
    - nessuna interferenza dei layer downstream
    """

    def assert_has_required_bus(self, metrics):
        for key in REQUIRED_BUS_KEYS:
            self.assertIn(
                key,
                metrics,
                f"Chiave '{key}' non presente nel bus Loventre"
            )

    def test_default_input_behaviour(self):
        """Se non passo nulla → kappa_eff default => SAFE."""
        out = loventre_global_decide_with_policy()
        decision = out["loventre_global"]["global_decision"]
        self.assertEqual(decision, "SAFE")
        self.assert_has_required_bus(out)

    def test_safe_path(self):
        """kappa_eff positivo => SAFE."""
        out = loventre_global_decide_with_policy(kappa_eff=+1.1)
        decision = out["loventre_global"]["global_decision"]
        self.assertEqual(decision, "SAFE")
        self.assert_has_required_bus(out)
        self.assertIn("strategy_hint", out)

    def test_blackhole_path(self):
        """kappa_eff negativo => BLACKHOLE."""
        out = loventre_global_decide_with_policy(kappa_eff=-2.2)
        decision = out["loventre_global"]["global_decision"]
        self.assertEqual(decision, "BLACKHOLE")
        self.assert_has_required_bus(out)
        self.assertIn("strategy_hint", out)

    def test_no_mutation_side_effects(self):
        """La decisione non viene alterata da analisi o strategie."""
        out = loventre_global_decide_with_policy(kappa_eff=-0.9)
        self.assertEqual(out["loventre_global"]["global_decision"], "BLACKHOLE")
        # Anche se policy e analysis esistono
        self.assertIn("policy_hints", out)
        self.assertIn("strategy_hint", out)

    def test_policy_is_annotative_only(self):
        """Policy non modifica decisione."""
        out_safe = loventre_global_decide_with_policy(kappa_eff=+0.5)
        out_bh = loventre_global_decide_with_policy(kappa_eff=-0.5)

        self.assertEqual(out_safe["loventre_global"]["global_color"], "GREEN")
        self.assertEqual(out_bh["loventre_global"]["global_color"], "RED")
        self.assertNotEqual(out_safe["loventre_global"], out_bh["loventre_global"])

    def test_missing_kappa_still_works(self):
        """Motore non crasha se mancano campi."""
        out = loventre_global_decide_with_policy(entropy_eff=5.0)
        decision = out["loventre_global"]["global_decision"]
        self.assertEqual(decision, "SAFE")
        self.assert_has_required_bus(out)


if __name__ == "__main__":
    unittest.main()

