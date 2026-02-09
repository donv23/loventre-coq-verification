import unittest
import sys
import os
sys.path.append(os.path.join(os.path.dirname(__file__), '../src/python_engine'))

from theory_tester import LoventreTheoremTester, TheoremStatus

class TestLoventreTester(unittest.TestCase):
    def setUp(self):
        self.tester = LoventreTheoremTester()

    def test_p_vs_np_separation(self):
        result = self.tester.test_p_vs_np_separation(n_samples=100)

        self.assertIn(result.status.value,
                     ['proved', 'disproved', 'undecided', 'contradiction']) 
        self.assertGreaterEqual(result.confidence, 0)
        self.assertLessEqual(result.confidence, 1)
        self.assertIsInstance(result.metrics_used, list)

    def test_metric_computation(self):
        metric = self.tester._compute_loventre_separation_metric()
        self.assertIsInstance(metric, float)
        self.assertGreater(metric, 0)

if __name__ == '__main__':
    unittest.main()
