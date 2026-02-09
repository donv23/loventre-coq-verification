import unittest
import sys
import os
sys.path.append(os.path.join(os.path.dirname(__file__), '../src/python_engine'))

from metric_analyzer import LoventreMetricAnalyzer

class TestMetricAnalyzer(unittest.TestCase):
    def setUp(self):
        self.analyzer = LoventreMetricAnalyzer()

    def test_complexity_analysis(self):
        def dummy_algo(data):
            return len(data)

        result = self.analyzer.analyze_complexity_metric(
            dummy_algo, [10, 20, 30]
        )

        self.assertIn('sizes', result)
        self.assertIn('times', result)
        self.assertEqual(len(result['sizes']), 3)

    def test_convergence(self):
        sequence = [1.0, 0.5, 0.25, 0.125]
        result = self.analyzer.compute_loventre_convergence(sequence)

        self.assertIn('convergence_rate', result)
        self.assertGreaterEqual(result['convergence_rate'], 0)

if __name__ == '__main__':
    unittest.main()
