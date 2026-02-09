import numpy as np
from typing import Dict, List
import time

class LoventreMetricAnalyzer:
    def __init__(self):
        self.metrics_history = []
    
    def analyze_complexity_metric(self, algorithm, input_sizes: List[int]) -> Dict:
        results = []
        
        for size in input_sizes:
            input_data = np.random.rand(size)
            start = time.perf_counter()
            algorithm(input_data)
            end = time.perf_counter()
            results.append((size, end - start))
        
        sizes = np.array([r[0] for r in results])
        times = np.array([r[1] for r in results])
        
        return {
            'sizes': sizes.tolist(),
            'times': times.tolist(),
            'avg_time': np.mean(times)
        }
    
    def compute_loventre_convergence(self, sequence: List[float]) -> Dict:
        seq_array = np.array(sequence)
        if len(seq_array) > 1:
            differences = np.diff(seq_array)
            convergence = np.mean(np.abs(differences))
        else:
            convergence = 0
        
        return {
            'convergence_rate': float(convergence),
            'sequence_length': len(sequence)
        }
