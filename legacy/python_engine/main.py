#!/usr/bin/env python3
"""
Loventre Python Engine - Main Application
Test avanzato di teoremi matematici con metriche Loventre
"""

import sys
import os
import json
from datetime import datetime

# Aggiungi il percorso per gli import
sys.path.append(os.path.dirname(os.path.abspath(__file__)))

from theory_tester import LoventreTheoremTester, TheoremStatus
from visualization_suite import TheoremVisualizer
from metric_analyzer import LoventreMetricAnalyzer
from coq_interface import CoqTheoremProver

class LoventreEngine:
    """Classe principale dell'engine Loventre"""
    
    def __init__(self):
        self.tester = LoventreTheoremTester()
        self.visualizer = TheoremVisualizer()
        self.analyzer = LoventreMetricAnalyzer()
        self.coq_prover = CoqTheoremProver()
        self.results = []
        self.session_id = datetime.now().strftime("%Y%m%d_%H%M%S")
        
    def run_all_tests(self):
        """Esegue tutti i test dei teoremi"""
        print("=" * 80)
        print(" " * 20 + "LOVENTRE MATHEMATICAL ENGINE v2.0")
        print("=" * 80)
        print(f"Sessione: {self.session_id}")
        print(f"Autore: Vincenzo Loventre")
        print("-" * 80)
        
        # 1. Test P vs NP
        self._test_p_vs_np()
        
        # 2. Test Ipotesi di Riemann
        self._test_riemann_hypothesis()
        
        # 3. Test Ultimo Teorema di Fermat
        self._test_fermat_last_theorem()
        
        # 4. Test Congettura Numeri Primi Gemelli
        self._test_twin_prime_conjecture()
        
        # 5. Analisi metriche avanzate
        self._run_advanced_analysis()
        
        # 6. Generazione report e visualizzazioni
        self._generate_report()
        
        print("\n" + "=" * 80)
        print(" " * 25 + "ESECUZIONE COMPLETATA!")
        print("=" * 80)
        
    def _test_p_vs_np(self):
        """Test del teorema P vs NP"""
        print("\n[1] TEOREMA P vs NP - SEPARAZIONE DI COMPLESSITÀ")
        print("=" * 60)
        
        result = self.tester.test_p_vs_np_separation(
            n_samples=2000,
            problem_size=100
        )
        
        self._display_theorem_result(result)
        
        # Analisi aggiuntiva
        print("\n   Metriche dettagliate:")
        if result.additional_data:
            for key, value in result.additional_data.items():
                print(f"   • {key.replace('_', ' ').title()}: {value:.6f}")
        
        self.results.append(('P vs NP', result))
    
    def _test_riemann_hypothesis(self):
        """Test dell'Ipotesi di Riemann"""
        print("\n[2] IPOTESI DI RIEMANN - DISTRIBUZIONE ZERI FUNZIONE ZETA")
        print("=" * 60)
        
        result = self.tester.test_riemann_hypothesis(
            n_zeros=50,
            precision=1e-10
        )
        
        self._display_theorem_result(result)
        
        # Informazioni specifiche per Riemann
        print("\n   Dettagli analisi zeri:")
        if result.additional_data:
            data = result.additional_data
            print(f"   • Zeri analizzati: {data.get('zeros_analyzed', 'N/A')}")
            print(f"   • Zeri sulla linea critica: {data.get('zeros_on_critical_line', 'N/A')}")
            print(f"   • Deviazione massima: {data.get('max_deviation', 'N/A'):.2e}")
            if data.get('max_deviation', 1) < 1e-6:
                print("   • ✅ Tutti gli zeri sulla linea critica entro precisione")
        
        self.results.append(('Riemann Hypothesis', result))
    
    def _test_fermat_last_theorem(self):
        """Test dell'Ultimo Teorema di Fermat"""
        print("\n[3] ULTIMO TEOREMA DI FERMAT - EQUAZIONE DIOFANTEA")
        print("=" * 60)
        
        result = self.tester.test_fermat_last_theorem(
            max_n=10,
            max_value=1000
        )
        
        self._display_theorem_result(result)
        
        # Informazioni specifiche per Fermat
        if result.status == TheoremStatus.DISPROVED and result.counter_example:
            print(f"\n   ⚠️  CONTROESEMPIO TROVATO!")
            print(f"   • a={result.counter_example.get('a')}")
            print(f"   • b={result.counter_example.get('b')}")
            print(f"   • c={result.counter_example.get('c')}")
            print(f"   • n={result.counter_example.get('n')}")
        
        self.results.append(("Fermat's Last Theorem", result))
    
    def _test_twin_prime_conjecture(self):
        """Test della Congettura dei Numeri Primi Gemelli"""
        print("\n[4] CONGETTURA NUMERI PRIMI GEMELLI - INFINITÀ PRIMI GEMELLI")
        print("=" * 60)
        
        result = self.tester.test_twin_prime_conjecture(limit=10000)
        
        self._display_theorem_result(result)
        
        # Informazioni specifiche per numeri primi gemelli
        print("\n   Statistiche numeri primi gemelli:")
        if result.additional_data:
            data = result.additional_data
            print(f"   • Limite ricerca: {data.get('limit_searched', 'N/A')}")
            print(f"   • Coppie trovate: {data.get('twin_primes_found', 'N/A')}")
            print(f"   • Coppia più grande: {data.get('largest_twin_prime', 'N/A')}")
            print(f"   • Densità stimata: {data.get('density_estimate', 'N/A'):.6f}")
            
            if data.get('twin_primes_found', 0) > 100:
                print("   • ✅ Evidenza forte per infiniti numeri primi gemelli")
        
        self.results.append(('Twin Prime Conjecture', result))
    
    def _run_advanced_analysis(self):
        """Esegue analisi metriche avanzate"""
        print("\n[5] ANALISI METRICHE AVANZATE LOVENTRE")
        print("=" * 60)
        
        # 1. Analisi complessità algoritmica
        print("\n   a) Analisi Complessità Algoritmica:")
        def sample_algorithm(data):
            # Algoritmo di esempio O(n log n)
            return sorted(data)
        
        complexity_result = self.analyzer.analyze_complexity_metric(
            sample_algorithm, 
            [100, 1000, 10000, 50000]
        )
        
        print(f"   • Dimensioni testate: {complexity_result['sizes']}")
        print(f"   • Tempo medio: {complexity_result['avg_time']:.6f}s")
        
        # 2. Analisi convergenza
        print("\n   b) Analisi Convergenza Sequenze:")
        
        # Sequenza convergente: 1/n
        convergent_seq = [1.0 / (n + 1) for n in range(50)]
        conv_result = self.analyzer.compute_loventre_convergence(convergent_seq)
        
        print(f"   • Tasso convergenza: {conv_result['convergence_rate']:.6f}")
        print(f"   • Lunghezza sequenza: {conv_result['sequence_length']}")
        
        # 3. Calcolo metriche Loventre avanzate
        print("\n   c) Metriche Loventre Fondamentali:")
        separation_metric = self.tester._compute_loventre_separation_metric()
        print(f"   • Metrica separazione: {separation_metric:.6f}")
        print(f"   • Soglia aurea (φ): {self.tester.metric_space['golden_ratio']:.6f}")
        
        if separation_metric > self.tester.metric_space['golden_ratio']:
            print("   • ✅ Separazione significativa rilevata")
        else:
            print("   • ⚠️  Separazione non significativa")
    
    def _display_theorem_result(self, result):
        """Visualizza i risultati di un teorema in formato leggibile"""
        status_icons = {
            'proved': '✅',
            'disproved': '❌',
            'undecided': '❓',
            'contradiction': '⚠️',
            'partially_proved': '🔶'
        }
        
        icon = status_icons.get(result.status.value, '❓')
        
        print(f"\n   {icon} Teorema: {result.theorem_name}")
        print(f"   • Stato: {result.status.value.upper()}")
        print(f"   • Confidenza: {result.confidence:.1%}")
        print(f"   • Tempo computazione: {result.computation_time:.2f}s")
        print(f"   • Metriche usate: {', '.join(result.metrics_used)}")
        
        # Mostra passi della dimostrazione (primi 3)
        if result.proof_steps:
            print(f"   • Passi dimostrazione:")
            for i, step in enumerate(result.proof_steps[:3]):
                print(f"     {i+1}. {step}")
            if len(result.proof_steps) > 3:
                print(f"     ... e altri {len(result.proof_steps) - 3} passi")
    
    def _generate_report(self):
        """Genera report finale e visualizzazioni"""
        print("\n[6] GENERAZIONE REPORT E VISUALIZZAZIONI")
        print("=" * 60)
        
        # 1. Genera visualizzazione 3D
        print("\n   a) Generazione visualizzazione 3D...")
        try:
            fig = self.visualizer.visualize_3d_space()
            filename_3d = f"loventre_3d_results_{self.session_id}.html"
            fig.write_html(filename_3d)
            print(f"   ✅ Visualizzazione salvata in: {filename_3d}")
        except Exception as e:
            print(f"   ⚠️  Errore generazione visualizzazione: {e}")
        
        # 2. Genera grafo dipendenze
        print("\n   b) Generazione grafo dipendenze...")
        try:
            dependencies = {
                'P vs NP': ['Complexity Theory', 'Turing Machines'],
                'Riemann Hypothesis': ['Complex Analysis', 'Number Theory'],
                "Fermat's Last Theorem": ['Number Theory', 'Algebraic Geometry'],
                'Twin Prime Conjecture': ['Number Theory', 'Analytic Number Theory']
            }
            graph = self.visualizer.create_dependency_graph(dependencies)
            print(f"   ✅ Grafo dipendenze generato ({len(dependencies)} nodi)")
        except Exception as e:
            print(f"   ⚠️  Errore generazione grafo: {e}")
        
        # 3. Salva risultati in JSON
        print("\n   c) Salvataggio risultati in JSON...")
        try:
            results_data = []
            for theorem_name, result in self.results:
                result_dict = {
                    'theorem': theorem_name,
                    'status': result.status.value,
                    'confidence': result.confidence,
                    'computation_time': result.computation_time,
                    'timestamp': self.session_id,
                    'additional_data': result.additional_data
                }
                results_data.append(result_dict)
            
            json_filename = f"loventre_results_{self.session_id}.json"
            with open(json_filename, 'w') as f:
                json.dump(results_data, f, indent=2, default=str)
            
            print(f"   ✅ Risultati salvati in: {json_filename}")
        except Exception as e:
            print(f"   ⚠️  Errore salvataggio JSON: {e}")
        
        # 4. Riepilogo statistiche
        print("\n   d) Riepilogo statistiche sessione:")
        total_tests = len(self.results)
        proved = sum(1 for _, r in self.results if r.status == TheoremStatus.PROVED)
        partially = sum(1 for _, r in self.results if r.status == TheoremStatus.PARTIALLY_PROVED)
        avg_confidence = sum(r.confidence for _, r in self.results) / total_tests if total_tests > 0 else 0
        
        print(f"   • Test eseguiti: {total_tests}")
        print(f"   • Teoremi dimostrati: {proved}")
        print(f"   • Parzialmente dimostrati: {partially}")
        print(f"   • Confidenza media: {avg_confidence:.1%}")
        print(f"   • ID sessione: {self.session_id}")
    
    def run_specific_test(self, test_name: str, **kwargs):
        """Esegue un test specifico"""
        test_methods = {
            'p_vs_np': self.tester.test_p_vs_np_separation,
            'riemann': self.tester.test_riemann_hypothesis,
            'fermat': self.tester.test_fermat_last_theorem,
            'twin_primes': self.tester.test_twin_prime_conjecture
        }
        
        if test_name in test_methods:
            print(f"\nEsecuzione test: {test_name}")
            result = test_methods[test_name](**kwargs)
            self._display_theorem_result(result)
            return result
        else:
            print(f"Test '{test_name}' non trovato")
            return None

def main():
    """Funzione principale dell'applicazione"""
    try:
        # Crea e avvia l'engine
        engine = LoventreEngine()
        
        # Menu interattivo
        print("Loventre Mathematical Engine - Menu")
        print("1. Esegui tutti i test")
        print("2. Test specifico P vs NP")
        print("3. Test specifico Ipotesi di Riemann")
        print("4. Test specifico Teorema di Fermat")
        print("5. Test specifico Numeri Primi Gemelli")
        print("6. Esci")
        
        choice = input("\nSeleziona opzione (1-6): ").strip()
        
        if choice == '1':
            engine.run_all_tests()
        elif choice == '2':
            engine.run_specific_test('p_vs_np', n_samples=1000, problem_size=50)
        elif choice == '3':
            engine.run_specific_test('riemann', n_zeros=30, precision=1e-8)
        elif choice == '4':
            engine.run_specific_test('fermat', max_n=5, max_value=500)
        elif choice == '5':
            engine.run_specific_test('twin_primes', limit=5000)
        elif choice == '6':
            print("Uscita...")
            return
        else:
            print("Scelta non valida. Esecuzione di tutti i test...")
            engine.run_all_tests()
            
    except KeyboardInterrupt:
        print("\n\nInterruzione manuale. Engine arrestato.")
    except Exception as e:
        print(f"\n❌ Errore durante l'esecuzione: {e}")
        import traceback
        traceback.print_exc()

if __name__ == "__main__":
    main()
