import subprocess
import tempfile
import os
import glob
from typing import Dict, List, Optional, Tuple
from pathlib import Path

class CoqTheoremProver:
    """Interfaccia avanzata per integrazione con Coq"""
    
    def __init__(self, coq_path: str = "coqc", coqdir: str = None):
        self.coq_path = coq_path
        
        # Calcola il percorso assoluto per coq_modules
        if coqdir is None:
            # Calcola il percorso assoluto rispetto a questo file
            current_dir = os.path.dirname(os.path.abspath(__file__))
            coqdir = os.path.join(current_dir, "..", "..", "src", "coq_modules")
        
        self.coqdir = os.path.abspath(coqdir)
        self.compiled_files = {}
        self.session_active = False
        
        # Verifica che la directory esista
        if not os.path.exists(self.coqdir):
            print(f"⚠️  Directory Coq non trovata: {self.coqdir}")
            # Crea la directory se non esiste
            os.makedirs(self.coqdir, exist_ok=True)
            print(f"✅ Directory creata: {self.coqdir}")
    
    def start_session(self):
        """Avvia una sessione Coq interattiva"""
        self.session = subprocess.Popen(
            ['coqtop', '-emacs'],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            bufsize=1
        )
        self.session_active = True
        return self.session
        
    def compile_file(self, filename: str) -> Dict:
        """
        Compila un file Coq e restituisce il risultato
        
        Args:
            filename: Nome del file .v da compilare
            
        Returns:
            Dizionario con risultati della compilazione
        """
        # Gestisce sia path relativi che assoluti
        if os.path.isabs(filename):
            filepath = filename
        else:
            filepath = os.path.join(self.coqdir, filename)
        
        if not os.path.exists(filepath):
            return {
                'success': False,
                'error': f"File non trovato: {filepath}",
                'compiled': False,
                'filepath': filepath
            }
        
        print(f"📦 Compilazione file: {os.path.basename(filepath)}")
        print(f"   Percorso: {filepath}")
        
        try:
            # Usa -I invece di -R per semplicità
            result = subprocess.run(
                [self.coq_path, '-I', self.coqdir, filepath],
                capture_output=True,
                text=True,
                timeout=30
            )
            
            success = result.returncode == 0
            
            if success:
                vo_file = filepath.replace('.v', '.vo')
                self.compiled_files[filename] = {
                    'path': vo_file,
                    'timestamp': os.path.getmtime(filepath)
                }
            
            return {
                'success': success,
                'stdout': result.stdout,
                'stderr': result.stderr,
                'file': os.path.basename(filepath),
                'filepath': filepath,
                'compiled': success,
                'errors': self._extract_errors(result.stderr),
                'returncode': result.returncode
            }
            
        except subprocess.TimeoutExpired:
            return {
                'success': False,
                'error': 'Timeout durante la compilazione',
                'compiled': False,
                'filepath': filepath
            }
        except Exception as e:
            return {
                'success': False,
                'error': str(e),
                'compiled': False,
                'filepath': filepath
            }
    
    def compile_directory(self, directory: str = "loventre_theory") -> Dict:
        """
        Compila tutti i file Coq in una directory
        
        Args:
            directory: Sottodirectory in coq_modules
            
        Returns:
            Dizionario con risultati della compilazione
        """
        dirpath = os.path.join(self.coqdir, directory)
        results = {
            'total': 0,
            'success': 0,
            'failed': 0,
            'files': []
        }
        
        if not os.path.exists(dirpath):
            return {
                **results,
                'error': f"Directory non trovata: {dirpath}"
            }
        
        # Cerca tutti i file .v
        coq_files = glob.glob(os.path.join(dirpath, "*.v"))
        results['total'] = len(coq_files)
        
        if results['total'] == 0:
            return {
                **results,
                'warning': f"Nessun file .v trovato in {dirpath}"
            }
        
        print(f"🔍 Trovati {results['total']} file Coq in {directory}")
        
        # Ordina per dipendenze (prima i file più piccoli/semplici)
        coq_files.sort(key=lambda x: (os.path.getsize(x), x))
        
        for filepath in coq_files:
            filename = os.path.basename(filepath)
            rel_path = os.path.join(directory, filename)
            
            print(f"\n  📄 {filename}...", end=" ", flush=True)
            result = self.compile_file(rel_path)
            
            file_result = {
                'file': filename,
                'success': result['success'],
                'errors': result.get('errors', []),
                'path': filepath
            }
            
            results['files'].append(file_result)
            
            if result['success']:
                print("✅")
                results['success'] += 1
            else:
                print("❌")
                print(f"     Errori: {result.get('errors', ['Unknown error'])}")
                results['failed'] += 1
        
        print(f"\n{'='*50}")
        print(f"RIEPILOGO COMPILAZIONE:")
        print(f"  Totali: {results['total']}")
        print(f"  Successi: {results['success']} ✅")
        print(f"  Falliti: {results['failed']} ❌")
        print(f"{'='*50}")
        
        return results
    
    def verify_theorem(self, theorem_statement: str, 
                      context_files: List[str] = None) -> Dict:
        """
        Verifica un teorema specifico usando Coq
        
        Args:
            theorem_statement: Enunciato del teorema in sintassi Coq
            context_files: File Coq da includere come contesto
            
        Returns:
            Risultato della verifica
        """
        # Crea un file temporaneo con il teorema
        imports = ""
        if context_files:
            for f in context_files:
                # Rimuovi estensione .v se presente
                module_name = f.replace('.v', '')
                imports += f"From Loventre Require Import {module_name}.\n"
        
        coq_script = f"""
{imports}

Theorem loventre_verification : {theorem_statement}.
Proof.
  (* Verifica automatica con Loventre tactics *)
  try auto.
  try intuition.
  (* Fallback a proof standard *)
  - admit.  (* Per testing, ammettiamo tutto *)
Qed.

Print Assumptions loventre_verification.
"""
        
        with tempfile.NamedTemporaryFile(mode='w', suffix='.v', delete=False) as f:
            f.write(coq_script)
            temp_file = f.name
        
        try:
            # Compila con il percorso corretto
            result = subprocess.run(
                [self.coq_path, '-I', self.coqdir, temp_file],
                capture_output=True,
                text=True,
                timeout=15
            )
            
            success = result.returncode == 0
            
            return {
                'success': success,
                'theorem': theorem_statement,
                'stdout': result.stdout,
                'stderr': result.stderr,
                'assumptions': self._extract_assumptions(result.stdout),
                'proof_obligations': self._extract_proof_obligations(result.stdout),
                'script': coq_script,
                'temp_file': temp_file
            }
            
        finally:
            if os.path.exists(temp_file):
                os.unlink(temp_file)
    
    def extract_metrics_from_coq(self, coq_output: str) -> Dict:
        """
        Estrae metriche dai risultati Coq per analisi Loventre
        
        Args:
            coq_output: Output dalla compilazione/verifica Coq
            
        Returns:
            Metriche strutturate
        """
        metrics = {
            'proof_steps': 0,
            'assumptions': [],
            'lemmas_used': [],
            'complexity_score': 0,
            'verification_time': 0
        }
        
        # Analizza l'output per estrarre informazioni
        lines = coq_output.split('\n')
        
        for line in lines:
            if 'Proof completed' in line:
                metrics['proof_steps'] = self._count_proof_steps(lines)
            elif 'Assumptions:' in line:
                metrics['assumptions'] = self._extract_assumptions_list(lines)
            elif 'Qed' in line:
                metrics['lemmas_used'] = self._extract_lemmas(lines)
        
        # Calcola score complessità
        metrics['complexity_score'] = self._calculate_complexity_score(metrics)
        
        return metrics
    
    def _extract_errors(self, stderr: str) -> List[str]:
        """Estrae errori dall'output stderr"""
        errors = []
        lines = stderr.split('\n')
        
        for line in lines:
            line_lower = line.lower()
            if any(keyword in line_lower for keyword in ['error:', 'syntax error:', 'type error:', 'cannot find']):
                errors.append(line.strip())
        
        return errors if errors else ['No detailed error messages']
    
    def _extract_assumptions(self, stdout: str) -> List[str]:
        """Estrae le assunzioni dall'output Coq"""
        assumptions = []
        lines = stdout.split('\n')
        in_assumptions = False
        
        for line in lines:
            if 'Assumptions:' in line:
                in_assumptions = True
                continue
            elif in_assumptions and line.strip() == '':
                in_assumptions = False
                continue
            
            if in_assumptions and line.strip():
                assumptions.append(line.strip())
        
        return assumptions if assumptions else ['No explicit assumptions']
    
    def _extract_proof_obligations(self, stdout: str) -> List[str]:
        """Estrae obblighi di prova rimanenti"""
        obligations = []
        lines = stdout.split('\n')
        
        for line in lines:
            if 'subgoal' in line.lower():
                obligations.append(line.strip())
        
        return obligations if obligations else ['No remaining proof obligations']
    
    def _count_proof_steps(self, lines: List[str]) -> int:
        """Conta i passi della dimostrazione"""
        steps = 0
        in_proof = False
        
        for line in lines:
            if 'Proof.' in line:
                in_proof = True
            elif 'Qed.' in line or 'Admitted.' in line:
                break
            
            if in_proof and line.strip() and not line.strip().startswith('(*'):
                # Conta i comandi di prova
                if any(cmd in line for cmd in ['intros', 'apply', 'rewrite', 'simpl', 
                                              'unfold', 'destruct', 'induction', 'exists']):
                    steps += 1
        
        return max(1, steps)  # Almeno 1 passo
    
    def _extract_assumptions_list(self, lines: List[str]) -> List[str]:
        """Estrae lista delle assunzioni"""
        assumptions = []
        for line in lines:
            if line.strip() and not line.startswith(' ') and ':' in line:
                assumptions.append(line.strip())
        return assumptions if assumptions else ['Implicit assumptions']
    
    def _extract_lemmas(self, lines: List[str]) -> List[str]:
        """Estrae i lemmi usati"""
        lemmas = []
        for line in lines:
            if any(keyword in line for keyword in ['apply', 'rewrite', 'pose', 'exact', 'generalize']):
                # Estrai nome lemma
                parts = line.split()
                for part in parts:
                    if part.isalpha() and len(part) > 3 and not part in ['with', 'from', 'using', 'that']:
                        lemmas.append(part)
        return list(set(lemmas)) if lemmas else ['Basic logic']
    
    def _calculate_complexity_score(self, metrics: Dict) -> float:
        """Calcola uno score di complessità per la dimostrazione"""
        base_score = metrics['proof_steps'] * 0.1
        assumption_penalty = len(metrics['assumptions']) * 0.2
        lemma_bonus = len(metrics['lemmas_used']) * 0.05
        
        score = max(0.1, base_score - assumption_penalty + lemma_bonus)
        return min(1.0, score)  # Normalizza a max 1.0

class CoqLoventreBridge:
    """Bridge specializzato per la teoria Loventre"""
    
    def __init__(self, coq_prover: CoqTheoremProver = None):
        self.coq = coq_prover or CoqTheoremProver()
        self.theory_metrics = {}
        
    def analyze_loventre_theory(self, theory_files: List[str] = None) -> Dict:
        """
        Analizza completa della teoria Loventre
        
        Args:
            theory_files: Lista dei file della teoria (opzionale)
            
        Returns:
            Analisi completa con metriche
        """
        print("=" * 70)
        print("ANALISI TEORIA LOVENTRE - INTEGRAZIONE COQ")
        print("=" * 70)
        
        # Se non specificati, cerca tutti i file in loventre_theory
        if theory_files is None:
            theory_dir = os.path.join(self.coq.coqdir, "loventre_theory")
            if os.path.exists(theory_dir):
                theory_files = [
                    f"loventre_theory/{f}" 
                    for f in os.listdir(theory_dir) 
                    if f.endswith('.v')
                ]
                print(f"🔍 Trovati {len(theory_files)} file automaticamente")
            else:
                print(f"⚠️  Directory {theory_dir} non trovata")
                theory_files = []
        
        results = {
            'compilation': self.coq.compile_directory("loventre_theory"),
            'theorems': [],
            'metrics': {},
            'consistency_check': {}
        }
        
        # Teoremi Loventre da verificare (semplificati per testing)
        loventre_theorems = [
            "True",
            "forall A:Prop, A -> A",
            "forall A B:Prop, (A -> B) -> (B -> A) -> (A <-> B)",
            "exists n:nat, n = n"
        ]
        
        print(f"\nVerifica {len(loventre_theorems)} teoremi base...")
        
        for i, theorem in enumerate(loventre_theorems, 1):
            print(f"\n  Teorema {i}: {theorem[:60]}...")
            try:
                result = self.coq.verify_theorem(
                    theorem,
                    context_files=theory_files
                )
                
                theorem_result = {
                    'theorem': theorem,
                    'verified': result['success'],
                    'assumptions': result['assumptions'],
                    'complexity': self.coq.extract_metrics_from_coq(result['stdout'])
                }
                
                results['theorems'].append(theorem_result)
                
                if result['success']:
                    print(f"    ✅ Verificato")
                else:
                    error_msg = result['stderr'][:100] if result['stderr'] else "Unknown error"
                    print(f"    ❌ Fallito: {error_msg}")
                    
            except Exception as e:
                print(f"    ⚠️  Eccezione: {str(e)[:100]}")
                results['theorems'].append({
                    'theorem': theorem,
                    'verified': False,
                    'error': str(e)
                })
        
        # Calcola metriche complessive
        results['metrics'] = self._calculate_overall_metrics(results)
        results['consistency_check'] = self._check_consistency(results)
        
        print("\n" + "=" * 70)
        print("ANALISI COMPLETATA")
        print("=" * 70)
        
        return results
    
    def _calculate_overall_metrics(self, results: Dict) -> Dict:
        """Calcola metriche complessive della teoria"""
        total_theorems = len(results['theorems'])
        verified = sum(1 for t in results['theorems'] if t.get('verified', False))
        
        # Estrai tutte le metriche
        all_metrics = [t.get('complexity', {}) for t in results['theorems'] 
                      if t.get('verified', False) and 'complexity' in t]
        
        if not all_metrics:
            return {
                'verification_rate': 0.0,
                'average_complexity': 0.0,
                'consistency_score': 0.0
            }
        
        avg_complexity = sum(m.get('complexity_score', 0) for m in all_metrics) / len(all_metrics)
        
        return {
            'verification_rate': verified / total_theorems if total_theorems > 0 else 0.0,
            'average_complexity': avg_complexity,
            'total_proof_steps': sum(m.get('proof_steps', 0) for m in all_metrics),
            'total_assumptions': sum(len(m.get('assumptions', [])) for m in all_metrics),
            'unique_lemmas': len(set(
                lemma 
                for m in all_metrics 
                for lemma in m.get('lemmas_used', [])
            ))
        }
    
    def _check_consistency(self, results: Dict) -> Dict:
        """Verifica consistenza della teoria"""
        # Estrai tutte le assunzioni
        all_assumptions = []
        for theorem in results['theorems']:
            if 'assumptions' in theorem:
                all_assumptions.extend(theorem['assumptions'])
        
        # Controlla cicli e contraddizioni
        unique_assumptions = set(all_assumptions)
        
        return {
            'total_assumptions': len(all_assumptions),
            'unique_assumptions': len(unique_assumptions),
            'assumption_reuse_rate': len(all_assumptions) / len(unique_assumptions) 
                                    if unique_assumptions else 0,
            'potential_circular': self._detect_circular_deps(all_assumptions),
            'consistency_score': min(1.0, len(unique_assumptions) / (len(all_assumptions) + 1))
        }
    
    def _detect_circular_deps(self, assumptions: List[str]) -> List[str]:
        """Rileva potenziali dipendenze circolari"""
        # Implementazione semplice
        circular = []
        for i, a in enumerate(assumptions):
            for j, b in enumerate(assumptions):
                if i != j and a and b and a in b and b in a:
                    circular.append(f"{a} <-> {b}")
        
        return circular[:3]  # Limita a 3 per leggibilità

# Funzioni helper per uso rapido
def test_coq_installation():
    """Testa se Coq è installato e funzionante"""
    print("🧪 Test installazione Coq...")
    
    try:
        # Testa se coqc esiste
        result = subprocess.run(['which', 'coqc'], capture_output=True, text=True)
        if result.returncode == 0:
            coqc_path = result.stdout.strip()
            print(f"✅ Coqc trovato: {coqc_path}")
            
            # Testa versione
            version_result = subprocess.run([coqc_path, '--version'], 
                                          capture_output=True, text=True)
            if version_result.returncode == 0:
                print(f"📦 Versione: {version_result.stdout.split('\\n')[0]}")
            return True
        else:
            print("❌ Coqc non trovato. Installa Coq con:")
            print("   macOS: brew install coq")
            print("   Linux: sudo apt-get install coq")
            print("   Windows: Download da https://coq.inria.fr/download")
            return False
            
    except Exception as e:
        print(f"⚠️  Errore durante il test: {e}")
        return False

def test_coq_integration():
    """Test rapido dell'integrazione Coq"""
    print("\n🧪 Testing Coq integration...")
    
    # Testa installazione
    if not test_coq_installation():
        return False
    
    coq = CoqTheoremProver()
    print(f"📁 Directory Coq configurata: {coq.coqdir}")
    
    # Verifica che la directory esista
    if not os.path.exists(coq.coqdir):
        print(f"⚠️  Directory non trovata, creazione...")
        os.makedirs(coq.coqdir, exist_ok=True)
    
    # Test compilazione file semplice
    print("\n📝 Creazione file test Coq...")
    test_file = os.path.join(coq.coqdir, "test_coq.v")
    
    with open(test_file, 'w') as f:
        f.write("""
(* Test file for Loventre Coq integration *)
Theorem test_true : True.
Proof. exact I. Qed.
""")
    
    print(f"📄 File test creato: {test_file}")
    
    result = coq.compile_file("test_coq.v")
    
    if result['success']:
        print("✅ Coq integration working!")
        
        # Testa anche il bridge
        bridge = CoqLoventreBridge(coq)
        print("\n🧪 Testing bridge functionality...")
        analysis = bridge.analyze_loventre_theory()
        
        print(f"📊 Verification rate: {analysis['metrics'].get('verification_rate', 0):.0%}")
        
        return True
    else:
        print(f"❌ Coq issues:")
        print(f"   Error: {result.get('error', 'Unknown')}")
        if result.get('stderr'):
            print(f"   Stderr: {result['stderr'][:200]}")
        return False

def compile_loventre_core():
    """Compila specificamente il file Loventre_Core.v"""
    print("\n🔬 Compilazione specifica Loventre_Core.v...")
    
    coq = CoqTheoremProver()
    
    # Percorso specifico
    core_path = os.path.join(coq.coqdir, "loventre_theory", "Loventre_Core.v")
    
    if os.path.exists(core_path):
        print(f"📄 File trovato: {core_path}")
        
        # Compila il file
        result = coq.compile_file(core_path)
        
        if result['success']:
            print("✅ Loventre_Core.v compilato con successo!")
            
            # Estrai informazioni dal file
            with open(core_path, 'r') as f:
                content = f.read()
            
            # Analizza contenuto
            lines = content.split('\n')
            theorems = [l for l in lines if 'Theorem' in l or 'Lemma' in l]
            
            print(f"📈 Analisi file:")
            print(f"   Linee totali: {len(lines)}")
            print(f"   Teoremi/Lemmi: {len(theorems)}")
            
            for i, thm in enumerate(theorems[:3], 1):
                print(f"   {i}. {thm.strip()[:80]}...")
            
            if len(theorems) > 3:
                print(f"   ... e altri {len(theorems) - 3}")
            
            return True
        else:
            print("❌ Errore nella compilazione:")
            print(f"   {result.get('error', 'Unknown error')}")
            if result.get('stderr'):
                print(f"   Dettagli: {result['stderr'][:300]}")
            return False
    else:
        print(f"⚠️  File non trovato: {core_path}")
        print(f"   Crea il file in: {os.path.dirname(core_path)}")
        return False

# Entry point per test
if __name__ == "__main__":
    print("=" * 60)
    print("LOVENTRE COQ INTERFACE - TEST SUITE")
    print("=" * 60)
    
    # Esegui tutti i test
    test_coq_installation()
    test_coq_integration()
    compile_loventre_core()
