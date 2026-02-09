import random
from flow_analyzer.core.state import InfoState
from flow_analyzer.multiscale.multiscale_runner import run_multiscale

def problem_generator(n, params):
    dim = params.get("dim", 3)
    x0 = [random.uniform(-1.0, 1.0) for _ in range(dim)]
    return InfoState(x0, n, t=0, meta={})

def main():
    params = {
        "alpha": 0.01,
        "critical_threshold": 0.5,
        "dim": 3,
        "max_steps": 20,
    }
    grid = [5, 10, 20, 40]

    print("=== Loventre Flow Analyzer — Multiscale Analyzer (Clean Seed) ===")
    results = run_multiscale(problem_generator, params, grid)

    for n, traj in results.items():
        last = traj[-1]
        meta = last.meta
        print(
            f"n={n:3d} | curv={meta['curvature']:.4f} | "
            f"ent={meta['entropy']:.4f} | "
            f"crit={meta['criticality']:.4f} | region={meta['region']}"
        )

if __name__ == "__main__":
    main()
