from flow_analyzer.core.state import InfoState
from flow_analyzer.pipeline.pipeline import run_pipeline

def main():
    params = {
        "alpha": 0.01,
        "critical_threshold": 0.5,
        "max_steps": 20,
    }

    s0 = InfoState([1.0, -0.5, 0.25], n=10, t=0, meta={})
    traj = run_pipeline(s0, params, max_steps=params["max_steps"])

    print("=== Loventre Flow Analyzer — Criticality Test (Clean Seed) ===")
    for s in traj:
        if not s.meta:
            print(f"{s.t:3d} | x={s.x} | meta={{}}")
        else:
            print(
                f"{s.t:3d} | x={s.x} | "
                f"curv={s.meta['curvature']:.4f} | "
                f"ent={s.meta['entropy']:.4f} | "
                f"dcurv={s.meta['delta_curvature']:.4f} | "
                f"crit={s.meta['criticality']:.4f} | "
                f"region={s.meta['region']}"
            )

if __name__ == "__main__":
    main()
