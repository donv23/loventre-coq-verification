from flow_analyzer.pipeline.pipeline import run_pipeline

def run_multiscale(problem_generator, params, grid):
    results = {}
    for n in grid:
        state0 = problem_generator(n, params)
        results[n] = run_pipeline(state0, params, max_steps=params.get("max_steps", 20))
    return results
