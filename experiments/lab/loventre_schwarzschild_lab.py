
import math


# Parameters for Schwarzschild-Loventre layer
K_SCHWARZSCHILD_DEFAULT = 1.0       # global scale factor (plays 2G/c^2 role)
LAMBDA_INERTIA_DEFAULT = 0.1        # how much inertia amplifies mass
INERTIA_CAP_DEFAULT = 10.0          # cap for inertial_difficulty_index

CHI_NEAR_HORIZON_THRESHOLD = 0.6    # below this: subcritical region
GAMMA_CAP_DEFAULT = 1e4             # upper bound for time dilation
EPS_COMP_DEFAULT = 1e-9             # epsilon to avoid division by zero


def compute_mass_effective(
    mass_mean,
    inertial_difficulty_index,
    lambda_inertia=LAMBDA_INERTIA_DEFAULT,
    inertia_cap=INERTIA_CAP_DEFAULT,
):
    # Effective informational mass:
    # mass_eff = mass_mean * (1 + lambda_inertia * clamp(idi, 0, inertia_cap))
    mass_mean_val = max(0.0, float(mass_mean))
    idi = max(0.0, float(inertial_difficulty_index))
    idi_clamped = min(float(inertia_cap), idi)

    inertia_factor = 1.0 + float(lambda_inertia) * idi_clamped
    mass_eff = mass_mean_val * inertia_factor
    return mass_eff


def compute_loventre_schwarzschild_radius(
    mass_mean,
    inertial_difficulty_index,
    k_schwarzschild=K_SCHWARZSCHILD_DEFAULT,
    lambda_inertia=LAMBDA_INERTIA_DEFAULT,
    inertia_cap=INERTIA_CAP_DEFAULT,
):
    # Informational Schwarzschild radius:
    # R_s_L = k_schwarzschild * mass_eff
    mass_eff = compute_mass_effective(
        mass_mean=mass_mean,
        inertial_difficulty_index=inertial_difficulty_index,
        lambda_inertia=lambda_inertia,
        inertia_cap=inertia_cap,
    )

    R_s_L = float(k_schwarzschild) * mass_eff
    return {
        'mass_eff': mass_eff,
        'R_s_L': R_s_L,
        'k_schwarzschild': float(k_schwarzschild),
        'lambda_inertia': float(lambda_inertia),
        'inertia_cap': float(inertia_cap),
    }


def _span(val_min, val_max):
    # Non-negative span between two values; returns 0.0 if inputs are missing.
    if val_min is None or val_max is None:
        return 0.0
    try:
        span_val = float(val_max) - float(val_min)
    except Exception:
        return 0.0
    return max(0.0, span_val)


def estimate_effective_radius_from_metrics(
    metrics,
    min_radius=1e-3,
    coeff_a_min=1.0,
    coeff_V0=0.1,
    coeff_C_span=0.05,
    coeff_H_span=0.05,
):
    # Estimate an effective problem radius R_eff using:
    # - a_min as geometric base
    # - V0 (using log(1+V0))
    # - complexity span (C_max - C_min)
    # - entropy span (H_max - H_min)
    a_min = float(metrics.get('a_min', 1.0))
    V0 = float(metrics.get('V0', 0.0))

    C_min = metrics.get('C_min', None)
    C_max = metrics.get('C_max', None)
    H_min = metrics.get('H_min', None)
    H_max = metrics.get('H_max', None)

    complexity_span = _span(C_min, C_max)
    entropy_span = _span(H_min, H_max)

    V0_term = math.log1p(max(0.0, V0))
    C_term = math.log1p(complexity_span)
    H_term = math.log1p(entropy_span)

    R_eff = (
        float(coeff_a_min) * a_min
        + float(coeff_V0) * V0_term
        + float(coeff_C_span) * C_term
        + float(coeff_H_span) * H_term
    )

    if R_eff < min_radius:
        R_eff = float(min_radius)

    return R_eff


def classify_schwarzschild_regime(
    compactness,
    near_horizon_threshold=CHI_NEAR_HORIZON_THRESHOLD,
    supercritical_threshold=1.0,
):
    # Classify compactness into three regimes:
    # SUBCRITICAL, NEAR_HORIZON, SUPERCRITICAL
    c = float(compactness)

    if c < float(near_horizon_threshold):
        return 'SUBCRITICAL'
    elif c < float(supercritical_threshold):
        return 'NEAR_HORIZON'
    else:
        return 'SUPERCRITICAL'


def compute_schwarzschild_gamma_from_compactness(
    compactness,
    gamma_cap=GAMMA_CAP_DEFAULT,
    eps=EPS_COMP_DEFAULT,
):
    # Schwarzschild-like time dilation:
    # gamma = 1 / sqrt(1 - chi), with chi in [0,1).
    c = max(0.0, float(compactness))

    one_minus_c = 1.0 - c
    if one_minus_c < eps:
        one_minus_c = eps

    gamma = 1.0 / math.sqrt(one_minus_c)

    gamma_cap_val = float(gamma_cap)
    if gamma > gamma_cap_val:
        gamma = gamma_cap_val

    return gamma


def compute_schwarzschild_compactness_from_metrics(
    metrics,
    k_schwarzschild=K_SCHWARZSCHILD_DEFAULT,
    lambda_inertia=LAMBDA_INERTIA_DEFAULT,
    inertia_cap=INERTIA_CAP_DEFAULT,
    min_radius=1e-3,
    coeff_a_min=1.0,
    coeff_V0=0.1,
    coeff_C_span=0.05,
    coeff_H_span=0.05,
):
    # Given metrics with at least:
    # - mass_mean
    # - inertial_difficulty_index
    # and optionally:
    # - a_min, V0, C_min, C_max, H_min, H_max
    # compute:
    # - mass_eff
    # - R_s_L (informational Schwarzschild radius)
    # - R_eff (effective problem radius)
    # - compactness = R_s_L / R_eff
    # - schwarzschild_regime
    mass_mean = metrics.get('mass_mean', 0.0)
    inertial_difficulty_index = metrics.get('inertial_difficulty_index', 0.0)

    radius_info = compute_loventre_schwarzschild_radius(
        mass_mean=mass_mean,
        inertial_difficulty_index=inertial_difficulty_index,
        k_schwarzschild=k_schwarzschild,
        lambda_inertia=lambda_inertia,
        inertia_cap=inertia_cap,
    )

    R_eff = estimate_effective_radius_from_metrics(
        metrics=metrics,
        min_radius=min_radius,
        coeff_a_min=coeff_a_min,
        coeff_V0=coeff_V0,
        coeff_C_span=coeff_C_span,
        coeff_H_span=coeff_H_span,
    )

    if R_eff <= 0.0:
        compactness = 0.0
    else:
        compactness = radius_info['R_s_L'] / R_eff

    regime = classify_schwarzschild_regime(compactness)

    result = {
        'mass_eff': radius_info['mass_eff'],
        'R_s_L': radius_info['R_s_L'],
        'R_eff': R_eff,
        'compactness': compactness,
        'schwarzschild_regime': regime,
        'k_schwarzschild': radius_info['k_schwarzschild'],
        'lambda_inertia': radius_info['lambda_inertia'],
        'inertia_cap': radius_info['inertia_cap'],
    }
    return result


def enrich_metrics_with_schwarzschild(
    metrics,
    overwrite=False,
    k_schwarzschild=K_SCHWARZSCHILD_DEFAULT,
    lambda_inertia=LAMBDA_INERTIA_DEFAULT,
    inertia_cap=INERTIA_CAP_DEFAULT,
    min_radius=1e-3,
    coeff_a_min=1.0,
    coeff_V0=0.1,
    coeff_C_span=0.05,
    coeff_H_span=0.05,
    gamma_cap=GAMMA_CAP_DEFAULT,
    eps=EPS_COMP_DEFAULT,
):
    # Return a copy of metrics enriched with:
    # - loventre_mass_eff
    # - loventre_R_s_L
    # - loventre_R_eff
    # - schwarzschild_compactness
    # - schwarzschild_regime
    # - gamma_dilation_schwarzschild
    if overwrite:
        m = metrics
    else:
        m = dict(metrics)

    comp_info = compute_schwarzschild_compactness_from_metrics(
        metrics=m,
        k_schwarzschild=k_schwarzschild,
        lambda_inertia=lambda_inertia,
        inertia_cap=inertia_cap,
        min_radius=min_radius,
        coeff_a_min=coeff_a_min,
        coeff_V0=coeff_V0,
        coeff_C_span=coeff_C_span,
        coeff_H_span=coeff_H_span,
    )

    gamma_schw = compute_schwarzschild_gamma_from_compactness(
        compactness=comp_info['compactness'],
        gamma_cap=gamma_cap,
        eps=eps,
    )

    m['loventre_mass_eff'] = comp_info['mass_eff']
    m['loventre_R_s_L'] = comp_info['R_s_L']
    m['loventre_R_eff'] = comp_info['R_eff']
    m['schwarzschild_compactness'] = comp_info['compactness']
    m['schwarzschild_regime'] = comp_info['schwarzschild_regime']
    m['gamma_dilation_schwarzschild'] = gamma_schw

    return m


if __name__ == '__main__':
    # Small internal demo to verify behavior.
    example_metrics = {
        'mass_mean': 3.0,
        'inertial_difficulty_index': 4.5,
        'a_min': 1.2,
        'V0': 5.0,
        'C_min': 10.0,
        'C_max': 25.0,
        'H_min': 1.0,
        'H_max': 3.5,
    }

    enriched = enrich_metrics_with_schwarzschild(example_metrics, overwrite=False)

    print('=== Schwarzschild-Loventre demo (toy values) ===')
    for key in sorted(enriched.keys()):
        print(f'{key:30s}: {enriched[key]}')
