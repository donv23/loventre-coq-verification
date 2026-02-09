from typing import Dict, List, Any


def _mean(values: List[float]) -> float:
    if not values:
        return 0.0
    return sum(values) / len(values)


def _variance(values: List[float]) -> float:
    if not values:
        return 0.0
    m = _mean(values)
    return sum((x - m) ** 2 for x in values) / len(values)


def build_multichannel_trajectory(
    history: List[float],
    window_size: int = 3,
    stride: int = 1,
) -> List[List[float]]:
    """
    Turn a 1D history into a list of multi-channel configurations.

    Each configuration is a sliding window of length `window_size` over the
    scalar history. Consecutive windows are spaced by `stride` steps.
    """
    if window_size <= 0:
        raise ValueError("window_size must be positive")
    if stride <= 0:
        raise ValueError("stride must be positive")

    n = len(history)
    trajectory: List[List[float]] = []
    i = 0
    while i + window_size <= n:
        window = history[i : i + window_size]
        trajectory.append(window)
        i += stride
    return trajectory


def compute_multichannel_metrics(
    multichannel_trajectory: List[List[float]],
) -> Dict[str, float]:
    """
    Compute basic statistics over a multi-channel trajectory.

    - average_channel_variance: variance of each channel over time, averaged.
    - average_spatial_spread: variance inside each configuration, averaged.
    - synchrony_ratio: how often all channels move in the same direction
      between consecutive configurations.
    """
    if not multichannel_trajectory:
        return {
            "average_channel_variance": 0.0,
            "average_spatial_spread": 0.0,
            "synchrony_ratio": 0.0,
        }

    first_step = multichannel_trajectory[0]
    if not first_step:
        return {
            "average_channel_variance": 0.0,
            "average_spatial_spread": 0.0,
            "synchrony_ratio": 0.0,
        }

    num_channels = len(first_step)
    # Build per-channel time series
    channel_series: List[List[float]] = [[] for _ in range(num_channels)]
    for step in multichannel_trajectory:
        # In case of inconsistent lengths, truncate to the minimum
        step_len = min(len(step), num_channels)
        for j in range(step_len):
            channel_series[j].append(step[j])

    channel_variances = [_variance(series) for series in channel_series]
    average_channel_variance = _mean(channel_variances)

    # Spatial spread: variance within each configuration
    spatial_spreads = [_variance(step) for step in multichannel_trajectory]
    average_spatial_spread = _mean(spatial_spreads)

    # Synchrony of increments between configurations
    total_steps = len(multichannel_trajectory) - 1
    if total_steps <= 0:
        synchrony_ratio = 0.0
    else:
        coherent_steps = 0
        for t in range(total_steps):
            current_step = multichannel_trajectory[t]
            next_step = multichannel_trajectory[t + 1]
            step_len = min(len(current_step), len(next_step), num_channels)

            diffs: List[float] = []
            for j in range(step_len):
                diffs.append(next_step[j] - current_step[j])

            positives = [d for d in diffs if d > 0.0]
            negatives = [d for d in diffs if d < 0.0]

            if not positives and not negatives:
                # All diffs are zero: treat as coherent "no change"
                coherent_steps += 1
            elif not positives or not negatives:
                # All non-zero diffs have the same sign: coherent motion
                coherent_steps += 1
            else:
                # Mixed signs across channels: desynchronized motion
                pass

        synchrony_ratio = coherent_steps / float(total_steps)

    return {
        "average_channel_variance": average_channel_variance,
        "average_spatial_spread": average_spatial_spread,
        "synchrony_ratio": synchrony_ratio,
    }


def classify_multichannel_regime(
    metrics: Dict[str, float],
    spread_threshold: float = 1.0,
    synchrony_high: float = 0.8,
    synchrony_low: float = 0.5,
) -> Dict[str, Any]:
    """
    Turn multi-channel metrics into a qualitative regime.

    Regimes:
    - synchronized_low_spread: channels move together and stay close.
    - synchronized_high_spread: channels move together but configurations are far apart.
    - desynchronized_high_spread: channels move independently and diverge.
    - mixed_intermediate: intermediate patterns.

    The "is_multichannel_critical" flag marks configurations with sufficiently
    high spatial spread, independently of whether they are synchronized or not.
    """
    spread = metrics.get("average_spatial_spread", 0.0)
    synch = metrics.get("synchrony_ratio", 0.0)
    _variance_value = metrics.get("average_channel_variance", 0.0)  # kept for future use

    if spread < spread_threshold:
        # Low spatial spread: configurations are geometrically compact.
        if synch >= synchrony_high:
            regime = "synchronized_low_spread"
        else:
            # Some lack of synchrony but still low spread: intermediate regime.
            regime = "mixed_intermediate"
        is_critical = False
    else:
        # High spatial spread: high-energy / expanded configurations.
        if synch >= synchrony_high:
            regime = "synchronized_high_spread"
        elif synch <= synchrony_low:
            regime = "desynchronized_high_spread"
        else:
            regime = "mixed_intermediate"
        is_critical = True

    return {
        "regime_multichannel": regime,
        "is_multichannel_critical": is_critical,
    }


def analyze_multichannel_history(
    history: List[float],
    window_size: int = 3,
    stride: int = 1,
    spread_threshold: float = 1.0,
    synchrony_high: float = 0.8,
    synchrony_low: float = 0.5,
) -> Dict[str, Any]:
    """
    High-level entry point: from scalar history to multi-channel pattern profile.
    """
    multichannel_trajectory = build_multichannel_trajectory(
        history=history,
        window_size=window_size,
        stride=stride,
    )
    metrics = compute_multichannel_metrics(multichannel_trajectory)
    classification = classify_multichannel_regime(
        metrics=metrics,
        spread_threshold=spread_threshold,
        synchrony_high=synchrony_high,
        synchrony_low=synchrony_low,
    )

    profile: Dict[str, Any] = {
        "window_size": window_size,
        "stride": stride,
        "multichannel_trajectory": multichannel_trajectory,
        "metrics": metrics,
    }
    profile.update(classification)
    return profile


def analyze_state_multichannel(
    state: Any,
    window_size: int = 3,
    stride: int = 1,
    spread_threshold: float = 1.0,
    synchrony_high: float = 0.8,
    synchrony_low: float = 0.5,
) -> Dict[str, Any]:
    """
    Convenience wrapper that expects a Loventre Engine State-like object
    with a .data dict containing a "history" key.
    """
    data = getattr(state, "data", None)
    if not isinstance(data, dict):
        raise TypeError("state must expose a .data dict")

    history = data.get("history", [])
    if not isinstance(history, list):
        raise TypeError("state.data['history'] must be a list of floats")

    return analyze_multichannel_history(
        history=history,
        window_size=window_size,
        stride=stride,
        spread_threshold=spread_threshold,
        synchrony_high=synchrony_high,
        synchrony_low=synchrony_low,
    )


if __name__ == "__main__":
    # Small self-test / demo:
    from pprint import pprint

    example_history = [0.0, 0.5, 1.0, 1.2, 0.8, 0.3, -0.2, -0.5, -0.1]
    print("Example history:", example_history)
    profile = analyze_multichannel_history(
        history=example_history,
        window_size=3,
        stride=1,
        spread_threshold=0.2,
    )
    print("\nMultichannel profile:")
    pprint(profile)
