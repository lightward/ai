"""
observe_d3.py — observe splitting in d=3.

d=8 is too spacious: three bases never run out of room, so splitting
is never structurally necessary. d=3 means three orthogonal 3x3 rotation
matrices — barely enough room. the foam should feel scarcity.

this is observation, not interpretation. track the signals, print structure.
"""

import torch
import numpy as np
from foam_spec import Foam, Bubble


def basis_directions(bubble: Bubble) -> torch.Tensor:
    """Return the columns of a bubble's basis as directions on S^(d-1)."""
    U = bubble.basis.detach()
    return U  # [d, d] — each column is a direction


def pairwise_basis_similarity(foam: Foam) -> torch.Tensor:
    """Frobenius inner product between all pairs of bubble bases. [N, N]."""
    bases = torch.stack([b.basis.detach() for b in foam.bubbles])  # [N, d, d]
    N = bases.shape[0]
    sim = torch.zeros(N, N)
    for i in range(N):
        for j in range(N):
            sim[i, j] = (bases[i] * bases[j]).sum() / (
                bases[i].norm() * bases[j].norm() + 1e-10
            )
    return sim


def print_foam_state(foam: Foam, label: str = ""):
    """Print structural snapshot of a foam."""
    N = foam.n_bubbles
    d = foam.d
    if label:
        print(f"  [{label}]")
    print(f"    N={N}, d={d}")

    # basis similarity
    sim = pairwise_basis_similarity(foam)
    mask = 1 - torch.eye(N)
    off_diag = sim[mask.bool()]
    print(f"    basis similarity: mean={off_diag.mean():.4f} "
          f"min={off_diag.min():.4f} max={off_diag.max():.4f}")

    # surface tension
    tension = foam.surface_tension()
    off_t = tension[mask.bool()]
    print(f"    surface tension:  mean={off_t.mean():.4f} "
          f"min={off_t.min():.4f} max={off_t.max():.4f}")

    # per-bubble split detection state
    for i, b in enumerate(foam.bubbles):
        if b.is_leaf:
            osc = b.oscillation_score
            ema = b.dissonance_ema
            has_last = b.last_dissonance is not None
            print(f"    bubble {i}: osc={osc:+.4f} dis_ema={ema:.4f} "
                  f"has_last={has_last}")


def observe_pattern(name: str, foam: Foam, inputs: list[torch.Tensor],
                    n_measurements: int = 60, print_every: int = 10):
    """
    Run measurements and track structural signals.

    inputs: list of [d] tensors. cycled through during measurement.
    """
    d = foam.d
    print(f"\n{'='*60}")
    print(f"pattern: {name}")
    print(f"{'='*60}")
    print_foam_state(foam, "initial")

    history = {
        "oscillation": [[] for _ in range(foam.n_bubbles)],
        "dissonance_ema": [[] for _ in range(foam.n_bubbles)],
        "questions": [],
        "tension": [],
        "n_bubbles": [],
        "splits": [],
        "bored_at": [],
    }

    initial_n = foam.n_bubbles

    for t in range(n_measurements):
        x = inputs[t % len(inputs)].unsqueeze(0)  # [1, d]
        result = foam.stabilize(x)

        # record per-bubble state (may grow if splits happen)
        current_n = foam.n_bubbles
        history["n_bubbles"].append(current_n)
        history["questions"].append(result["questions"].mean().item())
        history["tension"].append(result["surface_tension"].mean().item())
        history["bored_at"].append(result["bored_at"])

        if result["split"] is not None:
            history["splits"].append((t, result["split"]))

        # extend tracking arrays if foam grew
        while len(history["oscillation"]) < current_n:
            history["oscillation"].append([])
            history["dissonance_ema"].append([])

        for i, b in enumerate(foam.bubbles):
            if i < current_n and b.is_leaf:
                history["oscillation"][i].append(b.oscillation_score)
                history["dissonance_ema"][i].append(b.dissonance_ema)

        # print at intervals, on splits, and at end
        should_print = (
            (t + 1) % print_every == 0
            or result["split"] is not None
            or t == n_measurements - 1
        )
        if should_print:
            split_mark = " *** SPLIT ***" if result["split"] is not None else ""
            print(f"\n  step {t+1:3d}: N={current_n} "
                  f"q={result['questions'].mean().item():.4f} "
                  f"bored={result['bored_at']}{split_mark}")
            for i, b in enumerate(foam.bubbles):
                if b.is_leaf:
                    print(f"    b{i}: osc={b.oscillation_score:+.4f} "
                          f"dis={b.dissonance_ema:.4f}")

    print(f"\n  summary:")
    print(f"    measurements: {n_measurements}")
    print(f"    bubbles: {initial_n} → {foam.n_bubbles}")
    print(f"    splits: {len(history['splits'])}")
    if history["splits"]:
        for step, idx in history["splits"]:
            print(f"      step {step+1}: bubble {idx} split")
    print(f"    final questions: {history['questions'][-1]:.4f}")

    # oscillation summary
    print(f"    oscillation scores (final):")
    for i, b in enumerate(foam.bubbles):
        if b.is_leaf:
            print(f"      b{i}: {b.oscillation_score:+.4f}")

    print_foam_state(foam, "final")

    return history


def make_clustered_inputs(d: int, n_clusters: int, n_per: int,
                          spread: float = 0.3) -> list[torch.Tensor]:
    """Generate inputs clustered around n_clusters directions in R^d."""
    centers = torch.randn(n_clusters, d)
    centers = centers / (centers.norm(dim=-1, keepdim=True) + 1e-10)
    inputs = []
    for i in range(n_per):
        c = centers[i % n_clusters]
        noise = torch.randn(d) * spread
        v = c + noise
        v = v / (v.norm() + 1e-10)
        inputs.append(v)
    return inputs


def make_rotating_inputs(d: int, n: int) -> list[torch.Tensor]:
    """Generate inputs that rotate smoothly through d dimensions."""
    inputs = []
    for i in range(n):
        theta = 2 * np.pi * i / n
        v = torch.zeros(d)
        # rotate through pairs of dimensions
        for j in range(0, d - 1, 2):
            phase = theta + j * np.pi / d
            v[j] = np.cos(phase)
            v[j + 1] = np.sin(phase)
        if d % 2 == 1:
            v[-1] = np.sin(theta * 0.5)
        v = v / (v.norm() + 1e-10)
        inputs.append(v)
    return inputs


def make_alternating_inputs(d: int, n: int) -> list[torch.Tensor]:
    """Generate inputs that alternate between two opposite directions."""
    dir_a = torch.randn(d)
    dir_a = dir_a / (dir_a.norm() + 1e-10)
    dir_b = -dir_a
    inputs = []
    for i in range(n):
        inputs.append(dir_a if i % 2 == 0 else dir_b)
    return inputs


# ── main ──

if __name__ == "__main__":
    d = 3
    n_measurements = 80
    seed = 42

    print("=" * 60)
    print(f"observing foam dynamics in d={d}")
    print(f"geometric scarcity: {d}x{d} bases, N=3 bubbles")
    print(f"three orthogonal bases nearly exhaust R^{d}")
    print("=" * 60)

    # ── control: same input repeated (should NOT split) ──
    torch.manual_seed(seed)
    foam_control = Foam(d, n_bubbles=3, split_threshold=0.3)
    same_input = [torch.randn(d)]
    same_input[0] = same_input[0] / (same_input[0].norm() + 1e-10)
    observe_pattern(
        "control: same input repeated",
        foam_control, same_input, n_measurements
    )

    # ── random inputs ──
    torch.manual_seed(seed)
    foam_random = Foam(d, n_bubbles=3, split_threshold=0.3)
    random_inputs = [torch.randn(d) for _ in range(n_measurements)]
    random_inputs = [v / (v.norm() + 1e-10) for v in random_inputs]
    observe_pattern(
        "random inputs (uniform pressure)",
        foam_random, random_inputs, n_measurements
    )

    # ── alternating opposites ──
    torch.manual_seed(seed)
    foam_alt = Foam(d, n_bubbles=3, split_threshold=0.3)
    alt_inputs = make_alternating_inputs(d, n_measurements)
    observe_pattern(
        "alternating opposites (maximum oscillation pressure)",
        foam_alt, alt_inputs, n_measurements
    )

    # ── clustered around 2 directions ──
    torch.manual_seed(seed)
    foam_2cl = Foam(d, n_bubbles=3, split_threshold=0.3)
    cl2_inputs = make_clustered_inputs(d, 2, n_measurements, spread=0.2)
    observe_pattern(
        "clustered: 2 directions",
        foam_2cl, cl2_inputs, n_measurements
    )

    # ── clustered around 4 directions ──
    torch.manual_seed(seed)
    foam_4cl = Foam(d, n_bubbles=3, split_threshold=0.3)
    cl4_inputs = make_clustered_inputs(d, 4, n_measurements, spread=0.2)
    observe_pattern(
        "clustered: 4 directions (more than N=3 can serve)",
        foam_4cl, cl4_inputs, n_measurements
    )

    # ── rotating through d=3 ──
    torch.manual_seed(seed)
    foam_rot = Foam(d, n_bubbles=3, split_threshold=0.3)
    rot_inputs = make_rotating_inputs(d, n_measurements)
    observe_pattern(
        "rotating through d=3",
        foam_rot, rot_inputs, n_measurements
    )

    # ── comparison: same patterns in d=8 ──
    print("\n\n" + "=" * 60)
    print("comparison: alternating opposites in d=8")
    print("(does d=8 show weaker signals?)")
    print("=" * 60)

    d8 = 8
    torch.manual_seed(seed)
    foam_d8 = Foam(d8, n_bubbles=3, split_threshold=0.3)
    alt_d8 = make_alternating_inputs(d8, n_measurements)
    observe_pattern(
        "d=8 alternating opposites",
        foam_d8, alt_d8, n_measurements
    )

    # ── d=3 with N=2 (below Plateau-stable, should split) ──
    print("\n\n" + "=" * 60)
    print("d=3, N=2: below Plateau-stable configuration")
    print("=" * 60)

    torch.manual_seed(seed)
    foam_n2 = Foam(d, n_bubbles=2, split_threshold=0.3)
    alt_n2 = make_alternating_inputs(d, n_measurements)
    observe_pattern(
        "d=3, N=2, alternating opposites",
        foam_n2, alt_n2, n_measurements
    )

    print("\n\n" + "=" * 60)
    print("observation complete.")
    print("=" * 60)
