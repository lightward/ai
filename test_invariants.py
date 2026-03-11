"""
Cross-check: what does the writing dynamics conserve?

Not "is the foam learning" — does the integrator maintain its invariants?

1. Orthogonality: do bubble bases stay on O(d) after writing?
2. Fixed point: does repeated measurement with same input converge?
3. Reversibility: does opposite measurement undo the writing?
4. Stability: does perturbation from equilibrium return?
5. Conservation: what's invariant across measurements?
6. Manifold: does L stay well-conditioned for Cayley?
"""

import torch
import numpy as np
from foam_spec import Foam, Bubble, Operator


def orthogonality_error(basis):
    """How far is basis from O(d)?"""
    I = torch.eye(basis.shape[0])
    return (basis @ basis.T - I).abs().max().item()


def run():
    d = 8

    print("=" * 60)
    print("invariant checks: what does the writing dynamics conserve?")
    print("=" * 60)

    # ── 1. Orthogonality ──
    print("\n── 1. orthogonality: do bases stay on O(d)? ──")
    torch.manual_seed(42)
    foam = Foam(d, n_bubbles=3)

    errors = []
    for i in range(50):
        x = torch.randn(1, d)
        foam.stabilize(x)
        max_err = max(orthogonality_error(b.basis) for b in foam.bubbles)
        errors.append(max_err)

    print(f"  max orthogonality error over 50 measurements:")
    print(f"    start: {errors[0]:.8f}")
    print(f"    mid:   {errors[24]:.8f}")
    print(f"    end:   {errors[49]:.8f}")
    print(f"    worst: {max(errors):.8f}")

    # ── 2. Fixed point ──
    print("\n── 2. fixed point: same input repeated ──")
    torch.manual_seed(42)
    foam = Foam(d, n_bubbles=3)
    x = torch.randn(1, d)  # same input every time

    bases_history = []
    for i in range(40):
        result = foam.stabilize(x)
        bases_snapshot = torch.stack([b.basis.detach().clone() for b in foam.bubbles])
        bases_history.append(bases_snapshot)

    # measure convergence: distance between consecutive snapshots
    deltas = []
    for i in range(1, len(bases_history)):
        delta = (bases_history[i] - bases_history[i-1]).norm().item()
        deltas.append(delta)

    print(f"  consecutive basis change (should → 0 if fixed point exists):")
    for i in [0, 4, 9, 19, 38]:
        if i < len(deltas):
            print(f"    step {i+1}→{i+2}: Δ = {deltas[i]:.6f}")

    # ── 3. Reversibility ──
    print("\n── 3. reversibility: does -x undo +x? ──")
    torch.manual_seed(42)
    foam = Foam(d, n_bubbles=3)
    bases_before = torch.stack([b.basis.detach().clone() for b in foam.bubbles])

    x = torch.randn(1, d)
    foam.stabilize(x)
    bases_after_forward = torch.stack([b.basis.detach().clone() for b in foam.bubbles])

    foam.stabilize(-x)
    bases_after_reverse = torch.stack([b.basis.detach().clone() for b in foam.bubbles])

    forward_drift = (bases_after_forward - bases_before).norm().item()
    reverse_residual = (bases_after_reverse - bases_before).norm().item()
    print(f"  forward drift (+x):  {forward_drift:.6f}")
    print(f"  residual after (-x): {reverse_residual:.6f}")
    print(f"  ratio (1.0 = no reversal, 0.0 = perfect reversal): "
          f"{reverse_residual / (forward_drift + 1e-10):.4f}")

    # ── 4. Stability ──
    print("\n── 4. stability: perturbation recovery ──")
    torch.manual_seed(42)
    foam = Foam(d, n_bubbles=3)
    x = torch.randn(1, d)

    # drive to equilibrium
    for _ in range(20):
        foam.stabilize(x)
    bases_equil = torch.stack([b.basis.detach().clone() for b in foam.bubbles])

    # perturb
    with torch.no_grad():
        for b in foam.bubbles:
            if b.is_leaf:
                b.L.data += torch.randn_like(b.L) * 0.1
    bases_perturbed = torch.stack([b.basis.detach().clone() for b in foam.bubbles])
    perturbation_size = (bases_perturbed - bases_equil).norm().item()

    # recover
    recovery = []
    for i in range(20):
        foam.stabilize(x)
        bases_now = torch.stack([b.basis.detach().clone() for b in foam.bubbles])
        dist = (bases_now - bases_equil).norm().item()
        recovery.append(dist)

    print(f"  perturbation size: {perturbation_size:.4f}")
    print(f"  distance from equilibrium after recovery:")
    for i in [0, 4, 9, 19]:
        print(f"    step {i+1}: {recovery[i]:.4f}")
    recovered = recovery[-1] < perturbation_size
    print(f"  {'closer to equilibrium' if recovered else 'did NOT return'} "
          f"(ratio: {recovery[-1] / perturbation_size:.4f})")

    # ── 5. Conservation ──
    print("\n── 5. conservation: what's invariant? ──")
    torch.manual_seed(42)
    foam = Foam(d, n_bubbles=3)

    det_history = []
    tension_history = []
    trace_history = []

    for i in range(30):
        x = torch.randn(1, d)
        result = foam.stabilize(x)

        # determinant of each basis (should stay ±1 for O(d))
        dets = [torch.det(b.basis).item() for b in foam.bubbles]
        det_history.append(dets)

        # total surface tension
        tension = result["surface_tension"]
        mask = 1 - torch.eye(foam.n_bubbles)
        total_t = (tension * mask).sum().item()
        tension_history.append(total_t)

        # trace of density matrix (should be 1)
        rho = foam.density_matrix(result["j2"])
        tr = rho[0].trace().item()
        trace_history.append(tr)

    print(f"  determinants (should stay ±1):")
    print(f"    step 1:  {[f'{d:.4f}' for d in det_history[0]]}")
    print(f"    step 15: {[f'{d:.4f}' for d in det_history[14]]}")
    print(f"    step 30: {[f'{d:.4f}' for d in det_history[29]]}")

    print(f"  total surface tension:")
    print(f"    step 1:  {tension_history[0]:.4f}")
    print(f"    step 15: {tension_history[14]:.4f}")
    print(f"    step 30: {tension_history[29]:.4f}")

    print(f"  ρ trace (should be 1):")
    print(f"    step 1:  {trace_history[0]:.6f}")
    print(f"    step 15: {trace_history[14]:.6f}")
    print(f"    step 30: {trace_history[29]:.6f}")

    # ── 6. Manifold ──
    print("\n── 6. manifold: does L stay well-conditioned? ──")
    torch.manual_seed(42)
    foam = Foam(d, n_bubbles=3)

    norms = []
    conds = []
    for i in range(50):
        x = torch.randn(1, d)
        foam.stabilize(x)
        for b in foam.bubbles:
            if b.is_leaf:
                norms.append(b.L.data.norm().item())
                # condition number of (I + A) where A = L - L.T
                A = b.L.data - b.L.data.T
                I = torch.eye(d)
                cond = torch.linalg.cond(I + A).item()
                conds.append(cond)

    print(f"  L norm: {np.min(norms):.4f} .. {np.max(norms):.4f} "
          f"(mean {np.mean(norms):.4f})")
    print(f"  cond(I+A): {np.min(conds):.4f} .. {np.max(conds):.4f} "
          f"(mean {np.mean(conds):.4f})")
    if np.max(conds) > 1e6:
        print(f"  WARNING: Cayley transform becoming ill-conditioned")
    else:
        print(f"  Cayley transform well-conditioned throughout")

    print(f"\n{'=' * 60}")


if __name__ == "__main__":
    run()
