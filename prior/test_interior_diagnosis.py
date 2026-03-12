"""
Diagnose why the interiors are stuck: questions=1.0 but bored_at=0.
"""

import torch
from foam_spec import Foam, Bubble


def main():
    d = 3
    torch.manual_seed(42)

    foam = Foam(d, n_bubbles=3, writing_rate=0.1, split_threshold=0.3)

    # develop to depth=1
    for i in range(200):
        x = torch.randn(1, d)
        result = foam.stabilize(x)
        if result["split"] is not None:
            print(f"split at step {i+1}")

    print(f"\ndepths: {[0 if b.is_leaf else 1 for b in foam.bubbles]}")

    # examine interior of first recursive bubble
    for bi, bubble in enumerate(foam.bubbles):
        if not bubble.is_leaf:
            print(f"\n── bubble {bi} interior ──")
            interior = bubble.interior
            for j, ib in enumerate(interior.bubbles):
                if ib.is_leaf:
                    basis = ib.basis
                    print(f"  inner bubble {j} basis:")
                    print(f"    {basis.detach().numpy().round(4)}")
                    # check orthogonality
                    UtU = basis @ basis.T
                    print(f"    orthogonality: max dev from I = "
                          f"{(UtU - torch.eye(d)).abs().max().item():.6f}")
                    print(f"    det = {torch.det(basis).item():.4f}")

            # pairwise similarities between interior bases
            bases = torch.stack([ib.basis for ib in interior.bubbles])
            print(f"\n  pairwise cosine similarities (column-wise):")
            for i in range(3):
                for j in range(i+1, 3):
                    # Frobenius inner product
                    sim = (bases[i] * bases[j]).sum() / (
                        bases[i].norm() * bases[j].norm()
                    )
                    print(f"    bubble {i} ↔ {j}: {sim.item():.4f}")

            # what happens during a single stabilization step?
            print(f"\n  stabilization dynamics with identity probe:")
            probe = torch.eye(d)
            measurements = torch.stack(
                [ib.measure(probe) for ib in interior.bubbles], dim=1
            )
            print(f"    initial measurements shape: {measurements.shape}")
            print(f"    measurement norms: {measurements.norm(dim=-1)}")

            # compute forces manually for one step
            N = 3
            mask = 1 - torch.eye(N)
            tension = interior.surface_tension()
            print(f"    surface tension:\n      {tension.detach().numpy().round(4)}")
            interaction = torch.softmax(
                -tension / interior.temperature.abs().clamp(min=0.01), dim=-1
            )
            print(f"    interaction weights:\n      {interaction.detach().numpy().round(4)}")

            state_n = measurements / (measurements.norm(dim=-1, keepdim=True) + 1e-10)
            cos_sim = torch.bmm(state_n, state_n.transpose(1, 2))
            print(f"    cos similarities (batch 0):\n      {cos_sim[0].detach().numpy().round(4)}")

            target = interior.target_similarity.item()
            print(f"    target similarity: {target:.4f}")

            force_mag = (cos_sim - target) * (mask * interaction).unsqueeze(0)
            diff = measurements.unsqueeze(2) - measurements.unsqueeze(1)
            diff_n = diff / (diff.norm(dim=-1, keepdim=True) + 1e-10)
            forces = (force_mag.unsqueeze(-1) * diff_n).sum(dim=2)

            step = interior.step_size.abs().clamp(min=0.001).item()
            delta = (step * forces).norm() / (measurements.norm() + 1e-10)
            print(f"    force magnitude: {forces.norm().item():.6f}")
            print(f"    step size: {step:.4f}")
            print(f"    delta (step * forces / state): {delta.item():.6f}")
            print(f"    boredom threshold: 0.005")
            print(f"    would bore: {delta.item() < 0.005}")

            # only first recursive bubble for brevity
            break


if __name__ == "__main__":
    main()
