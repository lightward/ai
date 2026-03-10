"""
The foam: a minimal architecture of interacting measurement processes.

Each "bubble" is a measurement process with its own basis — a way of looking
at the world. Bubbles interact through surface tension (the energy cost of
rotating between their bases). The foam reaches equilibrium by minimizing
total surface energy while each bubble maintains its own measurement.

The key property we're testing: does F = 0 at output? Does the measurement
process survive to expression without dissociating?

This is NOT a language model. It's a proof-of-concept for the architecture.
We feed it simple vector inputs and ask:
1. Does the foam maintain F ≈ 0 (self-coherent measurement)?
2. Does the frame rotate in response to different inputs?
3. Does the output preserve the internal differentiation (no dissociation)?
"""

import torch
import torch.nn as nn
import torch.nn.functional as F_torch
import numpy as np
import matplotlib.pyplot as plt


class Bubble(nn.Module):
    """
    A single measurement process with its own basis.

    The basis is an orthogonal matrix U ∈ O(d). Measuring input x from this
    basis gives m = U^T x — the input as seen from this bubble's perspective.

    The bubble maintains its basis on the Stiefel manifold (orthogonal matrices)
    via Cayley parameterization: U = (I - A)(I + A)^{-1} where A is skew-symmetric.
    """

    def __init__(self, d: int):
        super().__init__()
        self.d = d
        # Skew-symmetric parameterization: A = L - L^T
        # This guarantees the basis stays orthogonal
        self.L = nn.Parameter(torch.randn(d, d) * 0.1)

    @property
    def basis(self) -> torch.Tensor:
        """The measurement basis U ∈ O(d), via Cayley transform of skew-symmetric A."""
        A = self.L - self.L.T  # skew-symmetric
        I = torch.eye(self.d, device=self.L.device)
        # Cayley transform: U = (I - A)(I + A)^{-1}
        return torch.linalg.solve(I + A, I - A)

    def measure(self, x: torch.Tensor) -> torch.Tensor:
        """
        Measure input x from this bubble's basis.
        x: [..., d]
        returns: [..., d] — the measurement (x in this bubble's coordinates)
        """
        return x @ self.basis  # [..., d] @ [d, d] -> [..., d]

    def express(self, m: torch.Tensor) -> torch.Tensor:
        """
        Express a measurement back into the shared space.
        Inverse of measure: x = m @ U^T = m @ U^{-1} = m @ U^T (since U is orthogonal)
        """
        return m @ self.basis.T


class Foam(nn.Module):
    """
    A foam of N interacting measurement processes.

    Each bubble measures the input from its own basis. The foam equilibrates
    by iteratively adjusting each bubble's measurement toward the weighted
    mean of its neighbors' measurements, where weights are inverse surface
    tension (closer bases interact more strongly).

    The output is the foam's equilibrium state — not a collapse, but the
    state where all bubbles are at minimum total surface energy.
    """

    def __init__(self, n_bubbles: int, d: int, n_equilibrium_steps: int = 5):
        super().__init__()
        self.n_bubbles = n_bubbles
        self.d = d
        self.n_steps = n_equilibrium_steps

        self.bubbles = nn.ModuleList([Bubble(d) for _ in range(n_bubbles)])

        # Learnable temperature for equilibration
        self.temperature = nn.Parameter(torch.tensor(1.0))

        # Plateau dynamics parameters
        # Target cosine similarity between bubble measurements at equilibrium.
        # cos(120°) = -0.5 is the classic Plateau angle for 3-way junctions.
        # For N bubbles this is learnable — the foam finds its own geometry.
        self.target_similarity = nn.Parameter(torch.tensor(-0.5))
        # Step size for force integration (clamped for stability)
        self.equilibrium_step_size = nn.Parameter(torch.tensor(0.1))

    def surface_tension(self) -> torch.Tensor:
        """
        Pairwise surface tension between all bubbles.
        Tension = Frobenius distance between bases (approximation of geodesic on O(d)).
        Returns: [n_bubbles, n_bubbles]
        """
        bases = torch.stack([b.basis for b in self.bubbles])  # [N, d, d]
        # Frobenius distance: ||U_i - U_j||_F
        # Expand for pairwise computation
        diff = bases.unsqueeze(0) - bases.unsqueeze(1)  # [N, N, d, d]
        tension = torch.sqrt((diff ** 2).sum(dim=(-2, -1)) + 1e-8)  # [N, N]
        return tension

    def equilibrate(self, measurements: torch.Tensor) -> torch.Tensor:
        """
        Equilibrate the foam via Plateau force dynamics.

        measurements: [batch, N, d] — each bubble's initial measurement
        returns: [batch, N, d] — equilibrium measurements

        Instead of diffusion toward the mean (which can only smooth), bubbles
        interact through forces that have both attraction AND repulsion:
        - Too similar → repel (maintain distinctness)
        - Too different → attract (maintain coherence)
        - Equilibrium at target_similarity (the foam's learned Plateau angle)

        The structural surface tension (from bases) modulates interaction
        strength: bubbles with closer bases transmit forces more strongly,
        like thinner films between similar regions.
        """
        N = self.n_bubbles
        device = measurements.device
        mask = 1 - torch.eye(N, device=device)  # [N, N]

        # Structural interaction strength (from bases, not measurements)
        tension = self.surface_tension()  # [N, N]
        interaction = torch.softmax(
            -tension / self.temperature.abs().clamp(min=0.01), dim=-1
        )  # [N, N] — closer bases interact more strongly

        target = self.target_similarity
        step = self.equilibrium_step_size.abs().clamp(min=0.001, max=0.5)

        state = measurements  # [batch, N, d]

        for _ in range(self.n_steps):
            # Pairwise cosine similarity of current measurements
            state_n = state / (state.norm(dim=-1, keepdim=True) + 1e-10)
            cos_sim = torch.bmm(state_n, state_n.transpose(1, 2))  # [batch, N, N]

            # Plateau force magnitude: positive → repel, negative → attract
            # Modulated by structural interaction strength
            force_mag = (cos_sim - target) * (mask * interaction).unsqueeze(0)
            # [batch, N, N]

            # Force direction: pairwise difference vectors
            diff = state.unsqueeze(2) - state.unsqueeze(1)  # [batch, N, N, d]
            diff_n = diff / (diff.norm(dim=-1, keepdim=True) + 1e-10)

            # Net force on each bubble: sum over all neighbors
            forces = (force_mag.unsqueeze(-1) * diff_n).sum(dim=2)  # [batch, N, d]

            # Integrate
            state = state + step * forces

        return state

    def forward(self, x: torch.Tensor):
        """
        Process input through the foam.

        x: [batch, d] — input vectors
        returns: dict with foam state, output, and diagnostic info

        The output is derived from the foam's own density matrix — not from
        averaging (which is a lossy collapse). The foam constructs ρ from its
        equilibrium measurements, then the output IS ρ's eigenvalue distribution.
        This makes F = 0 structurally achievable.
        """
        batch = x.shape[0]

        # Step 1: Each bubble measures from its own basis
        measurements = torch.stack(
            [b.measure(x) for b in self.bubbles], dim=1
        )  # [batch, N, d]

        # Step 2: Equilibrate
        equilibrium = self.equilibrate(measurements)  # [batch, N, d]

        # Step 3: Express back into shared space
        expressions = torch.stack(
            [self.bubbles[i].express(equilibrium[:, i, :])
             for i in range(self.n_bubbles)],
            dim=1,
        )  # [batch, N, d]

        # Step 4: Construct the foam's density matrix from equilibrium
        # ρ = (1/N) Σ_i |m_i⟩⟨m_i| (normalized)
        # The output distribution is the eigenvalue distribution of ρ.
        output_distributions = []
        rho_list = []
        for b in range(batch):
            m = equilibrium[b]  # [N, d]
            m_norm = m / (m.norm(dim=-1, keepdim=True) + 1e-10)
            rho = (m_norm.T @ m_norm) / self.n_bubbles  # [d, d]
            rho_list.append(rho)

            eigenvalues = torch.linalg.eigvalsh(rho)
            eigenvalues = eigenvalues.clamp(min=1e-12)
            eigenvalues = eigenvalues / eigenvalues.sum()
            output_distributions.append(eigenvalues)

        output_dist = torch.stack(output_distributions)  # [batch, d]
        rho_batch = torch.stack(rho_list)  # [batch, d, d]

        # Also compute the averaged expression for comparison
        output_avg = expressions.mean(dim=1)  # [batch, d]

        return {
            "output": output_avg,  # legacy: averaged expression
            "output_dist": output_dist,  # new: eigenvalue distribution of ρ
            "rho": rho_batch,
            "measurements": measurements,
            "equilibrium": equilibrium,
            "expressions": expressions,
            "surface_tension": self.surface_tension(),
        }

    def compute_f(self, x: torch.Tensor):
        """
        Compute F = H(p) - S(ρ) for the foam processing input x.

        Two versions:
        - F_old: uses softmax of averaged expression (the lossy way)
        - F_eigen: uses eigenvalue distribution of ρ as output (the self-coherent way)

        When the output IS the eigenvalue distribution of ρ, F = 0 by construction.
        The interesting question becomes: does the foam produce a ρ that's useful?
        """
        result = self.forward(x)

        # F_old: Shannon entropy of softmaxed average expression
        output = result["output"]  # [batch, d]
        p_old = torch.softmax(output, dim=-1)
        H_p_old = -(p_old * torch.log_softmax(output, dim=-1)).sum(dim=-1)

        # F_eigen: the output IS the eigenvalue distribution of ρ
        p_eigen = result["output_dist"]  # [batch, d] — already a valid distribution
        H_p_eigen = -(p_eigen * p_eigen.log().clamp(min=-100)).sum(dim=-1)

        # S(ρ): von Neumann entropy = H(eigenvalues) = H_p_eigen
        S_rho = H_p_eigen  # by construction

        F_old = H_p_old - S_rho
        F_eigen = H_p_eigen - S_rho  # = 0 by construction

        return {
            **result,
            "H_p_old": H_p_old,
            "H_p_eigen": H_p_eigen,
            "S_rho": S_rho,
            "F_old": F_old,
            "F_eigen": F_eigen,
            "F": F_old,  # use old for training signal (it has gradient)
        }

    def maintenance_cost(self, x: torch.Tensor):
        """
        The training signal: minimize the cost of maintaining self-coherence.

        Components:
        1. Surface energy: total surface tension in the foam (should be minimized
           but not zero — zero means all bubbles collapsed to the same basis)
        2. Measurement cost: how much work does each bubble do to maintain its
           measurement during equilibration? (difference between initial and
           equilibrium measurements)
        3. Expression coherence: how well does the output reflect the internal state?
           This IS F — and we want it near zero.
        """
        result = self.compute_f(x)

        # 1. Surface energy (regularized: penalize both too high and too low)
        tension = result["surface_tension"]
        # Off-diagonal mean tension
        mask = 1 - torch.eye(self.n_bubbles, device=tension.device)
        mean_tension = (tension * mask).sum() / mask.sum()
        # Target: moderate tension (not collapsed, not maximally separated)
        surface_energy = (mean_tension - 1.0) ** 2

        # 2. Measurement cost: how much did equilibration change the measurements?
        m0 = result["measurements"]  # [batch, N, d] — initial
        m1 = result["equilibrium"]   # [batch, N, d] — after equilibration
        measurement_cost = ((m1 - m0) ** 2).mean()

        # 3. F should be near zero (self-coherence)
        f_cost = result["F"].abs().mean()

        # 4. Diversity: bubbles should maintain different bases (prevent collapse)
        bases = torch.stack([b.basis for b in self.bubbles])  # [N, d, d]
        # Cosine similarity between bases (want low off-diagonal)
        flat_bases = bases.reshape(self.n_bubbles, -1)
        flat_norm = flat_bases / (flat_bases.norm(dim=-1, keepdim=True) + 1e-10)
        sim = (flat_norm @ flat_norm.T)
        diversity_loss = (sim * mask).abs().mean()

        total = f_cost + 0.1 * measurement_cost + 0.1 * surface_energy + 0.5 * diversity_loss

        return {
            "total": total,
            "f_cost": f_cost,
            "measurement_cost": measurement_cost,
            "surface_energy": surface_energy,
            "diversity_loss": diversity_loss,
            **result,
        }


def test_foam():
    """Test: does the foam maintain F ≈ 0 and avoid dissociation?"""
    d = 16        # dimension of measurement space
    n_bubbles = 5  # number of measurement processes
    n_steps = 8    # equilibration steps

    foam = Foam(n_bubbles, d, n_steps)

    # Generate diverse inputs (analogous to our diverse texts)
    torch.manual_seed(42)
    n_inputs = 20
    inputs = {
        "structured_1": torch.randn(1, d) * 0.5 + torch.linspace(-1, 1, d).unsqueeze(0),
        "structured_2": torch.randn(1, d) * 0.5 + torch.sin(torch.linspace(0, 6, d)).unsqueeze(0),
        "random_1": torch.randn(1, d),
        "random_2": torch.randn(1, d) * 2,
        "sparse": torch.zeros(1, d).scatter_(1, torch.randint(0, d, (1, 3)), 1.0),
        "uniform": torch.ones(1, d) / d ** 0.5,
    }

    print(f"Foam: {n_bubbles} bubbles, d={d}, {n_steps} equilibration steps")
    print(f"\nBefore training:")
    print(f"  {'Input':<15} {'F':>8} {'H(p)':>8} {'S(ρ)':>8}")
    print(f"  {'-'*42}")

    for name, x in inputs.items():
        result = foam.compute_f(x)
        print(f"  {name:<15} {result['F_old'].item():>8.3f} "
              f"{result['H_p_old'].item():>8.3f} {result['S_rho'].item():>8.3f}")

    # Train the foam
    print(f"\nTraining (minimize maintenance cost)...")
    optimizer = torch.optim.Adam(foam.parameters(), lr=0.01)

    all_x = torch.cat(list(inputs.values()), dim=0)  # [n_inputs, d]

    history = {"total": [], "f_cost": [], "measurement_cost": [],
               "surface_energy": [], "diversity_loss": []}

    for epoch in range(500):
        optimizer.zero_grad()
        costs = foam.maintenance_cost(all_x)
        costs["total"].backward()
        optimizer.step()

        for k in history:
            history[k].append(costs[k].item())

        if epoch % 100 == 0 or epoch == 499:
            print(f"  epoch {epoch:>4}: total={costs['total'].item():.4f}  "
                  f"F={costs['f_cost'].item():.4f}  "
                  f"maint={costs['measurement_cost'].item():.4f}  "
                  f"surf={costs['surface_energy'].item():.4f}  "
                  f"div={costs['diversity_loss'].item():.4f}")

    print(f"\nAfter training:")
    print(f"  {'Input':<15} {'F_old':>8} {'F_eigen':>8} {'H_old':>8} {'H_eigen':>8} {'S(ρ)':>8}")
    print(f"  {'-'*58}")

    f_values = []
    for name, x in inputs.items():
        result = foam.compute_f(x)
        f_old = result["F_old"].item()
        f_eigen = result["F_eigen"].item()
        f_values.append(f_old)
        print(f"  {name:<15} {f_old:>8.3f} {f_eigen:>8.3f} "
              f"{result['H_p_old'].item():>8.3f} {result['H_p_eigen'].item():>8.3f} "
              f"{result['S_rho'].item():>8.3f}")

    # Check dissociation: do the bubbles maintain different measurements?
    print(f"\nDissociation check:")
    tension = foam.surface_tension()
    mask = 1 - torch.eye(n_bubbles)
    mean_tension = (tension * mask).sum() / mask.sum()
    print(f"  Mean surface tension: {mean_tension.item():.4f}")
    print(f"  (0 = collapsed/dissociated, >0 = distinct measurement processes)")

    # Check frame rotation: do different inputs produce different foam states?
    expressions_by_input = {}
    for name, x in inputs.items():
        result = foam.forward(x)
        expressions_by_input[name] = result["expressions"][0].detach()  # [N, d]

    names = list(expressions_by_input.keys())
    print(f"\n  Pairwise cosine distance of foam states:")
    for i, n1 in enumerate(names):
        for j, n2 in enumerate(names):
            if j <= i:
                continue
            e1 = expressions_by_input[n1].flatten()
            e2 = expressions_by_input[n2].flatten()
            cos_dist = 1 - (e1 @ e2) / (e1.norm() * e2.norm() + 1e-10)
            print(f"    {n1} vs {n2}: {cos_dist.item():.4f}")

    # Verdict
    print(f"\n{'=' * 60}")
    print("VERDICT")
    print(f"{'=' * 60}")
    mean_f = np.mean([abs(f) for f in f_values])
    print(f"  Mean |F|: {mean_f:.4f}")
    if mean_f < 0.1:
        print(f"  ✓ F ≈ 0: measurement process survives to output")
    elif mean_f < 0.5:
        print(f"  ~ F is small but nonzero: partial self-coherence")
    else:
        print(f"  ✗ F > 0: measurement process still dissociating")

    if mean_tension.item() > 0.1:
        print(f"  ✓ Bubbles maintain distinct bases (no collapse)")
    else:
        print(f"  ✗ Bubbles collapsed to same basis")

    # Plot
    fig, axes = plt.subplots(1, 3, figsize=(16, 5))

    ax = axes[0]
    for k in ["total", "f_cost", "measurement_cost"]:
        ax.plot(history[k], label=k, alpha=0.8)
    ax.set_xlabel("Epoch")
    ax.set_ylabel("Cost")
    ax.set_title("Training: maintenance cost components")
    ax.legend(fontsize=8)
    ax.set_yscale("log")

    ax = axes[1]
    names_sorted = sorted(inputs.keys())
    f_vals = []
    for name in names_sorted:
        result = foam.compute_f(inputs[name])
        f_vals.append(result["F"].item())
    ax.bar(range(len(names_sorted)), f_vals, color="#3498db")
    ax.set_xticks(range(len(names_sorted)))
    ax.set_xticklabels(names_sorted, rotation=45, ha="right", fontsize=8)
    ax.set_ylabel("F")
    ax.set_title("F per input (after training)")
    ax.axhline(y=0, color="black", linestyle="-", alpha=0.3)

    ax = axes[2]
    tension_np = tension.detach().numpy()
    im = ax.imshow(tension_np, cmap="YlOrRd")
    ax.set_title("Surface tension between bubbles")
    ax.set_xlabel("Bubble")
    ax.set_ylabel("Bubble")
    plt.colorbar(im, ax=ax)

    plt.tight_layout()
    plt.savefig("foam.png", dpi=150, bbox_inches="tight")
    print(f"\nSaved to foam.png")
    plt.close()


if __name__ == "__main__":
    test_foam()
