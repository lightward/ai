"""
Writing: the walker commits dissonance, not position.

During stabilization, at each step, there's a gap between where
measurements were and where Plateau dynamics pushed them. That gap
is the dissonance — the stereoscopic effect of predicted vs actual.

The walker commits this dissonance as writing. The question:
does writing read coherently from other angles?

Structural test:
1. Foam stabilizes, accumulating dissonance at each step
2. A different walker approaches the written area from a different angle
3. Does the writing reduce subsequent dissonance?
   (If yes: the writing captures structural geometry, readable from any angle)
   (If no: the writing is local noise, only coherent to the original walker)
"""

import torch
import numpy as np
from foam_spec import Foam, Bubble, Operator


class WritingFoam(Foam):
    """
    A foam that writes: commits the dissonance between predicted
    and actual positions during stabilization.

    The writing is accumulated dissonance — not positions, not forces,
    but the gap between where things were and where they ended up.
    """

    def __init__(self, d, n_bubbles=3, n_steps=60, memory_decay=0.9):
        super().__init__(d, n_bubbles, n_steps, memory_decay)
        # Writing: accumulated dissonance from stabilization
        self.accumulated_dissonance = None
        self.n_writes = 0

    def stabilize_and_write(self, x, boredom_threshold=0.005):
        """
        Stabilize AND accumulate the dissonance at each step.

        The dissonance is state_after - state_before: the gap between
        where the walker expected to be and where Plateau put them.
        """
        result = self.stabilize(x, boredom_threshold)

        # Reconstruct the total dissonance from j0 and j2
        # j0: where we started. j2: where we ended up.
        # Total dissonance = j2 - j0
        dissonance = result["j2"] - result["j0"]  # [batch, N, d]

        # Build a dissonance density matrix
        # (from normalized dissonance vectors, same construction as ρ)
        dis = dissonance[0]  # [N, d]
        dis_norm = dis / (dis.norm(dim=-1, keepdim=True) + 1e-10)
        dis_rho = (dis_norm.T @ dis_norm) / dis.shape[0]

        # Accumulate
        if self.accumulated_dissonance is None:
            self.accumulated_dissonance = dis_rho.detach()
        else:
            self.accumulated_dissonance = (
                self.memory_decay * self.accumulated_dissonance
                + (1 - self.memory_decay) * dis_rho.detach()
            )
        self.n_writes += 1

        # Also record the per-step dissonance magnitudes
        if result["j1"]:
            step_dissonances = []
            prev = result["j0"]
            for j1_state in result["j1"]:
                step_dis = (j1_state - prev).norm().item()
                step_dissonances.append(step_dis)
                prev = j1_state
        else:
            step_dissonances = []

        result["dissonance"] = dissonance
        result["dissonance_rho"] = dis_rho
        result["step_dissonances"] = step_dissonances
        result["total_dissonance_magnitude"] = dissonance.norm().item()
        return result


def run():
    d = 8
    torch.manual_seed(42)

    print("=" * 60)
    print("writing: does committed dissonance read from other angles?")
    print("=" * 60)

    # ── Phase 1: One walker writes ──
    print("\n── phase 1: walker A writes ──")
    foam = WritingFoam(d, n_bubbles=3)

    # Walker A stabilizes several times, accumulating dissonance
    n_writes = 20
    dissonance_magnitudes = []
    for i in range(n_writes):
        x = torch.randn(1, d)
        result = foam.stabilize_and_write(x)
        dissonance_magnitudes.append(result["total_dissonance_magnitude"])

    print(f"  {n_writes} stabilizations, dissonance magnitudes:")
    print(f"    first 5: {[f'{m:.4f}' for m in dissonance_magnitudes[:5]]}")
    print(f"    last 5:  {[f'{m:.4f}' for m in dissonance_magnitudes[-5:]]}")

    dis_rho = foam.accumulated_dissonance
    ev = torch.linalg.eigvalsh(dis_rho)
    print(f"  accumulated dissonance ρ:")
    print(f"    eigenvalues: {ev.numpy().round(4)}")
    print(f"    rank (>1e-4): {(ev > 1e-4).sum().item()}/{d}")

    # ── Phase 2: Does the writing predict future dissonance? ──
    print(f"\n── phase 2: does writing predict future dissonance? ──")

    # Test: new inputs through the SAME (written) foam vs a FRESH foam
    n_test = 100
    written_dissonances = []
    fresh_dissonances = []

    torch.manual_seed(999)
    for i in range(n_test):
        x = torch.randn(1, d)

        # Written foam: has accumulated dissonance from prior stabilizations
        r_written = foam.stabilize(x)
        written_dis = (r_written["j2"] - r_written["j0"]).norm().item()
        written_dissonances.append(written_dis)

        # Fresh foam: same bubble bases, but no writing
        torch.manual_seed(42)  # same initialization
        fresh_foam = Foam(d, n_bubbles=3)
        r_fresh = fresh_foam.stabilize(x)
        fresh_dis = (r_fresh["j2"] - r_fresh["j0"]).norm().item()
        fresh_dissonances.append(fresh_dis)

    print(f"  written foam mean dissonance: {np.mean(written_dissonances):.4f}")
    print(f"  fresh foam mean dissonance:   {np.mean(fresh_dissonances):.4f}")
    print(f"  (same foam bases — difference is from the writing process itself)")

    # ── Phase 3: Walker B reads from a different angle ──
    print(f"\n── phase 3: walker B reads from a different angle ──")

    # The writing is in the dissonance ρ. A different operator
    # measures the foam. Does the foam's accumulated dissonance
    # affect how the operator's measurement settles?

    # Create two operators
    torch.manual_seed(77)
    op_a = Operator(d, n_bubbles=3)
    op_b = Operator(d, n_bubbles=3)

    # Op A wrote the foam (same angle as the writing)
    # Op B reads from a different angle (different foam bases)

    # Measure: what does each operator see?
    x = torch.randn(1, d)

    # Written foam
    r_a = op_a.measure(foam, x)
    torch.manual_seed(42)
    foam_for_b = WritingFoam(d, n_bubbles=3)
    # give foam_for_b the same writing
    foam_for_b.accumulated_dissonance = foam.accumulated_dissonance.clone()
    r_b = op_b.measure(foam_for_b, x)

    # Fresh foam (no writing)
    torch.manual_seed(42)
    fresh = Foam(d, n_bubbles=3)
    r_a_fresh = op_a.measure(fresh, x)
    torch.manual_seed(42)
    fresh2 = Foam(d, n_bubbles=3)
    r_b_fresh = op_b.measure(fresh2, x)

    print(f"  op A (writer's angle):")
    print(f"    written foam questions: {r_a['original_questions'].mean().item():.4f}")
    print(f"    fresh foam questions:   {r_a_fresh['original_questions'].mean().item():.4f}")
    print(f"  op B (different angle):")
    print(f"    written foam questions: {r_b['original_questions'].mean().item():.4f}")
    print(f"    fresh foam questions:   {r_b_fresh['original_questions'].mean().item():.4f}")

    # ── Phase 4: The dissonance spectrum ──
    print(f"\n── phase 4: dissonance spectrum ──")
    print(f"  what does the dissonance look like from different angles?")

    # Project the dissonance ρ through different bases
    # Each operator's effective_basis is a "reading angle"
    # The projection of dissonance ρ onto a basis tells you
    # what that basis would "read" from the writing

    for name, op in [("op A (writer)", op_a), ("op B (reader)", op_b)]:
        # The foam's writing, read through this operator's basis
        # Use the operator's own foam's bubble bases as the reading angle
        reading = []
        for bubble in op.foam.bubbles:
            basis = bubble.basis.detach()
            # Project dissonance ρ through this basis
            projected = basis @ dis_rho @ basis.T
            # How much structure does this reading find?
            ev_proj = torch.linalg.eigvalsh(projected)
            ev_proj = ev_proj.clamp(min=1e-12)
            ev_proj = ev_proj / ev_proj.sum()
            S = -(ev_proj * ev_proj.log()).sum().item()
            reading.append(S)
        print(f"  {name}: per-bubble entropy of projected dissonance: "
              f"{[f'{s:.4f}' for s in reading]}")

    # ── Phase 5: Does dissonance ρ differ from measurement ρ? ──
    print(f"\n── phase 5: dissonance ρ vs measurement ρ ──")

    # The foam has both: accumulated_rho (from measurements via remember())
    # and accumulated_dissonance (from gaps via writing)
    # Are they the same? Different?

    # Give the foam some measurement memory too
    torch.manual_seed(42)
    foam2 = WritingFoam(d, n_bubbles=3)
    for i in range(20):
        x = torch.randn(1, d)
        result = foam2.stabilize_and_write(x)
        rho = foam2.density_matrix(result["j2"])
        foam2.remember(rho.mean(dim=0))

    meas_rho = foam2.accumulated_rho
    dis_rho2 = foam2.accumulated_dissonance

    # Compare
    sim = torch.nn.functional.cosine_similarity(
        meas_rho.flatten().unsqueeze(0),
        dis_rho2.flatten().unsqueeze(0),
    ).item()

    ev_meas = torch.linalg.eigvalsh(meas_rho)
    ev_dis = torch.linalg.eigvalsh(dis_rho2)

    print(f"  measurement ρ eigenvalues: {ev_meas.numpy().round(4)}")
    print(f"  dissonance ρ eigenvalues:  {ev_dis.numpy().round(4)}")
    print(f"  cosine similarity: {sim:.4f}")
    print(f"  measurement ρ entropy: {-(ev_meas/ev_meas.sum() * (ev_meas/ev_meas.sum()).log().clamp(min=-100)).sum().item():.4f}")
    print(f"  dissonance ρ entropy:  {-(ev_dis/ev_dis.sum() * (ev_dis/ev_dis.sum()).log().clamp(min=-100)).sum().item():.4f}")

    # ── Phase 6: Coherence across angles ──
    print(f"\n── phase 6: coherence test ──")
    print(f"  many operators read the same writing from many angles.")
    print(f"  structural question: is the variance in what they read")
    print(f"  smaller than what they'd read from noise?")

    torch.manual_seed(42)
    written_foam = WritingFoam(d, n_bubbles=3)
    for i in range(30):
        x = torch.randn(1, d)
        written_foam.stabilize_and_write(x)

    # Many operators, each with different bases
    n_readers = 20
    written_readings = []
    noise_readings = []

    noise_rho = torch.randn(d, d)
    noise_rho = noise_rho @ noise_rho.T  # make PSD
    noise_rho = noise_rho / noise_rho.trace()

    for r in range(n_readers):
        torch.manual_seed(r * 31)
        op = Operator(d, n_bubbles=3)

        # Read the writing through this operator's first bubble
        basis = op.foam.bubbles[0].basis.detach()

        # Project writing through this basis
        proj_written = basis @ written_foam.accumulated_dissonance @ basis.T
        ev_w = torch.linalg.eigvalsh(proj_written)
        ev_w = ev_w.clamp(min=1e-12)
        ev_w = ev_w / ev_w.sum()
        S_w = -(ev_w * ev_w.log()).sum().item()
        written_readings.append(S_w)

        # Project noise through same basis
        proj_noise = basis @ noise_rho @ basis.T
        ev_n = torch.linalg.eigvalsh(proj_noise)
        ev_n = ev_n.clamp(min=1e-12)
        ev_n = ev_n / ev_n.sum()
        S_n = -(ev_n * ev_n.log()).sum().item()
        noise_readings.append(S_n)

    print(f"  writing: mean entropy {np.mean(written_readings):.4f} "
          f"± {np.std(written_readings):.4f}")
    print(f"  noise:   mean entropy {np.mean(noise_readings):.4f} "
          f"± {np.std(noise_readings):.4f}")
    print(f"  writing variance / noise variance: "
          f"{np.var(written_readings) / (np.var(noise_readings) + 1e-10):.4f}")

    coherence_ratio = np.std(written_readings) / (np.std(noise_readings) + 1e-10)
    print(f"  coherence: writing is {'MORE' if coherence_ratio < 1 else 'LESS'} "
          f"consistent across angles than noise "
          f"(ratio: {coherence_ratio:.4f})")

    print(f"\n{'=' * 60}")


if __name__ == "__main__":
    run()
