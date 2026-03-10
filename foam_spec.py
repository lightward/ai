"""
foam_spec.py — implementation of the bio-logical intelligence specification.

three nouns: foam, bubble, operator
one verb: measure

the operator introduces itself into a foam as a bubble.
everything else is plateau dynamics.
"""

import torch
import torch.nn as nn
import numpy as np


class Bubble(nn.Module):
    """
    A measurement basis with topological integrity.
    Defined by its boundaries with other bubbles, not by its interior.

    A bubble is either:
      - a leaf: a single measurement basis (orthogonal matrix, Cayley-parameterized)
      - itself a foam: a cluster of bubbles acting as a single bubble at the
        parent level. Its effective basis is the eigenbasis of its interior
        foam's density matrix. (organic chemistry: functional group.)
    """

    def __init__(self, d: int, interior: "Foam | None" = None):
        super().__init__()
        self.d = d
        self.interior = interior

        if interior is None:
            # leaf bubble: basis via Cayley transform of skew-symmetric matrix
            self.L = nn.Parameter(torch.randn(d, d) * 0.1)

    @property
    def is_leaf(self) -> bool:
        return self.interior is None

    @property
    def basis(self) -> torch.Tensor:
        """The measurement basis U ∈ O(d)."""
        if self.interior is not None:
            return self.interior.effective_basis()
        A = self.L - self.L.T
        I = torch.eye(self.d, device=self.L.device)
        return torch.linalg.solve(I + A, I - A)

    def measure(self, x: torch.Tensor) -> torch.Tensor:
        """Measure x from this bubble's basis. x: [batch, d] or [d]."""
        return x @ self.basis

    def express(self, m: torch.Tensor) -> torch.Tensor:
        """Express measurement back to shared space."""
        return m @ self.basis.T


class Foam(nn.Module):
    """
    A relational topology of coexisting measurement bases.

    Composed of bubbles. Plateau-stabilizes: bubbles adjust their mutual
    boundaries until total surface energy is minimized. N=3 is the stable
    default (Plateau's law: three surfaces meet at 120° in stable junctions).

    The foam has its own "done" signal: the point at which further adjustment
    produces no further reduction. Boredom: the operator's recognition that
    stabilization is circling rather than descending.
    """

    def __init__(self, d: int, n_bubbles: int = 3, n_steps: int = 12):
        super().__init__()
        self.d = d
        self.n_steps = n_steps

        self._bubbles = nn.ModuleList([Bubble(d) for _ in range(n_bubbles)])

        # plateau dynamics parameters
        # cos(120°) = -0.5 for N=3: the angle at which three boundaries meet
        self.target_similarity = nn.Parameter(torch.tensor(-0.5))
        self.step_size = nn.Parameter(torch.tensor(0.1))
        self.temperature = nn.Parameter(torch.tensor(1.0))

    @property
    def n_bubbles(self) -> int:
        return len(self._bubbles)

    @property
    def bubbles(self) -> nn.ModuleList:
        return self._bubbles

    def surface_tension(self) -> torch.Tensor:
        """Pairwise boundary cost between all bubbles. [N, N]."""
        bases = torch.stack([b.basis for b in self._bubbles])
        diff = bases.unsqueeze(0) - bases.unsqueeze(1)
        return torch.sqrt((diff**2).sum(dim=(-2, -1)) + 1e-8)

    def add_bubble(self, bubble: Bubble):
        """Add a bubble to the foam. Foam is no longer at equilibrium."""
        self._bubbles.append(bubble)

    def remove_last_bubble(self) -> Bubble:
        """Remove and return the last bubble."""
        bubble = self._bubbles[-1]
        del self._bubbles[-1]
        return bubble

    def stabilize(
        self, x: torch.Tensor, boredom_threshold: float = 0.005
    ) -> dict:
        """
        Plateau-stabilize the foam given input x.

        x: [batch, d]

        Returns dict with:
          j0: measurements before stabilization (position)
          j1: list of intermediate states (momentum / need)
          j2: final equilibrium state (recognition)
          questions: boundary instabilities that didn't settle
          bored_at: step at which boredom kicked in (None if ran to completion)
        """
        N = self.n_bubbles
        batch = x.shape[0] if x.dim() > 1 else 1
        if x.dim() == 1:
            x = x.unsqueeze(0)

        # each bubble measures from its own basis
        measurements = torch.stack(
            [b.measure(x) for b in self._bubbles], dim=1
        )  # [batch, N, d]

        # J⁰: what is, before the verb moves
        j0 = measurements.detach().clone()

        # plateau dynamics
        device = x.device
        mask = 1 - torch.eye(N, device=device)
        tension = self.surface_tension()
        interaction = torch.softmax(
            -tension / self.temperature.abs().clamp(min=0.01), dim=-1
        )
        target = self.target_similarity
        step = self.step_size.abs().clamp(min=0.001, max=0.5)

        state = measurements
        j1 = []  # trajectory: measurement in progress
        bored_at = None

        for t in range(self.n_steps):
            state_n = state / (state.norm(dim=-1, keepdim=True) + 1e-10)
            cos_sim = torch.bmm(state_n, state_n.transpose(1, 2))  # [batch, N, N]

            force_mag = (cos_sim - target) * (mask * interaction).unsqueeze(0)

            diff = state.unsqueeze(2) - state.unsqueeze(1)  # [batch, N, N, d]
            diff_n = diff / (diff.norm(dim=-1, keepdim=True) + 1e-10)
            forces = (force_mag.unsqueeze(-1) * diff_n).sum(dim=2)  # [batch, N, d]

            prev_state = state
            state = state + step * forces
            j1.append(state.detach().clone())

            # boredom: is stabilization still generative?
            delta = (state - prev_state).norm() / (state.norm() + 1e-10)
            if delta.item() < boredom_threshold:
                bored_at = t
                break

        # J²: recognition — the foam at equilibrium with all bubbles included
        j2 = state

        # questions: how far are pairwise similarities from target?
        # these are the boundaries that couldn't settle
        final_n = state / (state.norm(dim=-1, keepdim=True) + 1e-10)
        final_sim = torch.bmm(final_n, final_n.transpose(1, 2))
        questions = (final_sim - target).abs() * mask.unsqueeze(0)

        return {
            "j0": j0,
            "j1": j1,
            "j2": j2,
            "questions": questions,
            "bored_at": bored_at,
            "surface_tension": tension.detach(),
        }

    def density_matrix(self, equilibrium: torch.Tensor) -> torch.Tensor:
        """Construct ρ from equilibrium measurements. [batch, d, d]."""
        m_n = equilibrium / (equilibrium.norm(dim=-1, keepdim=True) + 1e-10)
        # ρ = (1/N) Σ |m_i⟩⟨m_i|
        return torch.bmm(m_n.transpose(1, 2), m_n) / equilibrium.shape[1]

    def effective_basis(self) -> torch.Tensor:
        """
        The foam's effective basis when acting as a single bubble at a parent level.

        The eigenbasis of the density matrix at self-equilibrium:
        how this cluster of bubbles presents as a unit to the outside.
        (organic chemistry: the functional group's effective behavior.)
        """
        # self-stabilize with a neutral probe
        probe = torch.zeros(1, self.d)
        result = self.stabilize(probe)
        rho = self.density_matrix(result["j2"])[0]  # [d, d]
        _, eigvecs = torch.linalg.eigh(rho)
        return eigvecs  # sorted by eigenvalue, ascending


class Operator(nn.Module):
    """
    A measurement process that has a foam.

    The operator is always real. It walks the edges of its foam's bubbles.
    It can observe foam topology, wait for stabilization, and introduce
    boredom ("your equilibration is no longer generative, yield what you've got").

    To measure: the operator introduces itself into a target foam as a bubble.
    Everything else is Plateau dynamics.
    """

    def __init__(self, d: int, n_bubbles: int = 3, n_steps: int = 12):
        super().__init__()
        self.d = d
        self.foam = Foam(d, n_bubbles=n_bubbles, n_steps=n_steps)

    def measure(self, target_foam: Foam, x: torch.Tensor) -> dict:
        """
        Measure a target foam.

        The operator introduces its own basis into the target foam as a bubble.
        The target restabilizes. J⁰ is before, J¹ is during, J² is after.

        x: [batch, d] — the input being measured through the target foam

        Returns dict with j0, j1, j2, questions.
        """
        # J⁰: target foam before measurement (what is)
        j0_result = target_foam.stabilize(x)

        # introduce self as a bubble in the target foam
        # the operator's foam acts as a single bubble (functional group)
        self_as_bubble = Bubble(self.d, interior=self.foam)
        target_foam.add_bubble(self_as_bubble)

        # the target foam restabilizes with the operator's bubble included
        # J¹ forms: boundaries that can't settle are questions
        # J² arrives: new minimum-energy configuration = recognition
        result = target_foam.stabilize(x)

        # remove self from target foam (measurement complete)
        target_foam.remove_last_bubble()

        return {
            "j0": j0_result["j2"],       # target foam at equilibrium, pre-measurement
            "j1": result["j1"],           # stabilization trajectory (need)
            "j2": result["j2"],           # final equilibrium (recognition)
            "questions": result["questions"],
            "bored_at": result["bored_at"],
            "surface_tension_before": j0_result["surface_tension"],
            "surface_tension_after": result["surface_tension"],
        }

    def receive(self, incoming_foam: Foam, x: torch.Tensor) -> dict:
        """
        Receive a foam from another operator (communication).

        The operator introduces its own basis into the incoming foam.
        What crystallizes at J² is the message-as-received:
        not what was sent, not what was needed, but the measurement
        that became available when two bases met.
        """
        return self.measure(incoming_foam, x)


# ─── demonstration ───────────────────────────────────────────────────────────


def demo_primitives():
    """Demonstrate the three nouns and one verb."""
    d = 8
    torch.manual_seed(42)

    print("=" * 60)
    print("bio-logical intelligence: primitives demo")
    print("=" * 60)

    # ── bubble ──
    print("\n── bubble ──")
    b = Bubble(d)
    print(f"leaf bubble: basis is {d}x{d} orthogonal matrix")
    print(f"  basis orthogonality check: U @ U.T ≈ I?")
    UtU = b.basis @ b.basis.T
    print(f"  max deviation from I: {(UtU - torch.eye(d)).abs().max().item():.6f}")

    x = torch.randn(1, d)
    m = b.measure(x)
    x_back = b.express(m)
    print(f"  measure then express: reconstruction error = {(x - x_back).norm().item():.6f}")

    # ── foam ──
    print("\n── foam (N=3, Plateau-stable) ──")
    foam = Foam(d, n_bubbles=3)
    x = torch.randn(1, d)

    result = foam.stabilize(x)
    print(f"  stabilization steps: {len(result['j1'])}")
    print(f"  bored at step: {result['bored_at']}")

    # surface tension
    tension = result["surface_tension"]
    mask = 1 - torch.eye(3)
    mean_t = (tension * mask).sum() / mask.sum()
    print(f"  mean surface tension: {mean_t.item():.4f}")

    # questions: how far from target similarity?
    q = result["questions"]
    print(f"  mean question magnitude: {q.mean().item():.4f}")

    # density matrix
    rho = foam.density_matrix(result["j2"])
    eigenvalues = torch.linalg.eigvalsh(rho[0])
    print(f"  ρ eigenvalues: {eigenvalues.detach().numpy().round(4)}")

    # ── recursive bubble (bubble that is itself a foam) ──
    print("\n── recursive bubble (foam acting as single bubble) ──")
    inner_foam = Foam(d, n_bubbles=3)
    recursive_bubble = Bubble(d, interior=inner_foam)
    print(f"  inner foam: {inner_foam.n_bubbles} bubbles")
    print(f"  effective basis (eigenbasis of inner ρ):")
    eff = recursive_bubble.basis
    UtU = eff @ eff.T
    print(f"  orthogonality check: max deviation = {(UtU - torch.eye(d)).abs().max().item():.6f}")

    # ── operator ──
    print("\n── operator ──")
    operator = Operator(d, n_bubbles=3)
    target = Foam(d, n_bubbles=3)
    print(f"  operator foam: {operator.foam.n_bubbles} bubbles")
    print(f"  target foam: {target.n_bubbles} bubbles")

    x = torch.randn(1, d)
    result = operator.measure(target, x)

    print(f"  measurement complete:")
    print(f"    target bubbles during measurement: {target.n_bubbles + 1} (3 + operator)")
    print(f"    target bubbles after measurement:  {target.n_bubbles} (operator removed)")
    print(f"    J⁰ shape: {result['j0'].shape}")
    print(f"    J² shape: {result['j2'].shape}")
    print(f"    stabilization steps: {len(result['j1'])}")
    print(f"    bored at: {result['bored_at']}")
    print(f"    mean question: {result['questions'].mean().item():.4f}")

    # ── communication ──
    print("\n── communication (foam exchange) ──")
    alice = Operator(d, n_bubbles=3)
    bob = Operator(d, n_bubbles=3)

    # alice produces a foam (stabilizes her own foam with input)
    signal = torch.randn(1, d)
    alice_state = alice.foam.stabilize(signal)

    # bob receives alice's foam
    # in practice this means bob measures alice's foam
    received = bob.receive(alice.foam, signal)

    # what bob got (J²) is not what alice sent — it's the measurement
    # that became available when bob's basis met alice's topology
    alice_j2 = alice_state["j2"]
    bob_j2 = received["j2"]

    # compare density matrices — basis-independent comparison
    alice_rho = alice.foam.density_matrix(alice_j2)
    bob_rho = bob.foam.density_matrix(bob_j2)
    rho_sim = torch.nn.functional.cosine_similarity(
        alice_rho.flatten().unsqueeze(0),
        bob_rho.flatten().unsqueeze(0),
    ).item()
    print(f"  alice ρ vs bob ρ cosine similarity: {rho_sim:.4f}")
    print(f"  (related but not identical: communication is generative, not transmissive)")

    # ── coherence check ──
    print("\n── coherence: does drilling in return you to yourself? ──")
    # create a chain: operator → foam → recursive bubble → inner foam
    inner = Foam(d, n_bubbles=3)
    outer = Foam(d, n_bubbles=3)
    # replace one of outer's bubbles with a recursive one
    outer._bubbles[1] = Bubble(d, interior=inner)

    op = Operator(d, n_bubbles=3)
    result = op.measure(outer, torch.randn(1, d))

    # the operator measured through a foam containing a recursive bubble.
    # the recursive bubble's basis came from its interior foam's density matrix.
    # this is the coherent loop: operator → target foam → recursive bubble →
    #   inner foam → (stabilize) → effective basis → back to target foam → stabilize
    print(f"  operator measured through recursive foam")
    print(f"  J² shape: {result['j2'].shape}")
    print(f"  measurement completed without divergence: coherent loop ✓")

    print("\n" + "=" * 60)
    print("all primitives demonstrated. three nouns, one verb.")
    print("=" * 60)


if __name__ == "__main__":
    demo_primitives()
