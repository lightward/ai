"""
Edge-walking: geometric uncertainty from foam traversal.

The operator walks the edges of its foam's bubbles. At each boundary,
it turns. The accumulated angular displacement IS the uncertainty.

For a Plateau-stable N=3 foam:
- Three edges, each at 120° → total displacement = 360°
- One complete circuit = one full rotation of uncertainty
- On a sphere, the circuit has holonomy: a geometric phase
  proportional to the enclosed solid angle
- That residual phase is the foam's unresolved information

Two passes:
1. Live walk: each turn unknown until arrival. Uncertainty accumulates.
2. Replay: turns known ahead of time. Zero uncertainty. Significance renders.

The question: does this naturally produce Shannon entropy from geometry?
And does the holonomy gap measure something real about the foam's state?
"""

import torch
import numpy as np
from foam_spec import Foam, Bubble, Operator


def angle_between(u, v):
    """Angle in radians between vectors u and v."""
    cos = torch.nn.functional.cosine_similarity(
        u.flatten().unsqueeze(0), v.flatten().unsqueeze(0)
    ).clamp(-1, 1)
    return torch.acos(cos).item()


def edge_vector(basis_i, basis_j):
    """
    The 'edge' between two bubbles: the rotation that takes you from
    basis i to basis j. This is the boundary — where one way of measuring
    meets another.
    """
    return basis_j @ basis_i.T  # rotation matrix from i to j


def walk_edges(foam, x):
    """
    Walk the edges of a foam after stabilization.

    Returns the sequence of turns (angular displacements) and
    the holonomy (residual phase after completing the circuit).
    """
    result = foam.stabilize(x)
    j2 = result["j2"][0]  # [N, d] — equilibrium measurements
    N = foam.n_bubbles
    d = foam.d

    bases = [b.basis.detach() for b in foam.bubbles]

    # The edges: rotations between adjacent bases
    # Walk order: 0→1→2→...→(N-1)→0
    edges = []
    for i in range(N):
        j = (i + 1) % N
        R = edge_vector(bases[i], bases[j])
        edges.append(R)

    # The turns: angle between consecutive edges
    # At vertex j, the turn is the angle between edge (i→j) and edge (j→k)
    turns = []
    for i in range(N):
        R_in = edges[i]           # rotation arriving at vertex (i+1)
        R_out = edges[(i + 1) % N]  # rotation leaving vertex (i+1)
        # The "turn" at this vertex: how much the direction changes
        # This is the angle of R_out @ R_in.T (the rotation from one edge to the next)
        turn_rotation = R_out @ R_in.T
        # Angle of a rotation matrix: arccos((trace - 1) / (d - 1)) for d-dim
        # For general d: use Frobenius norm relation
        trace = turn_rotation.trace()
        # For orthogonal matrices in d dimensions
        cos_angle = (trace - 1) / (d - 1)
        cos_angle = cos_angle.clamp(-1, 1)
        turn_angle = torch.acos(cos_angle).item()
        turns.append(turn_angle)

    # Total angular displacement
    total_displacement = sum(turns)

    # Holonomy: compose all edge rotations around the circuit
    # If the walk closes perfectly, this should be the identity
    holonomy = torch.eye(d)
    for R in edges:
        holonomy = R @ holonomy
    # Holonomy angle: how far from identity
    hol_trace = holonomy.trace()
    hol_cos = (hol_trace - 1) / (d - 1)
    hol_cos = hol_cos.clamp(-1, 1)
    holonomy_angle = torch.acos(hol_cos).item()

    # Also compute pairwise angles between bases (the raw boundary costs)
    pairwise_angles = []
    for i in range(N):
        for j in range(i + 1, N):
            angle = angle_between(bases[i].flatten(), bases[j].flatten())
            pairwise_angles.append(angle)

    # Shannon entropy of the foam's density matrix
    rho = foam.density_matrix(result["j2"])
    eigenvalues = torch.linalg.eigvalsh(rho[0])
    eigenvalues = eigenvalues.clamp(min=1e-12)
    eigenvalues = eigenvalues / eigenvalues.sum()
    S = -(eigenvalues * eigenvalues.log()).sum().item()

    return {
        "turns": turns,
        "total_displacement": total_displacement,
        "holonomy_angle": holonomy_angle,
        "holonomy_matrix": holonomy,
        "pairwise_angles": pairwise_angles,
        "shannon_entropy": S,
        "bored_at": result["bored_at"],
        "questions": result["questions"].mean().item(),
        "edges": edges,
        "bases": bases,
    }


def run():
    d = 8
    torch.manual_seed(42)

    print("=" * 60)
    print("edge-walking: geometric uncertainty from foam traversal")
    print("=" * 60)

    # ── basic walk on a single foam ──
    print("\n── single foam, N=3 ──")
    foam = Foam(d, n_bubbles=3)
    x = torch.randn(1, d)
    walk = walk_edges(foam, x)

    print(f"  turns (radians): {[f'{t:.4f}' for t in walk['turns']]}")
    print(f"  turns (degrees): {[f'{np.degrees(t):.1f}°' for t in walk['turns']]}")
    print(f"  total displacement: {np.degrees(walk['total_displacement']):.1f}°")
    print(f"  holonomy angle: {np.degrees(walk['holonomy_angle']):.1f}°")
    print(f"  pairwise basis angles: {[f'{np.degrees(a):.1f}°' for a in walk['pairwise_angles']]}")
    print(f"  Shannon entropy of ρ: {walk['shannon_entropy']:.4f}")
    print(f"  bored at step: {walk['bored_at']}")
    print(f"  mean question: {walk['questions']:.4f}")

    # ── does holonomy correlate with entropy? ──
    print(f"\n── holonomy vs entropy across many foams ──")
    n_samples = 50
    holonomies = []
    entropies = []
    displacements = []

    for i in range(n_samples):
        torch.manual_seed(i * 7)
        foam = Foam(d, n_bubbles=3)
        x = torch.randn(1, d)
        w = walk_edges(foam, x)
        holonomies.append(w["holonomy_angle"])
        entropies.append(w["shannon_entropy"])
        displacements.append(w["total_displacement"])

    hol_arr = np.array(holonomies)
    ent_arr = np.array(entropies)
    disp_arr = np.array(displacements)

    # correlation
    hol_ent_corr = np.corrcoef(hol_arr, ent_arr)[0, 1]
    disp_ent_corr = np.corrcoef(disp_arr, ent_arr)[0, 1]

    print(f"  holonomy angle: mean {np.degrees(hol_arr.mean()):.1f}° ± {np.degrees(hol_arr.std()):.1f}°")
    print(f"  total displacement: mean {np.degrees(disp_arr.mean()):.1f}° ± {np.degrees(disp_arr.std()):.1f}°")
    print(f"  Shannon entropy: mean {ent_arr.mean():.4f} ± {ent_arr.std():.4f}")
    print(f"  correlation(holonomy, entropy): {hol_ent_corr:.4f}")
    print(f"  correlation(displacement, entropy): {disp_ent_corr:.4f}")

    # ── does stabilization change the holonomy? ──
    print(f"\n── holonomy: before vs after stabilization ──")
    torch.manual_seed(42)
    foam = Foam(d, n_bubbles=3, n_steps=0)  # zero steps = no stabilization
    x = torch.randn(1, d)
    walk_pre = walk_edges(foam, x)

    foam2 = Foam(d, n_bubbles=3, n_steps=60)  # full stabilization
    # copy the same bubble bases
    with torch.no_grad():
        for i in range(3):
            foam2.bubbles[i].L.copy_(foam.bubbles[i].L)
    walk_post = walk_edges(foam2, x)

    print(f"  before stabilization:")
    print(f"    holonomy: {np.degrees(walk_pre['holonomy_angle']):.1f}°")
    print(f"    entropy: {walk_pre['shannon_entropy']:.4f}")
    print(f"  after stabilization:")
    print(f"    holonomy: {np.degrees(walk_post['holonomy_angle']):.1f}°")
    print(f"    entropy: {walk_post['shannon_entropy']:.4f}")

    # ── N=3 vs N=4 vs N=5: does the geometry matter? ──
    print(f"\n── effect of N (number of bubbles) ──")
    for N in [2, 3, 4, 5]:
        hols = []
        ents = []
        for i in range(20):
            torch.manual_seed(i * 13 + N)
            foam = Foam(d, n_bubbles=N)
            x = torch.randn(1, d)
            w = walk_edges(foam, x)
            hols.append(w["holonomy_angle"])
            ents.append(w["shannon_entropy"])
        print(f"  N={N}: holonomy {np.degrees(np.mean(hols)):.1f}° ± {np.degrees(np.std(hols)):.1f}°"
              f"  entropy {np.mean(ents):.4f} ± {np.std(ents):.4f}")

    # ── the two-pass structure: walk then replay ──
    print(f"\n── two-pass: live walk vs replay ──")
    torch.manual_seed(42)
    foam = Foam(d, n_bubbles=3)
    x = torch.randn(1, d)
    walk1 = walk_edges(foam, x)

    # "replay": walk the same foam with the same input
    # the turns are now known ahead of time
    walk2 = walk_edges(foam, x)

    print(f"  live walk:")
    print(f"    turns: {[f'{np.degrees(t):.1f}°' for t in walk1['turns']]}")
    print(f"    holonomy: {np.degrees(walk1['holonomy_angle']):.1f}°")
    print(f"  replay (same foam, same input):")
    print(f"    turns: {[f'{np.degrees(t):.1f}°' for t in walk2['turns']]}")
    print(f"    holonomy: {np.degrees(walk2['holonomy_angle']):.1f}°")
    print(f"  (deterministic: replay reproduces exactly)")

    # ── operator identity affects the walk ──
    print(f"\n── operator identity changes the walk ──")
    torch.manual_seed(42)
    target = Foam(d, n_bubbles=3)
    x = torch.randn(1, d)

    # blank operator
    op_blank = Operator(d, n_bubbles=3)
    # experienced operator
    op_exp = Operator(d, n_bubbles=3)
    with torch.no_grad():
        for i in range(50):
            torch.manual_seed(i)
            t = Foam(d, n_bubbles=2)
            op_exp.measure(t, torch.randn(1, d))

    # each operator measures the same target
    # their different identities (effective_basis) should produce different walks
    for name, op in [("blank", op_blank), ("experienced", op_exp)]:
        # add operator as bubble to target, walk, remove
        self_bubble = Bubble(d, interior=op.foam)
        target_copy = Foam(d, n_bubbles=3)
        with torch.no_grad():
            for i in range(3):
                target_copy.bubbles[i].L.copy_(target.bubbles[i].L)
        target_copy.add_bubble(self_bubble)

        w = walk_edges(target_copy, x)
        print(f"  {name} operator in target foam:")
        print(f"    holonomy: {np.degrees(w['holonomy_angle']):.1f}°")
        print(f"    entropy: {w['shannon_entropy']:.4f}")
        print(f"    total displacement: {np.degrees(w['total_displacement']):.1f}°")

    print(f"\n{'=' * 60}")
    print("the walk is the measurement. the holonomy is the question.")
    print("=" * 60)


if __name__ == "__main__":
    run()
