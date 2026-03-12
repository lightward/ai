"""
test_depth_conversation.py — two depth=1 foams measure each other.

the experiment from session 7: the eigenquestion.

session 5 showed flat-foam convergence (ρ similarity 0.81 → 0.98).
those foams had no interior, no depth, no address. now they do.

what happens when foams with interior structure exchange?
does the interior participate? do the addresses develop meaning?
"""

import torch
import torch.nn.functional as F
from foam_spec import Foam, Operator, Bubble


def develop_to_depth(foam: Foam, max_measurements: int = 200) -> int:
    """Measure a d=3 foam with random inputs until it develops depth=1.
    Returns number of measurements taken."""
    for i in range(max_measurements):
        x = torch.randn(1, foam.d)
        result = foam.stabilize(x)
        if result["split"] is not None:
            return i + 1
    return max_measurements


def foam_depth(foam: Foam) -> list[int]:
    """Return depth of each bubble."""
    depths = []
    for b in foam.bubbles:
        if b.is_leaf:
            depths.append(0)
        else:
            depths.append(1 + max(foam_depth(b.interior)))
    return depths


def rho_from_foam(foam: Foam) -> torch.Tensor:
    """Probe a foam and return its density matrix."""
    probe = torch.eye(foam.d)
    result = foam.stabilize(probe)
    return foam.density_matrix(result["j2"]).mean(dim=0)


def rho_similarity(rho_a: torch.Tensor, rho_b: torch.Tensor) -> float:
    """Cosine similarity between two density matrices."""
    return F.cosine_similarity(
        rho_a.flatten().unsqueeze(0),
        rho_b.flatten().unsqueeze(0),
    ).item()


def main():
    d = 3
    torch.manual_seed(42)

    print("=" * 60)
    print("depth conversation: two depth=1 foams measure each other")
    print("=" * 60)

    # ── phase 1: develop both foams to depth=1 ──
    print("\n── phase 1: developing foams to depth=1 ──")

    foam_a = Foam(d, n_bubbles=3, writing_rate=0.1, split_threshold=0.3)
    foam_b = Foam(d, n_bubbles=3, writing_rate=0.1, split_threshold=0.3)

    steps_a = develop_to_depth(foam_a)
    print(f"  foam A: depth=1 after {steps_a} measurements")
    print(f"    depths: {foam_depth(foam_a)}")

    # keep developing until all have chance to split or settle
    for _ in range(100):
        x = torch.randn(1, d)
        foam_a.stabilize(x)
    print(f"    depths after 100 more: {foam_depth(foam_a)}")

    torch.manual_seed(137)  # different seed for B
    steps_b = develop_to_depth(foam_b)
    print(f"  foam B: depth=1 after {steps_b} measurements")
    print(f"    depths: {foam_depth(foam_b)}")

    for _ in range(100):
        x = torch.randn(1, d)
        foam_b.stabilize(x)
    print(f"    depths after 100 more: {foam_depth(foam_b)}")

    # ── phase 2: baseline — how similar are the foams before exchange? ──
    print("\n── phase 2: pre-exchange baseline ──")
    with torch.no_grad():
        rho_a = rho_from_foam(foam_a)
        rho_b = rho_from_foam(foam_b)
        baseline_sim = rho_similarity(rho_a, rho_b)
        print(f"  ρ similarity before exchange: {baseline_sim:.4f}")

        ev_a = torch.linalg.eigvalsh(rho_a)
        ev_b = torch.linalg.eigvalsh(rho_b)
        print(f"  foam A ρ eigenvalues: {ev_a.detach().numpy().round(4)}")
        print(f"  foam B ρ eigenvalues: {ev_b.detach().numpy().round(4)}")

    # ── phase 3: flat-foam control — same setup without depth ──
    print("\n── phase 3: flat-foam control (no depth) ──")
    torch.manual_seed(42)
    flat_a = Foam(d, n_bubbles=3, writing_rate=0.1, split_threshold=10.0)  # high threshold = no split
    flat_b = Foam(d, n_bubbles=3, writing_rate=0.1, split_threshold=10.0)

    # develop flat foams with same number of measurements
    for _ in range(steps_a + 100):
        flat_a.stabilize(torch.randn(1, d))
    torch.manual_seed(137)
    for _ in range(steps_b + 100):
        flat_b.stabilize(torch.randn(1, d))

    print(f"  flat A depths: {foam_depth(flat_a)}")
    print(f"  flat B depths: {foam_depth(flat_b)}")

    # mutual measurement: flat foams
    print("\n  flat-foam mutual measurement:")
    op_flat_a = Operator(d, n_bubbles=3)
    op_flat_a.foam = flat_a
    op_flat_b = Operator(d, n_bubbles=3)
    op_flat_b.foam = flat_b

    flat_sims = []
    with torch.no_grad():
        for i in range(40):
            x = torch.randn(1, d)
            # A measures B's foam, then B measures A's foam
            op_flat_a.measure(flat_b, x)
            op_flat_b.measure(flat_a, x)

            if i % 10 == 0 or i == 39:
                rho_fa = rho_from_foam(flat_a)
                rho_fb = rho_from_foam(flat_b)
                sim = rho_similarity(rho_fa, rho_fb)
                flat_sims.append(sim)
                print(f"    step {i+1:3d}: ρ similarity {sim:.4f}")

    # ── phase 4: depth-foam mutual measurement ──
    print("\n── phase 4: depth-foam mutual measurement ──")
    op_a = Operator(d, n_bubbles=3)
    op_a.foam = foam_a
    op_b = Operator(d, n_bubbles=3)
    op_b.foam = foam_b

    depth_sims = []
    splits_during = []
    with torch.no_grad():
        for i in range(40):
            x = torch.randn(1, d)
            # A measures B's foam
            result_ab = op_a.measure(foam_b, x)
            # B measures A's foam
            result_ba = op_b.measure(foam_a, x)

            if i % 10 == 0 or i == 39:
                rho_da = rho_from_foam(foam_a)
                rho_db = rho_from_foam(foam_b)
                sim = rho_similarity(rho_da, rho_db)
                depth_sims.append(sim)
                q_ab = result_ab["questions"].mean().item()
                q_ba = result_ba["questions"].mean().item()
                print(f"    step {i+1:3d}: ρ similarity {sim:.4f}  "
                      f"q(A→B) {q_ab:.4f}  q(B→A) {q_ba:.4f}")
                print(f"      A depths: {foam_depth(foam_a)}  "
                      f"B depths: {foam_depth(foam_b)}")

    # ── phase 5: structural comparison ──
    print("\n── phase 5: structural comparison ──")
    print(f"  flat convergence:  {flat_sims[0]:.4f} → {flat_sims[-1]:.4f}")
    print(f"  depth convergence: {depth_sims[0]:.4f} → {depth_sims[-1]:.4f}")

    # check if depth grew during exchange
    print(f"\n  final foam A depths: {foam_depth(foam_a)}")
    print(f"  final foam B depths: {foam_depth(foam_b)}")

    # how different are the interiors?
    print("\n── phase 6: interior structure comparison ──")
    for name, foam in [("A", foam_a), ("B", foam_b)]:
        for i, b in enumerate(foam.bubbles):
            if not b.is_leaf:
                inner_rho = rho_from_foam(b.interior)
                ev = torch.linalg.eigvalsh(inner_rho)
                print(f"  foam {name}, bubble {i} interior ρ eigenvalues: "
                      f"{ev.detach().numpy().round(4)}")
                # how does the interior's effective basis relate to parent?
                eff = b.interior.effective_basis()
                # check if interior stabilized differently
                probe = torch.eye(d)
                inner_result = b.interior.stabilize(probe)
                inner_q = inner_result["questions"].mean().item()
                print(f"    interior questions: {inner_q:.4f}  "
                      f"bored at: {inner_result['bored_at']}")

    # ── the question: did the interior participate? ──
    print("\n── the question: did the interior participate? ──")
    # compare interior ρ before and after... we can't go back,
    # but we can check if the interiors of A and B became more similar
    # (mutual convergence propagating into depth)
    interior_sims = []
    for i_a, b_a in enumerate(foam_a.bubbles):
        if not b_a.is_leaf:
            rho_inner_a = rho_from_foam(b_a.interior)
            for i_b, b_b in enumerate(foam_b.bubbles):
                if not b_b.is_leaf:
                    rho_inner_b = rho_from_foam(b_b.interior)
                    sim = rho_similarity(rho_inner_a, rho_inner_b)
                    interior_sims.append(sim)
                    print(f"  A[{i_a}] interior ↔ B[{i_b}] interior: "
                          f"ρ similarity {sim:.4f}")

    if interior_sims:
        print(f"\n  mean interior similarity: {sum(interior_sims)/len(interior_sims):.4f}")
        print(f"  surface similarity: {depth_sims[-1]:.4f}")
        if sum(interior_sims)/len(interior_sims) > 0.5:
            print("  → interior is participating in convergence")
        else:
            print("  → interior convergence unclear — investigate further")

    print("\n" + "=" * 60)
    print("measurement is writing. training is runtime.")
    print("=" * 60)


if __name__ == "__main__":
    main()
