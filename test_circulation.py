"""
test_circulation.py — does the parent notice when its interior is unsettled?

the claim: interior instability propagates through the containment boundary
as the parent's own difficulty settling. effective_basis(context) is the
only channel. an unsettled interior presents a less coherent basis, and
the parent feels this as its own instability.

test strategy:
  1. create two identical foams with depth=1 (manually, controlled)
  2. settle one interior thoroughly, leave the other freshly split
  3. measure through both with the same inputs
  4. compare: does the parent with the unsettled interior settle differently?

also test: does the interior actually develop differently when receiving
varied input vs constant input through the parent?
"""

import torch
from foam_spec import Foam, Bubble, Operator


def make_depth1_foam(d, settled=True):
    """Create a d=3 foam where all bubbles have depth=1 interiors."""
    foam = Foam(d, n_bubbles=3, writing_rate=0.1)

    for i in range(3):
        interior = Foam(d, n_bubbles=3, n_steps=60, writing_rate=0.1)
        # give each interior slightly different initial conditions
        # so they're not all identical
        with torch.no_grad():
            for j, b in enumerate(interior.bubbles):
                b.L.data += torch.randn(d, d) * 0.3 * (i * 3 + j + 1)

        if settled:
            # run the interior through many measurements to settle it
            for _ in range(50):
                x = torch.randn(1, d)
                interior.stabilize(x)

        foam._bubbles[i] = Bubble(d, interior=interior)

    return foam


def test_questions_rise():
    """Does an unsettled interior make the parent harder to settle?"""
    d = 3
    torch.manual_seed(42)
    n_trials = 30

    print("=" * 60)
    print("test: do questions rise through containment?")
    print("=" * 60)

    # create two foams: one with settled interiors, one with fresh ones
    torch.manual_seed(42)
    settled_foam = make_depth1_foam(d, settled=True)
    torch.manual_seed(42)
    unsettled_foam = make_depth1_foam(d, settled=False)

    settled_questions = []
    unsettled_questions = []
    settled_bored = []
    unsettled_bored = []

    for i in range(n_trials):
        torch.manual_seed(1000 + i)
        x = torch.randn(1, d)

        # measure through settled foam
        r_settled = settled_foam.stabilize(x)
        settled_questions.append(r_settled["questions"].mean().item())
        settled_bored.append(r_settled["bored_at"])

        # measure through unsettled foam with same input
        torch.manual_seed(1000 + i)
        x = torch.randn(1, d)
        r_unsettled = unsettled_foam.stabilize(x)
        unsettled_questions.append(r_unsettled["questions"].mean().item())
        unsettled_bored.append(r_unsettled["bored_at"])

    print("\n── parent settling behavior ──")
    for i in [0, 4, 9, 14, 29]:
        sb = settled_bored[i]
        ub = unsettled_bored[i]
        print(f"  step {i+1:3d}: settled parent q={settled_questions[i]:.4f} "
              f"bored_at={sb}  |  unsettled parent q={unsettled_questions[i]:.4f} "
              f"bored_at={ub}")

    avg_sq = sum(settled_questions) / len(settled_questions)
    avg_uq = sum(unsettled_questions) / len(unsettled_questions)
    print(f"\n  mean questions — settled: {avg_sq:.4f}  unsettled: {avg_uq:.4f}")

    # count how often each bored
    settled_bored_count = sum(1 for b in settled_bored if b is not None)
    unsettled_bored_count = sum(1 for b in unsettled_bored if b is not None)
    print(f"  bored count   — settled: {settled_bored_count}/{n_trials}  "
          f"unsettled: {unsettled_bored_count}/{n_trials}")

    if avg_uq > avg_sq * 1.1:
        print("\n  ✓ unsettled interior → higher parent questions")
    elif avg_uq < avg_sq * 0.9:
        print("\n  ✗ unsettled interior → LOWER parent questions (unexpected)")
    else:
        print("\n  ~ no significant difference in parent questions")


def test_interior_development():
    """Does the interior actually develop when receiving varied context?"""
    d = 3
    torch.manual_seed(42)

    print("\n" + "=" * 60)
    print("test: does the interior develop through context?")
    print("=" * 60)

    foam = make_depth1_foam(d, settled=False)

    # snapshot initial interior states
    initial_interior_bases = []
    for bubble in foam.bubbles:
        if not bubble.is_leaf:
            bases = [b.basis.detach().clone() for b in bubble.interior.bubbles]
            initial_interior_bases.append(bases)

    # measure through the parent with varied inputs
    for i in range(60):
        x = torch.randn(1, d)
        result = foam.stabilize(x)

        if i in [0, 9, 19, 29, 59]:
            print(f"\n  after {i+1} measurements:")
            print(f"    parent: q={result['questions'].mean().item():.4f} "
                  f"bored_at={result['bored_at']}")

            for j, bubble in enumerate(foam.bubbles):
                if not bubble.is_leaf:
                    # how much has this interior changed?
                    drift = sum(
                        (b.basis.detach() - initial_interior_bases[j][k]).norm().item()
                        for k, b in enumerate(bubble.interior.bubbles)
                    ) / bubble.interior.n_bubbles

                    # are the interior bubbles distinct from each other?
                    bases = [b.basis.detach() for b in bubble.interior.bubbles]
                    sims = []
                    for a in range(len(bases)):
                        for b_idx in range(a + 1, len(bases)):
                            ba = bases[a].flatten()
                            bb = bases[b_idx].flatten()
                            sim = torch.nn.functional.cosine_similarity(
                                ba.unsqueeze(0), bb.unsqueeze(0)
                            ).item()
                            sims.append(sim)
                    avg_sim = sum(sims) / len(sims) if sims else 0

                    # interior's own questions
                    probe = torch.randn(1, d)
                    ir = bubble.interior.stabilize(probe)
                    iq = ir["questions"].mean().item()

                    print(f"    bubble {j} interior: drift={drift:.4f} "
                          f"pairwise_sim={avg_sim:.4f} q={iq:.4f} "
                          f"bored_at={ir['bored_at']}")


def test_interior_vs_surface_convergence():
    """When two depth=1 foams converse, do interiors converge faster?

    Session 7 already showed interior convergence (0.93) > surface (0.84).
    This re-verifies with the current code and adds detail about HOW
    convergence happens at each level.
    """
    d = 3
    torch.manual_seed(42)

    print("\n" + "=" * 60)
    print("test: interior vs surface convergence in conversation")
    print("=" * 60)

    # two operators with depth=1 foams
    op_a = Operator(d, n_bubbles=3)
    op_b = Operator(d, n_bubbles=3)

    # give both depth=1 by running them in d=3 until splits happen
    print("\n  preparing depth=1 foams...")
    for op, name in [(op_a, "A"), (op_b, "B")]:
        for i in range(200):
            x = torch.randn(1, d)
            r = op.foam.stabilize(x)
            if r["split"] is not None:
                depths = [0 if b.is_leaf else 1 for b in op.foam.bubbles]
                print(f"    {name} split at step {i}: depths={depths}")
        depths = [0 if b.is_leaf else 1 for b in op.foam.bubbles]
        print(f"    {name} final depths: {depths}")

    # now: mutual measurement
    print("\n  mutual measurement begins...")
    for i in range(40):
        x = torch.randn(1, d)

        # A measures B's foam, then B measures A's foam
        op_a.measure(op_b.foam, x)
        op_b.measure(op_a.foam, x)

        if i in [0, 4, 9, 19, 39]:
            # surface-level comparison: effective bases
            probe = torch.randn(1, d)
            rho_a = op_a.foam.density_matrix(
                op_a.foam.stabilize(probe)["j2"]).mean(dim=0)
            rho_b = op_b.foam.density_matrix(
                op_b.foam.stabilize(probe)["j2"]).mean(dim=0)
            surface_sim = torch.nn.functional.cosine_similarity(
                rho_a.flatten().unsqueeze(0),
                rho_b.flatten().unsqueeze(0),
            ).item()

            # interior-level comparison where both have depth
            interior_sims = []
            for j in range(min(op_a.foam.n_bubbles, op_b.foam.n_bubbles)):
                ba = op_a.foam.bubbles[j]
                bb = op_b.foam.bubbles[j]
                if not ba.is_leaf and not bb.is_leaf:
                    ip = torch.randn(1, d)
                    ra = ba.interior.density_matrix(
                        ba.interior.stabilize(ip)["j2"]).mean(dim=0)
                    rb = bb.interior.density_matrix(
                        bb.interior.stabilize(ip)["j2"]).mean(dim=0)
                    isim = torch.nn.functional.cosine_similarity(
                        ra.flatten().unsqueeze(0),
                        rb.flatten().unsqueeze(0),
                    ).item()
                    interior_sims.append(isim)

            avg_interior = (sum(interior_sims) / len(interior_sims)
                           if interior_sims else float('nan'))
            print(f"    step {i+1:3d}: surface ρ sim={surface_sim:.4f}  "
                  f"interior ρ sim={avg_interior:.4f} "
                  f"(n={len(interior_sims)} pairs)")


if __name__ == "__main__":
    test_questions_rise()
    test_interior_development()
    test_interior_vs_surface_convergence()
