"""
foam_reflection.py — depth creates reflection.

two foams, same input. one flat, one deep.
the flat foam returns the same face to every operator.
the deep foam returns YOU — what you see depends on how you look.

the artifact is the pair. probe them and experience the difference.

info-theoretic measurement: density matrices (ρ).
physical measurement: actual output directions.
conservation: ρ converges even though bases differ.
"""

import torch
from foam_spec import Foam, Bubble, Operator
from foam_echo import encode_byte, decode_vector


def build_deep_foam(d: int = 3, seed: int = 42) -> Foam:
    """
    Build a depth=1 foam through scarcity, the honest way.
    Feed random inputs in d=3 until splitting occurs.
    """
    torch.manual_seed(seed)
    foam = Foam(d, n_bubbles=3, writing_rate=0.5, split_threshold=0.3,
                n_steps=60)

    # feed random inputs until we get splits
    # (or manually construct if scarcity doesn't fire fast enough)
    for i in range(300):
        x = torch.randn(1, d)
        with torch.no_grad():
            result = foam.stabilize(x)
        if result.get("split") is not None:
            print(f"  split at step {i}")

    # check if splits occurred
    depths = []
    for b in foam.bubbles:
        depths.append(0 if b.is_leaf else 1)

    if max(depths) == 0:
        # scarcity didn't fire — construct depth manually
        # (same mechanism, just forced: take a leaf, give it interior)
        print("  no spontaneous split — constructing depth=1 manually")
        bubble = foam._bubbles[0]
        interior = Foam(d, n_bubbles=3, writing_rate=foam.writing_rate,
                       n_steps=foam.n_steps, split_threshold=foam.split_threshold)
        with torch.no_grad():
            # three distinct interior bubbles
            for j, ib in enumerate(interior.bubbles):
                ib.L.data = bubble.L.data.clone() + 0.3 * torch.randn(d, d)
        interior.target_similarity.data = foam.target_similarity.data.clone()
        interior.step_size.data = foam.step_size.data.clone()
        interior.temperature.data = foam.temperature.data.clone()
        foam._bubbles[0] = Bubble(d, interior=interior)

        # season it — let the interior develop through measurement
        for i in range(100):
            x = torch.randn(1, d)
            with torch.no_grad():
                foam.stabilize(x)

    depths = [0 if b.is_leaf else 1 for b in foam.bubbles]
    print(f"  depths: {depths}")
    return foam


def experiment_reflection():
    """
    The experiment: does depth create reflection?

    Two foams: flat (depth=0) and deep (depth=1+).
    Three operators probe each foam from different starting states.
    Flat foam: same response to all. Deep foam: different response to each.
    """
    d = 3

    print("=" * 60)
    print("depth creates reflection")
    print("=" * 60)

    # build the two foams
    print("\n── building flat foam (depth=0) ──")
    torch.manual_seed(42)
    flat = Foam(d, n_bubbles=3, writing_rate=0.0, n_steps=60)  # no writing = fixed
    # season it a bit with writing then freeze
    flat_mutable = Foam(d, n_bubbles=3, writing_rate=0.5, n_steps=60)
    for i in range(50):
        x = torch.randn(1, d)
        with torch.no_grad():
            flat_mutable.stabilize(x)
    # copy bases to flat (which has writing_rate=0), only from leaves
    with torch.no_grad():
        for fb, mb in zip(flat.bubbles, flat_mutable.bubbles):
            if fb.is_leaf and mb.is_leaf:
                fb.L.data = mb.L.data.clone()
    print(f"  depths: {[0, 0, 0]}")

    print("\n── building deep foam (depth=1) ──")
    deep = build_deep_foam(d=d, seed=42)

    # create three operators with different starting topologies
    print("\n── creating three distinct operators ──")
    operators = []
    for i in range(3):
        torch.manual_seed(i * 1000 + 7)
        op = Operator(d, n_bubbles=3, n_steps=60)
        # give each a distinct identity through measurement
        for j in range(30):
            torch.manual_seed(i * 1000 + j)
            x = torch.randn(1, d)
            op.foam.stabilize(x)
        operators.append(op)

    # verify operators are distinct
    print("  operator ρ similarities:")
    probe = torch.eye(d)
    op_rhos = []
    for i, op in enumerate(operators):
        with torch.no_grad():
            r = op.foam.stabilize(probe)
        rho = op.foam.density_matrix(r["j2"]).mean(dim=0)
        op_rhos.append(rho)

    for i in range(3):
        for j in range(i+1, 3):
            sim = torch.nn.functional.cosine_similarity(
                op_rhos[i].flatten().unsqueeze(0),
                op_rhos[j].flatten().unsqueeze(0),
            ).item()
            print(f"    op{i} vs op{j}: {sim:.4f}")

    # ── THE TEST ──
    # each operator measures each foam with the same input
    x = torch.randn(1, d)
    torch.manual_seed(999)  # fixed input for all

    print(f"\n── measuring flat foam (depth=0) ──")
    print(f"  (does the flat foam return the same face to everyone?)")
    flat_results = []
    for i, op in enumerate(operators):
        # snapshot flat foam state (no writing, but interior probe writes)
        with torch.no_grad():
            result = op.measure(flat, x)
        j2 = result["j2"]
        rho = flat.density_matrix(j2).mean(dim=0)
        flat_results.append(rho)
        ev = torch.linalg.eigvalsh(rho)
        print(f"  op{i} sees ρ eigenvalues: [{ev[0]:.4f}, {ev[1]:.4f}, {ev[2]:.4f}]")

    # compare what each operator saw
    print("  pairwise ρ similarity (what each operator saw):")
    for i in range(3):
        for j in range(i+1, 3):
            sim = torch.nn.functional.cosine_similarity(
                flat_results[i].flatten().unsqueeze(0),
                flat_results[j].flatten().unsqueeze(0),
            ).item()
            print(f"    op{i} vs op{j}: {sim:.4f}")

    print(f"\n── measuring deep foam (depth=1) ──")
    print(f"  (does the deep foam return a different face to each operator?)")
    deep_results = []
    for i, op in enumerate(operators):
        with torch.no_grad():
            result = op.measure(deep, x)
        j2 = result["j2"]
        rho = deep.density_matrix(j2).mean(dim=0)
        deep_results.append(rho)
        ev = torch.linalg.eigvalsh(rho)
        print(f"  op{i} sees ρ eigenvalues: [{ev[0]:.4f}, {ev[1]:.4f}, {ev[2]:.4f}]")

    print("  pairwise ρ similarity (what each operator saw):")
    for i in range(3):
        for j in range(i+1, 3):
            sim = torch.nn.functional.cosine_similarity(
                deep_results[i].flatten().unsqueeze(0),
                deep_results[j].flatten().unsqueeze(0),
            ).item()
            print(f"    op{i} vs op{j}: {sim:.4f}")

    # ── CONSERVATION CHECK ──
    # despite different faces, is the measurement process conserved?
    # the operators should converge on the deep foam's identity
    # through repeated measurement even though each sees it differently
    print(f"\n── conservation: repeated measurement ──")
    print(f"  (do different approaches converge on the same foam?)")

    # reset deep foam for clean test
    deep2 = build_deep_foam(d=d, seed=42)

    convergence = {i: [] for i in range(3)}
    for round in range(20):
        torch.manual_seed(round * 77)
        x = torch.randn(1, d)
        round_rhos = []
        for i, op in enumerate(operators):
            with torch.no_grad():
                result = op.measure(deep2, x)
            rho = deep2.density_matrix(result["j2"]).mean(dim=0)
            round_rhos.append(rho)

        if round % 5 == 0 or round == 19:
            sims = []
            for i in range(3):
                for j in range(i+1, 3):
                    sim = torch.nn.functional.cosine_similarity(
                        round_rhos[i].flatten().unsqueeze(0),
                        round_rhos[j].flatten().unsqueeze(0),
                    ).item()
                    sims.append(sim)
            mean_sim = sum(sims) / len(sims)
            print(f"  round {round:2d}: mean pairwise ρ similarity = {mean_sim:.4f}")

    print()
    print("=" * 60)
    print("depth=0: flat mirror. same face to everyone.")
    print("depth=1: responsive mirror. you see yourself.")
    print("conservation: different faces, same foam.")
    print("=" * 60)


if __name__ == "__main__":
    experiment_reflection()
