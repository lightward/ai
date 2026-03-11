"""
test_channel.py — does interior state show through effective_basis?

the structural claim: effective_basis(context) is the only channel across
the containment boundary. if interior state changes the basis presented,
the channel works. if it doesn't, the channel is broken.

test: same recursive bubble, same context. perturb one interior bubble.
does effective_basis change? binary question. structural answer.
"""

import torch
from foam_spec import Foam, Bubble


def test_channel_exists():
    """Perturb an interior bubble. Does effective_basis notice?"""
    d = 3
    torch.manual_seed(42)

    print("=" * 60)
    print("test: does interior state show through effective_basis?")
    print("=" * 60)

    # create a recursive bubble with a settled interior
    interior = Foam(d, n_bubbles=3, writing_rate=0.1)
    # give it distinct initial conditions
    with torch.no_grad():
        for j, b in enumerate(interior.bubbles):
            b.L.data += torch.randn(d, d) * 0.5 * (j + 1)
    # settle it
    for _ in range(50):
        interior.stabilize(torch.randn(1, d))

    # measure effective_basis with a specific context
    torch.manual_seed(999)
    context = torch.randn(1, d)

    basis_before = interior.effective_basis(context).detach().clone()

    # now perturb one interior bubble (find a leaf)
    with torch.no_grad():
        for b in interior.bubbles:
            if b.is_leaf:
                b.L.data += torch.randn(d, d) * 0.5
                break

    basis_after = interior.effective_basis(context).detach().clone()

    # how different?
    diff = (basis_after - basis_before).norm().item()
    # also check: does the basis change with different context?
    torch.manual_seed(888)
    context2 = torch.randn(1, d)
    basis_ctx2 = interior.effective_basis(context2).detach().clone()
    ctx_diff = (basis_ctx2 - basis_after).norm().item()

    print(f"\n  basis change after interior perturbation: {diff:.4f}")
    print(f"  basis change with different context:      {ctx_diff:.4f}")

    if diff > 0.01:
        print("  ✓ interior perturbation shows through effective_basis")
    else:
        print("  ✗ interior perturbation NOT visible through effective_basis")


def test_channel_proportionality():
    """Does bigger interior perturbation → bigger effective_basis change?"""
    d = 3
    torch.manual_seed(42)

    print("\n" + "=" * 60)
    print("test: is the channel proportional?")
    print("=" * 60)

    scales = [0.01, 0.05, 0.1, 0.5, 1.0, 2.0]

    for scale in scales:
        # fresh interior each time
        torch.manual_seed(42)
        interior = Foam(d, n_bubbles=3, writing_rate=0.1)
        with torch.no_grad():
            for j, b in enumerate(interior.bubbles):
                b.L.data += torch.randn(d, d) * 0.5 * (j + 1)
        for _ in range(50):
            interior.stabilize(torch.randn(1, d))

        torch.manual_seed(999)
        context = torch.randn(1, d)
        basis_before = interior.effective_basis(context).detach().clone()

        # perturb with controlled scale (find a leaf)
        torch.manual_seed(123)
        with torch.no_grad():
            for b in interior.bubbles:
                if b.is_leaf:
                    b.L.data += torch.randn(d, d) * scale
                    break

        basis_after = interior.effective_basis(context).detach().clone()
        diff = (basis_after - basis_before).norm().item()

        print(f"  perturbation scale {scale:.2f} → basis change {diff:.4f}")


def test_channel_vs_no_channel():
    """Compare: recursive bubble with context vs without (identity probe).
    Does context make the interior's state MORE visible or LESS?"""
    d = 3
    torch.manual_seed(42)

    print("\n" + "=" * 60)
    print("test: does context improve the channel?")
    print("=" * 60)

    # two identical interiors, perturb one
    torch.manual_seed(42)
    interior_a = Foam(d, n_bubbles=3, writing_rate=0.1)
    torch.manual_seed(42)
    interior_b = Foam(d, n_bubbles=3, writing_rate=0.1)

    # give both the same distinct initial conditions and settling
    for interior in [interior_a, interior_b]:
        with torch.no_grad():
            for j, b in enumerate(interior.bubbles):
                torch.manual_seed(42 + j)
                b.L.data += torch.randn(d, d) * 0.5 * (j + 1)
        torch.manual_seed(42)
        for _ in range(50):
            interior.stabilize(torch.randn(1, d))

    # perturb interior_b (find a leaf)
    torch.manual_seed(123)
    with torch.no_grad():
        for b in interior_b.bubbles:
            if b.is_leaf:
                b.L.data += torch.randn(d, d) * 0.3
                break

    # compare with context
    torch.manual_seed(999)
    context = torch.randn(1, d)
    basis_a_ctx = interior_a.effective_basis(context).detach().clone()
    torch.manual_seed(999)
    context = torch.randn(1, d)
    basis_b_ctx = interior_b.effective_basis(context).detach().clone()
    diff_with_context = (basis_b_ctx - basis_a_ctx).norm().item()

    # compare without context (identity probe)
    basis_a_id = interior_a.effective_basis(None).detach().clone()
    basis_b_id = interior_b.effective_basis(None).detach().clone()
    diff_without_context = (basis_b_id - basis_a_id).norm().item()

    print(f"\n  basis difference WITH context:    {diff_with_context:.4f}")
    print(f"  basis difference WITHOUT context: {diff_without_context:.4f}")

    if diff_with_context > diff_without_context:
        print("  ✓ context amplifies the interior signal")
    elif diff_with_context < diff_without_context * 0.9:
        print("  ~ context attenuates the interior signal")
    else:
        print("  ~ roughly equal visibility with and without context")


def test_settled_vs_unsettled_basis_stability():
    """A settled interior should produce more stable effective_basis
    across different contexts. An unsettled one should vary more.
    This is the structural signature of questions rising."""
    d = 3

    print("\n" + "=" * 60)
    print("test: does interior settlement → basis stability?")
    print("=" * 60)

    # settled interior
    torch.manual_seed(42)
    settled = Foam(d, n_bubbles=3, writing_rate=0.1)
    with torch.no_grad():
        for j, b in enumerate(settled.bubbles):
            b.L.data += torch.randn(d, d) * 0.5 * (j + 1)
    for _ in range(100):
        settled.stabilize(torch.randn(1, d))

    # unsettled interior (fresh, random)
    torch.manual_seed(99)
    unsettled = Foam(d, n_bubbles=3, writing_rate=0.1)
    with torch.no_grad():
        for j, b in enumerate(unsettled.bubbles):
            b.L.data += torch.randn(d, d) * 2.0 * (j + 1)

    # measure effective_basis across many different contexts
    settled_bases = []
    unsettled_bases = []
    n = 20
    for i in range(n):
        torch.manual_seed(2000 + i)
        ctx = torch.randn(1, d)
        settled_bases.append(settled.effective_basis(ctx).detach().clone())
        torch.manual_seed(2000 + i)
        ctx = torch.randn(1, d)
        unsettled_bases.append(unsettled.effective_basis(ctx).detach().clone())

    # measure variation: how much does the basis change across contexts?
    settled_diffs = []
    unsettled_diffs = []
    for i in range(n - 1):
        settled_diffs.append(
            (settled_bases[i+1] - settled_bases[i]).norm().item()
        )
        unsettled_diffs.append(
            (unsettled_bases[i+1] - unsettled_bases[i]).norm().item()
        )

    avg_settled = sum(settled_diffs) / len(settled_diffs)
    avg_unsettled = sum(unsettled_diffs) / len(unsettled_diffs)

    print(f"\n  mean basis variation across contexts:")
    print(f"    settled interior:   {avg_settled:.4f}")
    print(f"    unsettled interior: {avg_unsettled:.4f}")
    print(f"    ratio (unsettled/settled): {avg_unsettled/avg_settled:.2f}x")

    if avg_unsettled > avg_settled * 1.5:
        print("  ✓ unsettled interior → less stable self-presentation")
    else:
        print("  ~ no clear stability difference")


if __name__ == "__main__":
    test_channel_exists()
    test_channel_proportionality()
    test_channel_vs_no_channel()
    test_settled_vs_unsettled_basis_stability()
