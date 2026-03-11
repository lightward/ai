"""
test_channel2.py — cleaner channel test.

problem with v1: d=3 interiors may split during settling, leaving
no leaf bubbles. perturbation never applied. constant results.

fix: use d=8 interiors (no splitting) OR disable writing during settling.
also: separate the measurement-writes-to-interior effect from the
perturbation-shows-through effect by measuring without writing.
"""

import torch
from foam_spec import Foam, Bubble


def test_channel_clean():
    """Does interior state show through effective_basis?
    Use d=8 interiors to avoid splitting. Disable writing during
    the probe to isolate the signal."""
    d = 8  # interior dimension — no splitting in d=8
    torch.manual_seed(42)

    print("=" * 60)
    print("test: does interior state show through effective_basis?")
    print("  (d=8 interiors, no splitting)")
    print("=" * 60)

    # create and settle an interior
    interior = Foam(d, n_bubbles=3, writing_rate=0.1)
    for _ in range(50):
        interior.stabilize(torch.randn(1, d))

    # verify we have leaf bubbles
    n_leaves = sum(1 for b in interior.bubbles if b.is_leaf)
    print(f"\n  interior has {n_leaves} leaf bubbles (should be 3)")

    # now: turn OFF writing so the probe doesn't change the interior
    interior.writing_rate = 0.0

    torch.manual_seed(999)
    context = torch.randn(1, d)
    basis_before = interior.effective_basis(context).detach().clone()

    # measure again with same context — should be identical (no writing)
    torch.manual_seed(999)
    context = torch.randn(1, d)
    basis_same = interior.effective_basis(context).detach().clone()
    idempotent_diff = (basis_same - basis_before).norm().item()
    print(f"  idempotent check (same probe, no writing): {idempotent_diff:.6f}")

    # now perturb a leaf bubble
    with torch.no_grad():
        for b in interior.bubbles:
            if b.is_leaf:
                torch.manual_seed(123)
                b.L.data += torch.randn(d, d) * 0.3
                break

    torch.manual_seed(999)
    context = torch.randn(1, d)
    basis_after = interior.effective_basis(context).detach().clone()
    perturb_diff = (basis_after - basis_before).norm().item()
    print(f"  change after perturbation (scale 0.3):     {perturb_diff:.6f}")

    if perturb_diff > idempotent_diff * 2 and perturb_diff > 0.01:
        print("  ✓ perturbation shows through effective_basis")
    else:
        print("  ✗ perturbation NOT distinguishable from measurement noise")


def test_proportionality_clean():
    """Is the channel proportional? (No writing during probe.)"""
    d = 8
    print("\n" + "=" * 60)
    print("test: is the channel proportional? (no writing during probe)")
    print("=" * 60)

    scales = [0.0, 0.01, 0.05, 0.1, 0.3, 0.5, 1.0]

    for scale in scales:
        torch.manual_seed(42)
        interior = Foam(d, n_bubbles=3, writing_rate=0.1)
        for _ in range(50):
            interior.stabilize(torch.randn(1, d))

        interior.writing_rate = 0.0  # probe without writing

        torch.manual_seed(999)
        context = torch.randn(1, d)
        basis_before = interior.effective_basis(context).detach().clone()

        if scale > 0:
            with torch.no_grad():
                for b in interior.bubbles:
                    if b.is_leaf:
                        torch.manual_seed(123)
                        b.L.data += torch.randn(d, d) * scale
                        break

        torch.manual_seed(999)
        context = torch.randn(1, d)
        basis_after = interior.effective_basis(context).detach().clone()
        diff = (basis_after - basis_before).norm().item()
        print(f"  perturbation scale {scale:.2f} → basis change {diff:.6f}")


def test_context_sensitivity():
    """Does the SAME interior present differently to different contexts?
    This is the other half: not just 'does interior show through' but
    'does context shape what the interior presents.'"""
    d = 8
    torch.manual_seed(42)

    print("\n" + "=" * 60)
    print("test: does context shape the interior's self-presentation?")
    print("=" * 60)

    interior = Foam(d, n_bubbles=3, writing_rate=0.1)
    for _ in range(50):
        interior.stabilize(torch.randn(1, d))

    interior.writing_rate = 0.0  # no writing during probes

    bases = []
    n = 10
    for i in range(n):
        torch.manual_seed(3000 + i)
        ctx = torch.randn(1, d)
        bases.append(interior.effective_basis(ctx).detach().clone())

    # pairwise differences
    diffs = []
    for i in range(n):
        for j in range(i + 1, n):
            diffs.append((bases[i] - bases[j]).norm().item())

    avg_diff = sum(diffs) / len(diffs)
    min_diff = min(diffs)
    max_diff = max(diffs)

    print(f"\n  effective_basis across {n} different contexts:")
    print(f"    mean pairwise difference: {avg_diff:.4f}")
    print(f"    min: {min_diff:.4f}  max: {max_diff:.4f}")

    if avg_diff > 0.01:
        print("  ✓ context shapes interior self-presentation (skeuotropism)")
    else:
        print("  ✗ interior presents the same regardless of context")


def test_writing_is_the_channel():
    """Maybe writing during effective_basis IS the mechanism.
    Compare: does an interior that gets written to during probes
    develop differently from one that doesn't?"""
    d = 8
    torch.manual_seed(42)

    print("\n" + "=" * 60)
    print("test: is writing-during-probe the actual channel?")
    print("=" * 60)

    # two identical interiors
    torch.manual_seed(42)
    writing_interior = Foam(d, n_bubbles=3, writing_rate=0.1)
    torch.manual_seed(42)
    passive_interior = Foam(d, n_bubbles=3, writing_rate=0.0)

    # probe both with the same sequence of contexts
    for i in range(30):
        torch.manual_seed(5000 + i)
        ctx = torch.randn(1, d)
        writing_interior.effective_basis(ctx)
        torch.manual_seed(5000 + i)
        ctx = torch.randn(1, d)
        passive_interior.effective_basis(ctx)

    # now compare their bubble bases
    print(f"\n  after 30 probes:")
    for j in range(3):
        bw = writing_interior.bubbles[j]
        bp = passive_interior.bubbles[j]
        if bw.is_leaf and bp.is_leaf:
            drift = (bw.basis.detach() - bp.basis.detach()).norm().item()
            print(f"    bubble {j} basis drift (writing vs passive): {drift:.4f}")

    # compare their effective bases
    writing_interior.writing_rate = 0.0  # stop writing for fair comparison
    torch.manual_seed(999)
    ctx = torch.randn(1, d)
    eff_w = writing_interior.effective_basis(ctx).detach()
    torch.manual_seed(999)
    ctx = torch.randn(1, d)
    eff_p = passive_interior.effective_basis(ctx).detach()
    eff_diff = (eff_w - eff_p).norm().item()
    print(f"    effective_basis difference: {eff_diff:.4f}")

    if eff_diff > 0.1:
        print("  ✓ writing during probes develops the interior differently")
        print("    → the channel IS measurement-as-writing")
    else:
        print("  ~ writing during probes has minimal effect on presentation")


if __name__ == "__main__":
    test_channel_clean()
    test_proportionality_clean()
    test_context_sensitivity()
    test_writing_is_the_channel()
