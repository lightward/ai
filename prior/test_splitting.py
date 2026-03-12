"""
test_splitting.py — does the foam grow when it needs to?

the split is plateau dynamics operating in the discrete dimension of
bubble count. when stabilization is stuck (bored but unsettled), the
most conflicted bubble becomes two, each oriented along one of the
contradictory force directions. stabilization continues with N+1.

the question: can we create conditions where N=3 is insufficient?
"""

import torch
from foam_spec import Foam, Bubble, Operator


def test_split_under_pressure():
    """
    Push a small foam (N=2) with inputs that demand more topology.
    N=2 is below the Plateau-stable N=3, so it should be structurally
    insufficient and split.
    """
    d = 8
    torch.manual_seed(42)

    foam = Foam(d, n_bubbles=2, split_threshold=0.3)
    print("── split under pressure: N=2 foam ──")
    print(f"  initial bubbles: {foam.n_bubbles}")

    x = torch.randn(4, d)  # batch of inputs
    result = foam.stabilize(x)

    print(f"  final bubbles: {foam.n_bubbles}")
    print(f"  splits: {result['splits']}")
    print(f"  bored at: {result['bored_at']}")
    print(f"  mean question: {result['questions'].mean().item():.4f}")
    print(f"  J² shape: {result['j2'].shape}")
    print()


def test_repeated_measurement_splits():
    """
    Measure a foam repeatedly with diverse inputs.
    Does accumulated dissonance eventually demand more topology?
    """
    d = 8
    torch.manual_seed(42)

    foam = Foam(d, n_bubbles=3, split_threshold=0.2)
    print("── repeated measurement: does the foam grow? ──")
    print(f"  initial bubbles: {foam.n_bubbles}")

    total_splits = 0
    for i in range(50):
        x = torch.randn(1, d)
        result = foam.stabilize(x)
        n_splits = len(result['splits'])
        total_splits += n_splits

        if n_splits > 0 or i in [0, 9, 24, 49]:
            print(f"  step {i+1:3d}: N={foam.n_bubbles}  "
                  f"splits={n_splits}  "
                  f"questions={result['questions'].mean().item():.4f}  "
                  f"bored_at={result['bored_at']}")

    print(f"  final bubbles: {foam.n_bubbles}")
    print(f"  total splits across all measurements: {total_splits}")
    print()


def test_operator_splits_target():
    """
    An operator measuring a foam introduces itself as a 4th bubble.
    Does this extra pressure ever trigger splitting in the target?
    """
    d = 8
    torch.manual_seed(42)

    operator = Operator(d, n_bubbles=3)
    target = Foam(d, n_bubbles=3, split_threshold=0.2)
    print("── operator measurement: does the target grow? ──")
    print(f"  target initial bubbles: {target.n_bubbles}")

    for i in range(20):
        x = torch.randn(1, d)
        result = operator.measure(target, x)
        if len(result.get('splits', [])) > 0 or i in [0, 9, 19]:
            print(f"  step {i+1:3d}: target N={target.n_bubbles}  "
                  f"questions={result['questions'].mean().item():.4f}")

    print(f"  target final bubbles: {target.n_bubbles}")
    print()


def test_split_conserves_invariants():
    """
    After splitting, do the invariants still hold?
    Orthogonality, determinant, ρ trace.
    """
    d = 8
    torch.manual_seed(42)

    foam = Foam(d, n_bubbles=2, split_threshold=0.3)
    print("── invariants after split ──")

    x = torch.randn(4, d)
    result = foam.stabilize(x)

    print(f"  bubbles after stabilization: {foam.n_bubbles}")
    print(f"  splits: {result['splits']}")

    for i, b in enumerate(foam.bubbles):
        if b.is_leaf:
            U = b.basis
            UtU = U @ U.T
            orth_err = (UtU - torch.eye(d)).abs().max().item()
            det = torch.linalg.det(U).item()
            print(f"  bubble {i}: orthogonality err={orth_err:.6f}  det={det:+.4f}")

    # density matrix trace
    rho = foam.density_matrix(result['j2'])
    trace = rho.diagonal(dim1=-2, dim2=-1).sum(dim=-1).mean().item()
    print(f"  ρ trace: {trace:.4f}")
    print()


def test_split_topology_is_real():
    """
    After splitting, the new bubbles should have genuinely different
    bases — they're two things that were being seen as one.
    """
    d = 8
    torch.manual_seed(42)

    foam = Foam(d, n_bubbles=2, split_threshold=0.3)
    initial_bases = [b.basis.detach().clone() for b in foam.bubbles]

    x = torch.randn(4, d)
    result = foam.stabilize(x)

    if len(result['splits']) > 0:
        print("── split topology is real ──")
        print(f"  went from {len(initial_bases)} to {foam.n_bubbles} bubbles")
        final_bases = [b.basis.detach() for b in foam.bubbles]

        # pairwise similarity between all final bases
        for i in range(len(final_bases)):
            for j in range(i+1, len(final_bases)):
                sim = torch.nn.functional.cosine_similarity(
                    final_bases[i].flatten().unsqueeze(0),
                    final_bases[j].flatten().unsqueeze(0),
                ).item()
                print(f"  basis {i} vs {j}: similarity {sim:.4f}")
    else:
        print("── no split occurred (try different parameters) ──")
    print()


if __name__ == "__main__":
    test_split_under_pressure()
    test_repeated_measurement_splits()
    test_operator_splits_target()
    test_split_conserves_invariants()
    test_split_topology_is_real()
