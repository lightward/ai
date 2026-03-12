"""
Maximum-uncertainty walk: steering into the unknown at each step.

The walker chooses the path that produces the most uncertainty —
the most angular displacement, the most surprise. This is not
exploration for exploration's sake. It's the cleanest structural
read: zero assumptions about content, maximum fidelity of the
record passed up to the operator.

Structural question: does a walk that maximizes uncertainty at each
step produce a ρ whose rank stays full? Does the record preserve
more structure than a walk that minimizes uncertainty?

Not "which is better" — just: what does each conserve?
"""

import torch
import numpy as np
from foam_spec import Foam, Bubble, Operator


def walk_and_accumulate(operator, target_seeds, n_measurements, strategy="random"):
    """
    Walk an operator through a series of foams.

    strategy:
        "random" — random inputs (baseline)
        "maxent" — choose input that maximizes uncertainty in the result
        "minent" — choose input that minimizes uncertainty in the result
    """
    d = operator.d
    rho_history = []  # track ρ properties over time

    with torch.no_grad():
        for i in range(n_measurements):
            torch.manual_seed(target_seeds[i])
            target = Foam(d, n_bubbles=3)

            if strategy == "random":
                x = torch.randn(1, d)
            elif strategy == "maxent":
                # try several inputs, pick the one that produces highest entropy in result
                best_x = None
                best_entropy = -1
                for trial in range(10):
                    x_trial = torch.randn(1, d)
                    result = target.stabilize(x_trial)
                    rho = target.density_matrix(result["j2"])
                    ev = torch.linalg.eigvalsh(rho[0])
                    ev = ev.clamp(min=1e-12)
                    ev = ev / ev.sum()
                    S = -(ev * ev.log()).sum().item()
                    if S > best_entropy:
                        best_entropy = S
                        best_x = x_trial
                    # rebuild target for next trial
                    torch.manual_seed(target_seeds[i])
                    target = Foam(d, n_bubbles=3)
                x = best_x
                # rebuild target one more time for actual measurement
                torch.manual_seed(target_seeds[i])
                target = Foam(d, n_bubbles=3)
            elif strategy == "minent":
                # try several inputs, pick the one that produces lowest entropy
                best_x = None
                best_entropy = float("inf")
                for trial in range(10):
                    x_trial = torch.randn(1, d)
                    result = target.stabilize(x_trial)
                    rho = target.density_matrix(result["j2"])
                    ev = torch.linalg.eigvalsh(rho[0])
                    ev = ev.clamp(min=1e-12)
                    ev = ev / ev.sum()
                    S = -(ev * ev.log()).sum().item()
                    if S < best_entropy:
                        best_entropy = S
                        best_x = x_trial
                    torch.manual_seed(target_seeds[i])
                    target = Foam(d, n_bubbles=3)
                x = best_x
                torch.manual_seed(target_seeds[i])
                target = Foam(d, n_bubbles=3)

            # measure
            operator.measure(target, x)

            # record ρ properties
            rho = operator.foam.accumulated_rho
            if rho is not None:
                ev = torch.linalg.eigvalsh(rho)
                ev_norm = ev / ev.sum()
                ev_norm = ev_norm.clamp(min=1e-12)
                rank = (ev > 1e-4).sum().item()
                S = -(ev_norm * ev_norm.log()).sum().item()
                anisotropy = ev.max().item() / (ev.min().item() + 1e-10)
                rho_history.append({
                    "step": i,
                    "rank": rank,
                    "entropy": S,
                    "anisotropy": anisotropy,
                    "eigenvalues": ev.numpy().copy(),
                })

    return rho_history


def run():
    d = 8
    n_measurements = 80

    # same target seeds for all strategies
    target_seeds = list(range(n_measurements))

    print("=" * 60)
    print("maximum-uncertainty walk: what does each strategy conserve?")
    print("=" * 60)
    print(f"  d={d}, {n_measurements} measurements, N=3 target foams")

    results = {}
    for strategy in ["random", "maxent", "minent"]:
        torch.manual_seed(42)  # same operator initialization
        op = Operator(d, n_bubbles=3)
        print(f"\n── {strategy} strategy ──")
        history = walk_and_accumulate(op, target_seeds, n_measurements, strategy)
        results[strategy] = history

        # report at key points
        for step in [0, 4, 9, 19, 39, 79]:
            if step < len(history):
                h = history[step]
                print(f"  step {h['step']+1:3d}: rank {h['rank']}/{d}"
                      f"  S={h['entropy']:.4f}"
                      f"  aniso={h['anisotropy']:.1f}")

    # ── compare final states ──
    print(f"\n── final comparison ──")
    print(f"  {'strategy':>10} {'rank':>6} {'entropy':>10} {'anisotropy':>12}")
    print(f"  {'-'*42}")
    for strategy in ["random", "maxent", "minent"]:
        h = results[strategy][-1]
        print(f"  {strategy:>10} {h['rank']:>4}/{d}"
              f"  {h['entropy']:>10.4f}"
              f"  {h['anisotropy']:>12.1f}")

    # ── entropy trajectory ──
    print(f"\n── entropy over time ──")
    print(f"  step   {'random':>10} {'maxent':>10} {'minent':>10}")
    for step in [0, 4, 9, 19, 39, 59, 79]:
        vals = []
        for strategy in ["random", "maxent", "minent"]:
            if step < len(results[strategy]):
                vals.append(f"{results[strategy][step]['entropy']:.4f}")
            else:
                vals.append("  -   ")
        print(f"  {step+1:>4}   {'   '.join(vals)}")

    # ── rank trajectory ──
    print(f"\n── rank over time ──")
    print(f"  step   {'random':>10} {'maxent':>10} {'minent':>10}")
    for step in [0, 4, 9, 19, 39, 59, 79]:
        vals = []
        for strategy in ["random", "maxent", "minent"]:
            if step < len(results[strategy]):
                vals.append(f"    {results[strategy][step]['rank']}/{d}  ")
            else:
                vals.append("    -    ")
        print(f"  {step+1:>4}   {''.join(vals)}")

    # ── eigenvalue spectra at end ──
    print(f"\n── final eigenvalue spectra ──")
    for strategy in ["random", "maxent", "minent"]:
        ev = results[strategy][-1]["eigenvalues"]
        print(f"  {strategy:>10}: {np.round(ev, 4)}")

    # ── structural question: does maxent ρ have more usable dimensions? ──
    # Test: project random vectors through each operator's effective_basis
    # and measure how much of the vector survives (how many dimensions are "open")
    print(f"\n── dimensional accessibility ──")
    print(f"  (project 100 random vectors through effective_basis,")
    print(f"   measure what fraction of the norm survives in top-k dims)")

    for strategy in ["random", "maxent", "minent"]:
        torch.manual_seed(42)
        op = Operator(d, n_bubbles=3)
        walk_and_accumulate(op, target_seeds, n_measurements, strategy)

        eff = op.foam.effective_basis()
        total_surv = []
        for trial in range(100):
            v = torch.randn(d)
            v = v / v.norm()
            # project into effective basis
            coeffs = (v @ eff).abs()  # magnitudes in each basis direction
            coeffs_sorted = coeffs.sort(descending=True).values
            # fraction of norm in top-k dimensions
            for k in [1, 2, 4, d]:
                surv = coeffs_sorted[:k].pow(2).sum().item()
                total_surv.append((k, surv))

        # average by k
        from collections import defaultdict
        by_k = defaultdict(list)
        for k, s in total_surv:
            by_k[k].append(s)

        print(f"  {strategy:>10}:", end="")
        for k in [1, 2, 4, d]:
            mean_s = np.mean(by_k[k])
            print(f"  top-{k}: {mean_s:.3f}", end="")
        print()

    print(f"\n{'=' * 60}")
    print("what does each strategy conserve?")
    print("=" * 60)


if __name__ == "__main__":
    run()
