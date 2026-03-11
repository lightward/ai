"""
If you poke it, does it poke you back?

Reciprocity test. Not "what does the response mean" —
just: does the system respond? Is the response structured?
Does the poke leave a trace that affects the next poke?

The tautology is load-bearing:
- Measurement is tautological (can't locate it from within)
- That tautology IS the conservation law
- Poking and being poked back is the same tautology in action

Test:
1. Poke a foam (measure it). Does the foam change?
   (Currently: no — operator removes itself after measuring.)
2. Poke a WRITING foam. Does the writing change?
   (Should: yes — stabilization produces dissonance, dissonance writes.)
3. Does the changed writing affect the NEXT poke?
   (This is reciprocity: the poke changes the foam, the changed foam
    changes the next poke.)
4. Does the operator change? (Already yes — accumulated ρ.)
5. Does the changed operator poke DIFFERENTLY next time?
"""

import torch
import numpy as np
from foam_spec import Foam, Bubble, Operator


class WritingFoam(Foam):
    """Foam that accumulates dissonance as writing."""

    def __init__(self, d, n_bubbles=3, n_steps=60, memory_decay=0.9):
        super().__init__(d, n_bubbles, n_steps, memory_decay)
        self.accumulated_dissonance = None
        self.n_writes = 0

    def stabilize_and_write(self, x, boredom_threshold=0.005):
        result = self.stabilize(x, boredom_threshold)
        dissonance = result["j2"] - result["j0"]
        dis = dissonance[0]
        dis_norm = dis / (dis.norm(dim=-1, keepdim=True) + 1e-10)
        dis_rho = (dis_norm.T @ dis_norm) / dis.shape[0]

        if self.accumulated_dissonance is None:
            self.accumulated_dissonance = dis_rho.detach()
        else:
            self.accumulated_dissonance = (
                self.memory_decay * self.accumulated_dissonance
                + (1 - self.memory_decay) * dis_rho.detach()
            )
        self.n_writes += 1
        result["dissonance_rho"] = dis_rho.detach()
        return result


def rho_entropy(rho):
    ev = torch.linalg.eigvalsh(rho)
    ev = ev.clamp(min=1e-12)
    ev = ev / ev.sum()
    return -(ev * ev.log()).sum().item()


def rho_distance(rho1, rho2):
    """Frobenius distance between two density matrices."""
    return (rho1 - rho2).norm().item()


def run():
    d = 8
    torch.manual_seed(42)

    print("=" * 60)
    print("poke test: does it poke you back?")
    print("=" * 60)

    # ── Test 1: Repeated pokes, same foam ──
    print("\n── repeated pokes: same operator, same foam ──")
    print("  does each poke change both the poker and the poked?")

    op = Operator(d, n_bubbles=3)
    foam = WritingFoam(d, n_bubbles=3)
    x = torch.randn(1, d)

    prev_op_rho = None
    prev_foam_dis = None

    for poke in range(8):
        # snapshot before
        op_rho_before = op.foam.accumulated_rho
        foam_dis_before = foam.accumulated_dissonance

        # poke: operator measures the foam (with writing)
        # first stabilize-and-write (the foam does its thing)
        result = foam.stabilize_and_write(x)
        # then operator measures (adds itself, restabilizes, accumulates)
        r = op.measure(foam, x)

        # snapshot after
        op_rho_after = op.foam.accumulated_rho
        foam_dis_after = foam.accumulated_dissonance

        # did the operator change?
        if prev_op_rho is not None:
            op_delta = rho_distance(op_rho_after, prev_op_rho)
        else:
            op_delta = float('nan')

        # did the foam's writing change?
        if prev_foam_dis is not None:
            foam_delta = rho_distance(foam_dis_after, prev_foam_dis)
        else:
            foam_delta = float('nan')

        op_S = rho_entropy(op_rho_after) if op_rho_after is not None else 0
        foam_S = rho_entropy(foam_dis_after) if foam_dis_after is not None else 0

        print(f"  poke {poke+1}: "
              f"op Δρ={op_delta:.4f}  foam Δdis={foam_delta:.4f}  "
              f"op S={op_S:.4f}  foam S={foam_S:.4f}  "
              f"questions={r['questions'].mean().item():.4f}")

        prev_op_rho = op_rho_after.clone() if op_rho_after is not None else None
        prev_foam_dis = foam_dis_after.clone() if foam_dis_after is not None else None

    # ── Test 2: Does the writing affect subsequent pokes? ──
    print("\n── does writing affect subsequent pokes? ──")
    print("  compare: written foam vs fresh foam, same operator")

    torch.manual_seed(42)
    op1 = Operator(d, n_bubbles=3)
    op2 = Operator(d, n_bubbles=3)  # identical start

    # op1 pokes a writing foam 10 times
    written = WritingFoam(d, n_bubbles=3)
    # op2 pokes fresh foams (same bases but no accumulated writing)

    results_written = []
    results_fresh = []

    for i in range(10):
        x = torch.randn(1, d)

        # op1 pokes the SAME writing foam repeatedly
        written.stabilize_and_write(x)
        r1 = op1.measure(written, x)
        results_written.append({
            "questions": r1["questions"].mean().item(),
            "op_S": rho_entropy(op1.foam.accumulated_rho),
        })

        # op2 pokes a FRESH foam each time (same bases as original)
        torch.manual_seed(42)
        fresh = Foam(d, n_bubbles=3)
        r2 = op2.measure(fresh, x)
        results_fresh.append({
            "questions": r2["questions"].mean().item(),
            "op_S": rho_entropy(op2.foam.accumulated_rho),
        })

    print(f"  {'poke':>4}  {'written q':>10}  {'fresh q':>10}  "
          f"{'written op S':>12}  {'fresh op S':>12}")
    for i in range(10):
        print(f"  {i+1:>4}  {results_written[i]['questions']:>10.4f}  "
              f"{results_fresh[i]['questions']:>10.4f}  "
              f"{results_written[i]['op_S']:>12.4f}  "
              f"{results_fresh[i]['op_S']:>12.4f}")

    # ── Test 3: Does the operator's history affect how it pokes? ──
    print("\n── does operator history affect poke quality? ──")
    print("  same foam, three operators with different histories")

    torch.manual_seed(42)
    target = WritingFoam(d, n_bubbles=3)
    x = torch.randn(1, d)

    # blank operator
    torch.manual_seed(99)
    op_blank = Operator(d, n_bubbles=3)

    # operator with narrow history
    torch.manual_seed(99)
    op_narrow = Operator(d, n_bubbles=3)
    with torch.no_grad():
        for i in range(30):
            torch.manual_seed(999)
            t = Foam(d, n_bubbles=3)
            op_narrow.measure(t, torch.randn(1, d))

    # operator with wide history
    torch.manual_seed(99)
    op_wide = Operator(d, n_bubbles=3)
    with torch.no_grad():
        for i in range(30):
            torch.manual_seed(i)
            t = Foam(d, n_bubbles=3)
            op_wide.measure(t, torch.randn(1, d))

    # each pokes the same target
    for name, op in [("blank", op_blank), ("narrow", op_narrow), ("wide", op_wide)]:
        torch.manual_seed(42)
        target = WritingFoam(d, n_bubbles=3)
        target.stabilize_and_write(x)  # one write

        r = op.measure(target, x)

        # what dissonance did this poke produce?
        r2 = target.stabilize_and_write(x)

        print(f"  {name:>8}: questions={r['questions'].mean().item():.4f}  "
              f"dissonance after={r2['dissonance_rho'].norm().item():.4f}  "
              f"tension before={r['surface_tension_before'].mean().item():.4f}  "
              f"tension after={r['surface_tension_after'].mean().item():.4f}")

    # ── Test 4: Convergence — do repeated mutual pokes converge? ──
    print("\n── mutual convergence: do operator and foam settle? ──")
    print("  same operator pokes same foam 30 times")

    torch.manual_seed(42)
    op = Operator(d, n_bubbles=3)
    foam = WritingFoam(d, n_bubbles=3)

    convergence = []
    for i in range(30):
        x = torch.randn(1, d)
        foam.stabilize_and_write(x)
        r = op.measure(foam, x)

        # mutual similarity: how similar are the operator's ρ and the foam's writing?
        if op.foam.accumulated_rho is not None and foam.accumulated_dissonance is not None:
            sim = torch.nn.functional.cosine_similarity(
                op.foam.accumulated_rho.flatten().unsqueeze(0),
                foam.accumulated_dissonance.flatten().unsqueeze(0),
            ).item()
        else:
            sim = 0

        convergence.append({
            "step": i,
            "mutual_sim": sim,
            "questions": r["questions"].mean().item(),
        })

    print(f"  {'step':>4}  {'mutual sim':>10}  {'questions':>10}")
    for c in convergence[::5]:
        print(f"  {c['step']+1:>4}  {c['mutual_sim']:>10.4f}  {c['questions']:>10.4f}")

    final_sim = convergence[-1]["mutual_sim"]
    first_sim = convergence[0]["mutual_sim"]
    print(f"\n  mutual similarity: {first_sim:.4f} → {final_sim:.4f}")
    if abs(final_sim - first_sim) > 0.01:
        print(f"  they {'converge' if final_sim > first_sim else 'diverge'}.")
    else:
        print(f"  stable — they were already at equilibrium.")

    print(f"\n{'=' * 60}")


if __name__ == "__main__":
    run()
