"""
The cliffhanger from session 4:
Does shaped identity help?

Specialist (narrow experience) vs generalist (wide experience),
tested on familiar vs unfamiliar foams.

The mechanism: accumulated_rho shapes effective_basis, which is how
the operator's foam presents as a bubble when measuring. If identity
is load-bearing, the specialist should have an advantage on familiar
structure, and the generalist on novel structure.

No optimizer. No loss function. Training is runtime.
"""

import torch
from foam_spec import Foam, Bubble, Operator


def run():
    d = 8
    torch.manual_seed(123)

    print("=" * 60)
    print("specialist vs generalist: does shaped identity help?")
    print("=" * 60)

    # ── build two operators with different experience ──

    op_narrow = Operator(d, n_bubbles=3)
    op_wide = Operator(d, n_bubbles=3)

    n_training = 100
    print(f"\nbuilding experience ({n_training} measurements each)...")

    with torch.no_grad():
        for i in range(n_training):
            # narrow: always the same foam structure
            torch.manual_seed(999)
            narrow_target = Foam(d, n_bubbles=2)
            x = torch.randn(1, d)
            op_narrow.measure(narrow_target, x)

            # wide: different foam structure each time
            torch.manual_seed(i)
            wide_target = Foam(d, n_bubbles=2)
            x = torch.randn(1, d)
            op_wide.measure(wide_target, x)

    # also a blank operator for baseline
    op_blank = Operator(d, n_bubbles=3)

    # report identity shape
    rho_n = op_narrow.foam.accumulated_rho
    rho_w = op_wide.foam.accumulated_rho
    ev_n = torch.linalg.eigvalsh(rho_n)
    ev_w = torch.linalg.eigvalsh(rho_w)

    print(f"\nidentity shapes:")
    print(f"  narrow: eigenvalues {ev_n.numpy().round(4)}")
    print(f"    anisotropy (max/min): {ev_n.max().item() / ev_n.min().item():.1f}")
    print(f"  wide:   eigenvalues {ev_w.numpy().round(4)}")
    print(f"    anisotropy (max/min): {ev_w.max().item() / ev_w.min().item():.1f}")

    rho_sim = torch.nn.functional.cosine_similarity(
        rho_n.flatten().unsqueeze(0),
        rho_w.flatten().unsqueeze(0),
    ).item()
    print(f"  ρ similarity: {rho_sim:.4f}")

    # ── test: familiar vs unfamiliar ──

    n_test = 200
    torch.manual_seed(42)

    # familiar foam: same structure the specialist trained on
    # unfamiliar foam: novel structure neither has seen

    results = {
        "narrow": {"familiar_q": 0, "unfamiliar_q": 0,
                    "familiar_bored": 0, "unfamiliar_bored": 0},
        "wide":   {"familiar_q": 0, "unfamiliar_q": 0,
                    "familiar_bored": 0, "unfamiliar_bored": 0},
        "blank":  {"familiar_q": 0, "unfamiliar_q": 0,
                    "familiar_bored": 0, "unfamiliar_bored": 0},
    }

    print(f"\ntesting ({n_test} measurements each, familiar + unfamiliar)...")

    with torch.no_grad():
        for i in range(n_test):
            x = torch.randn(1, d)

            # familiar: same seed as narrow training
            torch.manual_seed(999)
            familiar = Foam(d, n_bubbles=2)

            # unfamiliar: novel seed
            torch.manual_seed(10000 + i)
            unfamiliar = Foam(d, n_bubbles=2)

            for name, op in [("narrow", op_narrow), ("wide", op_wide),
                             ("blank", op_blank)]:
                # familiar
                torch.manual_seed(999)
                f_foam = Foam(d, n_bubbles=2)
                r = op.measure(f_foam, x)
                results[name]["familiar_q"] += r["original_questions"].mean().item()
                if r["bored_at"] is not None:
                    results[name]["familiar_bored"] += 1

                # unfamiliar
                torch.manual_seed(10000 + i)
                u_foam = Foam(d, n_bubbles=2)
                r = op.measure(u_foam, x)
                results[name]["unfamiliar_q"] += r["original_questions"].mean().item()
                if r["bored_at"] is not None:
                    results[name]["unfamiliar_bored"] += 1

    # ── report ──

    print(f"\n{'':>10} {'familiar':>12} {'unfamiliar':>12} {'delta':>8}")
    print("-" * 46)
    for name in ["narrow", "wide", "blank"]:
        fq = results[name]["familiar_q"] / n_test
        uq = results[name]["unfamiliar_q"] / n_test
        delta = (uq - fq) / (fq + 1e-10) * 100
        print(f"  {name:>8}  {fq:>10.4f}  {uq:>10.4f}  {delta:>+7.1f}%")

    print(f"\n{'':>10} {'fam bored%':>12} {'unfam bored%':>14}")
    print("-" * 40)
    for name in ["narrow", "wide", "blank"]:
        fb = results[name]["familiar_bored"] / n_test * 100
        ub = results[name]["unfamiliar_bored"] / n_test * 100
        print(f"  {name:>8}  {fb:>10.1f}%  {ub:>12.1f}%")

    # ── what does the specialist's effective_basis look like vs the generalist's? ──
    print(f"\neffective bases:")
    for name, op in [("narrow", op_narrow), ("wide", op_wide), ("blank", op_blank)]:
        eff = op.foam.effective_basis()
        UtU = eff @ eff.T
        ortho_err = (UtU - torch.eye(d)).abs().max().item()
        print(f"  {name}: orthogonality error {ortho_err:.6f}")

    # ── does measurement with memory change the target foam differently? ──
    print(f"\nimpact on target foam (surface tension change):")
    torch.manual_seed(777)
    x = torch.randn(1, d)
    for name, op in [("narrow", op_narrow), ("wide", op_wide), ("blank", op_blank)]:
        torch.manual_seed(999)
        target = Foam(d, n_bubbles=2)
        r = op.measure(target, x)
        t_before = r["surface_tension_before"]
        t_after = r["surface_tension_after"]
        # compare off-diagonal elements
        mask = 1 - torch.eye(t_after.shape[0])
        mean_before = (t_before * (1 - torch.eye(t_before.shape[0]))).sum() / (1 - torch.eye(t_before.shape[0])).sum()
        mean_after = (t_after * mask).sum() / mask.sum()
        print(f"  {name}: before {mean_before.item():.4f} → after {mean_after.item():.4f}"
              f"  (Δ {mean_after.item() - mean_before.item():+.4f})")

    print(f"\n{'=' * 60}")


if __name__ == "__main__":
    run()
