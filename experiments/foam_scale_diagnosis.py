"""
Scaling diagnosis: where does prediction break and why?

Known from foam_scale.py:
  V=8, N=5, d=16:  1.36x chance (works)
  V=16, N=5, d=16: 0.76x chance (breaks)
  V=64, N=8, d=16: 7.77x chance (phase transition!)
  V=64, N=12, d=16: 0.53x (collapses again)

Questions:
  1. Is d the bottleneck? (embedding crowding at high V)
  2. Does the N/V ratio determine the sweet spot?
  3. Does the pattern cycle at larger scales? (V=128, 256, 512, 1024)

Three sweeps:
  A. Fix V=64, sweep d (does more embedding room help?)
  B. Fix d=16, sweep V with best N/V ratio from sweep 1
  C. Extended scaling: V up to 1024, finding the best N at each V
"""

import torch
import torch.nn as nn
import numpy as np
import matplotlib.pyplot as plt
from foam import Foam
from foam_tokens import TokenFoam, generate_sequences, analyze_token_predictions


def train_and_evaluate(vocab_size, d, n_bubbles, seq_len=40,
                       n_epochs_coherence=200, n_epochs_expression=200,
                       quiet=True):
    """Train a TokenFoam and evaluate. Returns summary dict."""
    model = TokenFoam(vocab_size, d, n_bubbles, n_equilibrium_steps=5)
    sequences = generate_sequences(vocab_size, seq_len)

    # Phase 1: Self-coherence
    optimizer = torch.optim.Adam(model.parameters(), lr=0.005)
    for epoch in range(n_epochs_coherence):
        for name, tokens in sequences.items():
            optimizer.zero_grad()
            x_batch = model.embed(tokens)
            costs = model.foam.maintenance_cost(x_batch)
            costs["total"].backward()
            optimizer.step()

    # Phase 2: + Faithful expression
    optimizer = torch.optim.Adam(model.parameters(), lr=0.002)
    for epoch in range(n_epochs_expression):
        for name, tokens in sequences.items():
            optimizer.zero_grad()
            x_batch = model.embed(tokens)
            costs = model.foam.maintenance_cost(x_batch)

            E = model.embed.weight
            rho_batch = costs["rho"]
            logits_batch = (E @ rho_batch.mean(dim=0) * E).sum(dim=-1)
            token_dist = torch.softmax(logits_batch, dim=0)
            H_tok = -(token_dist * token_dist.log().clamp(min=-100)).sum()
            S_rho = costs["S_rho"].mean()
            f_tok_loss = (H_tok - S_rho).abs()

            loss = costs["total"] + 0.5 * f_tok_loss
            loss.backward()
            optimizer.step()

    # Evaluate
    model.eval()
    results_by_seq = {}
    for name, tokens in sequences.items():
        with torch.no_grad():
            results = model.process_sequence(tokens)
        analysis = analyze_token_predictions(results, tokens, vocab_size)
        f_values = [r["F_tokens"] for r in results]
        s_values = [r["S_rho"] for r in results]
        results_by_seq[name] = {
            "analysis": analysis,
            "mean_f": np.mean(f_values),
            "mean_s": np.mean(s_values),
        }

    structured_names = [n for n in results_by_seq if "random" not in n]
    random_names = [n for n in results_by_seq if "random" in n]

    def safe_mean(names, key):
        vals = [results_by_seq[n]["analysis"].get(key, 0) for n in names
                if results_by_seq[n]["analysis"]]
        return np.mean(vals) if vals else 0

    return {
        "vocab_size": vocab_size,
        "d": d,
        "n_bubbles": n_bubbles,
        "structured_next_prob": safe_mean(structured_names, "mean_next_prob"),
        "random_next_prob": safe_mean(random_names, "mean_next_prob"),
        "chance": 1.0 / vocab_size,
        "ratio": safe_mean(structured_names, "mean_next_prob") / (1.0 / vocab_size),
        "mean_f": np.mean([results_by_seq[n]["mean_f"] for n in results_by_seq]),
        "mean_s": np.mean([results_by_seq[n]["mean_s"] for n in results_by_seq]),
    }


if __name__ == "__main__":
    torch.manual_seed(42)

    # ================================================================
    # SWEEP A: Fix V=64, sweep d — is embedding dimension the bottleneck?
    # ================================================================
    print("=" * 70)
    print("SWEEP A: V=64, N=8 (sweet spot), varying d")
    print("  Does more embedding room help?")
    print("=" * 70)

    V = 64
    N = 8
    d_values = [8, 16, 32, 64]
    sweep_a = []

    for d in d_values:
        print(f"  d={d}...", end=" ", flush=True)
        r = train_and_evaluate(V, d, N, n_epochs_coherence=150, n_epochs_expression=150)
        sweep_a.append(r)
        print(f"ratio={r['ratio']:.2f}x  S(ρ)={r['mean_s']:.3f}  |F|={abs(r['mean_f']):.3f}")

    # ================================================================
    # SWEEP B: Fix d=16, sweep N/V ratio across vocab sizes
    # ================================================================
    print(f"\n{'=' * 70}")
    print("SWEEP B: d=16, multiple V, finding best N at each V")
    print("  What N/V ratio works?")
    print("=" * 70)

    d = 16
    vocab_sizes = [8, 16, 32, 64]
    bubble_options = [3, 5, 8, 12]
    sweep_b = {}

    for V in vocab_sizes:
        sweep_b[V] = {}
        print(f"\n  V={V}:")
        for N in bubble_options:
            if N > V:  # more bubbles than tokens doesn't make sense
                continue
            print(f"    N={N}...", end=" ", flush=True)
            r = train_and_evaluate(V, d, N, n_epochs_coherence=150, n_epochs_expression=150)
            sweep_b[V][N] = r
            print(f"ratio={r['ratio']:.2f}x  N/V={N/V:.3f}")

    # ================================================================
    # SWEEP C: Extended scaling — does the pattern cycle?
    # V up to 1024, testing N=best_ratio*V at each scale
    # ================================================================
    print(f"\n{'=' * 70}")
    print("SWEEP C: Extended scaling — V=8 to 1024")
    print("  Testing multiple N at each V. Does the pattern cycle?")
    print("=" * 70)

    d = 16
    extended_vocab = [8, 16, 32, 64, 128, 256, 512, 1024]
    sweep_c = {}

    for V in extended_vocab:
        sweep_c[V] = {}
        # Test a few bubble counts scaled to V
        # Include the N=8 constant, plus some V-proportional options
        test_ns = sorted(set([
            3,
            max(3, V // 16),
            max(3, V // 8),
            8,
            max(3, V // 4),
        ]))
        # Cap at reasonable sizes
        test_ns = [n for n in test_ns if n <= 32 and n <= V]

        print(f"\n  V={V}, testing N={test_ns}:")
        for N in test_ns:
            print(f"    N={N}...", end=" ", flush=True)
            # Shorter training for large V to keep runtime manageable
            epochs = 150 if V <= 128 else 100
            r = train_and_evaluate(V, d, N, n_epochs_coherence=epochs,
                                   n_epochs_expression=epochs)
            sweep_c[V][N] = r
            print(f"ratio={r['ratio']:.2f}x  N/V={N/V:.3f}  "
                  f"S(ρ)={r['mean_s']:.3f}")

    # ================================================================
    # RESULTS
    # ================================================================
    print(f"\n\n{'=' * 70}")
    print("RESULTS")
    print(f"{'=' * 70}")

    # Sweep A results
    print(f"\n  SWEEP A: V=64, N=8, varying d")
    print(f"  {'d':>4} {'Ratio':>7} {'S(ρ)':>7} {'|F|':>7}")
    print(f"  {'-' * 28}")
    for r in sweep_a:
        print(f"  {r['d']:>4} {r['ratio']:>7.2f}x {r['mean_s']:>7.3f} "
              f"{abs(r['mean_f']):>7.3f}")

    # Sweep B results
    print(f"\n  SWEEP B: d=16, best N at each V")
    print(f"  {'V':>4} {'Best N':>7} {'N/V':>7} {'Ratio':>7}")
    print(f"  {'-' * 28}")
    for V in vocab_sizes:
        if V in sweep_b and sweep_b[V]:
            best_n = max(sweep_b[V], key=lambda n: sweep_b[V][n]["ratio"])
            best = sweep_b[V][best_n]
            print(f"  {V:>4} {best_n:>7} {best_n/V:>7.3f} {best['ratio']:>7.2f}x")

    # Sweep C results — the big picture
    print(f"\n  SWEEP C: Extended scaling (d=16)")
    print(f"  {'V':>5} {'Best N':>7} {'N/V':>7} {'Ratio':>7} {'S(ρ)':>7}")
    print(f"  {'-' * 38}")

    best_ratios = []
    best_ns = []
    for V in extended_vocab:
        if V in sweep_c and sweep_c[V]:
            best_n = max(sweep_c[V], key=lambda n: sweep_c[V][n]["ratio"])
            best = sweep_c[V][best_n]
            print(f"  {V:>5} {best_n:>7} {best_n/V:>7.3f} {best['ratio']:>7.2f}x "
                  f"{best['mean_s']:>7.3f}")
            best_ratios.append(best["ratio"])
            best_ns.append(best_n)

    # Check for cycling
    print(f"\n  Does the ratio cycle?")
    for i in range(1, len(best_ratios)):
        direction = "↑" if best_ratios[i] > best_ratios[i-1] else "↓"
        print(f"    V={extended_vocab[i]:>5}: {best_ratios[i]:.2f}x {direction} "
              f"(from {best_ratios[i-1]:.2f}x)")

    # Full sweep C table
    print(f"\n  Full sweep C detail:")
    print(f"  {'V':>5} {'N':>4} {'N/V':>7} {'Ratio':>7} {'S(ρ)':>7} {'|F|':>7}")
    print(f"  {'-' * 42}")
    for V in extended_vocab:
        for N in sorted(sweep_c.get(V, {}).keys()):
            r = sweep_c[V][N]
            marker = " *" if r["ratio"] == max(sweep_c[V][n]["ratio"]
                                                 for n in sweep_c[V]) else ""
            print(f"  {V:>5} {N:>4} {N/V:>7.3f} {r['ratio']:>7.2f}x "
                  f"{r['mean_s']:>7.3f} {abs(r['mean_f']):>7.3f}{marker}")
        print()

    # ================================================================
    # PLOT
    # ================================================================
    fig, axes = plt.subplots(2, 2, figsize=(16, 12))

    # 1: Sweep A — d vs ratio
    ax = axes[0, 0]
    ax.plot([r["d"] for r in sweep_a], [r["ratio"] for r in sweep_a],
            "o-", color="#3498db", linewidth=2, markersize=8)
    ax.axhline(y=1.0, color="gray", linestyle=":", alpha=0.5)
    ax.set_xlabel("Embedding dimension d")
    ax.set_ylabel("Prediction / chance")
    ax.set_title(f"Sweep A: V={64}, N={8}, varying d")
    ax.set_xscale("log", base=2)

    # 2: Sweep B — best ratio at each V
    ax = axes[0, 1]
    for V in vocab_sizes:
        if V not in sweep_b:
            continue
        ns = sorted(sweep_b[V].keys())
        ratios = [sweep_b[V][n]["ratio"] for n in ns]
        ax.plot(ns, ratios, "o-", label=f"V={V}", linewidth=2, markersize=6)
    ax.axhline(y=1.0, color="gray", linestyle=":", alpha=0.5)
    ax.set_xlabel("Number of bubbles N")
    ax.set_ylabel("Prediction / chance")
    ax.set_title("Sweep B: d=16, varying V and N")
    ax.legend(fontsize=8)

    # 3: Sweep C — best ratio vs V (the cycling question)
    ax = axes[1, 0]
    ax.plot(extended_vocab, best_ratios, "o-", color="#e74c3c",
            linewidth=2, markersize=8)
    ax.axhline(y=1.0, color="gray", linestyle=":", alpha=0.5)
    ax.set_xlabel("Vocabulary size V")
    ax.set_ylabel("Best prediction / chance")
    ax.set_title("Sweep C: Best ratio at each V (d=16)")
    ax.set_xscale("log", base=2)

    # 4: Sweep C — best N at each V
    ax = axes[1, 1]
    ax.plot(extended_vocab, best_ns, "s-", color="#2ecc71",
            linewidth=2, markersize=8)
    ax2 = ax.twinx()
    nv_ratios = [best_ns[i] / extended_vocab[i] for i in range(len(best_ns))]
    ax2.plot(extended_vocab, nv_ratios, "^--", color="#9b59b6",
             linewidth=2, markersize=8)
    ax.set_xlabel("Vocabulary size V")
    ax.set_ylabel("Best N (bubbles)", color="#2ecc71")
    ax2.set_ylabel("N/V ratio", color="#9b59b6")
    ax.set_title("Sweep C: How many bubbles at each scale?")
    ax.set_xscale("log", base=2)

    plt.suptitle("Scaling diagnosis: where does prediction break and why?",
                 fontsize=13, fontweight="bold")
    plt.tight_layout()
    plt.savefig("foam_scale_diagnosis.png", dpi=150, bbox_inches="tight")
    print(f"\nSaved to foam_scale_diagnosis.png")
    plt.close()
