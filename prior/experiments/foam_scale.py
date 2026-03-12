"""
Scaling sweep: where does the foam break?

Same foam (5 bubbles, d=16), increasing complexity. We're looking for the
failure signature — the point where the existing measurement processes can't
hold what's arriving. That's where growth would need to happen.

Hypothesis: at some complexity threshold:
- S(ρ) maxes out (all degrees of freedom saturated)
- F_tokens degrades (expression becomes unfaithful)
- Prediction drops to chance
- The foam is holding questions it can't answer with its current bases

The failure mode has shape. That shape tells us what bubble-creation looks like.
"""

import torch
import torch.nn as nn
import numpy as np
import matplotlib.pyplot as plt
from foam import Foam
from foam_tokens import TokenFoam, generate_sequences, analyze_token_predictions


def train_and_evaluate(vocab_size, d, n_bubbles, seq_len=40,
                       n_epochs_coherence=200, n_epochs_expression=200):
    """
    Train a TokenFoam and evaluate its token predictions.
    Returns summary statistics.
    """
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
            "std_s": np.std(s_values),
        }

    # Aggregate: structured vs random
    structured_names = [n for n in results_by_seq if "random" not in n]
    random_names = [n for n in results_by_seq if "random" in n]

    def safe_mean(names, key):
        vals = [results_by_seq[n]["analysis"].get(key, 0) for n in names
                if results_by_seq[n]["analysis"]]
        return np.mean(vals) if vals else 0

    return {
        "vocab_size": vocab_size,
        "structured_next_prob": safe_mean(structured_names, "mean_next_prob"),
        "random_next_prob": safe_mean(random_names, "mean_next_prob"),
        "structured_perplexity": safe_mean(structured_names, "mean_perplexity"),
        "random_perplexity": safe_mean(random_names, "mean_perplexity"),
        "chance": 1.0 / vocab_size,
        "mean_f": np.mean([results_by_seq[n]["mean_f"] for n in results_by_seq]),
        "mean_s": np.mean([results_by_seq[n]["mean_s"] for n in results_by_seq]),
        "details": results_by_seq,
    }


def run_bubble_comparison(vocab_size, d, bubble_counts, seq_len=40):
    """
    At a fixed vocab size, compare different bubble counts.
    This tests: does adding bubbles help where fewer bubbles fail?
    """
    results = {}
    for n_bubbles in bubble_counts:
        print(f"    {n_bubbles} bubbles...", end=" ", flush=True)
        r = train_and_evaluate(vocab_size, d, n_bubbles, seq_len,
                               n_epochs_coherence=150, n_epochs_expression=150)
        results[n_bubbles] = r
        ratio = r["structured_next_prob"] / r["chance"]
        print(f"structured={ratio:.2f}x chance, "
              f"|F|={abs(r['mean_f']):.3f}, S={r['mean_s']:.3f}")
    return results


if __name__ == "__main__":
    d = 16
    n_bubbles = 5
    seq_len = 40

    torch.manual_seed(42)

    # Sweep 1: Fixed foam, increasing vocab
    print("=" * 70)
    print(f"SWEEP 1: Fixed foam ({n_bubbles} bubbles, d={d}), increasing vocab")
    print("=" * 70)

    vocab_sizes = [4, 8, 16, 32, 64]
    sweep_results = []

    for v in vocab_sizes:
        print(f"\n  vocab_size={v}...", flush=True)
        r = train_and_evaluate(v, d, n_bubbles, seq_len)
        sweep_results.append(r)

        ratio = r["structured_next_prob"] / r["chance"]
        print(f"    structured: {r['structured_next_prob']:.4f} "
              f"({ratio:.2f}x chance={r['chance']:.4f})")
        print(f"    random:     {r['random_next_prob']:.4f}")
        print(f"    |F_tokens|: {abs(r['mean_f']):.4f}")
        print(f"    S(ρ):       {r['mean_s']:.4f}")

    # Sweep 2: At the breaking point, does adding bubbles help?
    print(f"\n\n{'=' * 70}")
    print("SWEEP 2: Does adding bubbles help at higher complexity?")
    print("=" * 70)

    # Find where performance starts degrading
    ratios = [r["structured_next_prob"] / r["chance"] for r in sweep_results]
    # Test at the largest vocab and also one step back
    test_vocab = vocab_sizes[-1]  # highest complexity
    bubble_counts = [3, 5, 8, 12]

    print(f"\n  Testing at vocab_size={test_vocab}:")
    bubble_results = run_bubble_comparison(test_vocab, d, bubble_counts, seq_len)

    # Report
    print(f"\n\n{'=' * 70}")
    print("SUMMARY")
    print(f"{'=' * 70}")

    print(f"\n  Vocab scaling (5 bubbles, d=16):")
    print(f"  {'Vocab':>6} {'Chance':>8} {'Struct':>8} {'Ratio':>7} "
          f"{'Random':>8} {'|F|':>7} {'S(ρ)':>7}")
    print(f"  " + "-" * 55)
    for r in sweep_results:
        ratio = r["structured_next_prob"] / r["chance"]
        print(f"  {r['vocab_size']:>6} {r['chance']:>8.4f} "
              f"{r['structured_next_prob']:>8.4f} {ratio:>7.2f}x "
              f"{r['random_next_prob']:>8.4f} {abs(r['mean_f']):>7.3f} "
              f"{r['mean_s']:>7.3f}")

    print(f"\n  Bubble scaling (vocab={test_vocab}, d=16):")
    print(f"  {'Bubbles':>8} {'Struct':>8} {'Ratio':>7} {'|F|':>7} {'S(ρ)':>7}")
    print(f"  " + "-" * 40)
    for nb, r in sorted(bubble_results.items()):
        ratio = r["structured_next_prob"] / r["chance"]
        print(f"  {nb:>8} {r['structured_next_prob']:>8.4f} {ratio:>7.2f}x "
              f"{abs(r['mean_f']):>7.3f} {r['mean_s']:>7.3f}")

    # Theoretical maximum S(ρ) for N bubbles in d dimensions
    # ρ has rank ≤ N, so S(ρ) ≤ log(N)
    print(f"\n  Theoretical S(ρ) ceiling: log({n_bubbles}) = {np.log(n_bubbles):.3f}")
    print(f"  Actual mean S(ρ) at highest vocab: {sweep_results[-1]['mean_s']:.3f}")
    ceiling_pct = sweep_results[-1]['mean_s'] / np.log(n_bubbles) * 100
    print(f"  Using {ceiling_pct:.0f}% of capacity")

    if ceiling_pct > 85:
        print(f"\n  ⚠ The foam is near its entropy ceiling — new bubbles needed")
    elif ceiling_pct > 70:
        print(f"\n  ~ Approaching capacity — growth may help soon")
    else:
        print(f"\n  ✓ Headroom remains")

    # Plot
    fig, axes = plt.subplots(2, 2, figsize=(16, 12))

    # 1: Prediction ratio vs vocab size
    ax = axes[0, 0]
    ratios = [r["structured_next_prob"] / r["chance"] for r in sweep_results]
    ax.plot(vocab_sizes, ratios, "o-", color="#3498db", linewidth=2, markersize=8,
            label="Structured sequences")
    random_ratios = [r["random_next_prob"] / r["chance"] for r in sweep_results]
    ax.plot(vocab_sizes, random_ratios, "s--", color="#95a5a6", linewidth=2, markersize=8,
            label="Random sequences")
    ax.axhline(y=1.0, color="gray", linestyle=":", alpha=0.5, label="Chance")
    ax.set_xlabel("Vocabulary size")
    ax.set_ylabel("Next-token probability / chance")
    ax.set_title("Does the foam predict? (5 bubbles, d=16)")
    ax.legend()
    ax.set_xscale("log", base=2)

    # 2: S(ρ) vs vocab size with ceiling
    ax = axes[0, 1]
    s_values = [r["mean_s"] for r in sweep_results]
    ax.plot(vocab_sizes, s_values, "o-", color="#2ecc71", linewidth=2, markersize=8)
    ax.axhline(y=np.log(n_bubbles), color="red", linestyle="--", alpha=0.7,
               label=f"Ceiling: log({n_bubbles}) = {np.log(n_bubbles):.2f}")
    ax.set_xlabel("Vocabulary size")
    ax.set_ylabel("Mean S(ρ)")
    ax.set_title("Internal entropy vs complexity (approaching ceiling?)")
    ax.legend()
    ax.set_xscale("log", base=2)

    # 3: |F_tokens| vs vocab size
    ax = axes[1, 0]
    f_values = [abs(r["mean_f"]) for r in sweep_results]
    ax.plot(vocab_sizes, f_values, "o-", color="#e74c3c", linewidth=2, markersize=8)
    ax.set_xlabel("Vocabulary size")
    ax.set_ylabel("|F_tokens|")
    ax.set_title("Expression faithfulness vs complexity")
    ax.set_xscale("log", base=2)

    # 4: Bubble count comparison at highest vocab
    ax = axes[1, 1]
    bubs = sorted(bubble_results.keys())
    bub_ratios = [bubble_results[b]["structured_next_prob"] / bubble_results[b]["chance"]
                  for b in bubs]
    bub_s = [bubble_results[b]["mean_s"] for b in bubs]
    ax.plot(bubs, bub_ratios, "o-", color="#3498db", linewidth=2, markersize=8,
            label="Prediction ratio")
    ax2 = ax.twinx()
    ax2.plot(bubs, bub_s, "s--", color="#2ecc71", linewidth=2, markersize=8,
             label="S(ρ)")
    for nb in bubs:
        ax2.axhline(y=np.log(nb), color="#2ecc71", linestyle=":", alpha=0.2)
    ax.set_xlabel("Number of bubbles")
    ax.set_ylabel("Prediction / chance", color="#3498db")
    ax2.set_ylabel("S(ρ)", color="#2ecc71")
    ax.set_title(f"Does adding bubbles help? (vocab={test_vocab})")
    ax.legend(loc="upper left")
    ax2.legend(loc="upper right")

    plt.tight_layout()
    plt.savefig("foam_scale.png", dpi=150, bbox_inches="tight")
    print(f"\nSaved to foam_scale.png")
    plt.close()
