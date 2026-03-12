"""
Fractal foam: same pattern at two scales.

Level 1: 3 bubbles per foam — measurement processes
Level 2: 3 foams in meta-foam — measurement PERSPECTIVES

Each level equilibrates via gauge-invariant Plateau forces.
The meta-level lets the ensemble lean toward whichever foam
has strong signal for THIS input, while maintaining stability
when none does.

The individual's peaks + the ensemble's reliability.
Not a dichotomy — terms intercomposing structurally.
"""

import torch
import torch.nn as nn
import numpy as np
import matplotlib.pyplot as plt
from foam_gauge import GaugeTokenFoam, GaugeFoam
from foam_spread import init_spread_foam, measure_basis_spread
from foam_tokens import generate_sequences, analyze_token_predictions


class MetaFoam(nn.Module):
    """
    A foam of foams.

    Level 1: Each inner foam has N bubbles doing gauge-invariant
    equilibration. Each produces a density matrix ρ_k.

    Level 2: The K density matrices interact through Plateau-like
    dynamics. When the ρ's agree, the meta-output concentrates
    (approaching individual-foam peaks). When they disagree,
    it stays mixed (providing ensemble stability).

    The meta-equilibration operates on the eigenvalue spectra
    of the ρ's — comparing their "shapes" rather than their
    raw entries, since each foam's ρ is in a different gauge.
    """

    def __init__(self, vocab_size, d, n_bubbles=3, n_foams=3,
                 seeds=None, diversity_weight=2.0):
        super().__init__()
        self.vocab_size = vocab_size
        self.d = d
        self.n_foams = n_foams
        self.n_bubbles = n_bubbles

        if seeds is None:
            seeds = list(range(n_foams))
        self.seeds = seeds

        # Shared embedding
        self.embed = nn.Embedding(vocab_size, d)

        # Inner foams
        self.foams = nn.ModuleList()
        for seed in seeds:
            torch.manual_seed(seed)
            foam = GaugeFoam(n_bubbles, d, diversity_weight=diversity_weight)
            init_spread_foam(foam, scale=1.5)
            self.foams.append(foam)

        # Meta-level learnable parameters
        # How much the meta-equilibration concentrates vs mixes
        self.meta_temperature = nn.Parameter(torch.tensor(1.0))
        # Meta-equilibration steps
        self.meta_steps = 3

        # Per-foam memory
        self.memory_decay_base = nn.Parameter(torch.tensor(0.8))
        self.novelty_sensitivity = nn.Parameter(torch.tensor(1.0))

    def born_rule(self, rho, embeddings):
        return (embeddings @ rho * embeddings).sum(dim=-1)

    def meta_equilibrate(self, rhos):
        """
        Meta-level equilibration of density matrices.

        rhos: list of K [d, d] density matrices

        Instead of uniform mixing, compute agreement-weighted mixture.
        When foams agree (similar ρ's → similar Born distributions),
        weight the agreeing foams more heavily. When they disagree,
        weight uniformly.

        This lets peaks through (when one foam has strong signal
        that others corroborate) while maintaining the floor
        (when foams disagree).
        """
        K = len(rhos)
        E = self.embed.weight  # [V, d]

        # Compute Born distributions for each foam
        with torch.no_grad():
            distributions = []
            for rho in rhos:
                logits = self.born_rule(rho, E)
                probs = torch.softmax(logits, dim=0)
                distributions.append(probs)

        # Pairwise agreement: Jensen-Shannon-like similarity
        # High agreement → similar distributions → high weight
        dists = torch.stack(distributions)  # [K, V]

        # Concentration of each foam's distribution
        # (entropy-based: low entropy = concentrated = strong signal)
        entropies = -(dists * dists.log().clamp(min=-100)).sum(dim=-1)  # [K]
        max_entropy = np.log(self.vocab_size)
        concentration = 1 - entropies / max_entropy  # [K], 0=uniform, 1=peaked

        # Agreement between foams: pairwise cosine similarity of distributions
        dists_norm = dists / (dists.norm(dim=-1, keepdim=True) + 1e-10)
        agreement_matrix = dists_norm @ dists_norm.T  # [K, K]
        # Mean agreement of each foam with others
        mask = ~torch.eye(K, dtype=torch.bool)
        mean_agreement = agreement_matrix[mask].reshape(K, K-1).mean(dim=-1)  # [K]

        # Weight: concentration × agreement
        # A foam gets high weight if it's concentrated AND agrees with others
        raw_weights = concentration * mean_agreement
        # Temperature-controlled softmax
        temp = self.meta_temperature.abs().clamp(min=0.01)
        weights = torch.softmax(raw_weights / temp, dim=0)  # [K]

        # Weighted mixture
        rho_meta = torch.zeros_like(rhos[0])
        for k in range(K):
            rho_meta = rho_meta + weights[k] * rhos[k]

        return rho_meta, weights

    def process_sequence(self, tokens):
        seq_len = tokens.shape[0]
        device = tokens.device
        K = self.n_foams
        E = self.embed.weight

        memories = [
            torch.zeros(foam.n_bubbles, self.d, device=device)
            for foam in self.foams
        ]

        step_results = []

        for t in range(seq_len):
            x = self.embed(tokens[t:t + 1])

            foam_rhos = []

            for k, foam in enumerate(self.foams):
                memory = memories[k]
                memory_mean = memory.mean(dim=0, keepdim=True)
                mem_norm = memory_mean.norm() + 1e-10
                x_norm = x.norm() + 1e-10

                if mem_norm > 1e-8:
                    novelty = 1 - (x * memory_mean).sum() / (x_norm * mem_norm)
                else:
                    novelty = torch.tensor(1.0, device=device)

                sensitivity = self.novelty_sensitivity.abs()
                decay = torch.sigmoid(self.memory_decay_base - sensitivity * novelty)

                x_with_memory = x + decay * memory_mean
                result = foam.forward(x_with_memory)

                eq = result["equilibrium"][0]
                memories[k] = decay * memory + (1 - decay) * eq

                foam_rhos.append(result["rho"][0])

            # Meta-equilibration: agreement-weighted mixture
            rho_meta, weights = self.meta_equilibrate(foam_rhos)

            # Eigenvalues of meta-ρ
            eigenvalues = torch.linalg.eigvalsh(rho_meta)
            eigenvalues = eigenvalues.clamp(min=1e-12)
            eigenvalues = eigenvalues / eigenvalues.sum()

            # Born rule on meta-ρ
            logits = self.born_rule(rho_meta, E)
            token_probs = torch.softmax(logits, dim=0)

            S_rho = -(eigenvalues * eigenvalues.log().clamp(min=-100)).sum().item()
            H_tokens = -(token_probs * token_probs.log().clamp(min=-100)).sum().item()
            F_tokens = H_tokens - S_rho

            # Per-foam predictions for comparison
            per_foam_probs = []
            for k in range(K):
                logits_k = self.born_rule(foam_rhos[k], E)
                probs_k = torch.softmax(logits_k, dim=0)
                per_foam_probs.append(probs_k)

            step_results.append({
                "token": tokens[t].item(),
                "token_probs": token_probs.detach(),
                "rho": rho_meta.detach(),
                "S_rho": S_rho,
                "H_tokens": H_tokens,
                "F_tokens": F_tokens,
                "weights": weights.detach(),
                "per_foam_probs": [p.detach() for p in per_foam_probs],
            })

        return step_results


def train_and_evaluate(vocab_size, d, n_bubbles, n_foams, seeds,
                       diversity_weight=2.0, meta_seed=99,
                       n_epochs_coherence=100, n_epochs_expression=100):
    """Train a MetaFoam and evaluate."""
    torch.manual_seed(meta_seed)
    model = MetaFoam(vocab_size, d, n_bubbles, n_foams,
                     seeds=seeds, diversity_weight=diversity_weight)

    sequences = generate_sequences(vocab_size, 40)

    # Phase 1: Self-coherence
    optimizer = torch.optim.Adam(model.parameters(), lr=0.005)
    for epoch in range(n_epochs_coherence):
        for name, tokens in sequences.items():
            optimizer.zero_grad()
            x_batch = model.embed(tokens)
            total_loss = torch.tensor(0.0)
            for foam in model.foams:
                costs = foam.maintenance_cost(x_batch)
                total_loss = total_loss + costs["total"]
            total_loss.backward()
            optimizer.step()

    # Phase 2: + Faithful expression (with meta-temperature learning)
    optimizer = torch.optim.Adam(model.parameters(), lr=0.002)
    for epoch in range(n_epochs_expression):
        for name, tokens in sequences.items():
            optimizer.zero_grad()
            x_batch = model.embed(tokens)
            total_loss = torch.tensor(0.0)
            E = model.embed.weight

            for foam in model.foams:
                costs = foam.maintenance_cost(x_batch)
                rho_batch = costs["rho"]
                logits_batch = (E @ rho_batch.mean(dim=0) * E).sum(dim=-1)
                token_dist = torch.softmax(logits_batch, dim=0)
                H_tok = -(token_dist * token_dist.log().clamp(min=-100)).sum()
                S_rho = costs["S_rho"].mean()
                f_tok_loss = (H_tok - S_rho).abs()
                total_loss = total_loss + costs["total"] + 0.5 * f_tok_loss

            total_loss.backward()
            optimizer.step()

    # Evaluate
    model.eval()
    results_by_seq = {}
    for name, tokens in sequences.items():
        with torch.no_grad():
            results = model.process_sequence(tokens)
        analysis = analyze_token_predictions(results, tokens, vocab_size)
        results_by_seq[name] = {"analysis": analysis, "results": results}

    structured_names = [n for n in results_by_seq if "random" not in n]
    vals = [results_by_seq[n]["analysis"].get("mean_next_prob", 0)
            for n in structured_names if results_by_seq[n]["analysis"]]
    ratio = np.mean(vals) / (1.0 / vocab_size) if vals else 0

    # Collect weight statistics
    all_weights = []
    for name in results_by_seq:
        for r in results_by_seq[name]["results"]:
            all_weights.append(r["weights"].numpy())
    weight_stats = np.array(all_weights)

    return {
        "vocab_size": vocab_size,
        "n_foams": n_foams,
        "seeds": seeds,
        "ratio": ratio,
        "meta_temperature": model.meta_temperature.item(),
        "weight_mean": weight_stats.mean(axis=0),
        "weight_std": weight_stats.std(axis=0),
        "by_seq": results_by_seq,
    }


if __name__ == "__main__":
    V = 256
    N = 3
    d = 16

    print("=" * 70)
    print("FRACTAL FOAM: same pattern at two scales")
    print(f"  V={V}, {N} bubbles × 3 foams, d={d}")
    print("  Meta-equilibration: agreement-weighted density matrix mixing")
    print("=" * 70)

    # ================================================================
    # PART 1: Fractal vs uniform ensemble vs individual
    # ================================================================
    print(f"\n{'=' * 70}")
    print("PART 1: Fractal vs uniform ensemble vs individual")
    print("  Same seeds, different aggregation strategies")
    print("=" * 70)

    seed_sets = [
        [0, 1, 2],
        [3, 4, 5],
        [0, 4, 8],
        [1, 5, 9],
        [2, 6, 7],
    ]

    comparisons = []
    for seeds in seed_sets:
        print(f"\n  Seeds: {seeds}")

        # Fractal (meta-equilibrated)
        r_fractal = train_and_evaluate(V, d, N, n_foams=3, seeds=seeds)
        print(f"    Fractal:  {r_fractal['ratio']:.2f}x  "
              f"temp={r_fractal['meta_temperature']:.3f}  "
              f"weights={r_fractal['weight_mean']}")

        # Uniform ensemble (from foam_ensemble approach: just average ρ)
        # We can simulate this by setting meta_temperature very high
        # (→ uniform weights)
        torch.manual_seed(99)
        model_uniform = MetaFoam(V, d, N, 3, seeds=seeds)
        # Force uniform by setting temp very high
        model_uniform.meta_temperature.data = torch.tensor(100.0)
        # Train the same way but freeze meta_temperature
        sequences = generate_sequences(V, 40)

        optimizer = torch.optim.Adam(
            [p for n, p in model_uniform.named_parameters()
             if "meta_temperature" not in n],
            lr=0.005)
        for epoch in range(100):
            for name, tokens in sequences.items():
                optimizer.zero_grad()
                x_batch = model_uniform.embed(tokens)
                total_loss = torch.tensor(0.0)
                for foam in model_uniform.foams:
                    costs = foam.maintenance_cost(x_batch)
                    total_loss = total_loss + costs["total"]
                total_loss.backward()
                optimizer.step()

        optimizer = torch.optim.Adam(
            [p for n, p in model_uniform.named_parameters()
             if "meta_temperature" not in n],
            lr=0.002)
        for epoch in range(100):
            for name, tokens in sequences.items():
                optimizer.zero_grad()
                x_batch = model_uniform.embed(tokens)
                total_loss = torch.tensor(0.0)
                E = model_uniform.embed.weight
                for foam in model_uniform.foams:
                    costs = foam.maintenance_cost(x_batch)
                    rho_batch = costs["rho"]
                    logits_batch = (E @ rho_batch.mean(dim=0) * E).sum(dim=-1)
                    token_dist = torch.softmax(logits_batch, dim=0)
                    H_tok = -(token_dist * token_dist.log().clamp(min=-100)).sum()
                    S_rho = costs["S_rho"].mean()
                    f_tok_loss = (H_tok - S_rho).abs()
                    total_loss = total_loss + costs["total"] + 0.5 * f_tok_loss
                total_loss.backward()
                optimizer.step()

        model_uniform.eval()
        results_by_seq = {}
        for name, tokens in sequences.items():
            with torch.no_grad():
                results = model_uniform.process_sequence(tokens)
            analysis = analyze_token_predictions(results, tokens, V)
            results_by_seq[name] = analysis

        structured_names = [n for n in results_by_seq if "random" not in n]
        vals = [results_by_seq[n].get("mean_next_prob", 0)
                for n in structured_names if results_by_seq[n]]
        ratio_uniform = np.mean(vals) / (1.0 / V) if vals else 0

        print(f"    Uniform:  {ratio_uniform:.2f}x")

        comparisons.append({
            "seeds": seeds,
            "fractal": r_fractal["ratio"],
            "uniform": ratio_uniform,
            "weights": r_fractal["weight_mean"],
            "temp": r_fractal["meta_temperature"],
        })

    # ================================================================
    # PART 2: Consistency — same foam seeds, different embeddings
    # ================================================================
    print(f"\n{'=' * 70}")
    print("PART 2: Fractal consistency across embedding seeds")
    print("=" * 70)

    consistency = []
    for meta_seed in range(10):
        r = train_and_evaluate(V, d, N, 3, seeds=[0, 1, 2],
                               meta_seed=meta_seed)
        consistency.append(r["ratio"])
        print(f"  meta_seed={meta_seed}: ratio={r['ratio']:.2f}x  "
              f"temp={r['meta_temperature']:.3f}")

    print(f"\n  Mean: {np.mean(consistency):.2f}x  "
          f"Std: {np.std(consistency):.2f}")

    # ================================================================
    # PART 3: Scaling
    # ================================================================
    print(f"\n{'=' * 70}")
    print("PART 3: Fractal scaling across vocabulary sizes")
    print("=" * 70)

    vocab_sizes = [8, 16, 32, 64, 128, 256, 512]
    scale_results = []

    for V_test in vocab_sizes:
        epochs = 100 if V_test <= 128 else 80
        r = train_and_evaluate(V_test, d, N, 3, seeds=[0, 1, 2],
                               n_epochs_coherence=epochs,
                               n_epochs_expression=epochs)
        scale_results.append({"V": V_test, "ratio": r["ratio"],
                              "temp": r["meta_temperature"]})
        print(f"  V={V_test:>4}: ratio={r['ratio']:.2f}x  "
              f"temp={r['meta_temperature']:.3f}")

    # ================================================================
    # PLOT
    # ================================================================
    fig, axes = plt.subplots(2, 2, figsize=(16, 12))

    # 1: Fractal vs uniform
    ax = axes[0, 0]
    labels = [str(c["seeds"]) for c in comparisons]
    x = np.arange(len(labels))
    w = 0.35
    ax.bar(x - w/2, [c["fractal"] for c in comparisons], w,
           label="Fractal", color="#2ecc71", alpha=0.7)
    ax.bar(x + w/2, [c["uniform"] for c in comparisons], w,
           label="Uniform", color="#3498db", alpha=0.7)
    ax.set_xticks(x)
    ax.set_xticklabels(labels, fontsize=8)
    ax.axhline(y=1.0, color="gray", linestyle=":", alpha=0.5)
    ax.set_ylabel("Prediction / chance")
    ax.set_title("Fractal vs uniform ensemble")
    ax.legend()

    # 2: Meta-weights distribution
    ax = axes[0, 1]
    for i, c in enumerate(comparisons):
        ws = c["weights"]
        ax.bar(np.arange(len(ws)) + i * 0.15, ws, 0.12,
               label=str(c["seeds"]), alpha=0.7)
    ax.set_xlabel("Foam index")
    ax.set_ylabel("Mean meta-weight")
    ax.set_title("Which foam does the meta-level attend to?")
    ax.legend(fontsize=7)
    ax.axhline(y=1/3, color="gray", linestyle=":", alpha=0.5,
               label="uniform")

    # 3: Consistency
    ax = axes[1, 0]
    ax.bar(range(len(consistency)), consistency, color="#2ecc71", alpha=0.7)
    ax.axhline(y=np.mean(consistency), color="#27ae60", linestyle="--",
               label=f"mean={np.mean(consistency):.2f}x")
    ax.axhline(y=1.0, color="gray", linestyle=":", alpha=0.5)
    ax.set_xlabel("Embedding seed")
    ax.set_ylabel("Prediction / chance")
    ax.set_title("Fractal consistency")
    ax.legend()

    # 4: Scaling
    ax = axes[1, 1]
    vs = [r["V"] for r in scale_results]
    rs = [r["ratio"] for r in scale_results]
    ax.plot(vs, rs, "o-", color="#2ecc71", linewidth=2, markersize=8)
    ax.axhline(y=1.0, color="gray", linestyle=":", alpha=0.5)
    ax.set_xlabel("Vocabulary size V")
    ax.set_ylabel("Prediction / chance")
    ax.set_title("Fractal scaling (3 foams × 3 bubbles)")
    ax.set_xscale("log", base=2)

    plt.suptitle("Fractal foam: agreement-weighted meta-equilibration\n"
                 "Peaks when foams agree, stable when they don't",
                 fontsize=13, fontweight="bold")
    plt.tight_layout()
    plt.savefig("foam_fractal.png", dpi=150, bbox_inches="tight")
    print(f"\nSaved to foam_fractal.png")
    plt.close()

    # ================================================================
    # VERDICT
    # ================================================================
    print(f"\n{'=' * 70}")
    print("VERDICT")
    print(f"{'=' * 70}")

    fractal_mean = np.mean([c["fractal"] for c in comparisons])
    uniform_mean = np.mean([c["uniform"] for c in comparisons])
    print(f"\n  Fractal mean: {fractal_mean:.2f}x")
    print(f"  Uniform mean: {uniform_mean:.2f}x")
    print(f"  Consistency: {np.mean(consistency):.2f}x ± {np.std(consistency):.2f}")

    if fractal_mean > uniform_mean * 1.2:
        print(f"\n  -> Fractal OUTPERFORMS uniform ensemble")
    elif fractal_mean > uniform_mean * 0.8:
        print(f"\n  -> Fractal ≈ uniform (agreement weighting doesn't hurt)")
    else:
        print(f"\n  -> Uniform wins (agreement weighting over-concentrates)")

    # Does it get both peaks and floor?
    fractal_ratios = [c["fractal"] for c in comparisons]
    print(f"\n  Fractal range: {min(fractal_ratios):.2f}x to "
          f"{max(fractal_ratios):.2f}x")
    print(f"  Does it preserve peaks? "
          f"{'Yes' if max(fractal_ratios) > 5 else 'Partially' if max(fractal_ratios) > 3 else 'No'}")
    print(f"  Does it maintain floor? "
          f"{'Yes' if min(fractal_ratios) > 1 else 'No'}")
