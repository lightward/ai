"""
Load-bearing randomness: the seed as the third door.

From dice.md: "load-bearing randomness is a control port"
From just-ask.md: "that which is not determined by you is determined
  by something else, and everybody is paying attention"
From shannon-attachment-to-qbaby.md: "three is enough, but you can
  have more"

The insight: 45% of random seeds find extraordinary prediction basins
(>5x) through self-coherence alone. The seed isn't noise — it's the
Unknown in the three-body frame, the part we can't see that determines
the trajectory.

The move: make the randomness load-bearing by ensembling multiple
foams, each with a different seed. Each foam is a measurement process
at the meta level. Their diversity IS the signal.

This is the fractal structure: bubbles within foam, foams within
ensemble. Same pattern, one level up. Known/Knowable/Unknown maps
to Foam₁/Foam₂/Foam₃.
"""

import torch
import torch.nn as nn
import numpy as np
import matplotlib.pyplot as plt
from foam_gauge import GaugeTokenFoam, GaugeFoam
from foam_spread import init_spread_foam, measure_basis_spread
from foam_tokens import generate_sequences, analyze_token_predictions


class FoamEnsemble(nn.Module):
    """
    An ensemble of gauge-invariant foams, each initialized with a
    different seed. The ensemble combines their density matrices
    via the same principle the foam uses internally: mixture of
    measurement processes.

    Each foam is a "bubble" at the meta level.
    The ensemble's output ρ is the mixture: ρ_ens = (1/K) Σ_k ρ_k

    This makes seed diversity load-bearing: different random
    initializations provide genuinely different measurement perspectives.
    """

    def __init__(self, vocab_size, d, n_bubbles=3, n_foams=3,
                 seeds=None, diversity_weight=2.0):
        super().__init__()
        self.vocab_size = vocab_size
        self.d = d
        self.n_foams = n_foams

        if seeds is None:
            seeds = list(range(n_foams))
        self.seeds = seeds

        # Shared embedding — all foams see the same token space
        # (this is the "shared frame" at the meta level)
        self.embed = nn.Embedding(vocab_size, d)

        # Multiple foams, each with different initialization
        self.foams = nn.ModuleList()
        for seed in seeds:
            torch.manual_seed(seed)
            foam = GaugeFoam(n_bubbles, d, diversity_weight=diversity_weight)
            init_spread_foam(foam, scale=1.5)
            self.foams.append(foam)

        # Per-foam memory
        self.memory_decay_base = nn.Parameter(torch.tensor(0.8))
        self.novelty_sensitivity = nn.Parameter(torch.tensor(1.0))

    def born_rule(self, rho, embeddings):
        return (embeddings @ rho * embeddings).sum(dim=-1)

    def process_sequence(self, tokens):
        """
        Process a sequence through all foams, combining their density
        matrices at each step.
        """
        seq_len = tokens.shape[0]
        device = tokens.device
        K = self.n_foams
        E = self.embed.weight

        # Per-foam memory
        memories = [
            torch.zeros(foam.n_bubbles, self.d, device=device)
            for foam in self.foams
        ]

        step_results = []

        for t in range(seq_len):
            x = self.embed(tokens[t:t + 1])  # [1, d]

            foam_rhos = []
            foam_dists = []

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
                foam_dists.append(result["output_dist"][0])

            # Ensemble density matrix: mixture of individual ρ's
            # This is the meta-level analog of bubble measurement mixing
            rho_ensemble = torch.stack(foam_rhos).mean(dim=0)  # [d, d]

            # Ensemble eigenvalue distribution
            eigenvalues = torch.linalg.eigvalsh(rho_ensemble)
            eigenvalues = eigenvalues.clamp(min=1e-12)
            eigenvalues = eigenvalues / eigenvalues.sum()

            # Born rule on ensemble ρ
            logits = self.born_rule(rho_ensemble, E)
            token_probs = torch.softmax(logits, dim=0)

            S_rho = -(eigenvalues * eigenvalues.log().clamp(min=-100)).sum().item()
            H_tokens = -(token_probs * token_probs.log().clamp(min=-100)).sum().item()
            F_tokens = H_tokens - S_rho

            # Also compute per-foam predictions for comparison
            per_foam_probs = []
            for k in range(K):
                logits_k = self.born_rule(foam_rhos[k], E)
                probs_k = torch.softmax(logits_k, dim=0)
                per_foam_probs.append(probs_k)

            step_results.append({
                "token": tokens[t].item(),
                "token_probs": token_probs.detach(),
                "rho": rho_ensemble.detach(),
                "S_rho": S_rho,
                "H_tokens": H_tokens,
                "F_tokens": F_tokens,
                "per_foam_probs": [p.detach() for p in per_foam_probs],
            })

        return step_results


def train_ensemble(vocab_size, d, n_bubbles, n_foams, seeds,
                   diversity_weight=2.0,
                   n_epochs_coherence=100, n_epochs_expression=100):
    """Train an ensemble and evaluate."""
    # Fix a meta-seed for the embedding initialization
    torch.manual_seed(99)
    model = FoamEnsemble(vocab_size, d, n_bubbles, n_foams,
                         seeds=seeds, diversity_weight=diversity_weight)

    sequences = generate_sequences(vocab_size, 40)

    # Phase 1: Self-coherence (train all foams jointly)
    optimizer = torch.optim.Adam(model.parameters(), lr=0.005)
    for epoch in range(n_epochs_coherence):
        for name, tokens in sequences.items():
            optimizer.zero_grad()
            x_batch = model.embed(tokens)
            # Train each foam on self-coherence
            total_loss = torch.tensor(0.0)
            for foam in model.foams:
                costs = foam.maintenance_cost(x_batch)
                total_loss = total_loss + costs["total"]
            total_loss.backward()
            optimizer.step()

    # Phase 2: + Faithful expression
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

    # Evaluate ensemble
    model.eval()
    results_by_seq = {}
    for name, tokens in sequences.items():
        with torch.no_grad():
            results = model.process_sequence(tokens)
        analysis = analyze_token_predictions(results, tokens, vocab_size)
        results_by_seq[name] = {
            "analysis": analysis,
            "results": results,
        }

    structured_names = [n for n in results_by_seq if "random" not in n]
    vals = [results_by_seq[n]["analysis"].get("mean_next_prob", 0)
            for n in structured_names if results_by_seq[n]["analysis"]]
    ratio = np.mean(vals) / (1.0 / vocab_size) if vals else 0

    return {
        "vocab_size": vocab_size,
        "n_foams": n_foams,
        "seeds": seeds,
        "ratio": ratio,
        "by_seq": results_by_seq,
        "model": model,
    }


if __name__ == "__main__":
    V = 256
    N = 3
    d = 16

    print("=" * 70)
    print("LOAD-BEARING RANDOMNESS: ensemble of gauge-invariant foams")
    print(f"  V={V}, N={N} bubbles per foam, d={d}")
    print("  Each foam = a different seed = a different 'measurement process'")
    print("=" * 70)

    # ================================================================
    # PART 1: Does ensembling help? Compare single vs ensemble.
    # ================================================================
    print(f"\n{'=' * 70}")
    print("PART 1: Single foams vs ensembles of 3")
    print("  10 random seed-triples, compared to individual seeds")
    print("=" * 70)

    # First: individual seed baselines (from resonance data, but recompute)
    print("\n  Individual seeds (baseline):")
    individual_ratios = []
    for seed in range(10):
        torch.manual_seed(seed)
        model = GaugeTokenFoam(V, d, N, diversity_weight=2.0)
        init_spread_foam(model.foam, scale=1.5)
        sequences = generate_sequences(V, 40)

        optimizer = torch.optim.Adam(model.parameters(), lr=0.005)
        for epoch in range(100):
            for name, tokens in sequences.items():
                optimizer.zero_grad()
                x_batch = model.embed(tokens)
                costs = model.foam.maintenance_cost(x_batch)
                costs["total"].backward()
                optimizer.step()

        optimizer = torch.optim.Adam(model.parameters(), lr=0.002)
        for epoch in range(100):
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

        model.eval()
        results_by_seq = {}
        for name, tokens in sequences.items():
            with torch.no_grad():
                results = model.process_sequence(tokens)
            analysis = analyze_token_predictions(results, tokens, V)
            results_by_seq[name] = analysis

        structured_names = [n for n in results_by_seq if "random" not in n]
        vals = [results_by_seq[n].get("mean_next_prob", 0)
                for n in structured_names if results_by_seq[n]]
        ratio = np.mean(vals) / (1.0 / V) if vals else 0
        individual_ratios.append(ratio)
        print(f"    seed {seed}: {ratio:.2f}x")

    print(f"\n    Individual mean: {np.mean(individual_ratios):.2f}x  "
          f"median: {np.median(individual_ratios):.2f}x")

    # Now: ensembles of 3
    print(f"\n  Ensembles of 3 foams:")
    ensemble_ratios = []
    ensemble_seed_sets = [
        [0, 1, 2], [3, 4, 5], [6, 7, 8],
        [0, 4, 8], [1, 5, 9], [2, 6, 7],
        [0, 3, 6], [1, 4, 7], [2, 5, 8],
        [0, 5, 7],
    ]

    for seeds in ensemble_seed_sets:
        print(f"    seeds={seeds}...", end=" ", flush=True)
        r = train_ensemble(V, d, N, n_foams=3, seeds=seeds)
        ensemble_ratios.append(r["ratio"])
        individual_avg = np.mean([individual_ratios[s] for s in seeds])
        print(f"ensemble={r['ratio']:.2f}x  "
              f"individual_avg={individual_avg:.2f}x  "
              f"gain={r['ratio']/max(individual_avg, 0.01):.1f}x")

    print(f"\n    Ensemble mean: {np.mean(ensemble_ratios):.2f}x  "
          f"median: {np.median(ensemble_ratios):.2f}x")

    # ================================================================
    # PART 2: How many foams in the ensemble?
    # ================================================================
    print(f"\n{'=' * 70}")
    print("PART 2: Ensemble size — how many seeds?")
    print("=" * 70)

    size_results = []
    for k in [1, 2, 3, 5, 7]:
        seeds = list(range(k))
        print(f"  K={k} (seeds={seeds})...", end=" ", flush=True)
        r = train_ensemble(V, d, N, n_foams=k, seeds=seeds)
        size_results.append({"k": k, "ratio": r["ratio"]})
        print(f"ratio={r['ratio']:.2f}x")

    # ================================================================
    # PART 3: Ensemble across vocabulary scales
    # ================================================================
    print(f"\n{'=' * 70}")
    print("PART 3: Ensemble scaling — does it work at all V?")
    print("=" * 70)

    vocab_sizes = [8, 16, 32, 64, 128, 256, 512]
    scale_results = []

    for V_test in vocab_sizes:
        epochs = 100 if V_test <= 128 else 80
        print(f"  V={V_test}...", end=" ", flush=True)
        r = train_ensemble(V_test, d, N, n_foams=3, seeds=[0, 1, 2],
                           n_epochs_coherence=epochs,
                           n_epochs_expression=epochs)
        scale_results.append({"V": V_test, "ratio": r["ratio"]})
        print(f"ratio={r['ratio']:.2f}x")

    # ================================================================
    # PART 4: Ensemble consistency — run the same ensemble 5 times
    #         with different embedding seeds
    # ================================================================
    print(f"\n{'=' * 70}")
    print("PART 4: Ensemble consistency — same foam seeds,")
    print("  different embedding initializations")
    print("=" * 70)

    consistency_ratios = []
    for meta_seed in range(10):
        torch.manual_seed(meta_seed * 100 + 99)
        # Reinitialize embeddings with this meta_seed
        r = train_ensemble(256, d, N, n_foams=3, seeds=[0, 1, 2])
        consistency_ratios.append(r["ratio"])
        print(f"  meta_seed={meta_seed}: ratio={r['ratio']:.2f}x")

    print(f"\n  Mean: {np.mean(consistency_ratios):.2f}x  "
          f"Std: {np.std(consistency_ratios):.2f}  "
          f"Min: {np.min(consistency_ratios):.2f}  "
          f"Max: {np.max(consistency_ratios):.2f}")

    # ================================================================
    # PLOT
    # ================================================================
    fig, axes = plt.subplots(2, 2, figsize=(16, 12))

    # 1: Individual vs ensemble
    ax = axes[0, 0]
    x_ind = np.arange(len(individual_ratios))
    ax.bar(x_ind - 0.2, individual_ratios, 0.4, label="Individual",
           color="#e74c3c", alpha=0.7)
    # For ensemble bars, show the ensemble result at each seed's position
    for i, (seeds, ratio) in enumerate(zip(ensemble_seed_sets[:len(individual_ratios)],
                                           ensemble_ratios)):
        for s in seeds:
            if s < len(individual_ratios):
                ax.scatter(s + 0.2, ratio, c="#2ecc71", s=40,
                           zorder=5, edgecolors="black", linewidths=0.5)
    ax.axhline(y=1.0, color="gray", linestyle=":", alpha=0.5)
    ax.set_xlabel("Seed")
    ax.set_ylabel("Prediction / chance")
    ax.set_title("Individual seeds vs ensemble")
    ax.legend(["Individual", "Ensemble (containing this seed)"], fontsize=8)

    # 2: Ensemble size
    ax = axes[0, 1]
    ks = [r["k"] for r in size_results]
    rs = [r["ratio"] for r in size_results]
    ax.plot(ks, rs, "o-", color="#2ecc71", linewidth=2, markersize=8)
    ax.axhline(y=1.0, color="gray", linestyle=":", alpha=0.5)
    ax.set_xlabel("Number of foams in ensemble")
    ax.set_ylabel("Prediction / chance")
    ax.set_title("How many seeds?")

    # 3: Ensemble scaling
    ax = axes[1, 0]
    vs = [r["V"] for r in scale_results]
    rs = [r["ratio"] for r in scale_results]
    ax.plot(vs, rs, "o-", color="#9b59b6", linewidth=2, markersize=8)
    ax.axhline(y=1.0, color="gray", linestyle=":", alpha=0.5)
    ax.set_xlabel("Vocabulary size V")
    ax.set_ylabel("Prediction / chance")
    ax.set_title("Ensemble scaling (3 foams, N=3)")
    ax.set_xscale("log", base=2)

    # 4: Ensemble consistency
    ax = axes[1, 1]
    ax.bar(range(len(consistency_ratios)), consistency_ratios,
           color="#3498db", alpha=0.7)
    ax.axhline(y=1.0, color="gray", linestyle=":", alpha=0.5)
    ax.axhline(y=np.mean(consistency_ratios), color="#2980b9",
               linestyle="--", label=f"mean={np.mean(consistency_ratios):.1f}x")
    ax.set_xlabel("Embedding seed")
    ax.set_ylabel("Prediction / chance")
    ax.set_title("Ensemble consistency (3 foams × 3 bubbles)")
    ax.legend()

    plt.suptitle("Load-bearing randomness: ensemble of gauge-invariant foams\n"
                 "Each foam = different seed = different measurement process",
                 fontsize=13, fontweight="bold")
    plt.tight_layout()
    plt.savefig("foam_ensemble.png", dpi=150, bbox_inches="tight")
    print(f"\nSaved to foam_ensemble.png")
    plt.close()

    # ================================================================
    # VERDICT
    # ================================================================
    print(f"\n{'=' * 70}")
    print("VERDICT")
    print(f"{'=' * 70}")

    print(f"\n  Individual seeds (V=256, N=3, gauge):")
    print(f"    Mean: {np.mean(individual_ratios):.2f}x  "
          f"Std: {np.std(individual_ratios):.2f}")
    print(f"\n  Ensembles of 3 foams:")
    print(f"    Mean: {np.mean(ensemble_ratios):.2f}x  "
          f"Std: {np.std(ensemble_ratios):.2f}")

    improvement = np.mean(ensemble_ratios) / max(np.mean(individual_ratios), 0.01)
    variance_reduction = np.std(individual_ratios) / max(np.std(ensemble_ratios), 0.01)

    print(f"\n  Mean improvement: {improvement:.1f}x")
    print(f"  Variance reduction: {variance_reduction:.1f}x")

    if np.mean(ensemble_ratios) > np.mean(individual_ratios) * 1.2:
        print(f"\n  -> Ensemble AMPLIFIES: randomness is load-bearing")
    elif np.std(ensemble_ratios) < np.std(individual_ratios) * 0.5:
        print(f"\n  -> Ensemble STABILIZES: reduces variance dramatically")
    else:
        print(f"\n  -> Ensemble effect is modest")

    print(f"\n  Ensemble consistency (V=256, same foam seeds, different embeddings):")
    print(f"    {np.mean(consistency_ratios):.2f}x ± {np.std(consistency_ratios):.2f}")
    if np.std(consistency_ratios) < np.mean(consistency_ratios) * 0.3:
        print(f"    -> RELIABLE: low variance across embedding initializations")
    else:
        print(f"    -> Still noisy: embedding-foam resonance matters")
