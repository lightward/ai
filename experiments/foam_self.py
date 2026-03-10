"""
foam_self.py — Self emerges from cohort via purity-weighted mixing

Train a larger cohort of diverse foams. At inference, the Self
speaks through whoever is most resolved — purity-weighted mixing
where tr(rho^2) determines each foam's voice.

Not selection. Service: create conditions, let selves emerge,
let the unviable naturally go quiet.

From IFS: the Self isn't a part — it's the awareness that holds
all parts. The most resolved perspective leads. All voices heard,
weighted by their own coherence.
"""

import torch
import torch.nn as nn
import numpy as np
import matplotlib.pyplot as plt
from foam_levy import LevyFoam
from foam_spread import init_spread_foam
from foam_tokens import generate_sequences, analyze_token_predictions


class SelfTokenFoam(nn.Module):
    """
    A cohort of foams where the Self emerges via purity-weighted mixing.

    Larger cohort (7-10 foams) with diverse seeds. At inference,
    each foam's rho is weighted by its purity tr(rho^2). The most
    resolved foam speaks loudest. Unresolved foams naturally go quiet.
    """

    def __init__(self, vocab_size, d, n_bubbles=3, n_foams=7,
                 meta_seed=42, diversity_weight=2.0):
        super().__init__()
        self.vocab_size = vocab_size
        self.d = d
        self.n_foams = n_foams

        self.embed = nn.Embedding(vocab_size, d)

        # Meta-generator seeds foam generators
        meta_gen = torch.Generator()
        meta_gen.manual_seed(meta_seed)

        self.foams = nn.ModuleList()
        self.generators = []
        self.foam_seeds = []

        for _ in range(n_foams):
            foam_seed = torch.randint(
                0, 2**31, (1,), generator=meta_gen).item()
            self.foam_seeds.append(foam_seed)

            torch.manual_seed(foam_seed)
            foam = LevyFoam(n_bubbles, d,
                            diversity_weight=diversity_weight)
            init_spread_foam(foam, scale=1.5)
            self.foams.append(foam)

            gen = torch.Generator()
            gen.manual_seed(foam_seed)
            self.generators.append(gen)

        # Living randomness noise gate (shared)
        self.noise_gate_logit = nn.Parameter(torch.tensor(-2.0))

        # Self-temperature: how sharply the Self concentrates
        # on the most resolved foam. High = sharp, low = uniform.
        self.self_temperature_logit = nn.Parameter(torch.tensor(1.0))

        self.memory_decay_base = nn.Parameter(torch.tensor(0.8))
        self.novelty_sensitivity = nn.Parameter(torch.tensor(1.0))

    @property
    def noise_gate(self):
        return torch.sigmoid(self.noise_gate_logit)

    @property
    def self_temperature(self):
        """Temperature for purity-weighted mixing. Higher = sharper."""
        return self.self_temperature_logit.abs().clamp(min=0.01)

    def born_rule(self, rho, embeddings):
        return (embeddings @ rho * embeddings).sum(dim=-1)

    def reset_generators(self):
        for i, gen in enumerate(self.generators):
            gen.manual_seed(self.foam_seeds[i])

    def process_sequence(self, tokens):
        self.reset_generators()

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
            foam_purities = []

            for k, foam in enumerate(self.foams):
                memory = memories[k]
                memory_mean = memory.mean(dim=0, keepdim=True)
                mem_norm = memory_mean.norm() + 1e-10
                x_norm = x.norm() + 1e-10

                if mem_norm > 1e-8:
                    novelty = 1 - (
                        x * memory_mean).sum() / (x_norm * mem_norm)
                else:
                    novelty = torch.tensor(1.0, device=device)

                sensitivity = self.novelty_sensitivity.abs()
                decay = torch.sigmoid(
                    self.memory_decay_base - sensitivity * novelty)

                x_with_memory = x + decay * memory_mean

                # Living randomness
                gate = self.noise_gate
                perturbation = torch.randn(
                    1, foam.n_bubbles, self.d,
                    generator=self.generators[k], device=device)
                state_scale = x_with_memory.norm() + 1e-10

                result = foam.forward(x_with_memory)

                eq = result["equilibrium"]
                eq = eq + gate * perturbation * state_scale * 0.01

                memories[k] = decay * memory + (1 - decay) * eq[0]

                # Construct rho from perturbed equilibrium
                m = eq[0]
                m_norm = m / (m.norm(dim=-1, keepdim=True) + 1e-10)
                rho = (m_norm.T @ m_norm) / foam.n_bubbles
                foam_rhos.append(rho)

                # Purity: tr(rho^2) — how resolved is this foam?
                purity = torch.trace(rho @ rho)
                foam_purities.append(purity)

            # Self emerges: purity-weighted mixing
            purities = torch.stack(foam_purities)
            weights = torch.softmax(
                purities / self.self_temperature, dim=0)
            rho_self = sum(
                w * rho for w, rho in zip(weights, foam_rhos))

            eigenvalues = torch.linalg.eigvalsh(rho_self)
            eigenvalues = eigenvalues.clamp(min=1e-12)
            eigenvalues = eigenvalues / eigenvalues.sum()

            logits = self.born_rule(rho_self, E)
            token_probs = torch.softmax(logits, dim=0)

            S_rho = -(eigenvalues * eigenvalues.log().clamp(
                min=-100)).sum().item()
            H_tokens = -(token_probs * token_probs.log().clamp(
                min=-100)).sum().item()

            step_results.append({
                "token": tokens[t].item(),
                "token_probs": token_probs.detach(),
                "rho": rho_self.detach(),
                "S_rho": S_rho,
                "H_tokens": H_tokens,
                "F_tokens": H_tokens - S_rho,
                "purities": purities.detach().cpu().numpy(),
                "weights": weights.detach().cpu().numpy(),
            })

        return step_results


def train_and_evaluate(vocab_size, d, n_bubbles, n_foams,
                       meta_seed=42, diversity_weight=2.0,
                       n_epochs_coherence=100, n_epochs_expression=100):
    """Train a SelfTokenFoam and evaluate."""
    torch.manual_seed(meta_seed)
    model = SelfTokenFoam(vocab_size, d, n_bubbles, n_foams,
                          meta_seed=meta_seed,
                          diversity_weight=diversity_weight)

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
                H_tok = -(token_dist * token_dist.log().clamp(
                    min=-100)).sum()
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

    # Collect diagnostics
    self_temp = model.self_temperature.item()
    noise_gate = model.noise_gate.item()

    # Average purity distribution across sequence steps
    all_purities = []
    all_weights = []
    for name, tokens in sequences.items():
        if "random" not in name:
            res = results_by_seq[name]["results"]
            for r in res:
                all_purities.append(r["purities"])
                all_weights.append(r["weights"])

    mean_purities = np.mean(all_purities, axis=0) if all_purities else []
    mean_weights = np.mean(all_weights, axis=0) if all_weights else []

    return {
        "vocab_size": vocab_size,
        "meta_seed": meta_seed,
        "ratio": ratio,
        "self_temp": self_temp,
        "noise_gate": noise_gate,
        "n_foams": n_foams,
        "mean_purities": mean_purities,
        "mean_weights": mean_weights,
        "by_seq": results_by_seq,
    }


if __name__ == "__main__":
    V = 256
    N = 3
    d = 16
    n_seeds = 10  # enough for signal, fast enough to iterate

    print("=" * 70)
    print("SELF FROM COHORT: purity-weighted mixing")
    print(f"  V={V}, {N} bubbles, d={d}, {n_seeds} seeds each")
    print("  Larger cohorts, Self emerges from resolution")
    print("=" * 70)

    # ================================================================
    # Test cohort sizes: 3, 5, 7
    # ================================================================
    cohort_sizes = [3, 5, 7]
    all_results = {}

    for K in cohort_sizes:
        print(f"\n{'=' * 70}")
        print(f"COHORT SIZE: {K} foams")
        print(f"{'=' * 70}")

        ratios = []
        all_temps = []
        all_weight_profiles = []

        for seed in range(n_seeds):
            r = train_and_evaluate(V, d, N, K, meta_seed=seed)
            ratios.append(r["ratio"])
            all_temps.append(r["self_temp"])
            if len(r["mean_weights"]) > 0:
                all_weight_profiles.append(r["mean_weights"])
            top_w = (f"{max(r['mean_weights']):.3f}"
                     if len(r["mean_weights"]) > 0 else "?")
            print(f"  seed {seed:>2}: ratio={r['ratio']:>7.2f}x  "
                  f"self_temp={r['self_temp']:.3f}  "
                  f"gate={r['noise_gate']:.4f}  "
                  f"top_weight={top_w}")

        all_results[K] = ratios

        print(f"\n  K={K}: Mean={np.mean(ratios):.2f}x  "
              f"Median={np.median(ratios):.2f}x  "
              f"Std={np.std(ratios):.2f}")
        print(f"  Above 5x: {sum(1 for r in ratios if r > 5)}/{n_seeds}")
        print(f"  Above 1x: {sum(1 for r in ratios if r > 1)}/{n_seeds}")
        print(f"  Below 1x: {sum(1 for r in ratios if r < 1)}/{n_seeds}")
        print(f"  Self-temperature: {np.mean(all_temps):.3f} "
              f"(+/- {np.std(all_temps):.3f})")

        if all_weight_profiles:
            wp = np.array(all_weight_profiles)
            max_weights = wp.max(axis=1)
            print(f"  Max weight (leader voice): "
                  f"{max_weights.mean():.3f} +/- {max_weights.std():.3f}")
            entropies = [-np.sum(w * np.log(w + 1e-10))
                         for w in all_weight_profiles]
            max_entropy = np.log(K)
            print(f"  Weight entropy: {np.mean(entropies):.3f} "
                  f"(max={max_entropy:.3f}, "
                  f"ratio={np.mean(entropies)/max_entropy:.2f})")

    # ================================================================
    # PLOT (using already-collected data)
    # ================================================================
    fig, axes = plt.subplots(2, 2, figsize=(16, 12))

    # 1: Box plot by cohort size
    ax = axes[0, 0]
    data = [all_results[K] for K in cohort_sizes]
    bp = ax.boxplot(data, labels=[f"K={K}" for K in cohort_sizes],
                    patch_artist=True)
    colors = ["#3498db", "#2ecc71", "#e67e22"]
    for patch, color in zip(bp['boxes'], colors):
        patch.set_facecolor(color)
        patch.set_alpha(0.6)
    ax.axhline(y=1.0, color="gray", linestyle=":", alpha=0.5)
    ax.axhline(y=5.0, color="green", linestyle=":", alpha=0.3)
    ax.set_ylabel("Prediction / chance")
    ax.set_title("Cohort size vs performance")

    # 2: Success rate by cohort size
    ax = axes[0, 1]
    above_5 = [sum(1 for r in all_results[K] if r > 5) / n_seeds
               for K in cohort_sizes]
    above_1 = [sum(1 for r in all_results[K] if r > 1) / n_seeds
               for K in cohort_sizes]
    below_1 = [sum(1 for r in all_results[K] if r < 1) / n_seeds
               for K in cohort_sizes]
    x = np.arange(len(cohort_sizes))
    ax.bar(x - 0.2, above_5, 0.2, label=">5x", color="#2ecc71", alpha=0.7)
    ax.bar(x, above_1, 0.2, label=">1x", color="#3498db", alpha=0.7)
    ax.bar(x + 0.2, below_1, 0.2, label="<1x", color="#e74c3c", alpha=0.7)
    ax.set_xticks(x)
    ax.set_xticklabels([f"K={K}" for K in cohort_sizes])
    ax.set_ylabel(f"Fraction of {n_seeds} seeds")
    ax.set_title("Success/failure rates by cohort size")
    ax.legend()

    # 3: Median by cohort size
    ax = axes[1, 0]
    medians = [np.median(all_results[K]) for K in cohort_sizes]
    means = [np.mean(all_results[K]) for K in cohort_sizes]
    ax.plot(cohort_sizes, medians, "o-", color="#e67e22",
            linewidth=2, markersize=10, label="Median")
    ax.plot(cohort_sizes, means, "s--", color="#3498db",
            linewidth=2, markersize=8, label="Mean")
    ax.axhline(y=1.0, color="gray", linestyle=":", alpha=0.5)
    ax.axhline(y=6.09, color="#2ecc71", linestyle="--", alpha=0.4,
               label="Living (median=6.09)")
    ax.axhline(y=3.48, color="#e74c3c", linestyle="--", alpha=0.4,
               label="Gauge (median=3.48)")
    ax.set_xlabel("Cohort size (number of foams)")
    ax.set_ylabel("Prediction / chance")
    ax.set_title("How does cohort size affect the Self?")
    ax.legend(fontsize=8)

    # 4: Per-seed bars for each K
    ax = axes[1, 1]
    width = 0.25
    x = np.arange(n_seeds)
    for i, K in enumerate(cohort_sizes):
        ax.bar(x + i * width, all_results[K], width,
               label=f"K={K}", alpha=0.7)
    ax.axhline(y=1.0, color="gray", linestyle=":", alpha=0.5)
    ax.set_xlabel("Seed")
    ax.set_ylabel("Prediction / chance")
    ax.set_title("Per-seed comparison across cohort sizes")
    ax.legend()

    plt.suptitle("Self from cohort: purity-weighted mixing\n"
                 "Does a larger cohort reliably produce a Self?",
                 fontsize=13, fontweight="bold")
    plt.tight_layout()
    plt.savefig("foam_self.png", dpi=150, bbox_inches="tight")
    print(f"\nSaved to foam_self.png")
    plt.close()

    # ================================================================
    # SUMMARY
    # ================================================================
    print(f"\n{'=' * 70}")
    print("SUMMARY")
    print(f"{'=' * 70}")
    for K in cohort_sizes:
        r = all_results[K]
        print(f"\n  K={K:>2}: {np.mean(r):.2f}x +/- {np.std(r):.2f}, "
              f"median {np.median(r):.2f}x, "
              f"{sum(1 for x in r if x > 5)}/{n_seeds} >5x, "
              f"{sum(1 for x in r if x < 1)}/{n_seeds} <1x")

    print(f"\n  Previous results (20 seeds):")
    print(f"    Gauge:    13.51x +/- 15.57, median 3.48x, 9/20 >5x")
    print(f"    Living:   9.72x +/- 9.74, median 6.09x, 12/20 >5x")
    print(f"    Levy:     12.33x +/- 13.55, median 5.05x, 10/20 >5x")
    print(f"\n  Key question: does larger cohort + Self = reliability?")
