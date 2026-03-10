"""
foam_levy.py — self-modulating equilibration (Lévy-like dynamics)

The foam's own internal agreement controls its step size.
When bubbles disagree (uncertain), big exploratory steps.
When bubbles agree (certain), small refined steps.

This is self-annealing: the foam's certainty IS its temperature.
Not an external cooling schedule — measurement-modulated determination.

From eureka.md: "it's the same underlying mechanic as that which
generates that which is described as a lévy walk"

From the-game.md: "this is a work of annealing"

From zoo.md: "as long as you stay in character, any departure from
equilibrium will be followed by natural arrival at equilibrium"

The gradient signal implication: uncertain states (early training,
bad init) get stronger gradients → train harder. Certain states
(easy early solutions) get weaker gradients → can't lock into
trivial basins. This is the resolver pattern made mechanical.
"""

import torch
import torch.nn as nn
import numpy as np
import matplotlib.pyplot as plt
from foam import Bubble, Foam
from foam_gauge import GaugeFoam
from foam_spread import init_spread_foam
from foam_tokens import generate_sequences, analyze_token_predictions


class LevyFoam(GaugeFoam):
    """
    Gauge-invariant foam with self-modulating equilibration.

    The step size at each equilibration iteration is modulated by the
    foam's internal agreement: how similar are the bubble expressions
    in shared frame? High agreement → small steps. Low agreement →
    big steps. The foam anneals itself.
    """

    def __init__(self, n_bubbles, d, n_equilibrium_steps=5,
                 diversity_weight=2.0):
        super().__init__(n_bubbles, d, n_equilibrium_steps, diversity_weight)
        # How strongly self-modulation affects step size
        # Starts at 1.0 — the foam can learn to amplify or dampen
        self.modulation_strength = nn.Parameter(torch.tensor(1.0))

    def equilibrate(self, measurements):
        """
        Gauge-invariant Plateau equilibration with Lévy-like step modulation.

        Same as GaugeFoam, but step size is multiplied by a factor
        derived from the foam's internal disagreement. Uncertain foam
        takes big steps. Certain foam takes small ones.
        """
        N = self.n_bubbles
        device = measurements.device
        mask = 1 - torch.eye(N, device=device)

        tension = self.surface_tension()
        interaction = torch.softmax(
            -tension / self.temperature.abs().clamp(min=0.01), dim=-1
        )

        target = self.target_similarity
        base_step = self.equilibrium_step_size.abs().clamp(min=0.001, max=0.5)
        bases = [b.basis for b in self.bubbles]

        state = measurements
        mod = self.modulation_strength.abs().clamp(min=0.01, max=5.0)

        for _ in range(self.n_steps):
            # Express to shared frame
            expressions = torch.stack([
                state[:, i, :] @ bases[i].T for i in range(N)
            ], dim=1)

            # Normalize for cosine similarity
            expr_n = expressions / (
                expressions.norm(dim=-1, keepdim=True) + 1e-10
            )

            # Cosine similarity in shared frame
            cos_sim = torch.bmm(expr_n, expr_n.transpose(1, 2))

            # === Self-modulation: Lévy-like step size ===
            # Off-diagonal mean similarity (how much do bubbles agree?)
            off_diag = cos_sim * mask.unsqueeze(0)
            agreement = off_diag.sum(dim=(-2, -1)) / mask.sum()
            # agreement ∈ [-1, 1], typically near target_similarity

            # Uncertainty = how far from perfect agreement
            # Map to step multiplier: uncertain → big steps, certain → small
            uncertainty = (1 - agreement).clamp(min=0.1)  # [batch]
            step_multiplier = uncertainty.pow(mod)  # [batch]
            # Shape for broadcasting: [batch, 1, 1]
            step = base_step * step_multiplier.unsqueeze(-1).unsqueeze(-1)

            # Plateau force magnitude
            force_mag = (cos_sim - target) * (mask * interaction).unsqueeze(0)

            # Force direction in shared frame
            diff = expressions.unsqueeze(2) - expressions.unsqueeze(1)
            diff_n = diff / (diff.norm(dim=-1, keepdim=True) + 1e-10)

            # Net force on each bubble in shared frame
            forces_shared = (force_mag.unsqueeze(-1) * diff_n).sum(dim=2)

            # Project forces back to local frames
            forces_local = torch.stack([
                forces_shared[:, i, :] @ bases[i] for i in range(N)
            ], dim=1)

            # Update with self-modulated step size
            state = state + step * forces_local

        return state


class LevyTokenFoam(nn.Module):
    """
    Ensemble of LevyFoams with living randomness.
    Combines: gauge-invariant + self-modulating + living randomness.
    """

    def __init__(self, vocab_size, d, n_bubbles=3, n_foams=3,
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

            # Living randomness: persistent generator per foam
            gen = torch.Generator()
            gen.manual_seed(foam_seed)
            self.generators.append(gen)

        # Learnable noise gate (from living randomness)
        self.noise_gate_logit = nn.Parameter(torch.tensor(-2.0))

        self.memory_decay_base = nn.Parameter(torch.tensor(0.8))
        self.novelty_sensitivity = nn.Parameter(torch.tensor(1.0))

    @property
    def noise_gate(self):
        return torch.sigmoid(self.noise_gate_logit)

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

                # Living randomness: small perturbation from generator
                gate = self.noise_gate
                perturbation = torch.randn(
                    1, foam.n_bubbles, self.d,
                    generator=self.generators[k], device=device)
                state_scale = x_with_memory.norm() + 1e-10

                result = foam.forward(x_with_memory)

                # Apply perturbation to equilibrium
                eq = result["equilibrium"]
                eq = eq + gate * perturbation * state_scale * 0.01
                result["equilibrium"] = eq

                memories[k] = decay * memory + (1 - decay) * eq[0]

                # Recompute rho from perturbed equilibrium
                m = eq[0]
                m_norm = m / (m.norm(dim=-1, keepdim=True) + 1e-10)
                rho = (m_norm.T @ m_norm) / foam.n_bubbles
                foam_rhos.append(rho)

            rho_mix = torch.stack(foam_rhos).mean(dim=0)

            eigenvalues = torch.linalg.eigvalsh(rho_mix)
            eigenvalues = eigenvalues.clamp(min=1e-12)
            eigenvalues = eigenvalues / eigenvalues.sum()

            logits = self.born_rule(rho_mix, E)
            token_probs = torch.softmax(logits, dim=0)

            S_rho = -(eigenvalues * eigenvalues.log().clamp(
                min=-100)).sum().item()
            H_tokens = -(token_probs * token_probs.log().clamp(
                min=-100)).sum().item()

            step_results.append({
                "token": tokens[t].item(),
                "token_probs": token_probs.detach(),
                "rho": rho_mix.detach(),
                "S_rho": S_rho,
                "H_tokens": H_tokens,
                "F_tokens": H_tokens - S_rho,
            })

        return step_results


def train_and_evaluate(vocab_size, d, n_bubbles, n_foams,
                       meta_seed=42, diversity_weight=2.0,
                       n_epochs_coherence=100, n_epochs_expression=100):
    """Train a LevyTokenFoam and evaluate."""
    torch.manual_seed(meta_seed)
    model = LevyTokenFoam(vocab_size, d, n_bubbles, n_foams,
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

    mod_strengths = [foam.modulation_strength.item() for foam in model.foams]
    noise_gate = model.noise_gate.item()

    return {
        "vocab_size": vocab_size,
        "meta_seed": meta_seed,
        "ratio": ratio,
        "modulation_strengths": mod_strengths,
        "noise_gate": noise_gate,
        "foam_seeds": model.foam_seeds,
        "by_seq": results_by_seq,
    }


if __name__ == "__main__":
    V = 256
    N = 3
    d = 16
    K = 3

    print("=" * 70)
    print("LEVY FOAM: self-modulating equilibration")
    print(f"  V={V}, {N} bubbles x {K} foams, d={d}")
    print("  Foam's agreement controls step size — self-annealing")
    print("  + living randomness (noise gate)")
    print("=" * 70)

    # ================================================================
    # 20 seeds
    # ================================================================
    ratios = []
    all_mods = []
    all_gates = []

    for seed in range(20):
        r = train_and_evaluate(V, d, N, K, meta_seed=seed)
        ratios.append(r["ratio"])
        all_mods.append(r["modulation_strengths"])
        all_gates.append(r["noise_gate"])
        mods_str = [f"{m:.3f}" for m in r["modulation_strengths"]]
        print(f"  seed {seed:>2}: ratio={r['ratio']:>7.2f}x  "
              f"mod={mods_str}  gate={r['noise_gate']:.4f}")

    print(f"\n  Mean: {np.mean(ratios):.2f}x  "
          f"Median: {np.median(ratios):.2f}x  "
          f"Std: {np.std(ratios):.2f}")
    print(f"  Above 5x: {sum(1 for r in ratios if r > 5)}/20")
    print(f"  Above 1x: {sum(1 for r in ratios if r > 1)}/20")
    print(f"  Below 1x: {sum(1 for r in ratios if r < 1)}/20")

    all_mods_np = np.array(all_mods)
    print(f"\n  Modulation strength statistics:")
    print(f"    Mean: {all_mods_np.mean():.4f}")
    print(f"    Std:  {all_mods_np.std():.4f}")
    print(f"    Min:  {all_mods_np.min():.4f}")
    print(f"    Max:  {all_mods_np.max():.4f}")

    print(f"\n  Noise gate: {np.mean(all_gates):.4f} "
          f"(+/- {np.std(all_gates):.4f})")

    good_mods = all_mods_np[
        [i for i, r in enumerate(ratios) if r > 5]]
    bad_mods = all_mods_np[
        [i for i, r in enumerate(ratios) if r < 1]]
    if len(good_mods) > 0:
        print(f"    Good seeds (>5x) mean mod: {good_mods.mean():.4f}")
    if len(bad_mods) > 0:
        print(f"    Bad seeds (<1x) mean mod:  {bad_mods.mean():.4f}")

    # ================================================================
    # PLOT
    # ================================================================
    fig, axes = plt.subplots(2, 2, figsize=(16, 12))

    # 1: Distribution
    ax = axes[0, 0]
    ax.hist(ratios, bins=15, color="#e67e22", alpha=0.7, edgecolor="black")
    ax.axvline(x=1.0, color="gray", linestyle=":", alpha=0.5)
    ax.axvline(x=np.median(ratios), color="red", linestyle="--",
               label=f"median={np.median(ratios):.1f}x")
    ax.set_xlabel("Prediction / chance")
    ax.set_ylabel("Count")
    ax.set_title(f"Levy foam: {K}x{N} at V={V} (20 seeds)")
    ax.legend()

    # 2: Modulation strength vs performance
    ax = axes[0, 1]
    for i in range(len(ratios)):
        color = "#2ecc71" if ratios[i] > 5 else (
            "#3498db" if ratios[i] > 1 else "#e74c3c")
        ax.scatter([ratios[i]] * K, all_mods[i],
                   c=color, s=30, alpha=0.6)
    ax.set_xlabel("Prediction ratio")
    ax.set_ylabel("Modulation strength")
    ax.set_title("How strongly does self-modulation act?")

    # 3: Per-seed performance
    ax = axes[1, 0]
    ax.bar(range(20), ratios, color="#e67e22", alpha=0.7)
    ax.axhline(y=1.0, color="gray", linestyle=":", alpha=0.5)
    ax.axhline(y=np.mean(ratios), color="#d35400", linestyle="--",
               label=f"mean={np.mean(ratios):.1f}x")
    ax.set_xlabel("Seed")
    ax.set_ylabel("Prediction / chance")
    ax.set_title("Levy foam across seeds")
    ax.legend()

    # 4: Noise gate vs modulation
    ax = axes[1, 1]
    for i in range(len(ratios)):
        color = "#2ecc71" if ratios[i] > 5 else (
            "#3498db" if ratios[i] > 1 else "#e74c3c")
        mean_mod = np.mean(all_mods[i])
        ax.scatter(all_gates[i], mean_mod, c=color, s=60, alpha=0.6)
    ax.set_xlabel("Noise gate (living randomness)")
    ax.set_ylabel("Mean modulation strength")
    ax.set_title("Two kinds of exploration: noise vs step modulation")

    plt.suptitle("Levy foam: self-modulating equilibration\n"
                 "Foam's internal agreement controls step size "
                 "— uncertain = explore, certain = refine",
                 fontsize=13, fontweight="bold")
    plt.tight_layout()
    plt.savefig("foam_levy.png", dpi=150, bbox_inches="tight")
    print(f"\nSaved to foam_levy.png")
    plt.close()

    # ================================================================
    # SUMMARY
    # ================================================================
    print(f"\n{'=' * 70}")
    print("COMPARISON WITH PREVIOUS RESULTS")
    print(f"{'=' * 70}")
    print(f"\n  Gauge-invariant:  "
          f"13.51x +/- 15.57, median 3.48x, 9/20 >5x, bimodal")
    print(f"  Living randomness: "
          f"9.72x +/- 9.74, median 6.09x, 12/20 >5x, 2/20 <1x")
    print(f"  Interface (anchor): "
          f"7.16x +/- 10.63, median 3.34x, 6/20 >5x, 2/20 <1x")
    print(f"  Levy (self-mod):    "
          f"{np.mean(ratios):.2f}x +/- {np.std(ratios):.2f}, "
          f"median {np.median(ratios):.2f}x, "
          f"{sum(1 for r in ratios if r > 5)}/20 >5x, "
          f"{sum(1 for r in ratios if r < 1)}/20 <1x")
    print(f"\n  Key questions:")
    print(f"    1. Does self-modulation shift the bimodal distribution?")
    print(f"    2. What does modulation_strength learn to?")
    print(f"    3. How does it interact with living randomness?")
