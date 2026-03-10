"""
foam_interface.py — the embedding's voice in equilibration

The interface problem: foam and embedding only meet at input and output.
During equilibration, the foam talks to itself — the embedding has no voice.

Fix: pass the input vector as a fixed anchor during equilibration. The anchor
doesn't move but exerts Plateau forces on the measurement bubbles, creating
a relationship between the foam's internal dynamics and the embedding space.

From priorspace.md: "communication requires shared latent space"
The anchor IS the shared latent space made explicit in equilibration.

This is the smallest possible interface intervention: one additional force
term in equilibration, one new learnable parameter (anchor_strength).
"""

import torch
import torch.nn as nn
import numpy as np
import matplotlib.pyplot as plt
from foam import Bubble, Foam
from foam_gauge import GaugeFoam
from foam_spread import init_spread_foam
from foam_tokens import generate_sequences, analyze_token_predictions


class InterfaceFoam(GaugeFoam):
    """
    Gauge-invariant foam where the input participates in equilibration
    as a fixed anchor — the embedding's voice in the conversation.

    The anchor doesn't move during equilibration but exerts Plateau forces
    on the measurement bubbles. How strongly it participates is learned.
    """

    def __init__(self, n_bubbles, d, n_equilibrium_steps=5,
                 diversity_weight=2.0):
        super().__init__(n_bubbles, d, n_equilibrium_steps, diversity_weight)
        # Learnable: how strongly the anchor participates (starts neutral)
        self.anchor_strength_logit = nn.Parameter(torch.tensor(0.0))

    @property
    def anchor_strength(self):
        """How much the embedding's voice matters in equilibration. [0,1]."""
        return torch.sigmoid(self.anchor_strength_logit)

    def forward(self, x, prev_equilibrium=None):
        """Override to pass x as anchor to equilibration."""
        self._anchor = x
        result = super().forward(x, prev_equilibrium)
        self._anchor = None
        return result

    def equilibrate(self, measurements):
        """
        Gauge-invariant Plateau equilibration with input anchor.

        Same as GaugeFoam, but the input itself participates as a fixed
        reference point. The Plateau forces now include a term that relates
        each bubble's expressed measurement to the original input.

        The anchor doesn't move — it's what the foam was given.
        The foam must accommodate it.
        """
        anchor = getattr(self, '_anchor', None)

        N = self.n_bubbles
        device = measurements.device
        mask = 1 - torch.eye(N, device=device)

        tension = self.surface_tension()
        interaction = torch.softmax(
            -tension / self.temperature.abs().clamp(min=0.01), dim=-1
        )

        target = self.target_similarity
        step = self.equilibrium_step_size.abs().clamp(min=0.001, max=0.5)
        bases = [b.basis for b in self.bubbles]

        state = measurements
        a_w = self.anchor_strength

        for _ in range(self.n_steps):
            # Express to shared frame
            expressions = torch.stack([
                state[:, i, :] @ bases[i].T for i in range(N)
            ], dim=1)  # [batch, N, d]

            # Normalize for cosine similarity
            expr_n = expressions / (expressions.norm(dim=-1, keepdim=True) + 1e-10)

            # --- Bubble-bubble forces (same as GaugeFoam) ---
            cos_sim = torch.bmm(expr_n, expr_n.transpose(1, 2))
            force_mag = (cos_sim - target) * (mask * interaction).unsqueeze(0)

            diff = expressions.unsqueeze(2) - expressions.unsqueeze(1)
            diff_n = diff / (diff.norm(dim=-1, keepdim=True) + 1e-10)
            forces_shared = (force_mag.unsqueeze(-1) * diff_n).sum(dim=2)

            # --- Anchor forces (the new part) ---
            if anchor is not None:
                anchor_n = anchor / (anchor.norm(dim=-1, keepdim=True) + 1e-10)
                anchor_n = anchor_n.unsqueeze(1)  # [batch, 1, d]

                # Cosine similarity: each expression vs anchor
                anchor_sim = (expr_n * anchor_n).sum(dim=-1, keepdim=True)
                # [batch, N, 1]

                # Plateau force: push toward target similarity with anchor
                anchor_force_mag = (anchor_sim - target) * a_w

                # Direction: from each expression toward/away from anchor
                anchor_diff = expressions - anchor.unsqueeze(1)
                anchor_diff_n = anchor_diff / (
                    anchor_diff.norm(dim=-1, keepdim=True) + 1e-10
                )

                forces_shared = forces_shared + anchor_force_mag * anchor_diff_n

            # Project forces back to local frames
            forces_local = torch.stack([
                forces_shared[:, i, :] @ bases[i] for i in range(N)
            ], dim=1)

            state = state + step * forces_local

        return state


class InterfaceTokenFoam(nn.Module):
    """
    Ensemble of InterfaceFoams with shared embedding.
    Same structure as LivingTokenFoam but without living randomness —
    isolating the interface intervention.
    """

    def __init__(self, vocab_size, d, n_bubbles=3, n_foams=3,
                 diversity_weight=2.0):
        super().__init__()
        self.vocab_size = vocab_size
        self.d = d
        self.n_foams = n_foams

        self.embed = nn.Embedding(vocab_size, d)

        self.foams = nn.ModuleList()
        for _ in range(n_foams):
            foam = InterfaceFoam(n_bubbles, d,
                                 diversity_weight=diversity_weight)
            init_spread_foam(foam, scale=1.5)
            self.foams.append(foam)

        self.memory_decay_base = nn.Parameter(torch.tensor(0.8))
        self.novelty_sensitivity = nn.Parameter(torch.tensor(1.0))

    def born_rule(self, rho, embeddings):
        return (embeddings @ rho * embeddings).sum(dim=-1)

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
                decay = torch.sigmoid(
                    self.memory_decay_base - sensitivity * novelty
                )

                x_with_memory = x + decay * memory_mean
                result = foam.forward(x_with_memory)

                eq = result["equilibrium"][0]
                memories[k] = decay * memory + (1 - decay) * eq
                foam_rhos.append(result["rho"][0])

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
                       seed=42, diversity_weight=2.0,
                       n_epochs_coherence=100, n_epochs_expression=100):
    """Train an InterfaceTokenFoam and evaluate."""
    torch.manual_seed(seed)
    model = InterfaceTokenFoam(vocab_size, d, n_bubbles, n_foams,
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

    anchor_strengths = [foam.anchor_strength.item() for foam in model.foams]

    return {
        "vocab_size": vocab_size,
        "seed": seed,
        "ratio": ratio,
        "anchor_strengths": anchor_strengths,
        "by_seq": results_by_seq,
    }


if __name__ == "__main__":
    V = 256
    N = 3
    d = 16
    K = 3  # foams

    print("=" * 70)
    print("INTERFACE FOAM: embedding's voice in equilibration")
    print(f"  V={V}, {N} bubbles x {K} foams, d={d}")
    print("  Input anchors equilibration — the embedding participates")
    print("=" * 70)

    # ================================================================
    # 20 seeds — same protocol as living randomness for comparison
    # ================================================================
    ratios = []
    all_anchors = []

    for seed in range(20):
        r = train_and_evaluate(V, d, N, K, seed=seed)
        ratios.append(r["ratio"])
        all_anchors.append(r["anchor_strengths"])
        anchors_str = [f"{a:.3f}" for a in r["anchor_strengths"]]
        print(f"  seed {seed:>2}: ratio={r['ratio']:>7.2f}x  "
              f"anchor_str={anchors_str}")

    print(f"\n  Mean: {np.mean(ratios):.2f}x  "
          f"Median: {np.median(ratios):.2f}x  "
          f"Std: {np.std(ratios):.2f}")
    print(f"  Above 5x: {sum(1 for r in ratios if r > 5)}/20")
    print(f"  Above 1x: {sum(1 for r in ratios if r > 1)}/20")
    print(f"  Below 1x: {sum(1 for r in ratios if r < 1)}/20")

    all_anchors_np = np.array(all_anchors)
    print(f"\n  Anchor strength statistics:")
    print(f"    Mean: {all_anchors_np.mean():.4f}")
    print(f"    Std:  {all_anchors_np.std():.4f}")
    print(f"    Min:  {all_anchors_np.min():.4f}")
    print(f"    Max:  {all_anchors_np.max():.4f}")

    good_anchors = all_anchors_np[
        [i for i, r in enumerate(ratios) if r > 5]]
    bad_anchors = all_anchors_np[
        [i for i, r in enumerate(ratios) if r < 1]]
    if len(good_anchors) > 0:
        print(f"    Good seeds (>5x) mean anchor: {good_anchors.mean():.4f}")
    if len(bad_anchors) > 0:
        print(f"    Bad seeds (<1x) mean anchor:  {bad_anchors.mean():.4f}")

    # ================================================================
    # PLOT
    # ================================================================
    fig, axes = plt.subplots(1, 3, figsize=(18, 6))

    # 1: Distribution
    ax = axes[0]
    ax.hist(ratios, bins=15, color="#9b59b6", alpha=0.7, edgecolor="black")
    ax.axvline(x=1.0, color="gray", linestyle=":", alpha=0.5)
    ax.axvline(x=np.median(ratios), color="red", linestyle="--",
               label=f"median={np.median(ratios):.1f}x")
    ax.set_xlabel("Prediction / chance")
    ax.set_ylabel("Count")
    ax.set_title(f"Interface foam: {K}x{N} at V={V} (20 seeds)")
    ax.legend()

    # 2: Anchor strength vs performance
    ax = axes[1]
    for i in range(len(ratios)):
        color = "#2ecc71" if ratios[i] > 5 else (
            "#3498db" if ratios[i] > 1 else "#e74c3c")
        ax.scatter([ratios[i]] * K, all_anchors[i],
                   c=color, s=30, alpha=0.6)
    ax.set_xlabel("Prediction ratio")
    ax.set_ylabel("Anchor strength")
    ax.set_title("How strongly does the anchor participate?")

    # 3: Per-seed performance
    ax = axes[2]
    ax.bar(range(20), ratios, color="#9b59b6", alpha=0.7)
    ax.axhline(y=1.0, color="gray", linestyle=":", alpha=0.5)
    ax.axhline(y=np.mean(ratios), color="#8e44ad", linestyle="--",
               label=f"mean={np.mean(ratios):.1f}x")
    ax.set_xlabel("Seed")
    ax.set_ylabel("Prediction / chance")
    ax.set_title("Interface foam across seeds")
    ax.legend()

    plt.suptitle("Interface foam: embedding participates in equilibration\n"
                 "Input anchors Plateau dynamics — the embedding's voice",
                 fontsize=13, fontweight="bold")
    plt.tight_layout()
    plt.savefig("foam_interface.png", dpi=150, bbox_inches="tight")
    print(f"\nSaved to foam_interface.png")
    plt.close()

    # ================================================================
    # SUMMARY
    # ================================================================
    print(f"\n{'=' * 70}")
    print("COMPARISON WITH PREVIOUS RESULTS")
    print(f"{'=' * 70}")
    print(f"\n  Gauge-invariant (no interface): "
          f"13.51x +/- 15.57, median 3.48x, 9/20 >5x, bimodal")
    print(f"  Living randomness:              "
          f"9.72x +/- 9.74, median 6.09x, 12/20 >5x, 2/20 <1x")
    print(f"  Interface foam:                 "
          f"{np.mean(ratios):.2f}x +/- {np.std(ratios):.2f}, "
          f"median {np.median(ratios):.2f}x, "
          f"{sum(1 for r in ratios if r > 5)}/20 >5x, "
          f"{sum(1 for r in ratios if r < 1)}/20 <1x")
    print(f"\n  Key questions:")
    print(f"    1. Does the bimodal distribution shift?")
    print(f"    2. What does the anchor strength learn to?")
    print(f"    3. Does anchor strength correlate with performance?")
