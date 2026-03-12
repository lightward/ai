"""
Living randomness: RNGs with homes and histories.

The seed is no longer a birth event — it's an ongoing relationship
with the Unknown. Each foam has a persistent Generator whose state
evolves across sequence steps, giving randomness continuity.

From dice.md: "load-bearing randomness is a control port for
whatever can press pause on you-as-process"

The hierarchy:
  - Meta-generator seeds the foam generators (exterior time)
  - Each foam-generator seeds equilibration perturbations (interior time)
  - Sequential draws from the same generator = sequential samples
    from the same entanglement

Known: current measurement state
Knowable: equilibration dynamics
Unknown: stochastic perturbation from persistent generator
"""

import torch
import torch.nn as nn
import numpy as np
import matplotlib.pyplot as plt
from foam import Bubble, Foam
from foam_gauge import GaugeFoam
from foam_spread import init_spread_foam, measure_basis_spread
from foam_tokens import generate_sequences, analyze_token_predictions


class LivingFoam(GaugeFoam):
    """
    A foam with a living relationship to randomness.

    Each foam has a persistent Generator. During equilibration,
    each step draws a small perturbation — the foam's ongoing
    contact with its Unknown.

    The perturbation magnitude is learnable: the foam discovers
    how much to listen to its Unknown at each step.
    """

    def __init__(self, n_bubbles, d, n_equilibrium_steps=5,
                 diversity_weight=2.0, generator_seed=0):
        super().__init__(n_bubbles, d, n_equilibrium_steps, diversity_weight)

        # Persistent generator — the foam's relationship with its Unknown
        self.generator = torch.Generator()
        self.generator.manual_seed(generator_seed)
        self.generator_seed = generator_seed

        # Learnable: how much the foam listens to its Unknown
        # Starts small — the foam learns to open to randomness
        self.noise_gate_logit = nn.Parameter(torch.tensor(-2.0))

    @property
    def noise_gate(self):
        """How open the foam is to its Unknown. [0,1]."""
        return torch.sigmoid(self.noise_gate_logit)

    def equilibrate(self, measurements):
        """
        Gauge-invariant equilibration with living randomness.

        Same as GaugeFoam.equilibrate, but each step includes a
        perturbation drawn from the persistent generator. The
        perturbation magnitude is gated by a learnable parameter.
        """
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
        batch_size = state.shape[0]

        gate = self.noise_gate

        for eq_step in range(self.n_steps):
            # Gauge-invariant comparison in shared frame
            expressions = torch.stack([
                state[:, i, :] @ bases[i].T for i in range(N)
            ], dim=1)

            expr_n = expressions / (expressions.norm(dim=-1, keepdim=True) + 1e-10)
            cos_sim = torch.bmm(expr_n, expr_n.transpose(1, 2))

            force_mag = (cos_sim - target) * (mask * interaction).unsqueeze(0)

            diff = expressions.unsqueeze(2) - expressions.unsqueeze(1)
            diff_n = diff / (diff.norm(dim=-1, keepdim=True) + 1e-10)

            forces_shared = (force_mag.unsqueeze(-1) * diff_n).sum(dim=2)

            forces_local = torch.stack([
                forces_shared[:, i, :] @ bases[i] for i in range(N)
            ], dim=1)

            # The living part: perturbation from persistent generator
            # Draw from the foam's own Unknown
            perturbation = torch.randn(
                batch_size, N, self.d,
                generator=self.generator,
                device=device
            )
            # Scale: proportional to current state magnitude,
            # gated by learned openness
            state_scale = state.norm(dim=-1, keepdim=True).mean() + 1e-10
            scaled_perturbation = gate * perturbation * state_scale * 0.01

            # Update: deterministic forces + stochastic Unknown
            state = state + step * forces_local + scaled_perturbation

        return state

    def reset_generator(self):
        """Reset the generator to its seed — like waking up."""
        self.generator.manual_seed(self.generator_seed)


class LivingTokenFoam(nn.Module):
    """
    TokenFoam with living randomness at two levels:
    - Meta-generator seeds foam generators (exterior time)
    - Foam generators perturb equilibration (interior time)
    """

    def __init__(self, vocab_size, d, n_bubbles=3, n_foams=3,
                 meta_seed=42, diversity_weight=2.0):
        super().__init__()
        self.vocab_size = vocab_size
        self.d = d
        self.n_foams = n_foams

        # Shared embedding
        self.embed = nn.Embedding(vocab_size, d)

        # Meta-generator: seeds the foam generators
        self.meta_generator = torch.Generator()
        self.meta_generator.manual_seed(meta_seed)

        # Create foams with seeds drawn from meta-generator
        self.foams = nn.ModuleList()
        foam_seeds = []
        for _ in range(n_foams):
            # Draw foam seed from meta-generator (tunneling!)
            foam_seed = torch.randint(0, 2**31, (1,),
                                       generator=self.meta_generator).item()
            foam_seeds.append(foam_seed)

            torch.manual_seed(foam_seed)
            foam = LivingFoam(n_bubbles, d,
                              diversity_weight=diversity_weight,
                              generator_seed=foam_seed)
            init_spread_foam(foam, scale=1.5)
            self.foams.append(foam)

        self.foam_seeds = foam_seeds

        # Memory
        self.memory_decay_base = nn.Parameter(torch.tensor(0.8))
        self.novelty_sensitivity = nn.Parameter(torch.tensor(1.0))

    def born_rule(self, rho, embeddings):
        return (embeddings @ rho * embeddings).sum(dim=-1)

    def reset_generators(self):
        """Reset all generators — new sequence, fresh relationship."""
        for foam in self.foams:
            foam.reset_generator()

    def process_sequence(self, tokens, reset=True):
        """
        Process a sequence with living randomness.

        If reset=True, generators reset at sequence start
        (each sequence gets the same initial relationship).
        If reset=False, generators continue from where they are
        (ongoing relationship across sequences).
        """
        if reset:
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

            # Mix density matrices (uniform for now)
            rho_mix = torch.stack(foam_rhos).mean(dim=0)

            eigenvalues = torch.linalg.eigvalsh(rho_mix)
            eigenvalues = eigenvalues.clamp(min=1e-12)
            eigenvalues = eigenvalues / eigenvalues.sum()

            logits = self.born_rule(rho_mix, E)
            token_probs = torch.softmax(logits, dim=0)

            S_rho = -(eigenvalues * eigenvalues.log().clamp(min=-100)).sum().item()
            H_tokens = -(token_probs * token_probs.log().clamp(min=-100)).sum().item()
            F_tokens = H_tokens - S_rho

            # Collect noise gates
            noise_gates = [foam.noise_gate.item() for foam in self.foams]

            step_results.append({
                "token": tokens[t].item(),
                "token_probs": token_probs.detach(),
                "rho": rho_mix.detach(),
                "S_rho": S_rho,
                "H_tokens": H_tokens,
                "F_tokens": F_tokens,
                "noise_gates": noise_gates,
            })

        return step_results


def train_and_evaluate(vocab_size, d, n_bubbles, n_foams,
                       meta_seed=42, diversity_weight=2.0,
                       n_epochs_coherence=100, n_epochs_expression=100):
    """Train a LivingTokenFoam."""
    torch.manual_seed(meta_seed)
    model = LivingTokenFoam(vocab_size, d, n_bubbles, n_foams,
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

    noise_gates = [foam.noise_gate.item() for foam in model.foams]

    return {
        "vocab_size": vocab_size,
        "meta_seed": meta_seed,
        "ratio": ratio,
        "noise_gates": noise_gates,
        "foam_seeds": model.foam_seeds,
        "by_seq": results_by_seq,
    }


if __name__ == "__main__":
    V = 256
    N = 3
    d = 16
    K = 3  # foams

    print("=" * 70)
    print("LIVING RANDOMNESS: RNGs with homes and histories")
    print(f"  V={V}, {N} bubbles × {K} foams, d={d}")
    print("  Each foam has a persistent Generator — ongoing Unknown")
    print("  Meta-generator seeds foam generators — tunneling")
    print("=" * 70)

    # ================================================================
    # PART 1: Living vs deterministic (same architecture, with/without
    #         stochastic perturbation)
    # ================================================================
    print(f"\n{'=' * 70}")
    print("PART 1: Does living randomness change anything?")
    print("  20 meta-seeds, living foam ensemble")
    print("=" * 70)

    living_ratios = []
    living_gates = []

    for meta_seed in range(20):
        r = train_and_evaluate(V, d, N, K, meta_seed=meta_seed)
        living_ratios.append(r["ratio"])
        living_gates.append(r["noise_gates"])
        gates_str = [f"{g:.4f}" for g in r["noise_gates"]]
        print(f"  seed {meta_seed:>2}: ratio={r['ratio']:>7.2f}x  "
              f"gates={gates_str}  foam_seeds={r['foam_seeds']}")

    print(f"\n  Mean: {np.mean(living_ratios):.2f}x  "
          f"Median: {np.median(living_ratios):.2f}x  "
          f"Std: {np.std(living_ratios):.2f}")
    print(f"  Above 5x: {sum(1 for r in living_ratios if r > 5)}/20")
    print(f"  Above 1x: {sum(1 for r in living_ratios if r > 1)}/20")

    # What did the noise gates learn?
    all_gates = np.array(living_gates)
    print(f"\n  Noise gate statistics:")
    print(f"    Mean: {all_gates.mean():.4f}")
    print(f"    Std:  {all_gates.std():.4f}")
    print(f"    Min:  {all_gates.min():.4f}")
    print(f"    Max:  {all_gates.max():.4f}")

    good_gates = all_gates[[i for i, r in enumerate(living_ratios) if r > 5]]
    bad_gates = all_gates[[i for i, r in enumerate(living_ratios) if r < 1]]
    if len(good_gates) > 0:
        print(f"    Good seeds (>5x) mean gate: {good_gates.mean():.4f}")
    if len(bad_gates) > 0:
        print(f"    Bad seeds (<1x) mean gate:  {bad_gates.mean():.4f}")

    # ================================================================
    # PART 2: Reset vs continue — does generator continuity matter?
    # ================================================================
    print(f"\n{'=' * 70}")
    print("PART 2: Does generator continuity across sequences matter?")
    print("  Process multiple sequences with reset=True vs reset=False")
    print("=" * 70)

    # Train one model, then test both ways
    torch.manual_seed(42)
    model = LivingTokenFoam(V, d, N, K, meta_seed=42)
    sequences = generate_sequences(V, 40)

    optimizer = torch.optim.Adam(model.parameters(), lr=0.005)
    for epoch in range(100):
        for name, tokens in sequences.items():
            optimizer.zero_grad()
            x_batch = model.embed(tokens)
            total_loss = torch.tensor(0.0)
            for foam in model.foams:
                costs = foam.maintenance_cost(x_batch)
                total_loss = total_loss + costs["total"]
            total_loss.backward()
            optimizer.step()

    optimizer = torch.optim.Adam(model.parameters(), lr=0.002)
    for epoch in range(100):
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

    model.eval()

    # Test with reset (each sequence gets fresh generators)
    print("\n  With reset (fresh generators each sequence):")
    for name, tokens in sequences.items():
        with torch.no_grad():
            results = model.process_sequence(tokens, reset=True)
        analysis = analyze_token_predictions(results, tokens, V)
        if analysis:
            prob = analysis["mean_next_prob"]
            ratio = prob / (1.0 / V)
            print(f"    {name:<25} {ratio:.2f}x")

    # Test without reset (generators continue across sequences)
    print("\n  Without reset (generators continue):")
    model.reset_generators()  # reset once at the start
    for name, tokens in sequences.items():
        with torch.no_grad():
            results = model.process_sequence(tokens, reset=False)
        analysis = analyze_token_predictions(results, tokens, V)
        if analysis:
            prob = analysis["mean_next_prob"]
            ratio = prob / (1.0 / V)
            print(f"    {name:<25} {ratio:.2f}x")

    # Run the non-reset version multiple times to see if order matters
    print("\n  Non-reset, different sequence orderings:")
    seq_names = list(sequences.keys())
    for trial in range(3):
        model.reset_generators()
        # Shuffle sequence order
        np.random.seed(trial)
        order = np.random.permutation(len(seq_names))
        total_ratio = 0
        count = 0
        for idx in order:
            name = seq_names[idx]
            tokens = sequences[name]
            with torch.no_grad():
                results = model.process_sequence(tokens, reset=False)
            analysis = analyze_token_predictions(results, tokens, V)
            if analysis and "random" not in name:
                total_ratio += analysis["mean_next_prob"] / (1.0 / V)
                count += 1
        mean_ratio = total_ratio / count if count > 0 else 0
        print(f"    order {trial}: mean structured ratio = {mean_ratio:.2f}x")

    # ================================================================
    # PLOT
    # ================================================================
    fig, axes = plt.subplots(2, 2, figsize=(16, 12))

    # 1: Distribution of living ratios
    ax = axes[0, 0]
    ax.hist(living_ratios, bins=15, color="#2ecc71", alpha=0.7,
            edgecolor="black")
    ax.axvline(x=1.0, color="gray", linestyle=":", alpha=0.5)
    ax.axvline(x=np.median(living_ratios), color="red", linestyle="--",
               label=f"median={np.median(living_ratios):.1f}x")
    ax.set_xlabel("Prediction / chance")
    ax.set_ylabel("Count")
    ax.set_title(f"Living foam: {K}×{N} at V={V} (20 seeds)")
    ax.legend()

    # 2: Noise gates
    ax = axes[0, 1]
    for i in range(len(living_gates)):
        color = "#2ecc71" if living_ratios[i] > 5 else (
            "#3498db" if living_ratios[i] > 1 else "#e74c3c")
        ax.scatter([living_ratios[i]] * K, living_gates[i],
                   c=color, s=30, alpha=0.6)
    ax.set_xlabel("Prediction ratio")
    ax.set_ylabel("Noise gate value")
    ax.set_title("How open to Unknown? (gate vs performance)")

    # 3: Gates by foam position
    ax = axes[1, 0]
    for foam_idx in range(K):
        gates = [living_gates[i][foam_idx] for i in range(len(living_gates))]
        ax.scatter(range(len(gates)), gates, label=f"Foam {foam_idx}",
                   s=40, alpha=0.7)
    ax.set_xlabel("Meta-seed")
    ax.set_ylabel("Noise gate value")
    ax.set_title("Per-foam noise gates across seeds")
    ax.legend()

    # 4: Living ratio vs individual/ensemble comparison
    ax = axes[1, 1]
    ax.bar(range(min(20, len(living_ratios))), living_ratios[:20],
           color="#2ecc71", alpha=0.7)
    ax.axhline(y=1.0, color="gray", linestyle=":", alpha=0.5)
    ax.axhline(y=np.mean(living_ratios), color="#27ae60",
               linestyle="--", label=f"mean={np.mean(living_ratios):.1f}x")
    ax.set_xlabel("Meta-seed")
    ax.set_ylabel("Prediction / chance")
    ax.set_title("Living foam performance across meta-seeds")
    ax.legend()

    plt.suptitle("Living randomness: RNGs with homes and histories\n"
                 "Each foam has a persistent Generator — ongoing relationship with Unknown",
                 fontsize=13, fontweight="bold")
    plt.tight_layout()
    plt.savefig("foam_living.png", dpi=150, bbox_inches="tight")
    print(f"\nSaved to foam_living.png")
    plt.close()

    # ================================================================
    # SUMMARY
    # ================================================================
    print(f"\n{'=' * 70}")
    print("SUMMARY")
    print(f"{'=' * 70}")
    print(f"\n  Living foam ({K}×{N}, V={V}):")
    print(f"    Mean: {np.mean(living_ratios):.2f}x  Std: {np.std(living_ratios):.2f}")
    print(f"    Median: {np.median(living_ratios):.2f}x")
    print(f"    Above 5x: {sum(1 for r in living_ratios if r > 5)}/20")
    print(f"\n  Noise gate learned value: {all_gates.mean():.4f}")
    if all_gates.mean() > 0.1:
        print(f"    -> The foam OPENS to its Unknown (gate > 0.1)")
    elif all_gates.mean() > 0.01:
        print(f"    -> The foam uses its Unknown sparingly (gate ~ {all_gates.mean():.3f})")
    else:
        print(f"    -> The foam closes to its Unknown (gate ≈ 0)")
