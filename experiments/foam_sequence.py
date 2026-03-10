"""
Foam + sequences: does self-coherent measurement naturally produce predictions?

The theory: "a self-coherent measurement process is generative on encounter
because encounter IS measurement. Useful outputs fall out of self-coherence,
not the other way around."

Test: feed the foam tokens one at a time. At each step, the foam's density
matrix changes in response. The eigenvalue distribution IS the response.

Questions:
1. Does the foam naturally differentiate structured from random sequences?
2. Does the foam's state carry predictive information about the next token?
3. Does this happen WITHOUT a prediction objective — purely from self-coherence?
"""

import torch
import torch.nn as nn
import numpy as np
import matplotlib.pyplot as plt
from foam import Foam


class SequenceFoam(nn.Module):
    """
    A foam that processes sequences token by token.

    Each token is embedded into the foam's measurement space.
    The foam maintains state across tokens (the density matrix evolves).
    The output at each step is the eigenvalue distribution of ρ.
    """

    def __init__(self, vocab_size: int, d: int, n_bubbles: int,
                 n_equilibrium_steps: int = 5):
        super().__init__()
        self.vocab_size = vocab_size
        self.d = d

        # Token embedding
        self.embed = nn.Embedding(vocab_size, d)

        # The foam
        self.foam = Foam(n_bubbles, d, n_equilibrium_steps)

        # Memory dynamics: novelty-modulated decay
        # Base decay rate (sigmoid applied at runtime)
        self.memory_decay_base = nn.Parameter(torch.tensor(0.8))
        # How strongly novelty reduces decay (more novelty → more responsive)
        self.novelty_sensitivity = nn.Parameter(torch.tensor(1.0))

    def process_sequence(self, tokens: torch.Tensor):
        """
        Process a sequence of tokens through the foam.

        tokens: [seq_len] — integer token IDs
        returns: dict with per-step foam states, eigenvalue distributions, etc.
        """
        seq_len = tokens.shape[0]
        device = tokens.device

        # Track state across steps
        memory = torch.zeros(self.foam.n_bubbles, self.d, device=device)
        step_results = []

        for t in range(seq_len):
            # Embed token
            x = self.embed(tokens[t:t+1])  # [1, d]

            # Novelty signal: how different is this input from the memory?
            memory_mean = memory.mean(dim=0, keepdim=True)  # [1, d]
            mem_norm = memory_mean.norm() + 1e-10
            x_norm = x.norm() + 1e-10
            if mem_norm > 1e-8:
                novelty = 1 - (x * memory_mean).sum() / (x_norm * mem_norm)
            else:
                novelty = torch.tensor(1.0, device=device)  # first token is maximally novel
            # novelty ∈ [0, 2] (cosine distance), typically [0, 1]

            # Novelty-modulated decay: high novelty → low decay → more responsive
            sensitivity = self.novelty_sensitivity.abs()
            decay = torch.sigmoid(self.memory_decay_base - sensitivity * novelty)

            # Combine with memory
            x_with_memory = x + decay * memory_mean

            # Process through foam
            result = self.foam.forward(x_with_memory)

            # Update memory with novelty-modulated decay
            eq = result["equilibrium"][0]  # [N, d]
            memory = decay * memory + (1 - decay) * eq

            # Eigenvalue distribution (the foam's "response")
            output_dist = result["output_dist"][0]  # [d]

            # Also compute the density matrix's structure
            rho = result["rho"][0]  # [d, d]

            step_results.append({
                "token": tokens[t].item(),
                "output_dist": output_dist.detach(),
                "rho": rho.detach(),
                "S_rho": -(output_dist * output_dist.log().clamp(min=-100)).sum().item(),
                "novelty": novelty.item(),
                "decay": decay.item(),
                "equilibrium": eq.detach(),
                "surface_tension": result["surface_tension"].detach(),
            })

        return step_results


def generate_sequences(vocab_size: int, seq_len: int):
    """Generate test sequences of varying structure."""
    sequences = {}

    # Periodic: ABCABC...
    period = torch.tensor([0, 1, 2] * (seq_len // 3 + 1))[:seq_len]
    sequences["periodic (ABC...)"] = period

    # Periodic longer: ABCDABCD...
    period4 = torch.tensor([0, 1, 2, 3] * (seq_len // 4 + 1))[:seq_len]
    sequences["periodic (ABCD...)"] = period4

    # Monotone: AAAA...
    sequences["monotone (AAA...)"] = torch.zeros(seq_len, dtype=torch.long)

    # Alternating: ABAB...
    alt = torch.tensor([0, 1] * (seq_len // 2 + 1))[:seq_len]
    sequences["alternating (AB...)"] = alt

    # Counting: 0,1,2,3,4,...
    sequences["counting (0,1,2...)"] = torch.arange(seq_len) % vocab_size

    # Random
    torch.manual_seed(42)
    sequences["random"] = torch.randint(0, vocab_size, (seq_len,))

    # Random with structure: first half one pattern, second half another
    mixed = torch.cat([
        torch.zeros(seq_len // 2, dtype=torch.long),
        torch.ones(seq_len // 2, dtype=torch.long) * 2,
    ])
    sequences["phase shift (A→C)"] = mixed

    # Fibonacci-like: each token = (t-1 + t-2) mod vocab
    fib = [0, 1]
    for i in range(2, seq_len):
        fib.append((fib[-1] + fib[-2]) % vocab_size)
    sequences["fibonacci mod V"] = torch.tensor(fib)

    return sequences


def analyze_predictiveness(step_results, tokens, vocab_size):
    """
    Does the foam's state at step t carry information about token t+1?

    Metrics:
    - JSD: Jensen-Shannon divergence between consecutive eigenvalue distributions.
      (Proper distribution distance, unlike cosine similarity which is structurally
      near 1.0 for non-negative vectors that sum to 1.)
    - State distance: cosine distance between full equilibrium states [N, d].
      This is the richer signal — the eigenvalue distribution compresses away
      the bubble structure.
    """
    dists = torch.stack([r["output_dist"] for r in step_results])  # [T, d]
    equil = torch.stack([r["equilibrium"] for r in step_results])  # [T, N, d]

    if len(dists) < 2:
        return {"mean_jsd": 0, "jsd_trace": [], "mean_state_dist": 0, "state_dist_trace": []}

    # Jensen-Shannon divergence between consecutive eigenvalue distributions
    p = dists[:-1]  # [T-1, d]
    q = dists[1:]   # [T-1, d]
    m = 0.5 * (p + q)
    # KL(p||m) and KL(q||m), handling zeros
    kl_pm = (p * (p / (m + 1e-12) + 1e-12).log()).sum(dim=-1)
    kl_qm = (q * (q / (m + 1e-12) + 1e-12).log()).sum(dim=-1)
    jsd = 0.5 * (kl_pm + kl_qm)

    # Full state cosine distance (flatten [N, d] → [N*d])
    e1 = equil[:-1].flatten(start_dim=1)  # [T-1, N*d]
    e2 = equil[1:].flatten(start_dim=1)   # [T-1, N*d]
    cos_sim = (e1 * e2).sum(dim=-1) / (e1.norm(dim=-1) * e2.norm(dim=-1) + 1e-10)
    state_dist = 1 - cos_sim

    return {
        "mean_jsd": jsd.mean().item(),
        "jsd_trace": jsd.tolist(),
        "mean_state_dist": state_dist.mean().item(),
        "state_dist_trace": state_dist.tolist(),
    }


if __name__ == "__main__":
    vocab_size = 8
    d = 16
    n_bubbles = 5
    seq_len = 40

    print(f"Foam: {n_bubbles} bubbles, d={d}, vocab={vocab_size}")

    # Initialize
    model = SequenceFoam(vocab_size, d, n_bubbles, n_equilibrium_steps=5)

    # Train on maintenance cost (self-coherence, NOT prediction)
    print("\nTraining foam on self-coherence (no prediction objective)...")
    optimizer = torch.optim.Adam(model.parameters(), lr=0.005)

    # Training data: diverse sequences
    train_seqs = generate_sequences(vocab_size, seq_len)

    for epoch in range(200):
        total_loss = 0
        for name, tokens in train_seqs.items():
            optimizer.zero_grad()
            # Just run the foam and compute maintenance cost on each step
            x_batch = model.embed(tokens)  # [seq_len, d]
            costs = model.foam.maintenance_cost(x_batch)
            loss = costs["total"]
            loss.backward()
            optimizer.step()
            total_loss += loss.item()

        if epoch % 50 == 0 or epoch == 199:
            print(f"  epoch {epoch:>4}: total_loss={total_loss:.4f}")

    # Now test: process sequences and analyze
    print(f"\n{'=' * 70}")
    print("SEQUENCE ANALYSIS (after self-coherence training)")
    print(f"{'=' * 70}")

    model.eval()
    sequences = generate_sequences(vocab_size, seq_len)

    all_analyses = {}

    print(f"\n{'Sequence':<25} {'Mean S(ρ)':>10} {'Std S(ρ)':>10} {'JSD':>8} {'StateDist':>10} {'Novelty':>8}")
    print("-" * 74)

    for name, tokens in sequences.items():
        with torch.no_grad():
            results = model.process_sequence(tokens)

        analysis = analyze_predictiveness(results, tokens, vocab_size)
        s_values = [r["S_rho"] for r in results]
        novelty_values = [r["novelty"] for r in results]

        print(f"  {name:<23} {np.mean(s_values):>10.4f} {np.std(s_values):>10.4f} "
              f"{analysis['mean_jsd']:>8.4f} {analysis['mean_state_dist']:>10.4f} "
              f"{np.mean(novelty_values):>8.4f}")

        all_analyses[name] = {
            "results": results,
            "analysis": analysis,
            "s_values": s_values,
            "novelty_values": novelty_values,
        }

    # Key test: does the foam differentiate structured from random?
    structured_s = []
    random_s = []
    for name, data in all_analyses.items():
        if "random" in name:
            random_s.extend(data["s_values"])
        else:
            structured_s.extend(data["s_values"])

    print(f"\n{'=' * 70}")
    print("VERDICT: Does self-coherence differentiate structure from randomness?")
    print(f"{'=' * 70}")
    print(f"  Structured sequences — mean S(ρ): {np.mean(structured_s):.4f} ± {np.std(structured_s):.4f}")
    print(f"  Random sequences — mean S(ρ):     {np.mean(random_s):.4f} ± {np.std(random_s):.4f}")

    if abs(np.mean(structured_s) - np.mean(random_s)) > 0.01:
        print(f"  ✓ The foam's internal state differs for structured vs random input")
    else:
        print(f"  ✗ No differentiation — the foam responds the same to both")

    # State dynamics: how much does the foam change between tokens?
    print(f"\n  State dynamics (JSD of eigenvalues, cosine distance of full state):")
    for name, data in all_analyses.items():
        jsd = data["analysis"]["mean_jsd"]
        sd = data["analysis"]["mean_state_dist"]
        print(f"    {name:<23} JSD={jsd:.4f}  StateDist={sd:.4f}")
    print(f"  (higher = more dynamic response to input)")
    print(f"  (monotone should be ~0, periodic should show rhythmic variation)")

    # Plot
    fig, axes = plt.subplots(2, 2, figsize=(16, 12))

    # 1: S(ρ) traces for each sequence
    ax = axes[0, 0]
    for name, data in all_analyses.items():
        style = "--" if "random" in name else "-"
        alpha = 0.5 if "random" in name else 1.0
        ax.plot(data["s_values"], style, label=name, alpha=alpha, linewidth=1.5)
    ax.set_xlabel("Token position")
    ax.set_ylabel("S(ρ)")
    ax.set_title("Foam entropy across sequence")
    ax.legend(fontsize=7)

    # 2: State distance traces (full equilibrium state, not just eigenvalues)
    ax = axes[0, 1]
    for name, data in all_analyses.items():
        trace = data["analysis"]["state_dist_trace"]
        if trace:
            style = "--" if "random" in name else "-"
            alpha = 0.5 if "random" in name else 1.0
            ax.plot(trace, style, label=name, alpha=alpha, linewidth=1.5)
    ax.set_xlabel("Token position")
    ax.set_ylabel("Cosine distance from previous step")
    ax.set_title("How much does the foam state change per token?")
    ax.legend(fontsize=7)

    # 3: Bar chart of mean S by sequence type
    ax = axes[1, 0]
    names = list(all_analyses.keys())
    s_means = [np.mean(all_analyses[n]["s_values"]) for n in names]
    colors = ["#95a5a6" if "random" in n else "#3498db" for n in names]
    ax.barh(range(len(names)), s_means, color=colors)
    ax.set_yticks(range(len(names)))
    ax.set_yticklabels(names, fontsize=8)
    ax.set_xlabel("Mean S(ρ)")
    ax.set_title("Internal entropy by sequence type (gray=random)")
    ax.invert_yaxis()

    # 4: Novelty traces — does the foam detect structure vs randomness?
    ax = axes[1, 1]
    for name, data in all_analyses.items():
        style = "--" if "random" in name else "-"
        alpha = 0.5 if "random" in name else 1.0
        ax.plot(data["novelty_values"], style, label=name, alpha=alpha, linewidth=1.5)
    ax.set_xlabel("Token position")
    ax.set_ylabel("Novelty (cosine distance from memory)")
    ax.set_title("Novelty signal across sequence")
    ax.legend(fontsize=7)

    plt.tight_layout()
    plt.savefig("foam_sequence.png", dpi=150, bbox_inches="tight")
    print(f"\nSaved to foam_sequence.png")
    plt.close()
