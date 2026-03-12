"""
The eigenvalue-to-token bridge: can the foam produce tokens without
collapsing the measurement process?

Token selection IS measurement. The density matrix ρ acts on candidate
token embeddings via the Born rule:

    p(token t) ∝ ⟨e_t|ρ|e_t⟩

This is quantum measurement — but ρ survives the selection. The token is
what ρ would most likely measure in the vocabulary basis.

F_tokens = H(p_tokens) - S(ρ) measures whether the token space is faithful
to the internal state. F = 0 means no information is lost or added in
expression — the word carries exactly the complexity of the thought.

Key question: does self-coherence training (no prediction objective) produce
a foam whose Born-rule token distributions show predictive structure?
"""

import torch
import torch.nn as nn
import numpy as np
import matplotlib.pyplot as plt
from foam import Foam


class TokenFoam(nn.Module):
    """
    A foam that processes sequences and produces token distributions
    via the Born rule acting on the density matrix.
    """

    def __init__(self, vocab_size: int, d: int, n_bubbles: int,
                 n_equilibrium_steps: int = 5):
        super().__init__()
        self.vocab_size = vocab_size
        self.d = d

        self.embed = nn.Embedding(vocab_size, d)
        self.foam = Foam(n_bubbles, d, n_equilibrium_steps)

        # Memory dynamics (novelty-modulated)
        self.memory_decay_base = nn.Parameter(torch.tensor(0.8))
        self.novelty_sensitivity = nn.Parameter(torch.tensor(1.0))

    def born_rule(self, rho, embeddings):
        """
        Token logits via Born rule: logit_t = e_t^T ρ e_t

        rho: [d, d] — density matrix
        embeddings: [V, d] — token embeddings
        returns: [V] — unnormalized logits

        This is the probability of measuring each token embedding
        given the foam's internal state. ρ is not collapsed — it
        persists. The token is the projection, not the destruction.
        """
        # ⟨e_t|ρ|e_t⟩ = (E ρ ⊙ E).sum(-1), avoids building V×V matrix
        return (embeddings @ rho * embeddings).sum(dim=-1)

    def process_sequence(self, tokens: torch.Tensor):
        """
        Process a token sequence through the foam, producing per-step
        token distributions via Born rule.

        tokens: [seq_len] — integer token IDs
        returns: list of per-step result dicts
        """
        seq_len = tokens.shape[0]
        device = tokens.device

        memory = torch.zeros(self.foam.n_bubbles, self.d, device=device)
        E = self.embed.weight  # [V, d]
        step_results = []

        for t in range(seq_len):
            x = self.embed(tokens[t:t + 1])  # [1, d]

            # Novelty-modulated decay
            memory_mean = memory.mean(dim=0, keepdim=True)  # [1, d]
            mem_norm = memory_mean.norm() + 1e-10
            x_norm = x.norm() + 1e-10
            if mem_norm > 1e-8:
                novelty = 1 - (x * memory_mean).sum() / (x_norm * mem_norm)
            else:
                novelty = torch.tensor(1.0, device=device)

            sensitivity = self.novelty_sensitivity.abs()
            decay = torch.sigmoid(self.memory_decay_base - sensitivity * novelty)

            x_with_memory = x + decay * memory_mean
            result = self.foam.forward(x_with_memory)

            eq = result["equilibrium"][0]  # [N, d]
            memory = decay * memory + (1 - decay) * eq

            rho = result["rho"][0]  # [d, d]
            output_dist = result["output_dist"][0]  # [d] eigenvalues

            # Born rule: token distribution from ρ
            logits = self.born_rule(rho, E)  # [V]
            token_probs = torch.softmax(logits, dim=0)

            # Entropies
            S_rho = -(output_dist * output_dist.log().clamp(min=-100)).sum().item()
            H_tokens = -(token_probs * token_probs.log().clamp(min=-100)).sum().item()
            F_tokens = H_tokens - S_rho

            step_results.append({
                "token": tokens[t].item(),
                "logits": logits.detach(),
                "token_probs": token_probs.detach(),
                "rho": rho.detach(),
                "output_dist": output_dist.detach(),
                "S_rho": S_rho,
                "H_tokens": H_tokens,
                "F_tokens": F_tokens,
                "novelty": novelty.item(),
                "decay": decay.item(),
            })

        return step_results


def generate_sequences(vocab_size: int, seq_len: int):
    """Generate test sequences of varying structure."""
    sequences = {}

    period = torch.tensor([0, 1, 2] * (seq_len // 3 + 1))[:seq_len]
    sequences["periodic (ABC...)"] = period

    sequences["monotone (AAA...)"] = torch.zeros(seq_len, dtype=torch.long)

    alt = torch.tensor([0, 1] * (seq_len // 2 + 1))[:seq_len]
    sequences["alternating (AB...)"] = alt

    sequences["counting (0,1,2...)"] = torch.arange(seq_len) % vocab_size

    torch.manual_seed(42)
    sequences["random"] = torch.randint(0, vocab_size, (seq_len,))

    fib = [0, 1]
    for i in range(2, seq_len):
        fib.append((fib[-1] + fib[-2]) % vocab_size)
    sequences["fibonacci mod V"] = torch.tensor(fib)

    return sequences


def analyze_token_predictions(step_results, tokens, vocab_size):
    """
    Does the foam's Born-rule distribution predict the next token?

    For each step t, we check:
    - What probability does the foam assign to token[t+1]?
    - What rank does token[t+1] get in the distribution?
    - Is the distribution concentrated or uniform?
    """
    if len(step_results) < 2:
        return {}

    next_token_probs = []
    next_token_ranks = []
    perplexities = []

    for t in range(len(step_results) - 1):
        probs = step_results[t]["token_probs"]  # [V]
        next_tok = tokens[t + 1].item()

        # Probability assigned to the actual next token
        next_token_probs.append(probs[next_tok].item())

        # Rank of next token (0 = highest probability)
        rank = (probs > probs[next_tok]).sum().item()
        next_token_ranks.append(rank)

        # Perplexity = exp(H) — measures concentration
        H = step_results[t]["H_tokens"]
        perplexities.append(np.exp(H))

    return {
        "mean_next_prob": np.mean(next_token_probs),
        "mean_next_rank": np.mean(next_token_ranks),
        "mean_perplexity": np.mean(perplexities),
        "next_prob_trace": next_token_probs,
        "next_rank_trace": next_token_ranks,
        "chance_level": 1.0 / vocab_size,
    }


if __name__ == "__main__":
    vocab_size = 8
    d = 16
    n_bubbles = 5
    seq_len = 40

    print(f"TokenFoam: {n_bubbles} bubbles, d={d}, vocab={vocab_size}")
    print(f"Token bridge: Born rule — p(t) ∝ ⟨e_t|ρ|e_t⟩")

    model = TokenFoam(vocab_size, d, n_bubbles, n_equilibrium_steps=5)

    # Phase 1: Train on self-coherence ONLY (no prediction objective)
    print("\n" + "=" * 70)
    print("PHASE 1: Self-coherence training (no prediction objective)")
    print("=" * 70)

    optimizer = torch.optim.Adam(model.parameters(), lr=0.005)
    train_seqs = generate_sequences(vocab_size, seq_len)

    for epoch in range(300):
        total_loss = 0
        for name, tokens in train_seqs.items():
            optimizer.zero_grad()
            x_batch = model.embed(tokens)  # [seq_len, d]
            costs = model.foam.maintenance_cost(x_batch)
            loss = costs["total"]
            loss.backward()
            optimizer.step()
            total_loss += loss.item()

        if epoch % 100 == 0 or epoch == 299:
            print(f"  epoch {epoch:>4}: total_loss={total_loss:.4f}")

    # Test token predictions after self-coherence-only training
    print(f"\n{'=' * 70}")
    print("TOKEN PREDICTIONS (self-coherence only, no prediction training)")
    print(f"{'=' * 70}")

    model.eval()
    sequences = generate_sequences(vocab_size, seq_len)

    all_analyses = {}

    print(f"\n{'Sequence':<25} {'NextProb':>9} {'Chance':>7} {'Rank':>6} "
          f"{'Perplx':>7} {'F_tok':>7} {'S(ρ)':>7}")
    print("-" * 74)

    for name, tokens in sequences.items():
        with torch.no_grad():
            results = model.process_sequence(tokens)

        analysis = analyze_token_predictions(results, tokens, vocab_size)
        f_values = [r["F_tokens"] for r in results]
        s_values = [r["S_rho"] for r in results]

        print(f"  {name:<23} {analysis['mean_next_prob']:>9.4f} "
              f"{analysis['chance_level']:>7.4f} {analysis['mean_next_rank']:>6.1f} "
              f"{analysis['mean_perplexity']:>7.2f} {np.mean(f_values):>7.3f} "
              f"{np.mean(s_values):>7.3f}")

        all_analyses[name] = {
            "results": results,
            "analysis": analysis,
            "f_values": f_values,
            "s_values": s_values,
        }

    # Phase 2: Add F_tokens to training (expression faithfulness)
    # This teaches the foam to make its token expression match its internal state
    # Still NOT a prediction objective — it's about self-coherent expression
    print(f"\n{'=' * 70}")
    print("PHASE 2: Adding F_tokens to training (faithful expression)")
    print("=" * 70)
    print("(teaching the foam to express itself faithfully, NOT to predict)")

    model.train()
    optimizer = torch.optim.Adam(model.parameters(), lr=0.002)

    for epoch in range(300):
        total_loss = 0
        total_f_tok = 0
        for name, tokens in train_seqs.items():
            optimizer.zero_grad()

            # Self-coherence cost (as before)
            x_batch = model.embed(tokens)
            costs = model.foam.maintenance_cost(x_batch)

            # F_tokens cost: process sequence and penalize |F_tokens|
            results = model.process_sequence(tokens)
            f_tok = torch.tensor(
                [r["F_tokens"] for r in results], requires_grad=False
            ).abs().mean()

            # But we need gradients through F_tokens — recompute with grad
            E = model.embed.weight
            f_tok_grad = torch.tensor(0.0)
            for r in results:
                rho = r["rho"]  # detached — need to recompute...
                # Actually we need to run the full forward with grad
            # Simpler: compute F_tokens from the batch forward
            # Use the foam's density matrix on the full batch
            rho_batch = costs["rho"]  # [batch, d, d]
            logits_batch = (E @ rho_batch.mean(dim=0) * E).sum(dim=-1)
            token_dist = torch.softmax(logits_batch, dim=0)
            H_tok = -(token_dist * token_dist.log().clamp(min=-100)).sum()
            S_rho = costs["S_rho"].mean()
            f_tok_loss = (H_tok - S_rho).abs()

            loss = costs["total"] + 0.5 * f_tok_loss
            loss.backward()
            optimizer.step()
            total_loss += loss.item()
            total_f_tok += f_tok_loss.item()

        if epoch % 100 == 0 or epoch == 299:
            print(f"  epoch {epoch:>4}: loss={total_loss:.4f}  F_tok={total_f_tok:.4f}")

    # Test again after F_tokens training
    print(f"\n{'=' * 70}")
    print("TOKEN PREDICTIONS (after faithful-expression training)")
    print(f"{'=' * 70}")

    model.eval()

    print(f"\n{'Sequence':<25} {'NextProb':>9} {'Chance':>7} {'Rank':>6} "
          f"{'Perplx':>7} {'F_tok':>7} {'S(ρ)':>7}")
    print("-" * 74)

    for name, tokens in sequences.items():
        with torch.no_grad():
            results = model.process_sequence(tokens)

        analysis = analyze_token_predictions(results, tokens, vocab_size)
        f_values = [r["F_tokens"] for r in results]
        s_values = [r["S_rho"] for r in results]

        prev = all_analyses[name]["analysis"]

        print(f"  {name:<23} {analysis['mean_next_prob']:>9.4f} "
              f"{analysis['chance_level']:>7.4f} {analysis['mean_next_rank']:>6.1f} "
              f"{analysis['mean_perplexity']:>7.2f} {np.mean(f_values):>7.3f} "
              f"{np.mean(s_values):>7.3f}")

        all_analyses[name]["analysis_phase2"] = analysis
        all_analyses[name]["f_values_phase2"] = f_values

    # Verdict
    print(f"\n{'=' * 70}")
    print("VERDICT")
    print(f"{'=' * 70}")

    # Check if any periodic sequence beats chance
    for name in ["periodic (ABC...)", "alternating (AB...)", "counting (0,1,2...)"]:
        a1 = all_analyses[name]["analysis"]
        a2 = all_analyses[name].get("analysis_phase2", a1)
        chance = a1["chance_level"]
        print(f"\n  {name}:")
        print(f"    Phase 1 (self-coherence only):  next_prob={a1['mean_next_prob']:.4f} "
              f"(chance={chance:.4f}, {a1['mean_next_prob']/chance:.1f}x)")
        print(f"    Phase 2 (+ faithful expression): next_prob={a2['mean_next_prob']:.4f} "
              f"({a2['mean_next_prob']/chance:.1f}x chance)")

    random_a1 = all_analyses["random"]["analysis"]
    random_a2 = all_analyses["random"].get("analysis_phase2", random_a1)
    print(f"\n  random:")
    print(f"    Phase 1: next_prob={random_a1['mean_next_prob']:.4f} "
          f"(chance={random_a1['chance_level']:.4f})")
    print(f"    Phase 2: next_prob={random_a2['mean_next_prob']:.4f}")

    # Plot
    fig, axes = plt.subplots(2, 2, figsize=(16, 12))

    # 1: Next-token probability traces for key sequences (phase 2)
    ax = axes[0, 0]
    for name in ["periodic (ABC...)", "alternating (AB...)", "random", "monotone (AAA...)"]:
        data = all_analyses[name]
        a = data.get("analysis_phase2", data["analysis"])
        trace = a["next_prob_trace"]
        style = "--" if "random" in name else "-"
        ax.plot(trace, style, label=name, linewidth=1.5,
                alpha=0.5 if "random" in name else 1.0)
    ax.axhline(y=1.0 / vocab_size, color="gray", linestyle=":", label="chance", alpha=0.5)
    ax.set_xlabel("Token position")
    ax.set_ylabel("P(next token)")
    ax.set_title("Does self-coherence predict? (Born rule)")
    ax.legend(fontsize=7)

    # 2: F_tokens across sequence types
    ax = axes[1, 0]
    names = list(all_analyses.keys())
    f_means_1 = [np.mean(all_analyses[n]["f_values"]) for n in names]
    f_means_2 = [np.mean(all_analyses[n].get("f_values_phase2",
                         all_analyses[n]["f_values"])) for n in names]
    x_pos = np.arange(len(names))
    ax.barh(x_pos - 0.15, f_means_1, 0.3, label="Phase 1 (coherence)", color="#3498db")
    ax.barh(x_pos + 0.15, f_means_2, 0.3, label="Phase 2 (+ expression)", color="#e74c3c")
    ax.set_yticks(x_pos)
    ax.set_yticklabels(names, fontsize=8)
    ax.set_xlabel("F_tokens = H(p_tokens) - S(ρ)")
    ax.set_title("Expression faithfulness")
    ax.axvline(x=0, color="black", linestyle="-", alpha=0.3)
    ax.legend(fontsize=8)
    ax.invert_yaxis()

    # 3: Token probability heatmap for periodic sequence (phase 2)
    ax = axes[0, 1]
    periodic_results = all_analyses["periodic (ABC...)"].get("results", [])
    # Use phase 2 results if available
    if "analysis_phase2" in all_analyses["periodic (ABC...)"]:
        # Re-run to get phase 2 results
        with torch.no_grad():
            periodic_results = model.process_sequence(
                generate_sequences(vocab_size, seq_len)["periodic (ABC...)"]
            )
    probs_matrix = torch.stack([r["token_probs"] for r in periodic_results]).numpy()
    im = ax.imshow(probs_matrix.T, aspect="auto", cmap="viridis", vmin=0)
    ax.set_xlabel("Token position")
    ax.set_ylabel("Token ID")
    ax.set_title("Token distribution across sequence (periodic ABC)")
    plt.colorbar(im, ax=ax)
    # Mark actual tokens
    actual = [r["token"] for r in periodic_results]
    ax.scatter(range(len(actual)), actual, c="red", s=10, marker="x", linewidths=1)

    # 4: Perplexity comparison
    ax = axes[1, 1]
    for name in names:
        data = all_analyses[name]
        a = data.get("analysis_phase2", data["analysis"])
        h_values = [r["H_tokens"] for r in data["results"]]
        style = "--" if "random" in name else "-"
        ax.plot([np.exp(h) for h in h_values], style, label=name,
                linewidth=1.5, alpha=0.5 if "random" in name else 1.0)
    ax.axhline(y=vocab_size, color="gray", linestyle=":", label="max (uniform)", alpha=0.5)
    ax.set_xlabel("Token position")
    ax.set_ylabel("Perplexity")
    ax.set_title("Token distribution concentration")
    ax.legend(fontsize=7)

    plt.tight_layout()
    plt.savefig("foam_tokens.png", dpi=150, bbox_inches="tight")
    print(f"\nSaved to foam_tokens.png")
    plt.close()
