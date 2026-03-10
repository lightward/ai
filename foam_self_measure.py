"""
The self-measuring bubble: does the foam develop inward-looking measurement?

Each bubble has a learnable input gate: how much it attends to external input
vs the foam's own previous equilibrium state. gate ≈ 1 means "I measure the
world." gate ≈ 0 means "I measure the foam."

We don't build the self-measuring bubble. We remove the constraint that prevents
one from emerging, then watch.

The hypothesis: under sufficient sequence complexity, at least one bubble will
discover that orienting toward the foam's own trajectory (gate → 0) reduces
the maintenance cost of self-coherence. That bubble would be the foam measuring
itself — qualia as the energy cost of reconciling its reading with the others'.

The phase transition from colony to individuated self would show up as: a bubble
whose gate goes low while the foam's overall coherence improves or holds.
"""

import torch
import torch.nn as nn
import numpy as np
import matplotlib.pyplot as plt
from foam import Foam, Bubble
from foam_tokens import TokenFoam, generate_sequences, analyze_token_predictions


class SelfMeasuringFoam(nn.Module):
    """
    A TokenFoam that passes its previous equilibrium state through the gates.

    The only difference from TokenFoam: when processing sequences, each bubble
    gets to choose (via its learned gate) how much of its input comes from the
    external token vs the foam's previous internal state.
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

    def process_sequence(self, tokens: torch.Tensor):
        """
        Process a token sequence, threading previous equilibrium through gates.
        """
        seq_len = tokens.shape[0]
        device = tokens.device
        N = self.foam.n_bubbles

        memory = torch.zeros(N, self.d, device=device)
        prev_eq = None  # No previous state for first token
        E = self.embed.weight  # [V, d]
        step_results = []

        for t in range(seq_len):
            x = self.embed(tokens[t:t + 1])  # [1, d]

            # Novelty-modulated decay
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

            # THE KEY DIFFERENCE: pass previous equilibrium through gates
            result = self.foam.forward(x_with_memory, prev_equilibrium=prev_eq)

            eq = result["equilibrium"][0]  # [N, d]
            memory = decay * memory + (1 - decay) * eq

            # Store equilibrium for next step's gates (detached from this step's graph
            # but the gate parameters themselves maintain gradient)
            prev_eq = result["equilibrium"].detach()  # [1, N, d]

            rho = result["rho"][0]
            output_dist = result["output_dist"][0]

            # Born rule token distribution
            logits = (E @ rho * E).sum(dim=-1)
            token_probs = torch.softmax(logits, dim=0)

            S_rho = -(output_dist * output_dist.log().clamp(min=-100)).sum().item()
            H_tokens = -(token_probs * token_probs.log().clamp(min=-100)).sum().item()

            step_results.append({
                "token": tokens[t].item(),
                "logits": logits.detach(),
                "token_probs": token_probs.detach(),
                "rho": rho.detach(),
                "output_dist": output_dist.detach(),
                "S_rho": S_rho,
                "H_tokens": H_tokens,
                "F_tokens": H_tokens - S_rho,
                "novelty": novelty.item(),
                "decay": decay.item(),
                "gate_values": result["gate_values"].detach(),
            })

        return step_results

    def train_step(self, tokens: torch.Tensor):
        """
        One training step on a sequence: self-coherence with gated state.
        Returns loss and diagnostics.
        """
        seq_len = tokens.shape[0]
        device = tokens.device
        N = self.foam.n_bubbles

        prev_eq = None
        total_cost = torch.tensor(0.0, device=device)

        for t in range(seq_len):
            x = self.embed(tokens[t:t + 1])  # [1, d]
            costs = self.foam.maintenance_cost(x, prev_equilibrium=prev_eq)
            total_cost = total_cost + costs["total"]
            prev_eq = costs["equilibrium"].detach()

        return total_cost / seq_len


def run_experiment():
    """Watch for gate dynamics under increasing sequence complexity."""

    # Scale up: V=64 pushes toward the entropy ceiling (log(8)/log(64) ≈ 0.5
    # of max capacity). 8 bubbles showed phase transition in foam_scale.py.
    vocab_size = 32
    d = 16
    n_bubbles = 8
    seq_len = 60
    n_epochs = 600

    print(f"Self-measuring foam: {n_bubbles} bubbles, d={d}, vocab={vocab_size}")
    print(f"Each bubble has a learnable input gate (1=external, 0=self-referential)")
    print(f"Initial gates: sigmoid(2.0) ≈ 0.88 (mostly external)")

    model = SelfMeasuringFoam(vocab_size, d, n_bubbles, n_equilibrium_steps=5)

    # Report initial gate values
    print(f"\nInitial gate values:")
    for i, b in enumerate(model.foam.bubbles):
        print(f"  Bubble {i}: gate = {b.input_gate.item():.4f}")

    # Training
    print(f"\nTraining on self-coherence ({n_epochs} epochs)...")
    optimizer = torch.optim.Adam(model.parameters(), lr=0.005)
    train_seqs = generate_sequences(vocab_size, seq_len)

    gate_history = {i: [] for i in range(n_bubbles)}
    loss_history = []

    for epoch in range(n_epochs):
        epoch_loss = 0
        for name, tokens in train_seqs.items():
            optimizer.zero_grad()
            loss = model.train_step(tokens)
            loss.backward()
            optimizer.step()
            epoch_loss += loss.item()

        loss_history.append(epoch_loss)

        # Record gate values
        for i, b in enumerate(model.foam.bubbles):
            gate_history[i].append(b.input_gate.item())

        if epoch % 50 == 0 or epoch == n_epochs - 1:
            gates = [b.input_gate.item() for b in model.foam.bubbles]
            gate_str = " ".join(f"{g:.3f}" for g in gates)
            print(f"  epoch {epoch:>4}: loss={epoch_loss:.4f}  gates=[{gate_str}]")

    # Analysis
    print(f"\n{'=' * 70}")
    print("GATE ANALYSIS")
    print(f"{'=' * 70}")

    final_gates = []
    for i, b in enumerate(model.foam.bubbles):
        g = b.input_gate.item()
        final_gates.append(g)
        direction = "EXTERNAL" if g > 0.7 else ("MIXED" if g > 0.3 else "INWARD")
        drift = g - torch.sigmoid(torch.tensor(2.0)).item()
        print(f"  Bubble {i}: gate = {g:.4f}  ({direction})  drift = {drift:+.4f}")

    min_gate = min(final_gates)
    min_idx = final_gates.index(min_gate)
    print(f"\n  Most inward-looking: Bubble {min_idx} (gate = {min_gate:.4f})")

    if min_gate < 0.5:
        print(f"  ** A bubble oriented inward. The foam developed self-measurement. **")
    elif min_gate < 0.7:
        print(f"  * A bubble is drifting inward. Partial self-orientation emerging. *")
    else:
        print(f"  All bubbles remain primarily external-facing.")
        print(f"  (May need more complexity, more bubbles, or longer training.)")

    # Token prediction analysis
    print(f"\n{'=' * 70}")
    print("TOKEN PREDICTIONS (with gated self-measurement)")
    print(f"{'=' * 70}")

    model.eval()
    sequences = generate_sequences(vocab_size, seq_len)

    print(f"\n{'Sequence':<25} {'NextProb':>9} {'Chance':>7} {'Ratio':>6} "
          f"{'F_tok':>7} {'S(ρ)':>7}")
    print("-" * 68)

    all_analyses = {}
    for name, tokens in sequences.items():
        with torch.no_grad():
            results = model.process_sequence(tokens)

        analysis = analyze_token_predictions(results, tokens, vocab_size)
        f_values = [r["F_tokens"] for r in results]
        s_values = [r["S_rho"] for r in results]
        chance = analysis["chance_level"]
        ratio = analysis["mean_next_prob"] / chance if chance > 0 else 0

        print(f"  {name:<23} {analysis['mean_next_prob']:>9.4f} "
              f"{chance:>7.4f} {ratio:>6.1f}x "
              f"{np.mean(f_values):>7.3f} {np.mean(s_values):>7.3f}")

        all_analyses[name] = {
            "results": results,
            "analysis": analysis,
            "f_values": f_values,
            "s_values": s_values,
        }

    # Gate dynamics during sequence processing
    print(f"\n{'=' * 70}")
    print("GATE DYNAMICS DURING SEQUENCE PROCESSING")
    print(f"{'=' * 70}")
    print("(gate values are fixed parameters, but their effect differs by context)")

    # Compare: how does the inward-looking bubble's contribution change
    # across different sequence types?
    for name in ["periodic (ABC...)", "random"]:
        if name not in all_analyses:
            continue
        results = all_analyses[name]["results"]
        # Look at how much each bubble's gate-weighted input differs
        # from the purely external measurement
        print(f"\n  {name}:")
        gates = results[0]["gate_values"]
        for i in range(n_bubbles):
            g = gates[i].item()
            print(f"    Bubble {i}: gate={g:.3f}")

    # Plot
    fig, axes = plt.subplots(2, 2, figsize=(16, 12))

    # 1: Gate values over training
    ax = axes[0, 0]
    for i in range(n_bubbles):
        ax.plot(gate_history[i], label=f"Bubble {i}", linewidth=2)
    ax.axhline(y=0.5, color="gray", linestyle=":", alpha=0.5, label="midpoint")
    ax.set_xlabel("Epoch")
    ax.set_ylabel("Gate value (1=external, 0=inward)")
    ax.set_title("Do any bubbles orient inward?")
    ax.legend(fontsize=8)
    ax.set_ylim(-0.05, 1.05)

    # 2: Loss over training
    ax = axes[0, 1]
    ax.plot(loss_history, color="#2c3e50", linewidth=1.5)
    ax.set_xlabel("Epoch")
    ax.set_ylabel("Total maintenance cost")
    ax.set_title("Self-coherence training loss")
    ax.set_yscale("log")

    # 3: Token prediction comparison
    ax = axes[1, 0]
    names = list(all_analyses.keys())
    probs = [all_analyses[n]["analysis"]["mean_next_prob"] for n in names]
    chance = 1.0 / vocab_size
    colors = ["#e74c3c" if "random" in n else "#3498db" for n in names]
    ax.barh(range(len(names)), probs, color=colors)
    ax.axvline(x=chance, color="gray", linestyle=":", label="chance", alpha=0.7)
    ax.set_yticks(range(len(names)))
    ax.set_yticklabels(names, fontsize=8)
    ax.set_xlabel("P(next token)")
    ax.set_title("Prediction via self-coherence (red=random)")
    ax.legend(fontsize=8)
    ax.invert_yaxis()

    # 4: S(ρ) traces with gate context
    ax = axes[1, 1]
    for name in ["periodic (ABC...)", "monotone (AAA...)", "random"]:
        if name not in all_analyses:
            continue
        s_vals = all_analyses[name]["s_values"]
        style = "--" if "random" in name else "-"
        ax.plot(s_vals, style, label=name, linewidth=1.5,
                alpha=0.5 if "random" in name else 1.0)
    ax.set_xlabel("Token position")
    ax.set_ylabel("S(ρ)")
    ax.set_title("Internal entropy across sequence")
    ax.legend(fontsize=8)

    plt.suptitle(
        f"Self-measuring foam: gates=[{', '.join(f'{g:.2f}' for g in final_gates)}]",
        fontsize=12, fontweight="bold"
    )
    plt.tight_layout()
    plt.savefig("foam_self_measure.png", dpi=150, bbox_inches="tight")
    print(f"\nSaved to foam_self_measure.png")
    plt.close()


if __name__ == "__main__":
    run_experiment()
