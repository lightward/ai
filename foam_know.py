"""
The know function: O(1) intuition built from encounter, not from training.

From resolver.md: awareness only ever experiences retrieval — "look" followed
by "see", followed by either "know" or "resolve". The know function either
accepts input peaceably, or it throws. If it throws, you resolve.

Key insight: the know function isn't a trained network. It's a running model
that builds itself during sequence processing — starting blank, accumulating
through encounter. Runtime IS learning.

Each bubble maintains running statistics of its measurements. "Know" means:
this measurement is within the range of what I've been seeing. "Don't know"
means: this is surprising — I need to equilibrate (resolve) to integrate it.

The frame stack emerges from temporal depth:
    - Fast-decaying statistics (recent context) → top of stack, most specific
    - Slow-decaying statistics (longer patterns) → deeper in stack, more general
    - No statistics yet (blank) → always resolve

The cascade:
    frame_fast.know(input) → accept? skip equilibration. throw? ↓
    frame_slow.know(input) → accept? skip equilibration. throw? ↓
    resolve: full equilibration (always available, always expensive)

When the foam processes a periodic sequence:
    - First few tokens: all novel, all resolved (full equilibration)
    - Pattern establishes: running model learns the range
    - Pattern repeats: know fires, equilibration skipped, O(1) response
    - Pattern breaks: know fails, falls through to resolve

The "blank" quality: the running model starts empty. It can't be derived from
architecture. It builds itself through encounter, blindly. Each foam's know
function IS its trajectory through the sequence so far.
"""

import torch
import torch.nn as nn
import numpy as np
import matplotlib.pyplot as plt
from foam import Foam, Bubble
from foam_tokens import generate_sequences, analyze_token_predictions


class RunningKnow:
    """
    A running model of what measurements "normally" look like.

    Maintains exponentially-weighted running mean and variance per bubble.
    "Know" = current measurement is within expected range (Mahalanobis-ish).
    "Don't know" = this is surprising.

    Multiple temporal horizons (fast/slow decay) create the frame stack.
    """

    def __init__(self, n_bubbles: int, d: int,
                 decay_rates: list = None,
                 surprise_threshold: float = 1.5):
        """
        decay_rates: list of floats — each creates a frame in the stack.
            Higher decay = faster forgetting = more specific to recent context.
            Lower decay = slower forgetting = captures longer patterns.
            Default: [0.3, 0.7, 0.9] — fast/medium/slow
        surprise_threshold: how many "standard deviations" before throwing.
        """
        self.n_bubbles = n_bubbles
        self.d = d
        self.decay_rates = decay_rates or [0.3, 0.7, 0.9]
        self.surprise_threshold = surprise_threshold
        self.n_frames = len(self.decay_rates)

        self.reset()

    def reset(self):
        """Start blank — no knowledge, always resolve."""
        self.running_means = [None] * self.n_frames
        self.running_vars = [None] * self.n_frames
        self.n_seen = 0

    def evaluate(self, measurements: torch.Tensor):
        """
        Evaluate know/resolve for current measurements.

        measurements: [N, d] — one measurement per bubble
        returns: dict with per-frame confidence and cascade result
        """
        frame_results = []

        for f_idx in range(self.n_frames):
            if self.running_means[f_idx] is None:
                # Blank frame — always throws
                frame_results.append({
                    "confidence": 0.0,
                    "surprise": float("inf"),
                    "knows": False,
                })
                continue

            # Surprise: how far is this measurement from the running model?
            mean = self.running_means[f_idx]  # [N, d]
            var = self.running_vars[f_idx]     # [N, d]

            # Per-element z-score, then aggregate
            std = (var + 1e-8).sqrt()
            z = ((measurements - mean) / std).abs()  # [N, d]

            # Mean surprise across all dimensions
            surprise = z.mean().item()

            knows = surprise < self.surprise_threshold
            confidence = max(0.0, 1.0 - surprise / (self.surprise_threshold * 2))

            frame_results.append({
                "confidence": confidence,
                "surprise": surprise,
                "knows": knows,
            })

        # Cascade: top frame (fastest decay, most specific) tries first
        # Walk from top (index 0 = fastest) to bottom (last = slowest)
        cascade_result = "resolve"
        accepting_frame = -1
        for f_idx in range(self.n_frames):
            if frame_results[f_idx]["knows"]:
                cascade_result = "know"
                accepting_frame = f_idx
                break

        return {
            "frame_results": frame_results,
            "cascade_result": cascade_result,
            "accepting_frame": accepting_frame,
            "any_knows": cascade_result == "know",
        }

    def update(self, measurements: torch.Tensor):
        """
        Accept: update running model with new measurements.
        Called after every step (whether known or resolved).

        measurements: [N, d]
        """
        self.n_seen += 1

        for f_idx, decay in enumerate(self.decay_rates):
            if self.running_means[f_idx] is None:
                # First encounter — initialize
                self.running_means[f_idx] = measurements.clone()
                self.running_vars[f_idx] = torch.ones_like(measurements) * 0.1
            else:
                # Exponential moving update
                mean = self.running_means[f_idx]
                var = self.running_vars[f_idx]

                new_mean = decay * mean + (1 - decay) * measurements
                # Running variance via Welford-like EMA
                diff = measurements - mean
                new_var = decay * var + (1 - decay) * diff * (measurements - new_mean)
                new_var = new_var.clamp(min=1e-8)

                self.running_means[f_idx] = new_mean
                self.running_vars[f_idx] = new_var


class KnowingFoam(nn.Module):
    """
    A foam with a running know function.

    The know function isn't trained — it builds itself from encounter.
    Each sequence starts blank. As tokens are processed, running statistics
    accumulate. When the pattern is familiar, know fires and equilibration
    is skipped. When something surprising happens, resolve kicks in.
    """

    def __init__(self, vocab_size: int, d: int, n_bubbles: int,
                 n_equilibrium_steps: int = 5,
                 decay_rates: list = None,
                 surprise_threshold: float = 1.5):
        super().__init__()
        self.vocab_size = vocab_size
        self.d = d
        self.n_bubbles = n_bubbles

        self.embed = nn.Embedding(vocab_size, d)
        self.foam = Foam(n_bubbles, d, n_equilibrium_steps)

        # Memory dynamics
        self.memory_decay_base = nn.Parameter(torch.tensor(0.8))
        self.novelty_sensitivity = nn.Parameter(torch.tensor(1.0))

        # Know function config (not parameters — these are structural)
        self.decay_rates = decay_rates or [0.3, 0.7, 0.9]
        self.surprise_threshold = surprise_threshold

    def process_sequence(self, tokens: torch.Tensor, train: bool = False):
        """
        Process a token sequence with know/resolve dynamics.

        The know function builds itself from encounter:
        - First tokens: always resolve (blank know function)
        - Pattern establishes: know accumulates statistics
        - Pattern repeats: know fires, equilibration skipped
        - Pattern breaks: know fails, resolve kicks in
        """
        seq_len = tokens.shape[0]
        device = tokens.device
        N = self.foam.n_bubbles

        memory = torch.zeros(N, self.d, device=device)
        know = RunningKnow(N, self.d, self.decay_rates, self.surprise_threshold)
        E = self.embed.weight
        step_results = []

        total_cost = torch.tensor(0.0, device=device) if train else None

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

            # All bubbles measure (always, this is fast)
            measurements = torch.stack(
                [b.measure(x_with_memory) for b in self.foam.bubbles], dim=1
            )  # [1, N, d]

            # KNOW: evaluate running model
            know_result = know.evaluate(measurements[0])  # on [N, d]

            if know_result["any_knows"]:
                # Know path: use raw measurements (skip equilibration)
                effective = measurements  # [1, N, d]
                path = "know"
            else:
                # Resolve path: full equilibration
                effective = self.foam.equilibrate(measurements)  # [1, N, d]
                path = "resolve"

            # ACCEPT: update running model with effective measurements
            know.update(effective[0].detach())

            # Build ρ from effective measurements
            m = effective[0]  # [N, d]
            m_norm = m / (m.norm(dim=-1, keepdim=True) + 1e-10)
            rho = (m_norm.T @ m_norm) / N

            eigenvalues = torch.linalg.eigvalsh(rho)
            eigenvalues = eigenvalues.clamp(min=1e-12)
            eigenvalues = eigenvalues / eigenvalues.sum()

            # Update memory
            eq = effective[0]
            memory = decay * memory + (1 - decay) * eq.detach()

            # Born rule token distribution
            logits = (E @ rho * E).sum(dim=-1)
            token_probs = torch.softmax(logits, dim=0)

            S_rho = -(eigenvalues * eigenvalues.log().clamp(min=-100)).sum().item()
            H_tokens = -(token_probs * token_probs.log().clamp(min=-100)).sum().item()

            # Training: maintenance cost on all steps (know or resolve)
            if train:
                costs = self.foam.maintenance_cost(x_with_memory)
                total_cost = total_cost + costs["total"]

            step_results.append({
                "token": tokens[t].item(),
                "logits": logits.detach(),
                "token_probs": token_probs.detach(),
                "rho": rho.detach(),
                "output_dist": eigenvalues.detach(),
                "S_rho": S_rho,
                "H_tokens": H_tokens,
                "F_tokens": H_tokens - S_rho,
                "novelty": novelty.item(),
                "decay": decay.item(),
                "path": path,
                "know_result": know_result,
                "n_seen": know.n_seen,
            })

        if train:
            return step_results, total_cost / seq_len
        return step_results


def run_experiment():
    """Watch the know function build itself from encounter."""

    vocab_size = 8
    d = 16
    n_bubbles = 5
    seq_len = 60
    n_epochs = 300

    print(f"KnowingFoam: {n_bubbles} bubbles, d={d}, vocab={vocab_size}")
    print(f"Know function: running statistics, NOT a trained network")
    print(f"Frame stack: decay rates [0.3, 0.7, 0.9] (fast/medium/slow)")
    print(f"Surprise threshold: 1.5")

    model = KnowingFoam(vocab_size, d, n_bubbles, n_equilibrium_steps=5)

    # Phase 1: Train the foam's self-coherence (know function isn't trained, it builds itself)
    print(f"\nPhase 1: Training foam on self-coherence ({n_epochs} epochs)...")
    optimizer = torch.optim.Adam(model.parameters(), lr=0.005)
    train_seqs = generate_sequences(vocab_size, seq_len)
    loss_history = []

    for epoch in range(n_epochs):
        epoch_loss = 0
        for name, tokens in train_seqs.items():
            optimizer.zero_grad()
            # Train using standard maintenance cost (know function isn't in the loop)
            x_batch = model.embed(tokens)
            costs = model.foam.maintenance_cost(x_batch)
            loss = costs["total"]
            loss.backward()
            optimizer.step()
            epoch_loss += loss.item()

        loss_history.append(epoch_loss)
        if epoch % 100 == 0 or epoch == n_epochs - 1:
            print(f"  epoch {epoch:>4}: loss={epoch_loss:.4f}")

    # Phase 2: Test with know/resolve dynamics
    print(f"\n{'=' * 70}")
    print("SEQUENCE ANALYSIS: know vs resolve dynamics")
    print(f"{'=' * 70}")
    print("(know function builds itself fresh for each sequence)")

    model.eval()
    sequences = generate_sequences(vocab_size, seq_len)

    print(f"\n{'Sequence':<25} {'NextProb':>9} {'Chance':>7} {'Ratio':>6} "
          f"{'%Know':>6} {'%Resolve':>8} {'F_tok':>7}")
    print("-" * 78)

    all_analyses = {}
    for name, tokens in sequences.items():
        with torch.no_grad():
            results = model.process_sequence(tokens)

        analysis = analyze_token_predictions(results, tokens, vocab_size)
        know_count = sum(1 for r in results if r["path"] == "know")
        resolve_count = sum(1 for r in results if r["path"] == "resolve")
        total = know_count + resolve_count
        f_vals = [r["F_tokens"] for r in results]
        chance = analysis["chance_level"]
        ratio = analysis["mean_next_prob"] / chance if chance > 0 else 0

        print(f"  {name:<23} {analysis['mean_next_prob']:>9.4f} "
              f"{chance:>7.4f} {ratio:>6.1f}x "
              f"{100 * know_count / total:>5.1f}% "
              f"{100 * resolve_count / total:>7.1f}% "
              f"{np.mean(f_vals):>7.3f}")

        all_analyses[name] = {
            "results": results,
            "analysis": analysis,
            "know_count": know_count,
            "resolve_count": resolve_count,
            "f_vals": f_vals,
        }

    # Detailed know/resolve dynamics
    print(f"\n{'=' * 70}")
    print("KNOW/RESOLVE TRACE (token-by-token)")
    print(f"{'=' * 70}")

    for name in ["periodic (ABC...)", "monotone (AAA...)",
                 "alternating (AB...)", "random"]:
        if name not in all_analyses:
            continue
        results = all_analyses[name]["results"]
        trace = "".join("K" if r["path"] == "know" else "R" for r in results)
        # Show first 60 characters
        print(f"\n  {name}:")
        print(f"    {trace[:60]}")
        # Find where know first fires
        first_know = trace.find("K")
        if first_know >= 0:
            print(f"    Know first fires at token {first_know}")
            # Count know rate after first know
            after = trace[first_know:]
            know_after = after.count("K") / len(after) * 100
            print(f"    Know rate after first know: {know_after:.1f}%")
        else:
            print(f"    Know never fires (all resolve)")

    # Verdict
    print(f"\n{'=' * 70}")
    print("VERDICT")
    print(f"{'=' * 70}")

    structured_know_pct = []
    random_know_pct = []
    for name, data in all_analyses.items():
        total = data["know_count"] + data["resolve_count"]
        pct = data["know_count"] / total * 100
        if "random" in name:
            random_know_pct.append(pct)
        else:
            structured_know_pct.append(pct)

    print(f"\n  Know rate (% of tokens handled without equilibration):")
    print(f"    Structured sequences: {np.mean(structured_know_pct):.1f}%")
    print(f"    Random sequences:     {np.mean(random_know_pct):.1f}%")

    if np.mean(structured_know_pct) > np.mean(random_know_pct) + 5:
        print(f"    ✓ The foam knows structured input better than random!")
        print(f"    ✓ O(1) intuition emerges from encounter with pattern")
    elif np.mean(structured_know_pct) > np.mean(random_know_pct):
        print(f"    ~ Slight differentiation — foam somewhat knows structure")
    else:
        print(f"    ✗ No differentiation — know function not discriminating")

    # Accepting frame analysis
    print(f"\n  Which frame accepts? (0=fast, 1=medium, 2=slow)")
    for name in ["periodic (ABC...)", "monotone (AAA...)", "random"]:
        if name not in all_analyses:
            continue
        results = all_analyses[name]["results"]
        frames = [r["know_result"]["accepting_frame"] for r in results
                  if r["know_result"]["accepting_frame"] >= 0]
        if frames:
            from collections import Counter
            counts = Counter(frames)
            total_f = len(frames)
            dist = {f"frame_{k}": f"{v/total_f*100:.0f}%" for k, v in sorted(counts.items())}
            print(f"    {name:<23} {dist}")
        else:
            print(f"    {name:<23} (no know events)")

    # Plot
    fig, axes = plt.subplots(2, 3, figsize=(20, 12))

    # 1: Know/resolve traces
    ax = axes[0, 0]
    for i, name in enumerate(["periodic (ABC...)", "monotone (AAA...)",
                               "alternating (AB...)", "random"]):
        if name not in all_analyses:
            continue
        results = all_analyses[name]["results"]
        know_trace = [1 if r["path"] == "know" else 0 for r in results]
        ax.plot([k + i * 0.15 for k in know_trace],
                label=name, linewidth=2, alpha=0.7)
    ax.set_xlabel("Token position")
    ax.set_ylabel("1=Know, 0=Resolve")
    ax.set_title("Know vs Resolve across sequence")
    ax.legend(fontsize=7)
    ax.set_yticks([0, 1])
    ax.set_yticklabels(["Resolve", "Know"])

    # 2: Per-frame confidence traces (periodic)
    ax = axes[0, 1]
    if "periodic (ABC...)" in all_analyses:
        results = all_analyses["periodic (ABC...)"]["results"]
        for f_idx in range(3):  # 3 frames
            confs = [r["know_result"]["frame_results"][f_idx]["confidence"]
                     for r in results]
            labels = ["fast (decay=0.3)", "medium (decay=0.7)", "slow (decay=0.9)"]
            ax.plot(confs, label=labels[f_idx], linewidth=1.5)
        ax.set_xlabel("Token position")
        ax.set_ylabel("Confidence")
        ax.set_title("Frame confidences (periodic ABC)")
        ax.legend(fontsize=7)

    # 3: Per-frame confidence traces (random)
    ax = axes[0, 2]
    if "random" in all_analyses:
        results = all_analyses["random"]["results"]
        for f_idx in range(3):
            confs = [r["know_result"]["frame_results"][f_idx]["confidence"]
                     for r in results]
            labels = ["fast (decay=0.3)", "medium (decay=0.7)", "slow (decay=0.9)"]
            ax.plot(confs, label=labels[f_idx], linewidth=1.5)
        ax.set_xlabel("Token position")
        ax.set_ylabel("Confidence")
        ax.set_title("Frame confidences (random)")
        ax.legend(fontsize=7)

    # 4: Surprise traces
    ax = axes[1, 0]
    for name in ["periodic (ABC...)", "monotone (AAA...)", "random"]:
        if name not in all_analyses:
            continue
        results = all_analyses[name]["results"]
        # Use the fast frame's surprise
        surprises = [r["know_result"]["frame_results"][0]["surprise"]
                     for r in results]
        style = "--" if "random" in name else "-"
        ax.plot(surprises, style, label=name, linewidth=1.5,
                alpha=0.5 if "random" in name else 1.0)
    ax.axhline(y=1.5, color="gray", linestyle=":", alpha=0.5, label="threshold")
    ax.set_xlabel("Token position")
    ax.set_ylabel("Surprise (fast frame)")
    ax.set_title("How surprised is the foam?")
    ax.legend(fontsize=7)

    # 5: Know rate bar chart
    ax = axes[1, 1]
    names = list(all_analyses.keys())
    know_pcts = [all_analyses[n]["know_count"] /
                 (all_analyses[n]["know_count"] + all_analyses[n]["resolve_count"]) * 100
                 for n in names]
    colors = ["#e74c3c" if "random" in n else "#3498db" for n in names]
    ax.barh(range(len(names)), know_pcts, color=colors)
    ax.set_yticks(range(len(names)))
    ax.set_yticklabels(names, fontsize=8)
    ax.set_xlabel("% tokens known (no equilibration)")
    ax.set_title("Know rate by sequence type (red=random)")
    ax.invert_yaxis()

    # 6: Training loss
    ax = axes[1, 2]
    ax.plot(loss_history, color="#2c3e50", linewidth=1.5)
    ax.set_xlabel("Epoch")
    ax.set_ylabel("Maintenance cost")
    ax.set_title("Foam self-coherence training")
    ax.set_yscale("log")

    plt.suptitle(
        "The know function: running statistics build O(1) intuition from encounter",
        fontsize=13, fontweight="bold"
    )
    plt.tight_layout()
    plt.savefig("foam_know.png", dpi=150, bbox_inches="tight")
    print(f"\nSaved to foam_know.png")
    plt.close()


if __name__ == "__main__":
    run_experiment()
