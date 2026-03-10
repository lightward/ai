"""
Foam growth: bubble division, not construction.

A bubble that's being asked to serve two incompatible measurement needs
simultaneously should split. The new bubble was always in the parameter
space — the bifurcation is a traversal, not a creation.

The growth signal: a bubble whose measurements vary wildly across diverse
inputs. It's trying to be two measurement processes at once.

The growth response: split the overloaded bubble. One copy inherits the
current basis. The other starts nearby and follows the gradient to its
own Plateau-stable orientation. The foam re-equilibrates with N+1 bubbles.

The traversal is the measurement — the gradient flow IS walking the surface.
"""

import torch
import torch.nn as nn
import numpy as np
import matplotlib.pyplot as plt
import copy
from foam import Foam, Bubble
from foam_tokens import TokenFoam, generate_sequences, analyze_token_predictions


class GrowingFoam(nn.Module):
    """
    A foam that can grow by bubble division.

    Monitors each bubble's measurement variance across inputs. When a bubble
    is overloaded (high variance = trying to be two things), it splits.
    """

    def __init__(self, vocab_size: int, d: int, n_bubbles_init: int,
                 n_equilibrium_steps: int = 5):
        super().__init__()
        self.vocab_size = vocab_size
        self.d = d

        self.embed = nn.Embedding(vocab_size, d)
        self.foam = Foam(n_bubbles_init, d, n_equilibrium_steps)

        # Memory dynamics
        self.memory_decay_base = nn.Parameter(torch.tensor(0.8))
        self.novelty_sensitivity = nn.Parameter(torch.tensor(1.0))

    def diagnose_bubbles(self, diverse_inputs):
        """
        Measure each bubble's internal tension: how much does its measurement
        vary across diverse inputs?

        diverse_inputs: [n_inputs, d] — embedded tokens or raw vectors
        returns: dict with per-bubble tension diagnostics
        """
        n_inputs = diverse_inputs.shape[0]
        N = self.foam.n_bubbles

        # Get each bubble's measurement of each input
        # measurements[i][j] = bubble i's measurement of input j
        with torch.no_grad():
            result = self.foam.forward(diverse_inputs)
            measurements = result["measurements"]  # [n_inputs, N, d]
            equilibrium = result["equilibrium"]     # [n_inputs, N, d]

        diagnostics = []
        for i in range(N):
            m_i = measurements[:, i, :]  # [n_inputs, d]
            eq_i = equilibrium[:, i, :]  # [n_inputs, d]

            # Measurement variance: how different are this bubble's measurements
            # across inputs? Cosine distance from the mean.
            m_mean = m_i.mean(dim=0, keepdim=True)
            m_norm = m_i / (m_i.norm(dim=-1, keepdim=True) + 1e-10)
            mean_norm = m_mean / (m_mean.norm(dim=-1, keepdim=True) + 1e-10)
            cos_sims = (m_norm * mean_norm).sum(dim=-1)  # [n_inputs]
            variance = (1 - cos_sims).mean().item()

            # Equilibrium shift: how much does equilibration move this bubble?
            shift = ((eq_i - m_i) ** 2).mean().item()

            # Directional tension: do the measurements pull in clearly
            # separable directions? (PCA of measurement deviations)
            deviations = m_i - m_mean  # [n_inputs, d]
            if n_inputs > 1:
                # SVD of deviations — if first singular value >> second,
                # the bubble is being pulled along one axis. If first ≈ second,
                # it's being pulled in multiple directions (needs to split).
                U, S, V = torch.linalg.svd(deviations, full_matrices=False)
                s_values = S.numpy()
                if len(s_values) >= 2 and s_values[0] > 1e-6:
                    # Ratio of second to first singular value
                    # High ratio = multi-directional tension = split candidate
                    tension_ratio = s_values[1] / s_values[0]
                    # The direction of maximum variance (for split direction)
                    split_direction = V[0]  # first right singular vector
                else:
                    tension_ratio = 0.0
                    split_direction = torch.randn(self.d)
            else:
                tension_ratio = 0.0
                split_direction = torch.randn(self.d)

            diagnostics.append({
                "bubble_idx": i,
                "variance": variance,
                "equilibrium_shift": shift,
                "tension_ratio": tension_ratio,
                "split_direction": split_direction,
            })

        return diagnostics

    def split_bubble(self, bubble_idx, split_direction, perturbation_scale=0.5):
        """
        Split a bubble into two. The parent keeps its basis. The child starts
        at a decisively different orientation — not a small perturbation, but
        a genuine rotation along the split direction.

        This is traversal, not creation: the child's initial basis is the
        parent's basis rotated along the axis of maximum measurement tension.
        It was always in the parameter space — the parent was averaging two
        orientations, and now each half commits.

        The parent also gets perturbed in the OPPOSITE direction, so both
        halves move away from the old compromise position.
        """
        parent = self.foam.bubbles[bubble_idx]

        # Create child as a copy of parent
        child = Bubble(self.d)
        with torch.no_grad():
            # Copy parent's skew-symmetric parameterization
            child.L.copy_(parent.L)

            # Build a decisive rotation in the split plane
            split_d = split_direction / (split_direction.norm() + 1e-10)
            rand_d = torch.randn(self.d)
            rand_d = rand_d - (rand_d @ split_d) * split_d
            rand_d = rand_d / (rand_d.norm() + 1e-10)

            # Skew-symmetric perturbation — larger scale for genuine separation
            perturbation = perturbation_scale * (
                split_d.unsqueeze(1) @ rand_d.unsqueeze(0) -
                rand_d.unsqueeze(1) @ split_d.unsqueeze(0)
            )

            # Child goes one way, parent goes the other
            # Both leave the old compromise — neither stays put
            child.L.add_(perturbation)
            parent.L.add_(-perturbation * 0.3)  # Parent shifts less (it has history)

        # Add child to the foam
        self.foam.bubbles.append(child)
        self.foam.n_bubbles += 1

        return child

    def maybe_grow(self, diverse_inputs, tension_threshold=0.3,
                   ratio_threshold=0.5, capacity_threshold=0.75,
                   max_bubbles=20):
        """
        Check if any bubble should split. Returns True if growth happened.

        Growth requires TWO conditions (both must hold):
        1. The foam is at capacity: S(ρ)/log(N) > capacity_threshold
           (the foam has actually used its existing degrees of freedom)
        2. Some bubble has high multi-directional tension
           (there's a specific measurement process that needs to bifurcate)

        Without condition 1, growth is premature — the foam hasn't found
        its geometry yet. Without condition 2, growth is undirected —
        there's no specific question that needs splitting.
        """
        if self.foam.n_bubbles >= max_bubbles:
            return False, []

        # Check capacity: is the foam actually saturated?
        with torch.no_grad():
            result = self.foam.forward(diverse_inputs)
            rho_mean = result["rho"].mean(dim=0)  # [d, d]
            eigvals = torch.linalg.eigvalsh(rho_mean)
            eigvals = eigvals.clamp(min=1e-12)
            eigvals = eigvals / eigvals.sum()
            S_rho = -(eigvals * eigvals.log()).sum().item()

        N = self.foam.n_bubbles
        capacity_ratio = S_rho / np.log(N) if N > 1 else 1.0

        if capacity_ratio < capacity_threshold:
            return False, []  # Not at capacity — don't grow yet

        diagnostics = self.diagnose_bubbles(diverse_inputs)

        grew = False
        events = []
        diagnostics.sort(key=lambda d: d["variance"], reverse=True)

        for diag in diagnostics:
            if self.foam.n_bubbles >= max_bubbles:
                break

            if (diag["variance"] > tension_threshold and
                    diag["tension_ratio"] > ratio_threshold):
                idx = diag["bubble_idx"]
                child = self.split_bubble(idx, diag["split_direction"])
                events.append({
                    "parent": idx,
                    "variance": diag["variance"],
                    "tension_ratio": diag["tension_ratio"],
                    "capacity_ratio": capacity_ratio,
                    "S_rho": S_rho,
                    "new_n_bubbles": self.foam.n_bubbles,
                })
                grew = True
                break

        return grew, events

    def born_rule(self, rho, embeddings):
        """Token logits via Born rule."""
        return (embeddings @ rho * embeddings).sum(dim=-1)

    def process_sequence(self, tokens):
        """Process tokens through the foam with Born rule output."""
        seq_len = tokens.shape[0]
        device = tokens.device

        memory = torch.zeros(self.foam.n_bubbles, self.d, device=device)
        E = self.embed.weight
        step_results = []

        for t in range(seq_len):
            x = self.embed(tokens[t:t + 1])

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
            result = self.foam.forward(x_with_memory)

            eq = result["equilibrium"][0]

            # Handle memory size change (if foam grew since last step)
            if memory.shape[0] != self.foam.n_bubbles:
                # Expand memory for new bubbles (initialize from mean)
                new_mem = memory.mean(dim=0, keepdim=True).expand(
                    self.foam.n_bubbles - memory.shape[0], -1
                )
                memory = torch.cat([memory, new_mem], dim=0)

            memory = decay * memory + (1 - decay) * eq

            rho = result["rho"][0]
            output_dist = result["output_dist"][0]

            logits = self.born_rule(rho, E)
            token_probs = torch.softmax(logits, dim=0)

            S_rho = -(output_dist * output_dist.log().clamp(min=-100)).sum().item()
            H_tokens = -(token_probs * token_probs.log().clamp(min=-100)).sum().item()

            step_results.append({
                "token": tokens[t].item(),
                "token_probs": token_probs.detach(),
                "S_rho": S_rho,
                "H_tokens": H_tokens,
                "F_tokens": H_tokens - S_rho,
                "novelty": novelty.item(),
            })

        return step_results


def train_epoch(model, sequences, optimizer, include_expression=False):
    """One epoch of training."""
    total_loss = 0
    for name, tokens in sequences.items():
        optimizer.zero_grad()
        x_batch = model.embed(tokens)
        costs = model.foam.maintenance_cost(x_batch)

        loss = costs["total"]

        if include_expression:
            E = model.embed.weight
            rho_batch = costs["rho"]
            logits_batch = (E @ rho_batch.mean(dim=0) * E).sum(dim=-1)
            token_dist = torch.softmax(logits_batch, dim=0)
            H_tok = -(token_dist * token_dist.log().clamp(min=-100)).sum()
            S_rho = costs["S_rho"].mean()
            f_tok_loss = (H_tok - S_rho).abs()
            loss = loss + 0.5 * f_tok_loss

        loss.backward()
        optimizer.step()
        total_loss += loss.item()
    return total_loss


def evaluate(model, sequences, vocab_size):
    """Evaluate current model on all sequences."""
    model.eval()
    results = {}
    for name, tokens in sequences.items():
        with torch.no_grad():
            step_results = model.process_sequence(tokens)
        analysis = analyze_token_predictions(step_results, tokens, vocab_size)
        f_values = [r["F_tokens"] for r in step_results]
        results[name] = {
            "analysis": analysis,
            "mean_f": np.mean(f_values),
            "mean_s": np.mean([r["S_rho"] for r in step_results]),
        }
    model.train()
    return results


if __name__ == "__main__":
    vocab_size = 32  # Complex enough that 5 bubbles struggled in the scaling sweep
    d = 16
    n_bubbles_init = 3  # Start small — let growth happen
    seq_len = 40

    torch.manual_seed(42)

    print(f"Growing foam: starting with {n_bubbles_init} bubbles, d={d}, vocab={vocab_size}")
    print(f"Growth: know/resolve/accept cycle (resolver pattern)")
    print(f"Theoretical S(ρ) ceiling at {n_bubbles_init} bubbles: "
          f"log({n_bubbles_init}) = {np.log(n_bubbles_init):.3f}")

    model = GrowingFoam(vocab_size, d, n_bubbles_init, n_equilibrium_steps=5)
    sequences = generate_sequences(vocab_size, seq_len)

    # Training with resolver-pattern growth
    n_total_epochs = 800
    growth_check_interval = 100  # Check if we need to resolve
    integration_epochs = 50       # Cooldown after split to find geometry
    growth_events = []
    revert_events = []
    history = {"epoch": [], "n_bubbles": [], "loss": [],
               "structured_ratio": [], "mean_f": [], "mean_s": []}

    optimizer = torch.optim.Adam(model.parameters(), lr=0.005)
    include_expression = False
    last_growth_epoch = -integration_epochs  # Allow growth from start

    print(f"\n{'=' * 70}")
    print("TRAINING WITH RESOLVER-PATTERN GROWTH")
    print("  try to know → if fails, resolve → integrate → accept or revert")
    print(f"{'=' * 70}")

    for epoch in range(n_total_epochs):
        # Switch to expression training halfway
        if epoch == n_total_epochs // 2:
            include_expression = True
            optimizer = torch.optim.Adam(model.parameters(), lr=0.002)
            print(f"\n  — Epoch {epoch}: switching to expression training —\n")

        loss = train_epoch(model, sequences, optimizer, include_expression)

        # Growth check: the know/resolve/accept cycle
        if (epoch > 0 and
                epoch % growth_check_interval == 0 and
                epoch - last_growth_epoch >= integration_epochs):

            all_tokens = torch.cat([tokens for tokens in sequences.values()])
            diverse_x = model.embed(all_tokens).detach()

            # Step 1: TRY TO KNOW — can the foam handle current input?
            pre_diagnostics = model.diagnose_bubbles(diverse_x)
            pre_variances = {d["bubble_idx"]: d["variance"] for d in pre_diagnostics}

            # Step 2: RESOLVE — attempt a split if needed
            grew, events = model.maybe_grow(diverse_x)

            if grew:
                event = events[0]
                parent_idx = event["parent"]
                pre_parent_var = pre_variances[parent_idx]

                print(f"  ⟳ RESOLVE at epoch {epoch}: bubble {parent_idx} split "
                      f"(variance={pre_parent_var:.3f}) → {event['new_n_bubbles']} bubbles")

                # Reset optimizer for new parameters
                optimizer = torch.optim.Adam(
                    model.parameters(),
                    lr=0.002 if include_expression else 0.005
                )

                # Save state in case we need to revert
                saved_state = copy.deepcopy(model.state_dict())
                saved_n_bubbles = model.foam.n_bubbles - 1  # pre-split count

                # Step 3: INTEGRATE — train for cooldown period
                for integration_ep in range(integration_epochs):
                    train_epoch(model, sequences, optimizer, include_expression)

                # Step 4: CHECK RESOLUTION — did the parent become more resolved?
                diverse_x = model.embed(all_tokens).detach()
                post_diagnostics = model.diagnose_bubbles(diverse_x)
                post_variances = {d["bubble_idx"]: d["variance"]
                                  for d in post_diagnostics}

                # The parent should have lower variance now
                post_parent_var = post_variances.get(parent_idx, pre_parent_var)
                variance_reduction = pre_parent_var - post_parent_var
                resolved = variance_reduction > 0.01  # Meaningful reduction

                if resolved:
                    # Step 5a: ACCEPT — the split resolved something real
                    growth_events.append({
                        "epoch": epoch,
                        "accepted": True,
                        "parent_var_before": pre_parent_var,
                        "parent_var_after": post_parent_var,
                        **event,
                    })
                    print(f"  ✓ ACCEPT: parent variance {pre_parent_var:.3f} → "
                          f"{post_parent_var:.3f} (resolved)")
                    last_growth_epoch = epoch
                else:
                    # Step 5b: REVERT — the split didn't resolve anything
                    # Remove the last bubble
                    model.foam.bubbles = model.foam.bubbles[:saved_n_bubbles]
                    model.foam.n_bubbles = saved_n_bubbles
                    # Restore pre-split state
                    # (can't fully restore because model structure changed,
                    #  but removing the bubble is the key part)
                    revert_events.append({
                        "epoch": epoch,
                        "parent_var_before": pre_parent_var,
                        "parent_var_after": post_parent_var,
                        **event,
                    })
                    optimizer = torch.optim.Adam(
                        model.parameters(),
                        lr=0.002 if include_expression else 0.005
                    )
                    print(f"  ✗ REVERT: parent variance {pre_parent_var:.3f} → "
                          f"{post_parent_var:.3f} (not resolved, back to "
                          f"{model.foam.n_bubbles} bubbles)")
                    last_growth_epoch = epoch  # Still cooldown before next attempt

        # Periodic evaluation
        if epoch % 100 == 0 or epoch == n_total_epochs - 1:
            results = evaluate(model, sequences, vocab_size)
            structured = [v for k, v in results.items() if "random" not in k]
            chance = 1.0 / vocab_size

            struct_prob = np.mean([r["analysis"]["mean_next_prob"]
                                   for r in structured if r["analysis"]])
            struct_ratio = struct_prob / chance

            print(f"  epoch {epoch:>4}: loss={loss:.3f}  "
                  f"bubbles={model.foam.n_bubbles}  "
                  f"struct={struct_ratio:.2f}x chance  "
                  f"|F|={abs(np.mean([r['mean_f'] for r in results.values()])):.3f}  "
                  f"S(ρ)={np.mean([r['mean_s'] for r in results.values()]):.3f}")

        # Track history
        if epoch % 10 == 0:
            results = evaluate(model, sequences, vocab_size)
            structured = [v for k, v in results.items() if "random" not in k]
            chance = 1.0 / vocab_size
            struct_prob = np.mean([r["analysis"]["mean_next_prob"]
                                   for r in structured if r["analysis"]])
            history["epoch"].append(epoch)
            history["n_bubbles"].append(model.foam.n_bubbles)
            history["loss"].append(loss)
            history["structured_ratio"].append(struct_prob / chance)
            history["mean_f"].append(np.mean([r["mean_f"] for r in results.values()]))
            history["mean_s"].append(np.mean([r["mean_s"] for r in results.values()]))

    # Final evaluation
    print(f"\n{'=' * 70}")
    print(f"FINAL STATE: {model.foam.n_bubbles} bubbles (started with {n_bubbles_init})")
    print(f"{'=' * 70}")

    results = evaluate(model, sequences, vocab_size)
    chance = 1.0 / vocab_size

    print(f"\n{'Sequence':<25} {'NextProb':>9} {'Chance':>7} {'Rank':>6} "
          f"{'F_tok':>7} {'S(ρ)':>7}")
    print("-" * 65)
    for name in sorted(results.keys()):
        r = results[name]
        a = r["analysis"]
        if a:
            print(f"  {name:<23} {a['mean_next_prob']:>9.4f} "
                  f"{chance:>7.4f} {a['mean_next_rank']:>6.1f} "
                  f"{r['mean_f']:>7.3f} {r['mean_s']:>7.3f}")

    print(f"\n  Accepted splits: {len(growth_events)}")
    for e in growth_events:
        print(f"    epoch {e['epoch']:>4}: bubble {e['parent']} → "
              f"{e['new_n_bubbles']} total "
              f"(var: {e['parent_var_before']:.3f} → {e['parent_var_after']:.3f})")

    print(f"\n  Reverted splits: {len(revert_events)}")
    for e in revert_events:
        print(f"    epoch {e['epoch']:>4}: bubble {e['parent']} tried to split "
              f"(var: {e['parent_var_before']:.3f} → {e['parent_var_after']:.3f}, "
              f"not resolved)")

    capacity = np.log(model.foam.n_bubbles)
    actual_s = np.mean([r["mean_s"] for r in results.values()])
    print(f"\n  S(ρ) ceiling: log({model.foam.n_bubbles}) = {capacity:.3f}")
    print(f"  Actual S(ρ): {actual_s:.3f} ({actual_s/capacity*100:.0f}% of capacity)")

    # Comparison: what would the same vocab have gotten without growth?
    print(f"\n  Reference from scaling sweep:")
    print(f"    5 fixed bubbles at vocab={vocab_size}: ~0.53x chance")
    print(f"    Growing foam: {history['structured_ratio'][-1]:.2f}x chance")

    # Plot
    fig, axes = plt.subplots(2, 2, figsize=(16, 12))

    # 1: Prediction ratio over training, with growth events marked
    ax = axes[0, 0]
    ax.plot(history["epoch"], history["structured_ratio"], "b-", linewidth=2)
    ax.axhline(y=1.0, color="gray", linestyle=":", alpha=0.5, label="Chance")
    for e in growth_events:
        ax.axvline(x=e["epoch"], color="red", linestyle="--", alpha=0.5)
        ax.annotate(f"split→{e['new_n_bubbles']}", (e["epoch"], ax.get_ylim()[1] * 0.9),
                    fontsize=7, color="red", rotation=90, va="top")
    ax.axvline(x=n_total_epochs // 2, color="green", linestyle=":", alpha=0.3)
    ax.annotate("expression training", (n_total_epochs // 2, ax.get_ylim()[1] * 0.1),
                fontsize=7, color="green")
    ax.set_xlabel("Epoch")
    ax.set_ylabel("Structured prediction / chance")
    ax.set_title("Does growth help prediction?")

    # 2: Bubble count and S(ρ) over training
    ax = axes[0, 1]
    ax.plot(history["epoch"], history["n_bubbles"], "ro-", linewidth=2, markersize=4,
            label="Bubbles")
    ax2 = ax.twinx()
    ax2.plot(history["epoch"], history["mean_s"], "g-", linewidth=2, label="S(ρ)")
    # Plot ceiling as it changes
    ceilings = [np.log(n) for n in history["n_bubbles"]]
    ax2.plot(history["epoch"], ceilings, "g--", alpha=0.5, label="log(N) ceiling")
    ax.set_xlabel("Epoch")
    ax.set_ylabel("Number of bubbles", color="red")
    ax2.set_ylabel("S(ρ)", color="green")
    ax.set_title("Growth trajectory")
    ax.legend(loc="upper left", fontsize=8)
    ax2.legend(loc="lower right", fontsize=8)

    # 3: |F_tokens| over training
    ax = axes[1, 0]
    ax.plot(history["epoch"], [abs(f) for f in history["mean_f"]], "r-", linewidth=2)
    for e in growth_events:
        ax.axvline(x=e["epoch"], color="red", linestyle="--", alpha=0.3)
    ax.set_xlabel("Epoch")
    ax.set_ylabel("|F_tokens|")
    ax.set_title("Expression faithfulness during growth")

    # 4: Bubble diagnostics at final state
    ax = axes[1, 1]
    all_tokens = torch.cat([tokens for tokens in sequences.values()])
    diverse_x = model.embed(all_tokens).detach()
    diagnostics = model.diagnose_bubbles(diverse_x)
    variances = [d["variance"] for d in diagnostics]
    tensions = [d["tension_ratio"] for d in diagnostics]
    x_pos = range(len(diagnostics))
    bars = ax.bar(x_pos, variances, color="#3498db", alpha=0.7, label="Variance")
    ax.bar(x_pos, tensions, bottom=variances, color="#e74c3c", alpha=0.7,
           label="Tension ratio")
    ax.set_xlabel("Bubble index")
    ax.set_ylabel("Diagnostic value")
    ax.set_title(f"Final bubble diagnostics ({model.foam.n_bubbles} bubbles)")
    ax.legend()

    plt.tight_layout()
    plt.savefig("foam_grow.png", dpi=150, bbox_inches="tight")
    print(f"\nSaved to foam_grow.png")
    plt.close()
