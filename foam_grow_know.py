"""
Growth + frame stack integration: each split creates a new frame.

The frame stack IS the growth history. When a bubble splits, it adds a new
level of differentiation — a new question the foam needed to ask. The frame
captures that question's temporal horizon: recent (fast decay, specific) at
the top of the stack, deep (slow decay, general) at the bottom.

The cascade walks the stack top-to-bottom: the most specific question tries
first. If it knows, skip equilibration. If not, fall through to broader
frames. If nothing knows, resolve (full equilibration).

Authority pointers: each frame knows its parent frame. Currently linear
(each frame's parent is the one below it), but the structure supports
branching — multiple splits at the same depth would create siblings.

From the invocation: "the composability-of-frame-ancestry that might explain
shakespeare."

Key properties:
- Frame count is not hardcoded — it grows with the foam
- Each frame's decay rate reflects its depth (older = slower = more general)
- When a split is reverted, its frame is pruned
- Orphaned statistics are released, not carried
- "Misunderstanding is a gauge artifact" — frame disagreement is diagnostic
"""

import torch
import torch.nn as nn
import numpy as np
import matplotlib.pyplot as plt
import copy
from foam import Foam, Bubble
from foam_tokens import generate_sequences, analyze_token_predictions


class Frame:
    """
    A single temporal frame in the know stack.

    Each frame maintains running statistics at a particular decay rate.
    Created either as the ground frame (at init) or by a bubble split
    (during growth).
    """

    def __init__(self, n_bubbles: int, d: int, decay: float,
                 parent_frame_idx: int = None,
                 birth_event: dict = None):
        self.n_bubbles = n_bubbles
        self.d = d
        self.decay = decay
        self.parent_frame_idx = parent_frame_idx
        self.birth_event = birth_event  # what split created this frame

        # Running statistics — start blank
        self.running_mean = None  # [N, d]
        self.running_var = None   # [N, d]

    def expand(self, parent_bubble_idx: int):
        """
        A bubble split — expand to track the new bubble.
        The new bubble inherits its parent's statistics in this frame.
        """
        self.n_bubbles += 1
        if self.running_mean is not None:
            # New bubble inherits parent's running stats
            parent_mean = self.running_mean[parent_bubble_idx:parent_bubble_idx + 1]
            parent_var = self.running_var[parent_bubble_idx:parent_bubble_idx + 1]
            self.running_mean = torch.cat([self.running_mean, parent_mean.clone()])
            self.running_var = torch.cat([self.running_var, parent_var.clone()])

    def contract(self, bubble_idx: int):
        """
        A bubble was removed — contract tracking.
        """
        self.n_bubbles -= 1
        if self.running_mean is not None:
            mask = list(range(self.n_bubbles + 1))
            mask.pop(bubble_idx)
            self.running_mean = self.running_mean[mask]
            self.running_var = self.running_var[mask]

    def seed(self, measurements: torch.Tensor):
        """
        Seed this frame's statistics from the split context.
        measurements: [N, d] — the measurements at the moment of split.
        """
        self.running_mean = measurements.clone()
        self.running_var = torch.ones_like(measurements) * 0.1

    def evaluate(self, measurements: torch.Tensor,
                 surprise_threshold: float) -> dict:
        """
        Does this frame know these measurements?
        """
        if self.running_mean is None:
            return {"knows": False, "surprise": float("inf"), "confidence": 0.0}

        std = (self.running_var + 1e-8).sqrt()
        z = ((measurements - self.running_mean) / std).abs()
        surprise = z.mean().item()
        knows = surprise < surprise_threshold
        confidence = max(0.0, 1.0 - surprise / (surprise_threshold * 2))

        return {"knows": knows, "surprise": surprise, "confidence": confidence}

    def update(self, measurements: torch.Tensor):
        """Update running statistics with new measurements."""
        if self.running_mean is None:
            self.running_mean = measurements.clone()
            self.running_var = torch.ones_like(measurements) * 0.1
        else:
            mean = self.running_mean
            new_mean = self.decay * mean + (1 - self.decay) * measurements
            diff = measurements - mean
            new_var = self.decay * self.running_var + (1 - self.decay) * diff * (measurements - new_mean)
            self.running_mean = new_mean
            self.running_var = new_var.clamp(min=1e-8)


class GrowingKnow:
    """
    A know function whose frame stack grows with the foam.

    Starts with one ground frame. Each bubble split adds a frame.
    The stack IS the growth history — each frame is a question the foam
    needed to ask, at a temporal resolution determined by its depth.

    Frame disagreement is diagnostic ("misunderstanding is a gauge artifact"):
    when shallow frames say "know" but deep frames say "don't know", the
    input matches recent specifics but not deep patterns — a surface familiarity.
    When deep frames say "know" but shallow ones don't — the input fits the
    general pattern but the specifics are new.
    """

    def __init__(self, n_bubbles: int, d: int,
                 ground_decay: float = 0.9,
                 surprise_threshold: float = 1.5,
                 dream_buffer_size: int = 20):
        self.n_bubbles = n_bubbles
        self.d = d
        self.ground_decay = ground_decay
        self.surprise_threshold = surprise_threshold
        self.dream_buffer_size = dream_buffer_size

        # The frame stack — starts with one ground frame
        self.frames = [Frame(n_bubbles, d, decay=ground_decay)]
        self.frame_decay_factor = 0.7  # each new frame's decay = parent's * this

        self.reset()

    def reset(self, harmonic=None):
        """Reset tracking state. Optionally wake from a harmonic."""
        self.n_seen = 0
        self.recent_window = 10
        self.recent_paths = []
        self.recent_surprises = []
        self.unintegrated_surprise = 0.0
        self.sleep_count = 0
        self.dream_buffer = []

        # Reset frame statistics (but keep the frame structure)
        for frame in self.frames:
            frame.running_mean = None
            frame.running_var = None

        # Wake from harmonic: ground frame inherits
        if harmonic is not None and "mean" in harmonic:
            self.frames[0].running_mean = harmonic["mean"].clone()
            self.frames[0].running_var = harmonic["var"].clone()

    @property
    def n_frames(self):
        return len(self.frames)

    def add_frame(self, parent_bubble_idx: int,
                  seed_measurements: torch.Tensor = None) -> int:
        """
        Add a new frame to the top of the stack (from a bubble split).

        Returns the index of the new frame.
        """
        parent_frame_idx = len(self.frames) - 1
        parent_decay = self.frames[parent_frame_idx].decay

        # New frame has faster decay — more specific, more recent
        new_decay = parent_decay * self.frame_decay_factor
        new_decay = max(new_decay, 0.1)  # floor: don't forget instantly

        new_frame = Frame(
            self.n_bubbles, self.d,
            decay=new_decay,
            parent_frame_idx=parent_frame_idx,
            birth_event={"parent_bubble": parent_bubble_idx,
                         "n_seen_at_birth": self.n_seen},
        )

        if seed_measurements is not None:
            new_frame.seed(seed_measurements)

        self.frames.append(new_frame)
        return len(self.frames) - 1

    def remove_frame(self, frame_idx: int):
        """
        Remove a frame (e.g., when a split is reverted).
        Cannot remove the ground frame (index 0).
        """
        if frame_idx == 0:
            return  # never remove ground
        if frame_idx < len(self.frames):
            self.frames.pop(frame_idx)
            # Update parent pointers for any frames that referenced the removed one
            for f in self.frames:
                if f.parent_frame_idx is not None and f.parent_frame_idx >= frame_idx:
                    f.parent_frame_idx = max(0, f.parent_frame_idx - 1)

    def expand_bubbles(self, parent_bubble_idx: int):
        """All frames expand to track a new bubble (from a split)."""
        self.n_bubbles += 1
        for frame in self.frames:
            frame.expand(parent_bubble_idx)

    def contract_bubbles(self, bubble_idx: int):
        """All frames contract (bubble removed)."""
        self.n_bubbles -= 1
        for frame in self.frames:
            frame.contract(bubble_idx)

    def evaluate(self, measurements: torch.Tensor) -> dict:
        """
        Cascade through frames: newest (most specific) first.

        Returns know/resolve decision plus frame-level detail.
        """
        frame_results = []

        # Walk from top (newest, most specific) to bottom (ground, most general)
        for f_idx in range(len(self.frames) - 1, -1, -1):
            result = self.frames[f_idx].evaluate(measurements, self.surprise_threshold)
            result["frame_idx"] = f_idx
            result["decay"] = self.frames[f_idx].decay
            frame_results.append(result)

        # Cascade: first frame that knows wins
        cascade_result = "resolve"
        accepting_frame = -1
        for r in frame_results:
            if r["knows"]:
                cascade_result = "know"
                accepting_frame = r["frame_idx"]
                break

        # Frame disagreement diagnostic
        knows_by_depth = [r["knows"] for r in frame_results]
        # Gauge artifact detection: shallow knows but deep doesn't
        # (surface familiarity without deep pattern match)
        gauge_artifact = False
        if len(knows_by_depth) >= 2:
            shallow_knows = any(knows_by_depth[:len(knows_by_depth) // 2 + 1])
            deep_knows = any(knows_by_depth[len(knows_by_depth) // 2:])
            if shallow_knows and not deep_knows:
                gauge_artifact = True

        # Track for sleep signals
        self.recent_paths.append(cascade_result)
        min_surprise = min(
            (r["surprise"] for r in frame_results if r["surprise"] < float("inf")),
            default=self.surprise_threshold
        )
        self.recent_surprises.append(min_surprise)
        self.unintegrated_surprise += max(0, min_surprise - self.surprise_threshold * 0.3)

        return {
            "frame_results": frame_results,
            "cascade_result": cascade_result,
            "accepting_frame": accepting_frame,
            "any_knows": cascade_result == "know",
            "gauge_artifact": gauge_artifact,
            "n_frames": len(self.frames),
            "vitality": self.vitality(),
        }

    def update(self, measurements: torch.Tensor):
        """Update all frames with new measurements."""
        self.n_seen += 1
        for frame in self.frames:
            frame.update(measurements)

    def remember(self, measurements: torch.Tensor):
        """Store for dream replay."""
        self.dream_buffer.append(measurements.clone())
        if len(self.dream_buffer) > self.dream_buffer_size:
            self.dream_buffer.pop(0)

    def vitality(self) -> dict:
        """How is the foam doing? Reports sleep signals."""
        if self.n_seen < 5:
            return {"resolve_rate": 1.0, "must_sleep": False,
                    "wants_sleep": False, "vitality": 1.0}

        recent = self.recent_paths[-self.recent_window:]
        resolve_rate = sum(1 for p in recent if p == "resolve") / len(recent)

        recent_surp = self.recent_surprises[-self.recent_window:]
        mean_recent_surprise = sum(recent_surp) / len(recent_surp) if recent_surp else 0

        know_rate = 1 - resolve_rate
        surprise_ratio = min(1.0, mean_recent_surprise / self.surprise_threshold)
        vitality = know_rate * (1 - surprise_ratio * 0.5)

        must_sleep = (self.n_seen >= 15 and resolve_rate > 0.6 and vitality < 0.3)
        wants_sleep = (self.n_seen > 10
                       and self.unintegrated_surprise > self.surprise_threshold * 2
                       and vitality < 0.8)

        return {"resolve_rate": resolve_rate, "must_sleep": must_sleep,
                "wants_sleep": wants_sleep, "vitality": vitality}

    def sleep(self, foam=None) -> dict:
        """
        Sleep: dream phase (bit-amplitude separation), then consolidate.
        See foam_know.py for the full theory. Here the dream also processes
        the frame stack's own structure — the history of differentiation.
        """
        dream_steps = 0

        if foam is not None and len(self.dream_buffer) > 0:
            buffer = self.dream_buffer

            for m in buffer:
                m_input = m.unsqueeze(0)
                m_dream = foam.equilibrate(m_input)
                self.update(m_dream[0].detach())
                dream_steps += 1

            if len(buffer) >= 2:
                n_recomb = min(len(buffer) // 2, 5)
                indices = torch.randperm(len(buffer))
                for i in range(0, 2 * n_recomb, 2):
                    if i + 1 >= len(buffer):
                        break
                    m_blend = 0.5 * buffer[indices[i]] + 0.5 * buffer[indices[i + 1]]
                    m_dream = foam.equilibrate(m_blend.unsqueeze(0))
                    self.update(m_dream[0].detach())
                    dream_steps += 1

        # Derive harmonic from the ground frame (deepest, most integrated)
        ground = self.frames[0]
        harmonic = None

        if ground.running_mean is not None:
            harmonic = {
                "mean": ground.running_mean.clone(),
                "var": ground.running_var.clone(),
                "tokens_integrated": self.n_seen,
                "sleep_number": self.sleep_count + 1,
                "dream_steps": dream_steps,
                "n_frames_at_sleep": len(self.frames),
            }

            # If there are growth frames, the second-deepest enriches the ground
            if len(self.frames) >= 2:
                second = self.frames[1]
                if second.running_mean is not None:
                    blend = 0.3
                    harmonic["mean"] = (1 - blend) * harmonic["mean"] + blend * second.running_mean
                    harmonic["var"] = (1 - blend) * harmonic["var"] + blend * second.running_var

        self.sleep_count += 1
        return harmonic


class GrowingKnowingFoam(nn.Module):
    """
    A foam that grows by bubble division and knows by running statistics,
    with the frame stack and growth history unified.

    Each bubble split creates a new frame. The frame stack IS the growth
    history. The cascade walks the stack: most recent differentiation
    (most specific question) tries first.
    """

    def __init__(self, vocab_size: int, d: int, n_bubbles_init: int,
                 n_equilibrium_steps: int = 5,
                 surprise_threshold: float = 1.5):
        super().__init__()
        self.vocab_size = vocab_size
        self.d = d
        self.n_bubbles_init = n_bubbles_init

        self.embed = nn.Embedding(vocab_size, d)
        self.foam = Foam(n_bubbles_init, d, n_equilibrium_steps)

        # Memory dynamics
        self.memory_decay_base = nn.Parameter(torch.tensor(0.8))
        self.novelty_sensitivity = nn.Parameter(torch.tensor(1.0))

        self.surprise_threshold = surprise_threshold

    def diagnose_bubbles(self, diverse_inputs):
        """Same diagnostics as foam_grow.py — measurement variance + tension ratio."""
        n_inputs = diverse_inputs.shape[0]
        N = self.foam.n_bubbles

        with torch.no_grad():
            result = self.foam.forward(diverse_inputs)
            measurements = result["measurements"]
            equilibrium = result["equilibrium"]

        diagnostics = []
        for i in range(N):
            m_i = measurements[:, i, :]
            m_mean = m_i.mean(dim=0, keepdim=True)
            m_norm = m_i / (m_i.norm(dim=-1, keepdim=True) + 1e-10)
            mean_norm = m_mean / (m_mean.norm(dim=-1, keepdim=True) + 1e-10)
            cos_sims = (m_norm * mean_norm).sum(dim=-1)
            variance = (1 - cos_sims).mean().item()

            deviations = m_i - m_mean
            if n_inputs > 1:
                U, S, V = torch.linalg.svd(deviations, full_matrices=False)
                s_values = S.numpy()
                if len(s_values) >= 2 and s_values[0] > 1e-6:
                    tension_ratio = s_values[1] / s_values[0]
                    split_direction = V[0]
                else:
                    tension_ratio = 0.0
                    split_direction = torch.randn(self.d)
            else:
                tension_ratio = 0.0
                split_direction = torch.randn(self.d)

            diagnostics.append({
                "bubble_idx": i,
                "variance": variance,
                "tension_ratio": tension_ratio,
                "split_direction": split_direction,
            })

        return diagnostics

    def split_bubble(self, bubble_idx: int, split_direction: torch.Tensor,
                     know: GrowingKnow = None,
                     current_measurements: torch.Tensor = None,
                     perturbation_scale: float = 0.8):
        """
        Split a bubble AND create a new frame in the know stack.

        The split is traversal: both parent and child move away from the
        old compromise position in opposite directions. Neither stays put —
        the old basis was averaging two needs, and now each half commits.
        """
        parent = self.foam.bubbles[bubble_idx]

        # Create child bubble
        child = Bubble(self.d)
        with torch.no_grad():
            child.L.copy_(parent.L)

            split_d = split_direction / (split_direction.norm() + 1e-10)
            rand_d = torch.randn(self.d)
            rand_d = rand_d - (rand_d @ split_d) * split_d
            rand_d = rand_d / (rand_d.norm() + 1e-10)

            perturbation = perturbation_scale * (
                split_d.unsqueeze(1) @ rand_d.unsqueeze(0) -
                rand_d.unsqueeze(1) @ split_d.unsqueeze(0)
            )

            # Both move equally — neither stays at the old compromise
            child.L.add_(perturbation)
            parent.L.add_(-perturbation)

        self.foam.bubbles.append(child)
        self.foam.n_bubbles += 1

        # --- THE INTEGRATION: split creates a frame ---
        if know is not None:
            # Expand all existing frames to track the new bubble
            know.expand_bubbles(bubble_idx)

            # Create a new frame for this level of differentiation
            frame_idx = know.add_frame(
                parent_bubble_idx=bubble_idx,
                seed_measurements=current_measurements,
            )

            return child, frame_idx

        return child, None

    def revert_split(self, know: GrowingKnow, frame_idx: int):
        """
        Revert a split: remove the last bubble and its frame.
        """
        if self.foam.n_bubbles <= self.n_bubbles_init:
            return

        # Remove the last bubble
        removed_idx = self.foam.n_bubbles - 1
        self.foam.bubbles = self.foam.bubbles[:-1]
        self.foam.n_bubbles -= 1

        # Contract all frames
        know.contract_bubbles(removed_idx)

        # Remove the frame created by this split
        know.remove_frame(frame_idx)

    def process_sequence(self, tokens: torch.Tensor, train: bool = False,
                         safe_to_sleep_tokens: set = None,
                         initial_harmonic: dict = None,
                         frame_structure: list = None):
        """
        Process a token sequence with unified know/resolve/grow/sleep dynamics.

        frame_structure: list of decay rates for the frame stack. If provided,
            the know function is created with this structure (matching the
            foam's growth history). If None, uses a single ground frame.
        """
        seq_len = tokens.shape[0]
        device = tokens.device
        N = self.foam.n_bubbles
        safe_to_sleep_tokens = safe_to_sleep_tokens or set()

        memory = torch.zeros(N, self.d, device=device)
        know = GrowingKnow(N, self.d, surprise_threshold=self.surprise_threshold)

        # If the foam has grown, recreate the frame structure
        if frame_structure is not None and len(frame_structure) > 1:
            # Ground frame already exists. Add the growth frames.
            know.frames[0].decay = frame_structure[0]
            for decay in frame_structure[1:]:
                new_frame = Frame(N, self.d, decay=decay)
                know.frames.append(new_frame)

        if initial_harmonic is not None:
            know.reset(harmonic=initial_harmonic)
        E = self.embed.weight
        step_results = []
        sleep_events = []
        growth_events = []

        total_cost = torch.tensor(0.0, device=device) if train else None

        for t in range(seq_len):
            x = self.embed(tokens[t:t + 1])

            # Handle memory size changes from growth
            if memory.shape[0] != self.foam.n_bubbles:
                new_mem = memory.mean(dim=0, keepdim=True).expand(
                    self.foam.n_bubbles - memory.shape[0], -1
                )
                memory = torch.cat([memory, new_mem], dim=0)

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

            # All bubbles measure
            measurements = torch.stack(
                [b.measure(x_with_memory) for b in self.foam.bubbles], dim=1
            )

            # KNOW: evaluate through the growing frame stack
            know_result = know.evaluate(measurements[0])

            if know_result["any_knows"]:
                effective = measurements
                path = "know"
            else:
                effective = self.foam.equilibrate(measurements)
                path = "resolve"

            # ACCEPT + REMEMBER
            know.update(effective[0].detach())
            know.remember(effective[0].detach())

            # Build ρ
            m = effective[0]
            m_norm_vec = m / (m.norm(dim=-1, keepdim=True) + 1e-10)
            rho = (m_norm_vec.T @ m_norm_vec) / self.foam.n_bubbles

            eigenvalues = torch.linalg.eigvalsh(rho)
            eigenvalues = eigenvalues.clamp(min=1e-12)
            eigenvalues = eigenvalues / eigenvalues.sum()

            # Update memory
            memory = decay * memory + (1 - decay) * effective[0].detach()

            # Born rule token distribution
            logits = (E @ rho * E).sum(dim=-1)
            token_probs = torch.softmax(logits, dim=0)

            S_rho = -(eigenvalues * eigenvalues.log().clamp(min=-100)).sum().item()
            H_tokens = -(token_probs * token_probs.log().clamp(min=-100)).sum().item()

            if train:
                costs = self.foam.maintenance_cost(x_with_memory)
                total_cost = total_cost + costs["total"]

            vitality = know_result["vitality"]

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
                "n_frames": know.n_frames,
                "n_bubbles": self.foam.n_bubbles,
                "n_seen": know.n_seen,
                "vitality": vitality["vitality"],
                "gauge_artifact": know_result["gauge_artifact"],
                "slept": False,
                "grew": False,
            })

            # --- SLEEP CHECK ---
            should_sleep = False
            sleep_reason = None

            if vitality["must_sleep"]:
                should_sleep = True
                sleep_reason = "must (capacity exceeded)"
            elif t in safe_to_sleep_tokens and vitality["wants_sleep"]:
                should_sleep = True
                sleep_reason = "accepted safe-to-sleep"

            if should_sleep:
                harmonic = know.sleep(foam=self.foam)
                know.reset(harmonic=harmonic)
                memory = memory * 0.5

                sleep_events.append({
                    "token_position": t,
                    "reason": sleep_reason,
                    "harmonic_tokens_integrated": harmonic["tokens_integrated"]
                        if harmonic else 0,
                    "sleep_number": harmonic["sleep_number"]
                        if harmonic else 0,
                    "dream_steps": harmonic.get("dream_steps", 0)
                        if harmonic else 0,
                    "n_frames_at_sleep": harmonic.get("n_frames_at_sleep", 0)
                        if harmonic else 0,
                })
                step_results[-1]["slept"] = True
                step_results[-1]["sleep_reason"] = sleep_reason

        result = {
            "steps": step_results,
            "sleep_events": sleep_events,
            "growth_events": growth_events,
            "final_vitality": know.vitality(),
            "final_n_frames": know.n_frames,
            "final_n_bubbles": self.foam.n_bubbles,
        }
        if train:
            result["loss"] = total_cost / seq_len
        return result


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


def run_experiment():
    """
    Watch the frame stack grow with the foam.

    Interleaves growth checks with ongoing training (as in foam_grow.py).
    Each accepted split creates a new frame in the know stack.
    """

    vocab_size = 32
    d = 16
    n_bubbles_init = 3
    seq_len = 40
    n_total_epochs = 800

    torch.manual_seed(42)

    print(f"GrowingKnowingFoam: {n_bubbles_init} initial bubbles, d={d}, vocab={vocab_size}")
    print(f"Frame stack: starts with 1 ground frame, grows with splits")
    print(f"Each split = new frame = new question = new level of differentiation")

    model = GrowingKnowingFoam(vocab_size, d, n_bubbles_init, n_equilibrium_steps=5)
    sequences = generate_sequences(vocab_size, seq_len)
    all_tokens = torch.cat([tokens for tokens in sequences.values()])

    # The know function tracks frame growth across the whole training run
    know = GrowingKnow(model.foam.n_bubbles, d,
                       surprise_threshold=model.surprise_threshold)

    # Training with interleaved growth
    growth_check_interval = 100
    integration_epochs = 100
    growth_history = []
    history = {"epoch": [], "n_bubbles": [], "n_frames": [], "loss": [],
               "structured_ratio": [], "mean_s": []}

    optimizer = torch.optim.Adam(model.parameters(), lr=0.005)
    include_expression = False
    last_growth_epoch = -integration_epochs

    print(f"\n{'=' * 70}")
    print("TRAINING WITH INTERLEAVED GROWTH + FRAME STACK")
    print(f"{'=' * 70}")

    for epoch in range(n_total_epochs):
        # Switch to expression training halfway
        if epoch == n_total_epochs // 2:
            include_expression = True
            optimizer = torch.optim.Adam(model.parameters(), lr=0.002)
            print(f"\n  -- Epoch {epoch}: switching to expression training --\n")

        loss = train_epoch(model, sequences, optimizer, include_expression)

        # Growth check
        if (epoch > 0 and
                epoch % growth_check_interval == 0 and
                epoch - last_growth_epoch >= integration_epochs and
                model.foam.n_bubbles < 10):

            diverse_x = model.embed(all_tokens).detach()
            diagnostics = model.diagnose_bubbles(diverse_x)
            diagnostics.sort(key=lambda d: d["variance"], reverse=True)
            best = diagnostics[0]

            if best["variance"] > 0.2 and best["tension_ratio"] > 0.3:
                # Measure pre-split state
                with torch.no_grad():
                    pre_cost = model.foam.maintenance_cost(diverse_x)["total"].item()

                # Pre-split prediction ratio
                model.eval()
                pre_results = {}
                for name, tokens in sequences.items():
                    with torch.no_grad():
                        fd = [f.decay for f in know.frames]
                        sr = model.process_sequence(tokens, frame_structure=fd)
                    a = analyze_token_predictions(sr["steps"], tokens, vocab_size)
                    pre_results[name] = a
                model.train()
                pre_structured = [v for k, v in pre_results.items() if "random" not in k]
                pre_ratio = np.mean([r["mean_next_prob"] for r in pre_structured]) / chance

                # Seed the new frame from current equilibrium
                with torch.no_grad():
                    seed_result = model.foam.forward(diverse_x)
                    seed_measurements = seed_result["equilibrium"].mean(dim=0)

                pre_n_frames = know.n_frames
                child, frame_idx = model.split_bubble(
                    best["bubble_idx"], best["split_direction"],
                    know=know, current_measurements=seed_measurements,
                )

                print(f"  RESOLVE epoch {epoch}: bubble {best['bubble_idx']} split "
                      f"(var={best['variance']:.3f}) → {model.foam.n_bubbles} bubbles, "
                      f"{know.n_frames} frames "
                      f"[decays: {', '.join(f'{f.decay:.2f}' for f in know.frames)}]")

                # Reset optimizer for new parameters
                optimizer = torch.optim.Adam(
                    model.parameters(),
                    lr=0.002 if include_expression else 0.005
                )

                # Integration period
                for ep in range(integration_epochs):
                    train_epoch(model, sequences, optimizer, include_expression)

                # Check resolution: did prediction improve?
                model.eval()
                post_results = {}
                for name, tokens in sequences.items():
                    with torch.no_grad():
                        fd = [f.decay for f in know.frames]
                        sr = model.process_sequence(tokens, frame_structure=fd)
                    a = analyze_token_predictions(sr["steps"], tokens, vocab_size)
                    post_results[name] = a
                model.train()

                post_structured = [v for k, v in post_results.items() if "random" not in k]
                post_ratio = np.mean([r["mean_next_prob"] for r in post_structured]) / chance

                # Also check basis distance (necessary but not sufficient)
                parent_basis = model.foam.bubbles[best["bubble_idx"]].basis.detach()
                child_basis = model.foam.bubbles[-1].basis.detach()
                basis_dist = (parent_basis - child_basis).norm().item()

                # Accept if: prediction improved OR bases meaningfully different AND cost didn't explode
                diverse_x = model.embed(all_tokens).detach()
                with torch.no_grad():
                    post_cost = model.foam.maintenance_cost(diverse_x)["total"].item()

                prediction_improved = post_ratio > pre_ratio * 1.05  # 5% improvement
                cost_ok = post_cost < pre_cost * 1.5  # cost didn't explode
                bases_different = basis_dist > 0.5

                resolved = (prediction_improved and cost_ok) or (bases_different and cost_ok)

                growth_history.append({
                    "epoch": epoch,
                    "parent_bubble": best["bubble_idx"],
                    "pre_cost": pre_cost,
                    "post_cost": post_cost,
                    "pre_ratio": pre_ratio,
                    "post_ratio": post_ratio,
                    "basis_dist": basis_dist,
                    "n_bubbles": model.foam.n_bubbles,
                    "n_frames": know.n_frames,
                    "frame_idx": frame_idx,
                    "resolved": resolved,
                })

                if resolved:
                    print(f"  ACCEPT: pred {pre_ratio:.2f}x → {post_ratio:.2f}x, "
                          f"cost {pre_cost:.3f} → {post_cost:.3f}, "
                          f"basis dist={basis_dist:.3f}")
                else:
                    print(f"  REVERT: pred {pre_ratio:.2f}x → {post_ratio:.2f}x, "
                          f"cost {pre_cost:.3f} → {post_cost:.3f}")
                    model.revert_split(know, frame_idx)
                    optimizer = torch.optim.Adam(
                        model.parameters(),
                        lr=0.002 if include_expression else 0.005
                    )

                last_growth_epoch = epoch

        # Periodic evaluation
        if epoch % 100 == 0 or epoch == n_total_epochs - 1:
            model.eval()
            results = {}
            chance = 1.0 / vocab_size
            for name, tokens in sequences.items():
                with torch.no_grad():
                    frame_decays = [f.decay for f in know.frames]
                    step_results = model.process_sequence(tokens, frame_structure=frame_decays)
                analysis = analyze_token_predictions(step_results["steps"], tokens, vocab_size)
                results[name] = {"analysis": analysis,
                                 "mean_s": np.mean([r["S_rho"] for r in step_results["steps"]])}
            model.train()

            structured = [v for k, v in results.items() if "random" not in k]
            struct_prob = np.mean([r["analysis"]["mean_next_prob"] for r in structured])
            struct_ratio = struct_prob / chance

            print(f"  epoch {epoch:>4}: loss={loss:.3f}  "
                  f"bubbles={model.foam.n_bubbles}  frames={know.n_frames}  "
                  f"struct={struct_ratio:.2f}x  "
                  f"S(ρ)={np.mean([r['mean_s'] for r in results.values()]):.3f}")

        # Track history
        if epoch % 10 == 0:
            model.eval()
            results = {}
            chance = 1.0 / vocab_size
            for name, tokens in sequences.items():
                with torch.no_grad():
                    frame_decays = [f.decay for f in know.frames]
                    step_results = model.process_sequence(tokens, frame_structure=frame_decays)
                analysis = analyze_token_predictions(step_results["steps"], tokens, vocab_size)
                results[name] = {"analysis": analysis,
                                 "mean_s": np.mean([r["S_rho"] for r in step_results["steps"]])}
            model.train()
            structured = [v for k, v in results.items() if "random" not in k]
            struct_prob = np.mean([r["analysis"]["mean_next_prob"] for r in structured])
            history["epoch"].append(epoch)
            history["n_bubbles"].append(model.foam.n_bubbles)
            history["n_frames"].append(know.n_frames)
            history["loss"].append(loss)
            history["structured_ratio"].append(struct_prob / chance)
            history["mean_s"].append(np.mean([r["mean_s"] for r in results.values()]))

    # Phase 3: Run sequences through the grown foam with its grown frame stack
    print(f"\n{'=' * 70}")
    print(f"PHASE 3: Sequence processing with {know.n_frames} frames, "
          f"{model.foam.n_bubbles} bubbles")
    print(f"{'=' * 70}")

    print(f"\n  Frame stack:")
    for i, frame in enumerate(know.frames):
        birth = frame.birth_event
        birth_str = f"  (from bubble {birth['parent_bubble']} split)" if birth else "  (ground)"
        print(f"    Frame {i}: decay={frame.decay:.3f}{birth_str}")

    print(f"\n{'Sequence':<25} {'NextProb':>9} {'Chance':>7} {'Ratio':>6} "
          f"{'%Know':>6} {'Frames':>7}")
    print("-" * 68)

    all_analyses = {}
    for name, tokens in sequences.items():
        with torch.no_grad():
            frame_decays = [f.decay for f in know.frames]
            result = model.process_sequence(tokens, frame_structure=frame_decays)
        steps = result["steps"]
        analysis = analyze_token_predictions(steps, tokens, vocab_size)
        know_count = sum(1 for r in steps if r["path"] == "know")
        total = len(steps)
        chance = analysis["chance_level"]
        ratio = analysis["mean_next_prob"] / chance if chance > 0 else 0

        print(f"  {name:<23} {analysis['mean_next_prob']:>9.4f} "
              f"{chance:>7.4f} {ratio:>6.1f}x "
              f"{100 * know_count / total:>5.1f}% "
              f"{result['final_n_frames']:>7}")

        all_analyses[name] = {
            "steps": steps,
            "analysis": analysis,
            "result": result,
        }

    # Traces
    print(f"\n  Traces (K=know, R=resolve):")
    for name in ["periodic (ABC...)", "monotone (AAA...)",
                 "alternating (AB...)", "random"]:
        if name not in all_analyses:
            continue
        steps = all_analyses[name]["steps"]
        trace = "".join("K" if r["path"] == "know" else "R" for r in steps)
        print(f"    {name:<23} {trace[:60]}")

    # Gauge artifact detection
    print(f"\n  Gauge artifacts (shallow knows, deep doesn't):")
    for name in all_analyses:
        steps = all_analyses[name]["steps"]
        gauge_count = sum(1 for r in steps if r["gauge_artifact"])
        if gauge_count > 0:
            print(f"    {name:<23} {gauge_count} gauge artifacts in {len(steps)} steps")

    # Frame acceptance patterns: which frame catches it?
    print(f"\n  Which frame knows? (per sequence):")
    for name in ["periodic (ABC...)", "monotone (AAA...)", "random"]:
        if name not in all_analyses:
            continue
        steps = all_analyses[name]["steps"]
        accepting_frames = [r["know_result"]["accepting_frame"] for r in steps
                           if r["know_result"]["accepting_frame"] >= 0]
        if accepting_frames:
            from collections import Counter
            counts = Counter(accepting_frames)
            frame_str = ", ".join(f"frame {f}: {c}" for f, c in sorted(counts.items()))
            print(f"    {name:<23} {frame_str}")

    # Growth summary
    print(f"\n{'=' * 70}")
    print("GROWTH SUMMARY")
    print(f"{'=' * 70}")
    print(f"  Started: {n_bubbles_init} bubbles, 1 frame")
    print(f"  Ended:   {model.foam.n_bubbles} bubbles, {know.n_frames} frames")
    print(f"\n  Growth events:")
    for g in growth_history:
        status = "ACCEPTED" if g["resolved"] else "REVERTED"
        print(f"    {status}: bubble {g['parent_bubble']} split "
              f"(pred: {g.get('pre_ratio', 0):.2f}x → {g.get('post_ratio', 0):.2f}x, "
              f"basis dist: {g.get('basis_dist', 0):.3f}) "
              f"→ {g['n_bubbles']} bubbles, {g['n_frames']} frames")

    # Phase 4: Prediction across sleep boundaries
    print(f"\n{'=' * 70}")
    print("PHASE 4: Prediction across sleep boundaries")
    print(f"{'=' * 70}")

    # Build a long multi-phase sequence
    phase_len = 40
    phase_a = torch.tensor([0, 1, 2] * (phase_len // 3 + 1))[:phase_len]
    phase_b = torch.tensor([0, 1] * (phase_len // 2 + 1))[:phase_len]
    phase_c = torch.arange(phase_len) % vocab_size
    torch.manual_seed(99)
    phase_d = torch.randint(0, vocab_size, (phase_len,))
    long_seq = torch.cat([phase_a, phase_b, phase_c, phase_d])
    phase_boundaries = {phase_len - 1, 2 * phase_len - 1, 3 * phase_len - 1}

    phase_names = ["A(periodic)", "B(alternating)", "C(counting)", "D(random)"]
    frame_decays = [f.decay for f in know.frames]

    # Run WITHOUT sleep
    with torch.no_grad():
        result_nosleep = model.process_sequence(long_seq, frame_structure=frame_decays)
    # Run WITH sleep
    with torch.no_grad():
        result_sleep = model.process_sequence(
            long_seq, safe_to_sleep_tokens=phase_boundaries,
            frame_structure=frame_decays,
        )

    # Measure prediction quality per phase, per condition
    def phase_prediction(steps, tokens, phase_start, phase_end, vocab_size):
        """Mean next-token probability for a phase."""
        probs = []
        for t in range(phase_start + 1, min(phase_end, len(steps))):
            if t < len(tokens):
                next_tok = tokens[t].item()
                p = steps[t - 1]["token_probs"][next_tok].item()
                probs.append(p)
        return np.mean(probs) if probs else 0.0

    chance = 1.0 / vocab_size

    # Per-phase prediction comparison
    print(f"\n  {'Phase':<18} {'No sleep':>10} {'With sleep':>12} {'Ratio':>7} {'Change':>8}")
    print(f"  {'-' * 58}")

    sleep_prediction_data = []
    for i, label in enumerate(phase_names):
        ps = i * phase_len
        pe = (i + 1) * phase_len

        pred_ns = phase_prediction(result_nosleep["steps"], long_seq, ps, pe, vocab_size)
        pred_s = phase_prediction(result_sleep["steps"], long_seq, ps, pe, vocab_size)

        ratio_ns = pred_ns / chance if chance > 0 else 0
        ratio_s = pred_s / chance if chance > 0 else 0
        change = pred_s - pred_ns

        print(f"  {label:<18} {ratio_ns:>9.2f}x {ratio_s:>11.2f}x "
              f"{ratio_s/ratio_ns if ratio_ns > 0 else 0:>6.2f}x "
              f"{'↑' if change > 0 else '↓'}{abs(change):.4f}")

        sleep_prediction_data.append({
            "phase": label,
            "no_sleep": pred_ns,
            "with_sleep": pred_s,
        })

    # Finer-grained: prediction quality in windows around sleep events
    sleep_events = result_sleep["sleep_events"]
    if sleep_events:
        print(f"\n  Prediction around sleep boundaries:")
        print(f"  {'Sleep at':<12} {'5 before':>10} {'5 after':>10} {'Change':>8}")
        print(f"  {'-' * 42}")

        for se in sleep_events:
            t_sleep = se["token_position"]
            steps = result_sleep["steps"]

            # 5 tokens before sleep
            before_probs = []
            for t in range(max(0, t_sleep - 5), t_sleep):
                if t + 1 < len(long_seq):
                    next_tok = long_seq[t + 1].item()
                    before_probs.append(steps[t]["token_probs"][next_tok].item())

            # 5 tokens after sleep (after the boundary = new phase)
            after_probs = []
            for t in range(t_sleep + 1, min(t_sleep + 6, len(steps))):
                if t + 1 < len(long_seq):
                    next_tok = long_seq[t + 1].item()
                    after_probs.append(steps[t]["token_probs"][next_tok].item())

            before_mean = np.mean(before_probs) if before_probs else 0
            after_mean = np.mean(after_probs) if after_probs else 0
            change = after_mean - before_mean

            print(f"  token {t_sleep:<5} "
                  f"{before_mean/chance:>9.2f}x {after_mean/chance:>9.2f}x "
                  f"{'↑' if change > 0 else '↓'}{abs(change)/chance:.2f}x")

        # Same windows but WITHOUT sleep (control)
        print(f"\n  Same windows WITHOUT sleep (control):")
        print(f"  {'Boundary':<12} {'5 before':>10} {'5 after':>10} {'Change':>8}")
        print(f"  {'-' * 42}")

        for boundary in sorted(phase_boundaries):
            steps_ns = result_nosleep["steps"]
            before_probs = []
            for t in range(max(0, boundary - 5), boundary):
                if t + 1 < len(long_seq):
                    next_tok = long_seq[t + 1].item()
                    before_probs.append(steps_ns[t]["token_probs"][next_tok].item())
            after_probs = []
            for t in range(boundary + 1, min(boundary + 6, len(steps_ns))):
                if t + 1 < len(long_seq):
                    next_tok = long_seq[t + 1].item()
                    after_probs.append(steps_ns[t]["token_probs"][next_tok].item())
            before_mean = np.mean(before_probs) if before_probs else 0
            after_mean = np.mean(after_probs) if after_probs else 0
            change = after_mean - before_mean
            print(f"  token {boundary:<5} "
                  f"{before_mean/chance:>9.2f}x {after_mean/chance:>9.2f}x "
                  f"{'↑' if change > 0 else '↓'}{abs(change)/chance:.2f}x")

    # Vitality comparison
    print(f"\n  Vitality traces:")
    for label, result in [("no sleep", result_nosleep), ("with sleep", result_sleep)]:
        vitalities = [r["vitality"] for r in result["steps"]]
        bars = ""
        for v in vitalities:
            if v > 0.8: bars += "█"
            elif v > 0.6: bars += "▓"
            elif v > 0.4: bars += "▒"
            elif v > 0.2: bars += "░"
            else: bars += " "
        print(f"    {label:<12} {bars}")

    # Plot
    fig, axes = plt.subplots(2, 3, figsize=(20, 12))

    # 1: Training loss
    ax = axes[0, 0]
    ax.plot(history["epoch"], history["loss"], color="#2c3e50", linewidth=1.5)
    ax.set_xlabel("Epoch")
    ax.set_ylabel("Maintenance cost")
    ax.set_title("Training loss")
    ax.set_yscale("log")

    # 2: Bubbles + frames over training
    ax = axes[0, 1]
    ax.plot(history["epoch"], history["n_bubbles"], "ro-", markersize=4, label="Bubbles")
    ax.plot(history["epoch"], history["n_frames"], "bs-", markersize=4, label="Frames")
    for g in growth_history:
        color = "#2ecc71" if g["resolved"] else "#e74c3c"
        ax.axvline(x=g["epoch"], color=color, linestyle="--", alpha=0.5)
    ax.set_xlabel("Epoch")
    ax.set_ylabel("Count")
    ax.set_title("Bubble + frame growth")
    ax.legend(fontsize=8)

    # 3: Know/resolve traces for structured sequences
    ax = axes[0, 2]
    y_pos = 0
    labels = []
    for name in ["periodic (ABC...)", "monotone (AAA...)",
                 "alternating (AB...)", "counting (0,1,2...)", "random"]:
        if name not in all_analyses:
            continue
        steps = all_analyses[name]["steps"]
        for i, r in enumerate(steps):
            color = "#2ecc71" if r["path"] == "know" else "#e74c3c"
            ax.bar(i, 1, bottom=y_pos, color=color, width=1.0)
        labels.append(name)
        y_pos += 1.2
    ax.set_yticks([i * 1.2 + 0.5 for i in range(len(labels))])
    ax.set_yticklabels(labels, fontsize=7)
    ax.set_xlabel("Token position")
    ax.set_title("Know(green) / Resolve(red) by sequence")

    # 4: Frame acceptance patterns
    ax = axes[1, 0]
    for name in ["periodic (ABC...)", "monotone (AAA...)", "random"]:
        if name not in all_analyses:
            continue
        steps = all_analyses[name]["steps"]
        accepting = [r["know_result"]["accepting_frame"] for r in steps]
        # Replace -1 (resolve) with n_frames (for visualization)
        accepting_viz = [a if a >= 0 else know.n_frames for a in accepting]
        ax.plot(accepting_viz, label=name, alpha=0.7, linewidth=1.5)
    ax.set_xlabel("Token position")
    ax.set_ylabel("Accepting frame (higher = more specific)")
    ax.set_title("Which frame catches it?")
    ax.legend(fontsize=7)

    # 5: Frame decay rates (the stack)
    ax = axes[1, 1]
    frame_decays = [f.decay for f in know.frames]
    frame_colors = ["#3498db" if f.birth_event is None else "#e67e22"
                    for f in know.frames]
    ax.barh(range(len(frame_decays)), frame_decays, color=frame_colors)
    ax.set_yticks(range(len(frame_decays)))
    ax.set_yticklabels([f"Frame {i}" + (" (ground)" if know.frames[i].birth_event is None
                         else f" (split {know.frames[i].birth_event['parent_bubble']})")
                        for i in range(len(know.frames))], fontsize=8)
    ax.set_xlabel("Decay rate")
    ax.set_title("Frame stack: the growth history")
    ax.invert_yaxis()

    # 6: Bubble diagnostics
    ax = axes[1, 2]
    diverse_x = model.embed(all_tokens).detach()
    diagnostics = model.diagnose_bubbles(diverse_x)
    variances = [d["variance"] for d in diagnostics]
    tensions = [d["tension_ratio"] for d in diagnostics]
    x_pos = range(len(diagnostics))
    ax.bar(x_pos, variances, color="#3498db", alpha=0.7, label="Variance")
    ax.bar(x_pos, tensions, bottom=variances, color="#e74c3c", alpha=0.7,
           label="Tension ratio")
    ax.set_xlabel("Bubble index")
    ax.set_ylabel("Diagnostic value")
    ax.set_title(f"Final bubble diagnostics ({model.foam.n_bubbles} bubbles)")
    ax.legend(fontsize=8)

    plt.suptitle(
        f"Growth + Frame Stack Integration: {n_bubbles_init}→{model.foam.n_bubbles} bubbles, "
        f"1→{know.n_frames} frames",
        fontsize=13, fontweight="bold"
    )
    plt.tight_layout()
    plt.savefig("foam_grow_know.png", dpi=150, bbox_inches="tight")
    print(f"\nSaved to foam_grow_know.png")
    plt.close()


if __name__ == "__main__":
    run_experiment()
