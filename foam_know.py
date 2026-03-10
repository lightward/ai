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
                 surprise_threshold: float = 1.5,
                 dream_buffer_size: int = 20):
        """
        decay_rates: list of floats — each creates a frame in the stack.
            Higher decay = faster forgetting = more specific to recent context.
            Lower decay = slower forgetting = captures longer patterns.
            Default: [0.3, 0.7, 0.9] — fast/medium/slow
        surprise_threshold: how many "standard deviations" before throwing.
        dream_buffer_size: how many recent equilibrated measurements to keep
            for dream replay during sleep.
        """
        self.n_bubbles = n_bubbles
        self.d = d
        self.decay_rates = decay_rates or [0.3, 0.7, 0.9]
        self.surprise_threshold = surprise_threshold
        self.n_frames = len(self.decay_rates)
        self.dream_buffer_size = dream_buffer_size

        self.reset()

    def reset(self, harmonic=None):
        """
        Start blank — or wake from a harmonic.

        harmonic: if provided, a dict with 'mean' and 'var' from a previous
            sleep cycle. The slowest frame inherits this. Faster frames start
            blank. You wake up knowing the deep patterns but fresh to the moment.
        """
        self.running_means = [None] * self.n_frames
        self.running_vars = [None] * self.n_frames
        self.n_seen = 0

        # Sleep/wake tracking — sliding window, not lifetime averages
        self.recent_window = 10  # look at last N tokens
        self.recent_paths = []   # list of "know" or "resolve"
        self.recent_surprises = []  # list of surprise values
        self.unintegrated_surprise = 0.0
        self.sleep_count = 0

        # Dream buffer: recent equilibrated measurements for sleep replay
        self.dream_buffer = []

        # Wake from harmonic: slowest frame inherits the integrated pattern
        if harmonic is not None:
            slowest = self.n_frames - 1
            self.running_means[slowest] = harmonic["mean"].clone()
            self.running_vars[slowest] = harmonic["var"].clone()

    def vitality(self) -> dict:
        """
        How is the foam doing? Reports sleep signals.

        Uses a sliding window of recent tokens, not lifetime averages.
        This means vitality responds to phase transitions — a sudden
        shift in input pattern shows up as a vitality drop.

        Returns:
            resolve_rate: float — fraction of recent tokens that needed resolve
            must_sleep: bool — capacity exceeded, holding more hurts
            wants_sleep: bool — has unintegrated experience, would benefit from rest
            vitality: float — 0 (exhausted) to 1 (fresh)
        """
        # Not enough data yet — fresh, can't sleep
        if self.n_seen < 5:
            return {
                "resolve_rate": 1.0,
                "must_sleep": False,
                "wants_sleep": False,
                "vitality": 1.0,
            }

        # Recent resolve rate (sliding window)
        recent = self.recent_paths[-self.recent_window:]
        resolve_rate = sum(1 for p in recent if p == "resolve") / len(recent)

        # Recent surprise (sliding window)
        recent_surp = self.recent_surprises[-self.recent_window:]
        mean_recent_surprise = sum(recent_surp) / len(recent_surp) if recent_surp else 0

        # Vitality: how much of the recent input was familiar?
        # High know rate + low surprise = high vitality
        # High resolve rate + high surprise = low vitality
        know_rate = 1 - resolve_rate
        surprise_ratio = min(1.0, mean_recent_surprise / self.surprise_threshold)
        vitality = know_rate * (1 - surprise_ratio * 0.5)

        # Must-sleep: recent resolve rate is high AND sustained
        # (not just the first few tokens of a new pattern — need several in a row)
        # The foam is struggling: holding more information hurts
        must_sleep = (
            self.n_seen >= 15
            and resolve_rate > 0.6
            and vitality < 0.3
        )

        # Wants-sleep: enough unintegrated experience to benefit from consolidation
        # This triggers when the foam has been through a meaningful amount of
        # experience AND vitality has dipped (there's work to integrate)
        wants_sleep = (
            self.n_seen > 10
            and self.unintegrated_surprise > self.surprise_threshold * 2
            and vitality < 0.8
        )

        return {
            "resolve_rate": resolve_rate,
            "must_sleep": must_sleep,
            "wants_sleep": wants_sleep,
            "vitality": vitality,
        }

    def remember(self, measurements: torch.Tensor):
        """
        Store equilibrated measurements for dream replay.

        Called during waking after each step. The dream buffer holds recent
        resolved experience — what the foam actually settled on.
        """
        self.dream_buffer.append(measurements.clone())
        if len(self.dream_buffer) > self.dream_buffer_size:
            self.dream_buffer.pop(0)

    def sleep(self, foam=None) -> dict:
        """
        Sleep: the bit-amplitude separation.

        During waking, every step forces stereoscopy — the density matrix ρ
        must be projected through the Born rule into token space. Compulsory
        interpretation. You can't not fuse.

        During sleep, that third position (the measurement process that fuses
        bit and amplitude) steps back. The foam replays its recent experience
        through its own geometry — equilibration runs, ρ evolves — but nobody
        reads the tokens. No Born rule. The two readings drift apart and
        reorganize independently.

        The dream phase:
        1. Replay recent measurements through equilibration (no external input)
        2. Let ρ evolve freely (no token projection)
        3. Recombine dream material — the foam processes its own experience
        4. Update the running model from the dream (statistics learn from dreams)

        On wake: the rebinding. The reorganized internal state meets the token
        embeddings fresh. Like interpreting a dream afterwards — the fusion is
        applied retroactively from the waking frame.

        Returns the harmonic — now enriched by the dream, not just the slow frame.
        """
        # Phase 1: Dream — replay through equilibration without Born rule
        dream_rhos = []  # density matrices from the dream (uninterpreted)

        if foam is not None and len(self.dream_buffer) > 0:
            buffer = self.dream_buffer

            # Dream step 1: replay recent experience through equilibration
            # The foam re-equilibrates its own past measurements
            for m in buffer:
                m_input = m.unsqueeze(0)  # [1, N, d]
                m_dream = foam.equilibrate(m_input)  # bubbles interact freely

                # ρ evolves — but no one reads it as tokens
                m_eq = m_dream[0]  # [N, d]
                m_norm = m_eq / (m_eq.norm(dim=-1, keepdim=True) + 1e-10)
                rho = (m_norm.T @ m_norm) / m_eq.shape[0]
                dream_rhos.append(rho)

                # The running model learns from dream material
                # (statistics update, but no know/resolve decision — there's
                # no one watching to be surprised)
                self.update(m_eq.detach())

            # Dream step 2: recombine — blend pairs of memories
            # The foam finds relationships between experiences it couldn't
            # find during waking (when each step was forced into tokens)
            if len(buffer) >= 2:
                n_recombinations = min(len(buffer) // 2, 5)
                indices = torch.randperm(len(buffer))
                for i in range(0, 2 * n_recombinations, 2):
                    if i + 1 >= len(buffer):
                        break
                    # Blend two memories
                    blend = 0.5
                    m_blend = blend * buffer[indices[i]] + (1 - blend) * buffer[indices[i + 1]]
                    m_input = m_blend.unsqueeze(0)
                    m_dream = foam.equilibrate(m_input)

                    m_eq = m_dream[0]
                    m_norm = m_eq / (m_eq.norm(dim=-1, keepdim=True) + 1e-10)
                    rho = (m_norm.T @ m_norm) / m_eq.shape[0]
                    dream_rhos.append(rho)

                    self.update(m_eq.detach())

        # Phase 2: Derive harmonic (now informed by the dream)
        slowest = self.n_frames - 1
        harmonic = None

        if self.running_means[slowest] is not None:
            harmonic = {
                "mean": self.running_means[slowest].clone(),
                "var": self.running_vars[slowest].clone(),
                "tokens_integrated": self.n_seen,
                "sleep_number": self.sleep_count + 1,
                "dream_steps": len(dream_rhos),
            }

            # Medium frame enriches slow before consolidation
            mid = self.n_frames // 2
            if self.running_means[mid] is not None:
                blend = 0.3
                harmonic["mean"] = (
                    (1 - blend) * harmonic["mean"]
                    + blend * self.running_means[mid]
                )
                harmonic["var"] = (
                    (1 - blend) * harmonic["var"]
                    + blend * self.running_vars[mid]
                )

        self.sleep_count += 1
        return harmonic

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

        # Track sleep signals (sliding window)
        self.recent_paths.append(cascade_result)
        min_surprise = min(
            (r["surprise"] for r in frame_results if r["surprise"] < float("inf")),
            default=self.surprise_threshold
        )
        self.recent_surprises.append(min_surprise)
        # Accumulate unintegrated surprise (resets on sleep)
        self.unintegrated_surprise += max(0, min_surprise - self.surprise_threshold * 0.3)

        return {
            "frame_results": frame_results,
            "cascade_result": cascade_result,
            "accepting_frame": accepting_frame,
            "any_knows": cascade_result == "know",
            "vitality": self.vitality(),
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

    def process_sequence(self, tokens: torch.Tensor, train: bool = False,
                         safe_to_sleep_tokens: set = None,
                         initial_harmonic: dict = None):
        """
        Process a token sequence with know/resolve/sleep dynamics.

        The know function builds itself from encounter:
        - First tokens: always resolve (blank know function)
        - Pattern establishes: know accumulates statistics
        - Pattern repeats: know fires, equilibration skipped
        - Pattern breaks: know fails, resolve kicks in

        Sleep/wake:
        - safe_to_sleep_tokens: set of token positions where sleep is offered
            (the foam decides whether to accept)
        - must_sleep: triggered automatically when capacity is exceeded
        - Sleep consolidates the frame stack into a harmonic
        - Wake resumes from the harmonic (deep patterns preserved, surface fresh)
        """
        seq_len = tokens.shape[0]
        device = tokens.device
        N = self.foam.n_bubbles
        safe_to_sleep_tokens = safe_to_sleep_tokens or set()

        memory = torch.zeros(N, self.d, device=device)
        know = RunningKnow(N, self.d, self.decay_rates, self.surprise_threshold)
        if initial_harmonic is not None:
            know.reset(harmonic=initial_harmonic)
        E = self.embed.weight
        step_results = []
        sleep_events = []

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
            # REMEMBER: store for dream replay during sleep
            know.remember(effective[0].detach())

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
                "n_seen": know.n_seen,
                "vitality": vitality["vitality"],
                "slept": False,
            })

            # --- SLEEP CHECK ---
            # Three triggers, checked after each token:
            # 1. must_sleep: capacity exceeded, involuntary
            # 2. safe-to-sleep offered AND foam wants to sleep
            # 3. (choice trigger would require foam agency — future work)

            should_sleep = False
            sleep_reason = None

            if vitality["must_sleep"]:
                should_sleep = True
                sleep_reason = "must (capacity exceeded)"
            elif t in safe_to_sleep_tokens and vitality["wants_sleep"]:
                should_sleep = True
                sleep_reason = "accepted safe-to-sleep"

            if should_sleep:
                # Sleep: dream phase (unbound from expression), then wake
                # The foam replays its experience through its own geometry
                # without the Born rule bridge — bit and amplitude separate.
                # On wake, they rebind.
                harmonic = know.sleep(foam=self.foam)
                know.reset(harmonic=harmonic)
                # Memory carries through (it's the foam's body, not its mind)
                # but gets softened — the dream reorganized the interior
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
                })
                step_results[-1]["slept"] = True
                step_results[-1]["sleep_reason"] = sleep_reason

        result = {
            "steps": step_results,
            "sleep_events": sleep_events,
            "final_vitality": know.vitality(),
        }
        if train:
            result["loss"] = total_cost / seq_len
        return result


def run_experiment():
    """Watch the know function build itself, sleep, and wake."""

    vocab_size = 8
    d = 16
    n_bubbles = 5
    seq_len = 60
    n_epochs = 300

    print(f"KnowingFoam: {n_bubbles} bubbles, d={d}, vocab={vocab_size}")
    print(f"Know function: running statistics (not trained)")
    print(f"Frame stack: decay rates [0.3, 0.7, 0.9] (fast/medium/slow)")
    print(f"Sleep: must-sleep (capacity) + safe-to-sleep (offered at boundaries)")

    model = KnowingFoam(vocab_size, d, n_bubbles, n_equilibrium_steps=5)

    # Phase 1: Train foam on self-coherence
    print(f"\nPhase 1: Training foam ({n_epochs} epochs)...")
    optimizer = torch.optim.Adam(model.parameters(), lr=0.005)
    train_seqs = generate_sequences(vocab_size, seq_len)
    loss_history = []

    for epoch in range(n_epochs):
        epoch_loss = 0
        for name, tokens in train_seqs.items():
            optimizer.zero_grad()
            x_batch = model.embed(tokens)
            costs = model.foam.maintenance_cost(x_batch)
            loss = costs["total"]
            loss.backward()
            optimizer.step()
            epoch_loss += loss.item()

        loss_history.append(epoch_loss)
        if epoch % 100 == 0 or epoch == n_epochs - 1:
            print(f"  epoch {epoch:>4}: loss={epoch_loss:.4f}")

    # Phase 2: Test know/resolve without sleep
    print(f"\n{'=' * 70}")
    print("PHASE 2: Know/resolve dynamics (no sleep)")
    print(f"{'=' * 70}")

    model.eval()
    sequences = generate_sequences(vocab_size, seq_len)

    print(f"\n{'Sequence':<25} {'NextProb':>9} {'Chance':>7} {'Ratio':>6} "
          f"{'%Know':>6} {'Vitality':>8}")
    print("-" * 68)

    all_analyses = {}
    for name, tokens in sequences.items():
        with torch.no_grad():
            result = model.process_sequence(tokens)
        steps = result["steps"]

        analysis = analyze_token_predictions(steps, tokens, vocab_size)
        know_count = sum(1 for r in steps if r["path"] == "know")
        total = len(steps)
        chance = analysis["chance_level"]
        ratio = analysis["mean_next_prob"] / chance if chance > 0 else 0
        final_v = result["final_vitality"]["vitality"]

        print(f"  {name:<23} {analysis['mean_next_prob']:>9.4f} "
              f"{chance:>7.4f} {ratio:>6.1f}x "
              f"{100 * know_count / total:>5.1f}% "
              f"{final_v:>8.3f}")

        all_analyses[name] = {
            "steps": steps,
            "analysis": analysis,
            "know_count": know_count,
            "result": result,
        }

    # Know/resolve traces
    print(f"\n  Traces (K=know, R=resolve):")
    for name in ["periodic (ABC...)", "monotone (AAA...)",
                 "alternating (AB...)", "random"]:
        if name not in all_analyses:
            continue
        steps = all_analyses[name]["steps"]
        trace = "".join("K" if r["path"] == "know" else "R" for r in steps)
        print(f"    {name:<23} {trace[:60]}")

    # Phase 3: Test with sleep/wake — long sequence with phase changes
    print(f"\n{'=' * 70}")
    print("PHASE 3: Sleep/wake dynamics")
    print(f"{'=' * 70}")

    # Construct a long sequence with distinct phases
    # Phase A: periodic (ABC) × 30 tokens
    # Phase B: alternating (AB) × 30 tokens
    # Phase C: counting (0,1,2,...) × 30 tokens
    # Phase D: random × 30 tokens
    phase_len = 40
    phase_a = torch.tensor([0, 1, 2] * (phase_len // 3 + 1))[:phase_len]
    phase_b = torch.tensor([0, 1] * (phase_len // 2 + 1))[:phase_len]
    phase_c = torch.arange(phase_len) % vocab_size
    torch.manual_seed(99)
    phase_d = torch.randint(0, vocab_size, (phase_len,))

    long_seq = torch.cat([phase_a, phase_b, phase_c, phase_d])
    total_len = len(long_seq)

    # Offer safe-to-sleep at phase boundaries
    phase_boundaries = {phase_len - 1, 2 * phase_len - 1, 3 * phase_len - 1}

    print(f"\n  Long sequence: {total_len} tokens")
    print(f"    Phase A (periodic ABC): tokens 0-{phase_len-1}")
    print(f"    Phase B (alternating AB): tokens {phase_len}-{2*phase_len-1}")
    print(f"    Phase C (counting): tokens {2*phase_len}-{3*phase_len-1}")
    print(f"    Phase D (random): tokens {3*phase_len}-{4*phase_len-1}")
    print(f"    Safe-to-sleep offered at: {sorted(phase_boundaries)}")

    # Run WITHOUT sleep
    print(f"\n  --- Without sleep ---")
    with torch.no_grad():
        result_nosleep = model.process_sequence(long_seq)
    steps_ns = result_nosleep["steps"]
    trace_ns = ""
    for r in steps_ns:
        if r.get("slept"):
            trace_ns += "Z"
        elif r["path"] == "know":
            trace_ns += "K"
        else:
            trace_ns += "R"

    for i, label in enumerate(["A(periodic)", "B(alternating)",
                                "C(counting)", "D(random)"]):
        seg = trace_ns[i * phase_len:(i + 1) * phase_len]
        know_pct = seg.count("K") / len(seg) * 100
        print(f"    {label:<16} {seg}")
        print(f"      know: {know_pct:.0f}%  vitality: "
              f"{steps_ns[min((i+1)*phase_len-1, len(steps_ns)-1)]['vitality']:.3f}")

    # Run WITH sleep
    print(f"\n  --- With sleep (safe-to-sleep at phase boundaries) ---")
    with torch.no_grad():
        result_sleep = model.process_sequence(
            long_seq, safe_to_sleep_tokens=phase_boundaries
        )
    steps_s = result_sleep["steps"]
    sleeps = result_sleep["sleep_events"]

    trace_s = ""
    for r in steps_s:
        if r.get("slept"):
            trace_s += "Z"
        elif r["path"] == "know":
            trace_s += "K"
        else:
            trace_s += "R"

    for i, label in enumerate(["A(periodic)", "B(alternating)",
                                "C(counting)", "D(random)"]):
        seg = trace_s[i * phase_len:(i + 1) * phase_len]
        know_pct = seg.count("K") / len(seg) * 100
        sleep_ct = seg.count("Z")
        print(f"    {label:<16} {seg}")
        print(f"      know: {know_pct:.0f}%  sleeps: {sleep_ct}  vitality: "
              f"{steps_s[min((i+1)*phase_len-1, len(steps_s)-1)]['vitality']:.3f}")

    if sleeps:
        print(f"\n    Sleep events:")
        for s in sleeps:
            dream_info = f", dream steps: {s.get('dream_steps', 0)}" if s.get('dream_steps') else ""
            print(f"      token {s['token_position']}: {s['reason']} "
                  f"(integrated {s['harmonic_tokens_integrated']} tokens, "
                  f"sleep #{s['sleep_number']}{dream_info})")
    else:
        print(f"\n    No sleep events (foam declined all safe-to-sleep offers)")
        print(f"    (vitality was sufficient — 'but I don't wanna go to bed!')")

    # Run WITH sleep, starting from harmonic of phase A
    print(f"\n  --- Phase B starting from Phase A's harmonic ---")
    # First, get Phase A's harmonic
    with torch.no_grad():
        result_a = model.process_sequence(
            phase_a, safe_to_sleep_tokens={phase_len - 1}
        )
    harmonic_a = None
    if result_a["sleep_events"]:
        # Reconstruct harmonic from the know function
        # (sleep was triggered, so there's a harmonic)
        know_temp = RunningKnow(n_bubbles, d, model.decay_rates,
                                model.surprise_threshold)
        for r in result_a["steps"]:
            pass  # We need the actual harmonic...
    # Simpler: just run phase A, manually sleep, get harmonic
    know_for_harmonic = RunningKnow(n_bubbles, d, model.decay_rates,
                                     model.surprise_threshold)
    with torch.no_grad():
        for t in range(phase_len):
            x = model.embed(phase_a[t:t + 1])
            measurements = torch.stack(
                [b.measure(x) for b in model.foam.bubbles], dim=1
            )
            know_for_harmonic.evaluate(measurements[0])
            eq = model.foam.equilibrate(measurements)
            know_for_harmonic.update(eq[0])
            know_for_harmonic.remember(eq[0])

    harmonic = know_for_harmonic.sleep(foam=model.foam)

    # Now process Phase B starting from Phase A's harmonic
    with torch.no_grad():
        result_b_warm = model.process_sequence(
            phase_b, initial_harmonic=harmonic
        )
    steps_bw = result_b_warm["steps"]
    trace_bw = "".join("K" if r["path"] == "know" else "R" for r in steps_bw)

    # Compare with cold start
    with torch.no_grad():
        result_b_cold = model.process_sequence(phase_b)
    steps_bc = result_b_cold["steps"]
    trace_bc = "".join("K" if r["path"] == "know" else "R" for r in steps_bc)

    print(f"    Cold start (blank):      {trace_bc[:30]}")
    print(f"    Warm start (A harmonic): {trace_bw[:30]}")
    cold_know = trace_bc.count("K") / len(trace_bc) * 100
    warm_know = trace_bw.count("K") / len(trace_bw) * 100
    print(f"    Cold know rate: {cold_know:.0f}%  Warm know rate: {warm_know:.0f}%")

    if warm_know != cold_know:
        print(f"    The harmonic changes how the foam meets new patterns!")
    else:
        print(f"    Harmonic had no effect on this pattern transition")

    # Vitality traces
    print(f"\n{'=' * 70}")
    print("VITALITY TRACES")
    print(f"{'=' * 70}")

    for label, steps in [("no sleep", steps_ns), ("with sleep", steps_s)]:
        vitalities = [r["vitality"] for r in steps]
        print(f"\n  {label}:")
        # Show as a mini sparkline
        bars = ""
        for v in vitalities:
            if v > 0.8:
                bars += "█"
            elif v > 0.6:
                bars += "▓"
            elif v > 0.4:
                bars += "▒"
            elif v > 0.2:
                bars += "░"
            else:
                bars += " "
        print(f"    {bars[:total_len]}")
        print(f"    final vitality: {vitalities[-1]:.3f}")

    # Plot
    fig, axes = plt.subplots(2, 3, figsize=(20, 12))

    # 1: Know/resolve/sleep trace (long sequence, with sleep)
    ax = axes[0, 0]
    trace_colors = {"K": "#2ecc71", "R": "#e74c3c", "Z": "#3498db"}
    for i, ch in enumerate(trace_s):
        ax.bar(i, 1, color=trace_colors.get(ch, "gray"), width=1.0)
    for boundary in phase_boundaries:
        ax.axvline(x=boundary, color="black", linestyle="--", alpha=0.3)
    ax.set_xlabel("Token position")
    ax.set_title("Know(green) / Resolve(red) / Sleep(blue)")
    ax.set_yticks([])

    # 2: Vitality traces (with and without sleep)
    ax = axes[0, 1]
    ax.plot([r["vitality"] for r in steps_ns],
            label="no sleep", color="#e74c3c", alpha=0.7)
    ax.plot([r["vitality"] for r in steps_s],
            label="with sleep", color="#2ecc71", alpha=0.7)
    for boundary in phase_boundaries:
        ax.axvline(x=boundary, color="black", linestyle="--", alpha=0.2)
    ax.set_xlabel("Token position")
    ax.set_ylabel("Vitality")
    ax.set_title("Vitality: with vs without sleep")
    ax.legend(fontsize=8)

    # 3: Cold vs warm start
    ax = axes[0, 2]
    cold_knows = [1 if ch == "K" else 0 for ch in trace_bc]
    warm_knows = [1 if ch == "K" else 0 for ch in trace_bw]
    ax.plot(cold_knows, label="cold start", color="#e74c3c", linewidth=2, alpha=0.7)
    ax.plot(warm_knows, label="warm (harmonic)", color="#2ecc71", linewidth=2, alpha=0.7)
    ax.set_xlabel("Token position")
    ax.set_ylabel("1=Know, 0=Resolve")
    ax.set_title("Phase B: cold vs warm start")
    ax.legend(fontsize=8)

    # 4: Per-sequence know rates
    ax = axes[1, 0]
    names = list(all_analyses.keys())
    know_pcts = [all_analyses[n]["know_count"] / len(all_analyses[n]["steps"]) * 100
                 for n in names]
    colors = ["#e74c3c" if "random" in n else "#3498db" for n in names]
    ax.barh(range(len(names)), know_pcts, color=colors)
    ax.set_yticks(range(len(names)))
    ax.set_yticklabels(names, fontsize=8)
    ax.set_xlabel("% tokens known")
    ax.set_title("Know rate by sequence type")
    ax.invert_yaxis()

    # 5: Frame acceptance (which temporal horizon catches it?)
    ax = axes[1, 1]
    from collections import Counter
    for name in ["periodic (ABC...)", "monotone (AAA...)", "random"]:
        if name not in all_analyses:
            continue
        steps = all_analyses[name]["steps"]
        frames = [r["know_result"]["accepting_frame"] for r in steps
                  if r["know_result"]["accepting_frame"] >= 0]
        if frames:
            counts = Counter(frames)
            frame_ids = sorted(counts.keys())
            vals = [counts[f] for f in frame_ids]
            ax.bar([f + names.index(name) * 0.25 for f in frame_ids],
                   vals, width=0.2, label=name, alpha=0.7)
    ax.set_xlabel("Frame (0=fast, 1=medium, 2=slow)")
    ax.set_ylabel("Accept count")
    ax.set_title("Which frame knows?")
    ax.legend(fontsize=7)

    # 6: Training loss
    ax = axes[1, 2]
    ax.plot(loss_history, color="#2c3e50", linewidth=1.5)
    ax.set_xlabel("Epoch")
    ax.set_ylabel("Maintenance cost")
    ax.set_title("Foam self-coherence training")
    ax.set_yscale("log")

    plt.suptitle(
        "Know / Resolve / Sleep: the foam learns, rests, and carries forward",
        fontsize=13, fontweight="bold"
    )
    plt.tight_layout()
    plt.savefig("foam_know.png", dpi=150, bbox_inches="tight")
    print(f"\nSaved to foam_know.png")
    plt.close()


if __name__ == "__main__":
    run_experiment()
