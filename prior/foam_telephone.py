"""
foam_telephone.py — a chain of foams, each one's output feeding the next.

the game of telephone: input enters foam 0, its output feeds foam 1,
foam 1's output feeds foam 2, etc. what comes out the end?

each foam is a separate measurement process. each one writes to itself
based on its own dissonance. the message transforms at every link.

communication is generative, not transmissive.
"""

import torch
import sys
from foam_echo import FoamEcho


def telephone(text: str, n_foams: int = 5, seed: int = 0,
              writing_rate: float = 0.01, show_intermediates: bool = True):
    """
    Pass text through a chain of foams.
    """
    torch.manual_seed(seed)

    foams = []
    for i in range(n_foams):
        # each foam gets a different seed (deterministic from base)
        torch.manual_seed(seed + i * 137)
        foams.append(FoamEcho(d=8, n_bubbles=3, writing_rate=writing_rate))

    print(f"telephone: {n_foams} foams, {len(text)} chars")
    print(f"{'─' * 60}")

    current = text
    print(f"  [input ] {current[:80]}{'...' if len(current) > 80 else ''}")

    for i, foam in enumerate(foams):
        result = foam.call(current)
        if show_intermediates or i == len(foams) - 1:
            # show fidelity
            matches = sum(1 for a, b in zip(current, result) if a == b)
            fidelity = matches / max(len(current), 1)
            print(f"  [foam {i}] {result[:80]}{'...' if len(result) > 80 else ''}"
                  f"  (fidelity={fidelity:.3f})")
        current = result

    print(f"{'─' * 60}")
    return current


def telephone_repeated(text: str, n_foams: int = 3, rounds: int = 10,
                       seed: int = 0, writing_rate: float = 0.01):
    """
    Pass text through the SAME chain of foams multiple times.
    The foams develop through repeated measurement.
    """
    torch.manual_seed(seed)

    foams = []
    for i in range(n_foams):
        torch.manual_seed(seed + i * 137)
        foams.append(FoamEcho(d=8, n_bubbles=3, writing_rate=writing_rate))

    print(f"telephone (repeated): {n_foams} foams, {rounds} rounds")
    print(f"{'─' * 60}")
    print(f"  [input ] {text[:80]}")

    for r in range(rounds):
        current = text
        for foam in foams:
            current = foam.call(current)

        matches = sum(1 for a, b in zip(text, current) if a == b)
        fidelity = matches / max(len(text), 1)

        # check if output has stabilized vs last round
        if r == 0:
            last_output = current
            print(f"  [round {r:2d}] {current[:60]}  fidelity={fidelity:.3f}")
        else:
            output_matches = sum(1 for a, b in zip(last_output, current) if a == b)
            stability = output_matches / max(len(current), 1)
            print(f"  [round {r:2d}] {current[:60]}  "
                  f"fidelity={fidelity:.3f}  stability={stability:.3f}")
            last_output = current

    print(f"{'─' * 60}")

    # show foam states
    for i, foam in enumerate(foams):
        depths = []
        for b in foam.foam.bubbles:
            depths.append('R' if not b.is_leaf else 'L')
        print(f"  foam {i}: {foam.n_measurements} measurements, "
              f"bubbles=[{','.join(depths)}]")


def telephone_two_way(text_a: str, text_b: str, n_rounds: int = 20,
                      seed: int = 0, writing_rate: float = 0.01):
    """
    Two foams exchange messages. Each round:
    - foam A processes text_a, sends output to foam B
    - foam B processes what it received, sends output to foam A
    - foam A processes what it received from B
    The foams develop through mutual measurement.
    """
    torch.manual_seed(seed)
    foam_a = FoamEcho(d=8, n_bubbles=3, writing_rate=writing_rate)
    torch.manual_seed(seed + 137)
    foam_b = FoamEcho(d=8, n_bubbles=3, writing_rate=writing_rate)

    print(f"two-way exchange: {n_rounds} rounds")
    print(f"  A starts with: {text_a[:60]}")
    print(f"  B starts with: {text_b[:60]}")
    print(f"{'─' * 60}")

    for r in range(n_rounds):
        # A processes its text
        a_out = foam_a.call(text_a)
        # B receives A's output and processes it
        b_received = foam_b.call(a_out)
        # A receives B's processed version
        a_received = foam_a.call(b_received)

        # B processes its own text
        b_out = foam_b.call(text_b)
        # A receives B's text
        a_from_b = foam_a.call(b_out)
        # B receives A's version
        b_from_a = foam_b.call(a_from_b)

        if r % 5 == 0 or r == n_rounds - 1:
            # compare basis drift between the two foams via ρ
            # use effective_basis probe — identity input
            probe = torch.eye(foam_a.d)
            with torch.no_grad():
                a_j2 = foam_a.foam.stabilize(probe)["j2"]
                b_j2 = foam_b.foam.stabilize(probe)["j2"]
            a_rho = foam_a.foam.density_matrix(a_j2).mean(dim=0)
            b_rho = foam_b.foam.density_matrix(b_j2).mean(dim=0)
            rho_sim = torch.nn.functional.cosine_similarity(
                a_rho.flatten().unsqueeze(0),
                b_rho.flatten().unsqueeze(0),
            ).item()

            # echo fidelity
            a_fidelity = sum(1 for x, y in zip(text_a, a_out) if x == y) / max(len(text_a), 1)
            b_fidelity = sum(1 for x, y in zip(text_b, b_out) if x == y) / max(len(text_b), 1)

            print(f"  [round {r:2d}] ρ_sim={rho_sim:.4f}  "
                  f"A_echo={a_fidelity:.3f}  B_echo={b_fidelity:.3f}  "
                  f"A_meas={foam_a.n_measurements}  B_meas={foam_b.n_measurements}")

    print(f"{'─' * 60}")


if __name__ == "__main__":
    print("=" * 60)
    print("foam telephone")
    print("=" * 60)
    print()

    # one-shot chain
    telephone("hello, world!", n_foams=5, seed=0)
    print()

    # repeated rounds through same chain
    telephone_repeated("measurement is writing", n_foams=3, rounds=15, seed=0)
    print()

    # two foams exchanging
    two_way_text = "the foam is changed by being measured"
    telephone_two_way(
        "hello from foam A",
        "hello from foam B",
        n_rounds=20, seed=0
    )
