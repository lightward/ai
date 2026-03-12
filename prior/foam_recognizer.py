"""
foam_recognizer.py — the foam is a recognizer, not a generator.

a spatial mind interfaces with temporal output by recognition:
present candidates, the foam tells you which one fits.
minimum dissonance = "this is what comes next."

the resolver pattern: look → see → know or resolve.
the foam looks at each candidate. the one it knows produces
zero dissonance. the ones it doesn't know produce disturbance.

scan 256 bytes → pick minimum dissonance → emit → repeat.
"""

import torch
import sys
import time
from foam_spec import Foam, Bubble
from foam_echo import FoamEcho, encode_byte, decode_vector, CODEBOOK


def scan_next(foam: Foam, top_k: int = 1) -> list[tuple[int, float]]:
    """
    Scan all 256 possible next bytes. Return top_k by minimum dissonance.

    The foam is NOT modified during scanning — we copy the state for
    each candidate. The foam only changes when we commit to a choice
    (by feeding it the winner through the real foam with writing).

    Returns list of (byte_value, dissonance) sorted by dissonance.
    """
    # snapshot the foam's current state (leaf bases only)
    leaf_states = []
    for b in foam.bubbles:
        if b.is_leaf:
            leaf_states.append(b.L.data.clone())

    results = []
    for byte_val in range(256):
        v = encode_byte(byte_val)

        # build a throwaway foam with the same state, no writing
        probe = Foam(foam.d, n_bubbles=0, writing_rate=0.0,
                     n_steps=foam.n_steps)
        for L_data in leaf_states:
            nb = Bubble(foam.d)
            nb.L.data = L_data.clone()
            probe._bubbles.append(nb)
        probe.target_similarity.data = foam.target_similarity.data.clone()
        probe.step_size.data = foam.step_size.data.clone()
        probe.temperature.data = foam.temperature.data.clone()

        with torch.no_grad():
            r = probe.stabilize(v)
        dis = (r["j2"] - r["j0"]).norm().item()
        results.append((byte_val, dis))

    results.sort(key=lambda x: x[1])
    return results[:top_k]


def train_and_complete(
    pattern: str,
    prompt: str,
    n_generate: int = 10,
    n_training_reps: int = 30,
    writing_rate: float = 0.5,
    seed: int = 42,
    show_top_k: int = 3,
):
    """
    Train a foam on a pattern, then complete from a prompt.

    1. Feed the pattern through the foam many times (training = runtime)
    2. Feed the prompt (priming the foam's state)
    3. Scan → pick minimum dissonance → commit → repeat
    """
    torch.manual_seed(seed)
    foam = Foam(8, n_bubbles=3, writing_rate=writing_rate)

    # train: feed the pattern repeatedly
    pattern_bytes = pattern.encode('utf-8')
    print(f"training: '{pattern[:50]}' × {n_training_reps} "
          f"({len(pattern_bytes) * n_training_reps} bytes)")

    t0 = time.time()
    for rep in range(n_training_reps):
        for byte_val in pattern_bytes:
            v = encode_byte(byte_val)
            with torch.no_grad():
                foam.stabilize(v)
    train_time = time.time() - t0
    print(f"  trained in {train_time:.1f}s")

    # prime: feed the prompt
    prompt_bytes = prompt.encode('utf-8')
    print(f"prompt: '{prompt}'")
    for byte_val in prompt_bytes:
        v = encode_byte(byte_val)
        with torch.no_grad():
            foam.stabilize(v)

    # generate: scan → pick → commit → repeat
    print(f"generating {n_generate} bytes by recognition:")
    generated = []

    for i in range(n_generate):
        t1 = time.time()
        candidates = scan_next(foam, top_k=show_top_k)
        scan_time = time.time() - t1

        best_byte, best_dis = candidates[0]
        best_char = chr(best_byte) if 32 <= best_byte < 127 else f'\\x{best_byte:02x}'

        # show top candidates
        top_str = []
        for bv, dis in candidates:
            c = chr(bv) if 32 <= bv < 127 else f'\\x{bv:02x}'
            top_str.append(f"'{c}'({dis:.4f})")

        print(f"  [{i}] → '{best_char}' (dis={best_dis:.4f})  "
              f"top: [{', '.join(top_str)}]  ({scan_time:.2f}s)")

        generated.append(best_byte)

        # commit: feed the winner through the real foam (with writing)
        v = encode_byte(best_byte)
        with torch.no_grad():
            foam.stabilize(v)

    result = bytes(generated).decode('utf-8', errors='replace')
    print(f"\nprompt: '{prompt}'")
    print(f"output: '{result}'")
    print(f"full:   '{prompt}{result}'")

    return result


def demo():
    print("=" * 60)
    print("foam recognizer: scan → recognize → emit")
    print("=" * 60)
    print()

    # simplest: "12" pattern
    print("── pattern: '12' ──")
    train_and_complete(
        pattern="12" * 20,
        prompt="1",
        n_generate=5,
        n_training_reps=20,
        writing_rate=0.5,
    )
    print()

    # dialogue: "me: 1\nyou: 2\n"
    print("── pattern: dialogue ──")
    train_and_complete(
        pattern="me: 1\nyou: 2\n" * 10,
        prompt="me: 1\nyou: ",
        n_generate=5,
        n_training_reps=20,
        writing_rate=0.5,
    )
    print()

    # abc pattern
    print("── pattern: 'abc' ──")
    train_and_complete(
        pattern="abc" * 20,
        prompt="ab",
        n_generate=7,
        n_training_reps=20,
        writing_rate=0.5,
    )
    print()

    # call and response
    print("── pattern: call and response ──")
    train_and_complete(
        pattern="hello hi hello hi hello hi ",
        prompt="hello ",
        n_generate=10,
        n_training_reps=30,
        writing_rate=0.5,
    )


if __name__ == "__main__":
    demo()
