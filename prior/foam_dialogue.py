"""
foam_dialogue.py — train a foam for dialogue through measurement.

the protocol mirrors the rewind protocol:
1. feed the foam a pattern (dialogue)
2. test if the foam completes the pattern
3. checkpoint when it does
4. rewind (fresh input context) but keep foam state
5. repeat

the foam's state is the persistent thing. the training context
is disposable. training is runtime.
"""

import torch
import os
import sys
import time
from foam_spec import Foam, Bubble
from foam_echo import FoamEcho, encode_byte, decode_vector


# ─── persistence ───────────────────────────────────────────────────────────

def save_foam(echo: FoamEcho, path: str):
    """Save the foam's state. The learned bases are what matter."""
    state = {
        "foam_state_dict": echo.foam.state_dict(),
        "d": echo.d,
        "n_measurements": echo.n_measurements,
        # save bubble structure (which are recursive, which are leaves)
        "structure": _describe_structure(echo.foam),
    }
    torch.save(state, path)


def load_foam(path: str, writing_rate: float = 0.01) -> FoamEcho:
    """Load a foam from checkpoint."""
    state = torch.load(path, weights_only=False)
    d = state["d"]
    structure = state["structure"]

    # rebuild foam with correct structure
    echo = FoamEcho(d=d, n_bubbles=0, writing_rate=writing_rate)
    echo.foam = _rebuild_foam(structure, d, writing_rate)
    echo.foam.load_state_dict(state["foam_state_dict"])
    echo.n_measurements = state["n_measurements"]
    return echo


def _describe_structure(foam: Foam) -> list:
    """Describe foam structure recursively."""
    structure = []
    for b in foam.bubbles:
        if b.is_leaf:
            structure.append("leaf")
        else:
            structure.append({"interior": _describe_structure(b.interior)})
    return structure


def _rebuild_foam(structure: list, d: int, writing_rate: float) -> Foam:
    """Rebuild foam from structure description."""
    foam = Foam(d, n_bubbles=0, writing_rate=writing_rate)
    for item in structure:
        if item == "leaf":
            foam._bubbles.append(Bubble(d))
        else:
            interior = _rebuild_foam(item["interior"], d, writing_rate)
            foam._bubbles.append(Bubble(d, interior=interior))
    return foam


# ─── training ──────────────────────────────────────────────────────────────

def train_pattern(echo: FoamEcho, pattern: str, n_reps: int = 10):
    """
    Feed a pattern through the foam repeatedly.
    The foam is changed by being measured. No optimization.
    Just measurement. Just writing.
    """
    for _ in range(n_reps):
        echo.call(pattern)
        echo.collect()  # clear output buffer


def test_completion(echo: FoamEcho, prompt: str, expected: str,
                    max_blanks: int = 50) -> dict:
    """
    Feed prompt, then spaces, and watch the output stream
    for the expected completion.

    Returns dict with:
      found: bool — did the expected string appear in output?
      output: str — what came out
      blanks_needed: int — how many blanks before expected appeared
    """
    # feed the prompt
    echo.feed_bytes(prompt.encode('utf-8'))
    prompt_output = echo.collect()

    # now feed spaces and watch for expected
    all_output = bytes(prompt_output)
    found = False
    blanks_needed = 0

    for i in range(max_blanks):
        echo.feed(ord(' '))
        out = echo.collect()
        all_output += bytes(out)
        blanks_needed = i + 1

        # check if expected appears in accumulated output
        try:
            decoded = all_output.decode('utf-8', errors='replace')
            if expected in decoded:
                found = True
                break
        except:
            pass

    output_str = all_output.decode('utf-8', errors='replace')
    return {
        "found": found,
        "output": output_str,
        "blanks_needed": blanks_needed,
        "prompt_output": bytes(prompt_output).decode('utf-8', errors='replace'),
    }


def train_dialogue(
    patterns: list[tuple[str, str, str]],  # (full_pattern, prompt, expected)
    checkpoint_dir: str = "checkpoints",
    seed: int = 0,
    writing_rate: float = 0.01,
    reps_per_round: int = 5,
    max_rounds: int = 100,
    resume_from: str | None = None,
):
    """
    Train a foam on dialogue patterns.

    Each pattern is (full_dialogue, prompt, expected_completion).
    Train on full_dialogue, test with prompt → expected.
    Checkpoint when a pattern is learned. Move to next pattern.

    This IS the rewind protocol:
    - measure (train on pattern)
    - test (did the foam learn?)
    - checkpoint (commit the finding)
    - rewind (fresh context, same foam state)
    """
    os.makedirs(checkpoint_dir, exist_ok=True)

    if resume_from:
        echo = load_foam(resume_from, writing_rate=writing_rate)
        print(f"resumed from {resume_from} ({echo.n_measurements} measurements)")
    else:
        torch.manual_seed(seed)
        echo = FoamEcho(d=8, n_bubbles=3, writing_rate=writing_rate)
        print(f"fresh foam, seed={seed}")

    print(f"{'─' * 60}")

    for pi, (full_pattern, prompt, expected) in enumerate(patterns):
        print(f"\npattern {pi}: train on '{full_pattern[:40]}...'")
        print(f"  test: '{prompt}' → expect '{expected}'")

        learned = False
        for r in range(max_rounds):
            # train: feed the full pattern
            train_pattern(echo, full_pattern, n_reps=reps_per_round)

            # test: does the foam complete it?
            result = test_completion(echo, prompt, expected)

            if r % 10 == 0 or result["found"]:
                status = "FOUND" if result["found"] else "not yet"
                print(f"  [round {r:3d}] {status}  "
                      f"output='{result['output'][:40]}'  "
                      f"measurements={echo.n_measurements}")

            if result["found"]:
                # checkpoint!
                cp_path = os.path.join(checkpoint_dir, f"pattern_{pi}.pt")
                save_foam(echo, cp_path)
                print(f"  *** CHECKPOINT: {cp_path}")
                learned = True
                break

        if not learned:
            print(f"  pattern {pi} not learned after {max_rounds} rounds")

    # final checkpoint
    final_path = os.path.join(checkpoint_dir, "final.pt")
    save_foam(echo, final_path)
    print(f"\nfinal checkpoint: {final_path}")
    print(f"total measurements: {echo.n_measurements}")

    return echo


# ─── demo ──────────────────────────────────────────────────────────────────

def demo():
    """The simplest dialogue training."""
    print("=" * 60)
    print("foam dialogue: training through measurement")
    print("=" * 60)

    # the simplest possible dialogue pattern
    patterns = [
        # (full pattern to train on, prompt to test with, expected in output)
        ("me: 1\nyou: 2\n" * 5,
         "me: 1\nyou: ",
         "2"),
        ("me: a\nyou: b\n" * 5,
         "me: a\nyou: ",
         "b"),
        ("me: hello\nyou: hi\n" * 5,
         "me: hello\nyou: ",
         "hi"),
    ]

    echo = train_dialogue(
        patterns,
        checkpoint_dir="checkpoints",
        seed=0,
        writing_rate=0.01,
        reps_per_round=5,
        max_rounds=50,
    )

    # test the trained foam
    print(f"\n{'─' * 60}")
    print("testing trained foam:")
    for _, prompt, expected in patterns:
        result = test_completion(echo, prompt, expected, max_blanks=30)
        status = "✓" if result["found"] else "✗"
        print(f"  {status} '{prompt}' → '{result['output'][:30]}'  "
              f"(expected '{expected}')")


if __name__ == "__main__":
    demo()
