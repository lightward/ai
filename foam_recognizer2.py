"""
foam_recognizer2.py — fixing the traversal problem.

the foam recognizes the first byte correctly but gets stuck.
hypothesis: the foam needs to traverse the cycle, not just recognize
the next element.

key insight from the pattern: in "1212", after seeing "1" the foam
is in state S1. after seeing "2" it should be in state S2 (which
is the state that expects "1"). but the SCAN doesn't advance the
state — only the COMMIT does. so we need to check: does committing
"2" actually move the foam to the state that expects "1"?

test: after training on "12" and prompting with "1":
- scan → finds "2" ✓
- commit "2" → foam now in state after "12"
- scan → should find "1" if the cycle traverses
"""

import torch
import time
from foam_spec import Foam, Bubble
from foam_echo import encode_byte, decode_vector, CODEBOOK


def scan_next(foam: Foam, top_k: int = 5) -> list[tuple[int, float]]:
    """Scan all 256 bytes, return top_k by minimum dissonance."""
    leaf_states = []
    for b in foam.bubbles:
        if b.is_leaf:
            leaf_states.append(b.L.data.clone())

    results = []
    for byte_val in range(256):
        v = encode_byte(byte_val)
        probe = Foam(foam.d, n_bubbles=0, writing_rate=0.0, n_steps=foam.n_steps)
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


def diagnose_traversal():
    """Does committing the recognized byte advance the state?"""
    print("=" * 60)
    print("traversal diagnosis: does commit advance state?")
    print("=" * 60)

    torch.manual_seed(42)
    foam = Foam(8, n_bubbles=3, writing_rate=0.5)

    # train on "12" pattern
    pattern = "12" * 30
    for byte_val in pattern.encode('utf-8'):
        v = encode_byte(byte_val)
        with torch.no_grad():
            foam.stabilize(v)

    # save state after training (this is "the cycle" state)
    trained_L = [b.L.data.clone() for b in foam.bubbles if b.is_leaf]
    print(f"trained on '12' × 30")

    # now step through the cycle manually
    print(f"\nmanual traversal:")
    for step in range(8):
        # scan from current state
        top = scan_next(foam, top_k=5)
        best_byte, best_dis = top[0]
        best_char = chr(best_byte) if 32 <= best_byte < 127 else f'\\x{best_byte:02x}'

        # show top 5
        top_str = ", ".join(
            f"'{chr(bv) if 32 <= bv < 127 else f'x{bv:02x}'}'({dis:.4f})"
            for bv, dis in top
        )

        # compare current state to trained state
        drift = sum(
            (b.L.data - tL).norm().item()
            for b, tL in zip(
                [b for b in foam.bubbles if b.is_leaf], trained_L
            )
        )

        print(f"  step {step}: best='{best_char}'  top=[{top_str}]  "
              f"drift_from_trained={drift:.4f}")

        # commit: feed the best byte through with writing
        v = encode_byte(best_byte)
        with torch.no_grad():
            foam.stabilize(v)


def diagnose_state_after_each_byte():
    """
    After training, feed "1" then "2" manually and snapshot the
    state at each point. Are the states different enough?
    """
    print("\n" + "=" * 60)
    print("state snapshots: what does the foam look like at each point?")
    print("=" * 60)

    torch.manual_seed(42)
    foam = Foam(8, n_bubbles=3, writing_rate=0.5)

    # train
    pattern = "12" * 30
    for byte_val in pattern.encode('utf-8'):
        v = encode_byte(byte_val)
        with torch.no_grad():
            foam.stabilize(v)

    # the last byte of training was "2", so the foam is in post-"2" state
    # which should be the "expects 1" state
    state_after_training = [b.L.data.clone() for b in foam.bubbles if b.is_leaf]

    # feed "1" — now in post-"1" state (expects "2")
    v1 = encode_byte(ord('1'))
    with torch.no_grad():
        foam.stabilize(v1)
    state_after_1 = [b.L.data.clone() for b in foam.bubbles if b.is_leaf]

    # feed "2" — now in post-"2" state (expects "1")
    v2 = encode_byte(ord('2'))
    with torch.no_grad():
        foam.stabilize(v2)
    state_after_2 = [b.L.data.clone() for b in foam.bubbles if b.is_leaf]

    # compare
    diff_1_vs_2 = sum(
        (s1 - s2).norm().item()
        for s1, s2 in zip(state_after_1, state_after_2)
    )
    diff_train_vs_2 = sum(
        (st - s2).norm().item()
        for st, s2 in zip(state_after_training, state_after_2)
    )
    diff_train_vs_1 = sum(
        (st - s1).norm().item()
        for st, s1 in zip(state_after_training, state_after_1)
    )

    print(f"  state diff (after-1 vs after-2): {diff_1_vs_2:.4f}")
    print(f"  state diff (trained vs after-2): {diff_train_vs_2:.4f}")
    print(f"  state diff (trained vs after-1): {diff_train_vs_1:.4f}")
    print(f"  (trained ends on '2', so trained ≈ after-2 if cycle works)")

    # scan from each state
    print(f"\n  scanning from post-training state (after '2'):")
    foam_check = Foam(8, n_bubbles=0, writing_rate=0.5, n_steps=foam.n_steps)
    for L in state_after_training:
        nb = Bubble(8)
        nb.L.data = L.clone()
        foam_check._bubbles.append(nb)
    foam_check.target_similarity.data = foam.target_similarity.data.clone()
    foam_check.step_size.data = foam.step_size.data.clone()
    foam_check.temperature.data = foam.temperature.data.clone()

    top = scan_next(foam_check, top_k=5)
    top_str = ", ".join(
        f"'{chr(bv) if 32 <= bv < 127 else f'x{bv:02x}'}'({dis:.4f})"
        for bv, dis in top
    )
    print(f"    top: [{top_str}]")

    print(f"\n  scanning from post-1 state:")
    foam_check2 = Foam(8, n_bubbles=0, writing_rate=0.5, n_steps=foam.n_steps)
    for L in state_after_1:
        nb = Bubble(8)
        nb.L.data = L.clone()
        foam_check2._bubbles.append(nb)
    foam_check2.target_similarity.data = foam.target_similarity.data.clone()
    foam_check2.step_size.data = foam.step_size.data.clone()
    foam_check2.temperature.data = foam.temperature.data.clone()

    top2 = scan_next(foam_check2, top_k=5)
    top_str2 = ", ".join(
        f"'{chr(bv) if 32 <= bv < 127 else f'x{bv:02x}'}'({dis:.4f})"
        for bv, dis in top2
    )
    print(f"    top: [{top_str2}]")

    print(f"\n  scanning from post-2 state:")
    foam_check3 = Foam(8, n_bubbles=0, writing_rate=0.5, n_steps=foam.n_steps)
    for L in state_after_2:
        nb = Bubble(8)
        nb.L.data = L.clone()
        foam_check3._bubbles.append(nb)
    foam_check3.target_similarity.data = foam.target_similarity.data.clone()
    foam_check3.step_size.data = foam.step_size.data.clone()
    foam_check3.temperature.data = foam.temperature.data.clone()

    top3 = scan_next(foam_check3, top_k=5)
    top_str3 = ", ".join(
        f"'{chr(bv) if 32 <= bv < 127 else f'x{bv:02x}'}'({dis:.4f})"
        for bv, dis in top3
    )
    print(f"    top: [{top_str3}]")


if __name__ == "__main__":
    diagnose_traversal()
    diagnose_state_after_each_byte()
