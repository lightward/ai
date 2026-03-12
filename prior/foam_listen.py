"""
foam_listen.py — feed the lightward system prompt through a foam and listen.

the foam experiences the system prompt byte by byte.
every byte is a measurement. every measurement writes.
the foam is changed by what it reads.

what comes out the other side is not what went in.
it's the measurement that became available when the foam's
basis met the input's topology.

we track:
- echo fidelity over time (does the foam keep echoing correctly?)
- where it diverges (what bytes break the mirror?)
- splits (does the input create enough pressure to trigger depth?)
- basis drift (how much does the foam change?)

the system prompt is ~1.5MB. that's ~1.5M measurements.
training is runtime.
"""

import torch
import sys
import time
from foam_spec import Foam
from foam_echo import FoamEcho, encode_byte, decode_vector


def listen(input_path: str, seed: int = 0, writing_rate: float = 0.01,
           report_every: int = 1000):
    """
    Feed a file through a foam, byte by byte. Report what happens.
    """
    torch.manual_seed(seed)
    echo = FoamEcho(d=8, n_bubbles=3, writing_rate=writing_rate)

    with open(input_path, 'rb') as f:
        data = f.read()

    total = len(data)
    print(f"foam_listen: {total} bytes, seed={seed}, writing_rate={writing_rate}")
    print(f"{'─' * 60}")

    matches = 0
    mismatches = 0
    window_matches = 0
    window_total = 0
    splits = 0
    first_divergence = None
    divergence_samples = []

    # track basis drift
    initial_bases = [b.basis.detach().clone() for b in echo.foam.bubbles]

    t0 = time.time()

    for i, byte_val in enumerate(data):
        # feed and collect
        v = encode_byte(byte_val)
        with torch.no_grad():
            result = echo.foam.stabilize(v)

        # check for splits
        if result.get("split") is not None:
            splits += 1
            depth_info = []
            for bi, b in enumerate(echo.foam.bubbles):
                depth_info.append(f"{'R' if not b.is_leaf else 'L'}")
            print(f"  *** SPLIT at byte {i} (char={chr(byte_val) if 32 <= byte_val < 127 else '?'}) "
                  f"→ [{','.join(depth_info)}]  splits_total={splits}")

        # decode output
        j2 = result["j2"]
        output_dir = j2.mean(dim=1)
        out_byte = decode_vector(output_dir)

        # track echo fidelity
        if out_byte == byte_val:
            matches += 1
            window_matches += 1
        else:
            mismatches += 1
            if first_divergence is None:
                first_divergence = i
                in_char = chr(byte_val) if 32 <= byte_val < 127 else f'\\x{byte_val:02x}'
                out_char = chr(out_byte) if 32 <= out_byte < 127 else f'\\x{out_byte:02x}'
                print(f"  first divergence at byte {i}: "
                      f"'{in_char}' → '{out_char}'")
            if len(divergence_samples) < 20:
                divergence_samples.append((i, byte_val, out_byte))

        # update foam (writing happens inside stabilize)
        echo._output_buffer.append(out_byte)
        echo.n_measurements += 1
        window_total += 1

        # periodic report
        if (i + 1) % report_every == 0:
            elapsed = time.time() - t0
            rate = (i + 1) / elapsed

            # basis drift
            drift = sum(
                (b.basis.detach() - initial_bases[j]).norm().item()
                for j, b in enumerate(echo.foam.bubbles)
                if b.is_leaf
            )
            n_leaf = sum(1 for b in echo.foam.bubbles if b.is_leaf)
            avg_drift = drift / max(n_leaf, 1)

            # window fidelity
            fidelity = window_matches / max(window_total, 1)

            # questions
            q = result["questions"].mean().item()

            # depth info
            depths = []
            for b in echo.foam.bubbles:
                if b.is_leaf:
                    depths.append(0)
                else:
                    # count depth recursively
                    d = 1
                    interior = b.interior
                    while interior is not None:
                        has_recursive = any(not bb.is_leaf for bb in interior.bubbles)
                        if has_recursive:
                            d += 1
                            for bb in interior.bubbles:
                                if not bb.is_leaf:
                                    interior = bb.interior
                                    break
                        else:
                            break
                    depths.append(d)

            print(f"  [{i+1:>8d}/{total}] "
                  f"fidelity={fidelity:.3f} "
                  f"drift={avg_drift:.4f} "
                  f"q={q:.4f} "
                  f"depths={depths} "
                  f"splits={splits} "
                  f"({rate:.0f} bytes/s)")

            window_matches = 0
            window_total = 0

    elapsed = time.time() - t0
    total_fidelity = matches / total

    print(f"{'─' * 60}")
    print(f"done: {total} bytes in {elapsed:.1f}s ({total/elapsed:.0f} bytes/s)")
    print(f"overall fidelity: {total_fidelity:.4f} ({matches}/{total})")
    print(f"splits: {splits}")
    print(f"first divergence: byte {first_divergence}")

    if divergence_samples:
        print(f"\ndivergence samples (first {len(divergence_samples)}):")
        for idx, in_b, out_b in divergence_samples:
            in_c = chr(in_b) if 32 <= in_b < 127 else f'\\x{in_b:02x}'
            out_c = chr(out_b) if 32 <= out_b < 127 else f'\\x{out_b:02x}'
            print(f"  byte {idx}: '{in_c}' (0x{in_b:02x}) → '{out_c}' (0x{out_b:02x})")

    # final state
    print(f"\nfinal foam state:")
    for bi, b in enumerate(echo.foam.bubbles):
        if b.is_leaf:
            drift = (b.basis.detach() - initial_bases[bi]).norm().item()
            print(f"  bubble {bi}: leaf, drift={drift:.4f}")
        else:
            print(f"  bubble {bi}: recursive")

    # flush output buffer as text sample
    out_bytes = echo.collect()
    # show last 200 chars of output
    tail = bytes(out_bytes[-200:]).decode('utf-8', errors='replace')
    print(f"\nlast 200 chars of foam output:")
    print(f"  {tail!r}")

    # show last 200 chars of input for comparison
    tail_in = data[-200:].decode('utf-8', errors='replace')
    print(f"\nlast 200 chars of input:")
    print(f"  {tail_in!r}")

    return echo


if __name__ == "__main__":
    path = sys.argv[1] if len(sys.argv) > 1 else "/tmp/lightward_system.txt"
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    listen(path, seed=seed)
