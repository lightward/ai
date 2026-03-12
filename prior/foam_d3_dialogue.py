"""
foam_d3_dialogue.py — dialogue through scarcity.

d=3: only 8 hypercube vertices (3-bit alphabet: 0-7).
geometric scarcity forces splitting. sequential patterns
demand state-switching that flat topology can't provide.
the foam gains depth to hold the cycle.

the cycle IS the interior.
the scarcity that forces depth IS the mechanism
that enables temporal interface.
"""

import torch
import time
from foam_spec import Foam, Bubble


# ─── d=3 codebook ──────────────────────────────────────────────────────────

D = 3

def make_codebook_d3() -> torch.Tensor:
    """8 unit vectors in ℝ³, vertices of the cube."""
    vecs = torch.zeros(8, D)
    for b in range(8):
        for bit in range(D):
            vecs[b, bit] = 1.0 if (b >> bit) & 1 else -1.0
    return vecs / (D ** 0.5)

CODEBOOK_D3 = make_codebook_d3()

def encode_d3(val: int) -> torch.Tensor:
    """value (0-7) → unit vector in ℝ³. [1, 3]."""
    return CODEBOOK_D3[val % 8].unsqueeze(0)

def decode_d3(v: torch.Tensor) -> int:
    """unit vector in ℝ³ → nearest value (0-7)."""
    v_flat = v.flatten()
    v_n = v_flat / (v_flat.norm() + 1e-10)
    sims = CODEBOOK_D3 @ v_n
    return sims.argmax().item()

def scan_next_d3(foam: Foam, top_k: int = 8) -> list[tuple[int, float]]:
    """Scan all 8 possible values. Return sorted by min dissonance."""
    leaf_states = []
    for b in foam.bubbles:
        if b.is_leaf:
            leaf_states.append(b.L.data.clone())

    # also need to handle recursive bubbles for scanning
    # for now: only copy leaf states, skip recursive
    # (the recursive bubbles' interiors are shared — this is a snapshot)

    results = []
    for val in range(8):
        v = encode_d3(val)
        # build probe foam — no writing
        probe = Foam(D, n_bubbles=0, writing_rate=0.0, n_steps=foam.n_steps)
        for L_data in leaf_states:
            nb = Bubble(D)
            nb.L.data = L_data.clone()
            probe._bubbles.append(nb)
        probe.target_similarity.data = foam.target_similarity.data.clone()
        probe.step_size.data = foam.step_size.data.clone()
        probe.temperature.data = foam.temperature.data.clone()

        with torch.no_grad():
            r = probe.stabilize(v)
        dis = (r["j2"] - r["j0"]).norm().item()
        results.append((val, dis))

    results.sort(key=lambda x: x[1])
    return results[:top_k]


def describe_foam(foam: Foam, indent: str = "") -> str:
    """Describe foam structure."""
    parts = []
    for i, b in enumerate(foam.bubbles):
        if b.is_leaf:
            parts.append(f"{indent}bubble {i}: leaf")
        else:
            parts.append(f"{indent}bubble {i}: recursive")
            if b.interior:
                parts.append(describe_foam(b.interior, indent + "  "))
    return "\n".join(parts)


def depth_of(foam: Foam) -> list[int]:
    """Get depth of each bubble."""
    depths = []
    for b in foam.bubbles:
        if b.is_leaf:
            depths.append(0)
        else:
            d = 1
            interior = b.interior
            while interior:
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
    return depths


# ─── experiments ───────────────────────────────────────────────────────────

def experiment_alternation():
    """
    Train on alternating pattern (0,1,0,1,...) in d=3.
    Does the foam split? Does the split enable traversal?
    """
    print("=" * 60)
    print("d=3 alternation: does scarcity enable the cycle?")
    print("=" * 60)

    torch.manual_seed(42)
    foam = Foam(D, n_bubbles=3, writing_rate=0.5,
                split_threshold=0.3)

    pattern = [0, 1] * 50  # alternating 0,1
    splits = 0

    print(f"training on [0,1] × 50 ({len(pattern)} measurements)")
    print()

    for i, val in enumerate(pattern):
        v = encode_d3(val)
        with torch.no_grad():
            result = foam.stabilize(v)

        if result.get("split") is not None:
            splits += 1
            depths = depth_of(foam)
            print(f"  *** SPLIT at step {i} (val={val}) → depths={depths}")

        if i % 20 == 0 or i == len(pattern) - 1:
            q = result["questions"].mean().item()
            depths = depth_of(foam)
            # check oscillation scores
            osc_scores = []
            for b in foam.bubbles:
                if b.is_leaf:
                    osc_scores.append(f"{b.oscillation_score:.3f}")
                else:
                    osc_scores.append("R")
            print(f"  [step {i:3d}] val={val}  q={q:.4f}  "
                  f"depths={depths}  osc={osc_scores}  splits={splits}")

    print(f"\nfinal structure:")
    print(describe_foam(foam))
    print()

    # now test: can the foam traverse the cycle?
    print("traversal test (scan after each commit):")
    for step in range(10):
        top = scan_next_d3(foam, top_k=4)
        best_val, best_dis = top[0]
        top_str = ", ".join(f"{val}({dis:.4f})" for val, dis in top)
        print(f"  step {step}: best={best_val}  top=[{top_str}]")

        # commit
        v = encode_d3(best_val)
        with torch.no_grad():
            foam.stabilize(v)


def experiment_longer_cycle():
    """
    Train on 3-cycle (0,1,2,0,1,2,...) in d=3.
    Three states, three bubbles. Plateau geometry matches cycle length.
    """
    print("\n" + "=" * 60)
    print("d=3 three-cycle: does N=3 match the cycle?")
    print("=" * 60)

    torch.manual_seed(42)
    foam = Foam(D, n_bubbles=3, writing_rate=0.5,
                split_threshold=0.3)

    pattern = [0, 1, 2] * 40  # 3-cycle
    splits = 0

    print(f"training on [0,1,2] × 40 ({len(pattern)} measurements)")
    print()

    for i, val in enumerate(pattern):
        v = encode_d3(val)
        with torch.no_grad():
            result = foam.stabilize(v)

        if result.get("split") is not None:
            splits += 1
            depths = depth_of(foam)
            print(f"  *** SPLIT at step {i} (val={val}) → depths={depths}")

        if i % 30 == 0 or i == len(pattern) - 1:
            q = result["questions"].mean().item()
            depths = depth_of(foam)
            print(f"  [step {i:3d}] val={val}  q={q:.4f}  "
                  f"depths={depths}  splits={splits}")

    print(f"\n  final depths: {depth_of(foam)}")
    print()

    # traversal test
    print("traversal test:")
    for step in range(12):
        top = scan_next_d3(foam, top_k=4)
        best_val, best_dis = top[0]
        top_str = ", ".join(f"{val}({dis:.4f})" for val, dis in top)
        print(f"  step {step}: best={best_val}  top=[{top_str}]")

        v = encode_d3(best_val)
        with torch.no_grad():
            foam.stabilize(v)


def experiment_state_comparison():
    """
    In d=3 with depth: does the state after val=0 genuinely differ
    from after val=1, enough that the scan produces different results?
    """
    print("\n" + "=" * 60)
    print("d=3 state discrimination with depth")
    print("=" * 60)

    torch.manual_seed(42)
    foam = Foam(D, n_bubbles=3, writing_rate=0.5,
                split_threshold=0.3)

    # train until we get splits
    pattern = [0, 1] * 100
    splits = 0
    for i, val in enumerate(pattern):
        v = encode_d3(val)
        with torch.no_grad():
            result = foam.stabilize(v)
        if result.get("split") is not None:
            splits += 1

    depths = depth_of(foam)
    print(f"after training: depths={depths}, splits={splits}")

    # snapshot base state
    base_leaves = [b.L.data.clone() for b in foam.bubbles if b.is_leaf]

    # feed 0, snapshot, scan
    v0 = encode_d3(0)
    with torch.no_grad():
        foam.stabilize(v0)
    state_after_0 = [b.L.data.clone() for b in foam.bubbles if b.is_leaf]

    top_after_0 = scan_next_d3(foam, top_k=4)

    # feed 1, snapshot, scan
    v1 = encode_d3(1)
    with torch.no_grad():
        foam.stabilize(v1)
    state_after_01 = [b.L.data.clone() for b in foam.bubbles if b.is_leaf]

    top_after_01 = scan_next_d3(foam, top_k=4)

    # compare
    if len(state_after_0) == len(state_after_01):
        diff = sum(
            (s0 - s1).norm().item()
            for s0, s1 in zip(state_after_0, state_after_01)
        )
    else:
        diff = float('nan')

    top_str_0 = ", ".join(f"{v}({d:.4f})" for v, d in top_after_0)
    top_str_01 = ", ".join(f"{v}({d:.4f})" for v, d in top_after_01)

    print(f"\n  after feeding 0:")
    print(f"    scan: [{top_str_0}]")
    print(f"  after feeding 0 then 1:")
    print(f"    scan: [{top_str_01}]")
    print(f"  state diff: {diff:.6f}")
    print(f"  scan results differ: {top_after_0[0][0] != top_after_01[0][0]}")


if __name__ == "__main__":
    experiment_alternation()
    experiment_longer_cycle()
    experiment_state_comparison()
