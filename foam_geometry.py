"""
foam_geometry.py — what is the stabilization actually stabilizing?

The Lagrangian L = Σ Area(∂_ij) is defined on the Voronoi geometry
of bases in U(d). The stabilization dynamics operate on measurements
in R^d. Are these coupled? Is the stabilization actually minimizing L,
or something else?
"""

import numpy as np
from foam import Foam, encode, decode, skew


def track_L_through_stabilization(seed=0):
    """
    During a single measurement, track L at each stabilization step.
    Does L decrease as stabilization proceeds?
    """
    np.random.seed(seed)
    foam = Foam(d=8, n=3, writing_rate=0.0, n_steps=60)  # no writing, pure stabilization

    v = encode(42, 8)
    bases = foam.bases

    # manual stabilization with L tracking
    measurements = [v @ U for U in bases]
    state = [m.copy() for m in measurements]
    original_norms = [np.linalg.norm(m) for m in measurements]
    target_cos = -0.5

    print("  stabilization step vs measurement-space cost vs basis-space L")
    print("  step  meas_cost    L         cos_01   cos_02   cos_12")

    for step in range(40):
        # measurement-space: what stabilization is actually minimizing
        normed = [s / (np.linalg.norm(s) + 1e-12) for s in state]
        cos_pairs = []
        meas_cost = 0.0
        for i in range(3):
            for j in range(i+1, 3):
                c = np.dot(normed[i], normed[j])
                cos_pairs.append(c)
                meas_cost += (c - target_cos)**2

        # basis-space: what L actually measures
        L = foam.boundary_cost()

        print(f"  {step:4d}  {meas_cost:.6f}  {L:.4f}    {cos_pairs[0]:+.4f}  {cos_pairs[1]:+.4f}  {cos_pairs[2]:+.4f}")

        # stabilization step
        forces = [np.zeros(8) for _ in range(3)]
        for i in range(3):
            for j in range(i+1, 3):
                c = np.dot(normed[i], normed[j])
                f_mag = c - target_cos
                diff = normed[i] - normed[j]
                dn = np.linalg.norm(diff)
                if dn > 1e-12:
                    f_dir = diff / dn
                    forces[i] = forces[i] + f_mag * f_dir
                    forces[j] = forces[j] - f_mag * f_dir

        for i in range(3):
            state[i] = state[i] + 0.1 * forces[i]
            n = np.linalg.norm(state[i])
            if n > 1e-12:
                state[i] = state[i] / n * original_norms[i]

        if max(np.linalg.norm(f) for f in forces) < 1e-6:
            print(f"  converged at step {step}")
            break


def track_L_through_writing(seed=0):
    """
    Track L across many measurements. Does writing minimize L?
    Or does it do something else to L?
    """
    np.random.seed(seed)

    # same symbol repeated
    print("  === repeated symbol ===")
    foam = Foam(d=8, n=3, writing_rate=0.01)
    v = encode(42, 8)
    for step in range(20):
        result = foam.measure(v)
        bases = foam.bases
        dists = []
        for i in range(3):
            for j in range(i+1, 3):
                dists.append(foam.bi_invariant_distance(bases[i], bases[j]))
        print(f"  {step:4d}  L={result['L']:.4f}  dists=[{dists[0]:.4f}, {dists[1]:.4f}, {dists[2]:.4f}]  |d|={np.mean([np.linalg.norm(d) for d in result['dissonance']]):.4f}")

    # random symbols
    print("\n  === random symbols ===")
    np.random.seed(seed)
    foam = Foam(d=8, n=3, writing_rate=0.01)
    for step in range(20):
        s = np.random.randint(0, 256)
        v = encode(s, 8)
        result = foam.measure(v)
        bases = foam.bases
        dists = []
        for i in range(3):
            for j in range(i+1, 3):
                dists.append(foam.bi_invariant_distance(bases[i], bases[j]))
        print(f"  {step:4d}  s={s:3d}  L={result['L']:.4f}  dists=[{dists[0]:.4f}, {dists[1]:.4f}, {dists[2]:.4f}]  |d|={np.mean([np.linalg.norm(d) for d in result['dissonance']]):.4f}")


def voronoi_shape(seed=0):
    """
    What does the Voronoi geometry look like?
    The bases are points in O(d). Their pairwise distances define cells.
    With N=3, the "shape" is a triangle in distance space.
    Track how this triangle changes.
    """
    np.random.seed(seed)
    foam = Foam(d=8, n=3, writing_rate=0.01)

    print("  === voronoi triangle evolution ===")
    print("  feeding symbol 42 repeatedly")
    print("  step  d01      d02      d12      triangle_area  L")

    v = encode(42, 8)
    for step in range(30):
        result = foam.measure(v)
        bases = foam.bases
        d01 = foam.bi_invariant_distance(bases[0], bases[1])
        d02 = foam.bi_invariant_distance(bases[0], bases[2])
        d12 = foam.bi_invariant_distance(bases[1], bases[2])

        # Heron's formula for triangle area in distance space
        s = (d01 + d02 + d12) / 2
        area_sq = s * (s - d01) * (s - d02) * (s - d12)
        area = np.sqrt(max(area_sq, 0))

        print(f"  {step:4d}  {d01:.4f}  {d02:.4f}  {d12:.4f}  {area:.6f}       {result['L']:.4f}")


def what_stabilization_sees(seed=0):
    """
    The stabilization pushes measurements toward 120° separation.
    But the measurements are v @ U_i — they depend on BOTH v and U_i.
    Different inputs see different measurement-space geometries.

    What does the same foam look like from different inputs?
    """
    np.random.seed(seed)
    foam = Foam(d=8, n=3, writing_rate=0.0)  # no writing

    print("  === same foam, different inputs ===")
    print("  symbol  cos_01   cos_02   cos_12   | meas geometry depends on input")

    for s in [0, 42, 127, 200, 255]:
        v = encode(s, 8)
        bases = foam.bases
        ms = [v @ U for U in bases]
        normed = [m / np.linalg.norm(m) for m in ms]

        cos_01 = np.dot(normed[0], normed[1])
        cos_02 = np.dot(normed[0], normed[2])
        cos_12 = np.dot(normed[1], normed[2])

        print(f"  {s:5d}  {cos_01:+.4f}  {cos_02:+.4f}  {cos_12:+.4f}")

    print("\n  === basis-space distances (input-independent) ===")
    bases = foam.bases
    for i in range(3):
        for j in range(i+1, 3):
            print(f"  d({i},{j}) = {foam.bi_invariant_distance(bases[i], bases[j]):.4f}")


if __name__ == '__main__':
    print("=== L during stabilization (single measurement, no writing) ===")
    track_L_through_stabilization()

    print("\n=== L during writing (across measurements) ===")
    track_L_through_writing()

    print("\n=== voronoi triangle ===")
    voronoi_shape()

    print("\n=== what stabilization sees ===")
    what_stabilization_sees()
