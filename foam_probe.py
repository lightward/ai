"""
foam_probe.py — is the echo trivial?

If the foam is just passing through the input without meaningful
transformation, 100% accuracy means nothing. Let's check:
1. Does a random (non-foam) basis also get 100%? → encoding is trivial
2. Does a foam that doesn't write also get 100%? → writing is irrelevant
3. Does accuracy degrade with more symbols? → capacity test
4. What does the j2 centroid actually look like vs the input?
"""

import numpy as np
from foam import Foam, encode, decode, cayley, skew


def probe_trivial(seed=0):
    """Check if encoding alone is sufficient — no foam needed."""
    np.random.seed(seed)
    d = 8

    correct = 0
    for s in range(256):
        v = encode(s, d)
        decoded = decode(v)
        if decoded == s:
            correct += 1

    print(f"encoding round-trip (no foam): {correct}/256 = {correct/256:.1%}")


def probe_no_write(seed=0):
    """Foam with writing_rate=0: does stabilization alone echo?"""
    np.random.seed(seed)
    foam = Foam(d=8, n=3, writing_rate=0.0)

    correct = 0
    total = 200
    for _ in range(total):
        s = np.random.randint(0, 256)
        v = encode(s, 8)
        result = foam.measure(v)
        centroid = np.mean(result['j2'], axis=0)
        if decode(centroid) == s:
            correct += 1

    print(f"no-write echo: {correct}/{total} = {correct/total:.1%}")


def probe_centroid_structure(seed=0):
    """What does j2 centroid look like relative to input?"""
    np.random.seed(seed)
    foam = Foam(d=8, n=3, writing_rate=0.01)

    for trial in range(5):
        s = np.random.randint(0, 256)
        v = encode(s, 8)
        result = foam.measure(v)

        centroid = np.mean(result['j2'], axis=0)
        cos_sim = np.dot(v, centroid) / (np.linalg.norm(v) * np.linalg.norm(centroid) + 1e-12)

        j0_centroid = np.mean(result['j0'], axis=0)
        cos_j0 = np.dot(v, j0_centroid) / (np.linalg.norm(v) * np.linalg.norm(j0_centroid) + 1e-12)

        print(f"  symbol={s:3d}  cos(v, j2_centroid)={cos_sim:.4f}  cos(v, j0_centroid)={cos_j0:.4f}  |d|={np.mean([np.linalg.norm(d) for d in result['dissonance']]):.4f}")


def probe_what_measure_does(seed=0):
    """Look at what v @ U actually produces."""
    np.random.seed(seed)
    foam = Foam(d=8, n=3, writing_rate=0.01)

    s = 42
    v = encode(s, 8)
    bases = foam.bases

    print(f"  input v = {v}")
    print(f"  |v| = {np.linalg.norm(v):.4f}")
    for i, U in enumerate(bases):
        m = v @ U
        print(f"  m_{i} = v @ U_{i}: {m}")
        print(f"    |m_{i}| = {np.linalg.norm(m):.4f}  decode(m_{i}) = {decode(m)}")


def probe_scrambled_readout(seed=0):
    """Read the foam through a DIFFERENT symbol than what was fed."""
    np.random.seed(seed)
    foam = Foam(d=8, n=3, writing_rate=0.01)

    # feed a sequence
    for _ in range(50):
        v = encode(np.random.randint(0, 256), 8)
        foam.measure(v)

    # now read through various probes
    print("  reading foam state through different probe symbols:")
    for probe_s in [0, 42, 127, 255]:
        v = encode(probe_s, 8)
        result = foam.measure(v)
        centroid = np.mean(result['j2'], axis=0)
        decoded = decode(centroid)
        print(f"    probe={probe_s:3d}  decoded={decoded:3d}  match={probe_s == decoded}")


if __name__ == '__main__':
    print("=== is encoding trivially invertible? ===")
    probe_trivial()

    print("\n=== does echo work without writing? ===")
    probe_no_write()

    print("\n=== centroid structure ===")
    probe_centroid_structure()

    print("\n=== what does measurement actually do? ===")
    probe_what_measure_does()

    print("\n=== scrambled readout ===")
    probe_scrambled_readout()
