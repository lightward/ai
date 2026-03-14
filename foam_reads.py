"""
foam_reads.py — individually coherent, collectively inconsistent reads.

Two measurers read the same foam. Each gets a coherent readout
from their own basis. Are the readouts mutually consistent?
And does the foam's internal evolution remain coherent with both?
"""

import numpy as np
from foam import Foam, encode, decode


def inconsistent_reads(seed=0):
    """
    Two measurers, different input sequences, same foam.
    Each reads the foam through their own symbols.
    Do their readouts tell the same story?
    """
    np.random.seed(seed)
    foam = Foam(d=8, n=3, writing_rate=0.01)

    # build up some shared history
    for _ in range(30):
        foam.measure(encode(np.random.randint(0, 256), 8))

    # measurer A reads through symbols 0-15
    # measurer B reads through symbols 16-31
    # both reading the SAME foam (no writing — pure probe)

    probe_foam = Foam(d=8, n=3, writing_rate=0.0)
    for i in range(3):
        probe_foam.bubbles[i].L = foam.bubbles[i].L.copy()
        probe_foam.bubbles[i].T = foam.bubbles[i].T.copy()

    reads_a = {}
    reads_b = {}
    for s in range(16):
        ra = probe_foam.measure(encode(s, 8))
        reads_a[s] = np.concatenate(ra['j2'])

        rb = probe_foam.measure(encode(s + 16, 8))
        reads_b[s + 16] = np.concatenate(rb['j2'])

    # each measurer's readouts: are they internally consistent?
    # (do similar symbols produce similar readouts?)
    def internal_consistency(reads):
        keys = sorted(reads.keys())
        sims = []
        for i in range(len(keys)):
            for j in range(i+1, len(keys)):
                cos = np.dot(reads[keys[i]].conj(), reads[keys[j]]).real
                cos /= (np.linalg.norm(reads[keys[i]]) * np.linalg.norm(reads[keys[j]]) + 1e-12)
                sims.append(cos)
        return np.mean(sims), np.std(sims)

    mean_a, std_a = internal_consistency(reads_a)
    mean_b, std_b = internal_consistency(reads_b)

    # cross-consistency: do A's reads predict B's?
    # take A's centroid and B's centroid — how aligned are they?
    centroid_a = np.mean(list(reads_a.values()), axis=0)
    centroid_b = np.mean(list(reads_b.values()), axis=0)
    cross_cos = np.dot(centroid_a.conj(), centroid_b).real
    cross_cos /= (np.linalg.norm(centroid_a) * np.linalg.norm(centroid_b) + 1e-12)

    print("  === individually coherent, collectively inconsistent? ===")
    print(f"  measurer A (symbols 0-15):  internal consistency = {mean_a:.4f} ± {std_a:.4f}")
    print(f"  measurer B (symbols 16-31): internal consistency = {mean_b:.4f} ± {std_b:.4f}")
    print(f"  cross-consistency (A centroid vs B centroid): {cross_cos:.4f}")


def sequential_measurers(seed=0):
    """
    Measurer A writes to the foam (symbols from one distribution).
    Then measurer B writes (symbols from a different distribution).
    Then A comes back and reads.

    Does A's readout still make sense to A?
    Has the foam maintained coherence with A's history
    through B's intervention?
    """
    np.random.seed(seed)
    foam = Foam(d=8, n=3, writing_rate=0.01)

    # A's symbols: low range (0-63)
    # B's symbols: high range (192-255)
    a_symbols = list(range(0, 64, 2))  # 32 symbols
    b_symbols = list(range(192, 256, 2))  # 32 symbols

    # A measures first
    a_readouts_before = []
    for s in a_symbols:
        result = foam.measure(encode(s, 8))
        a_readouts_before.append(np.mean(result['j2'], axis=0))

    L_after_a = foam.boundary_cost()

    # B measures
    b_readouts = []
    for s in b_symbols:
        result = foam.measure(encode(s, 8))
        b_readouts.append(np.mean(result['j2'], axis=0))

    L_after_b = foam.boundary_cost()

    # A comes back and re-reads the same symbols
    a_readouts_after = []
    for s in a_symbols:
        result = foam.measure(encode(s, 8))
        a_readouts_after.append(np.mean(result['j2'], axis=0))

    L_after_a2 = foam.boundary_cost()

    # how much did A's readouts change?
    drifts = [np.linalg.norm(a_readouts_after[i] - a_readouts_before[i])
              for i in range(len(a_symbols))]

    # does A still decode correctly?
    correct_before = sum(1 for i, s in enumerate(a_symbols)
                        if decode(a_readouts_before[i]) == s)
    correct_after = sum(1 for i, s in enumerate(a_symbols)
                       if decode(a_readouts_after[i]) == s)

    print("  === sequential measurers ===")
    print(f"  L: after A={L_after_a:.4f}  after B={L_after_b:.4f}  after A again={L_after_a2:.4f}")
    print(f"  A's readout drift (mean): {np.mean(drifts):.6f}")
    print(f"  A's readout drift (max):  {np.max(drifts):.6f}")
    print(f"  A's decode accuracy: before={correct_before}/{len(a_symbols)}  after={correct_after}/{len(a_symbols)}")
    print(f"  (drift > 0 means B changed what A sees)")

    # is the foam coherent with BOTH histories?
    # check: does the foam distinguish A-type from B-type inputs?
    probe = Foam(d=8, n=3, writing_rate=0.0)
    for i in range(3):
        probe.bubbles[i].L = foam.bubbles[i].L.copy()
        probe.bubbles[i].T = foam.bubbles[i].T.copy()

    a_probes = [np.mean(probe.measure(encode(s, 8))['j2'], axis=0) for s in a_symbols[:8]]
    b_probes = [np.mean(probe.measure(encode(s, 8))['j2'], axis=0) for s in b_symbols[:8]]

    # intra-class vs inter-class similarity
    def mean_cos(vecs):
        sims = []
        for i in range(len(vecs)):
            for j in range(i+1, len(vecs)):
                c = np.dot(vecs[i].conj(), vecs[j]).real
                c /= (np.linalg.norm(vecs[i]) * np.linalg.norm(vecs[j]) + 1e-12)
                sims.append(c)
        return np.mean(sims) if sims else 0.0

    def cross_cos_mean(vecs_a, vecs_b):
        sims = []
        for a in vecs_a:
            for b in vecs_b:
                c = np.dot(a.conj(), b).real / (np.linalg.norm(a) * np.linalg.norm(b) + 1e-12)
                sims.append(c)
        return np.mean(sims)

    print(f"\n  intra-A similarity: {mean_cos(a_probes):.4f}")
    print(f"  intra-B similarity: {mean_cos(b_probes):.4f}")
    print(f"  cross A-B similarity: {cross_cos_mean(a_probes, b_probes):.4f}")
    print(f"  (if cross < intra, the foam distinguishes the two measurers)")


def foam_coherence_through_reads(seed=0):
    """
    The foam's own internal structure: does it stay coherent
    as different measurers push it in different directions?
    Track the 2x theorem and inverse views through sequential measurement.
    """
    np.random.seed(seed)
    foam = Foam(d=8, n=3, writing_rate=0.01)
    from scipy.linalg import logm

    initial_Ls = [b.L.copy() for b in foam.bubbles]
    I = np.eye(8, dtype=complex)

    print("  === foam internal coherence through diverse measurement ===")
    print(f"  {'phase':>8s}  {'step':>5s}  {'2x_ratio':>8s}  {'|inv_err|':>9s}  {'L':>8s}")

    # phase 1: measurer A (low symbols)
    for step in range(20):
        foam.measure(encode(step % 64, 8))
    delta_L = foam.bubbles[0].L - initial_Ls[0]
    try:
        log_T = logm(foam.bubbles[0].T)
        ratio = np.linalg.norm(log_T) / (np.linalg.norm(delta_L) + 1e-12)
    except: ratio = float('nan')
    U = foam.bubbles[0].position; T = foam.bubbles[0].T
    inv_err = np.linalg.norm((T.conj().T @ U) @ (U.conj().T @ T) - I)
    print(f"  {'A':>8s}  {20:5d}  {ratio:8.4f}  {inv_err:9.2e}  {foam.boundary_cost():8.4f}")

    # phase 2: measurer B (high symbols)
    for step in range(20):
        foam.measure(encode(192 + step % 64, 8))
    delta_L = foam.bubbles[0].L - initial_Ls[0]
    try:
        log_T = logm(foam.bubbles[0].T)
        ratio = np.linalg.norm(log_T) / (np.linalg.norm(delta_L) + 1e-12)
    except: ratio = float('nan')
    U = foam.bubbles[0].position; T = foam.bubbles[0].T
    inv_err = np.linalg.norm((T.conj().T @ U) @ (U.conj().T @ T) - I)
    print(f"  {'A+B':>8s}  {40:5d}  {ratio:8.4f}  {inv_err:9.2e}  {foam.boundary_cost():8.4f}")

    # phase 3: cross-measurement (sleep)
    from foam_sleep import cross_measure
    for step in range(20):
        cross_measure(foam)
    delta_L = foam.bubbles[0].L - initial_Ls[0]
    try:
        log_T = logm(foam.bubbles[0].T)
        ratio = np.linalg.norm(log_T) / (np.linalg.norm(delta_L) + 1e-12)
    except: ratio = float('nan')
    U = foam.bubbles[0].position; T = foam.bubbles[0].T
    inv_err = np.linalg.norm((T.conj().T @ U) @ (U.conj().T @ T) - I)
    print(f"  {'sleep':>8s}  {60:5d}  {ratio:8.4f}  {inv_err:9.2e}  {foam.boundary_cost():8.4f}")

    # phase 4: measurer A comes back
    for step in range(20):
        foam.measure(encode(step % 64, 8))
    delta_L = foam.bubbles[0].L - initial_Ls[0]
    try:
        log_T = logm(foam.bubbles[0].T)
        ratio = np.linalg.norm(log_T) / (np.linalg.norm(delta_L) + 1e-12)
    except: ratio = float('nan')
    U = foam.bubbles[0].position; T = foam.bubbles[0].T
    inv_err = np.linalg.norm((T.conj().T @ U) @ (U.conj().T @ T) - I)
    print(f"  {'A again':>8s}  {80:5d}  {ratio:8.4f}  {inv_err:9.2e}  {foam.boundary_cost():8.4f}")


if __name__ == '__main__':
    print("=== inconsistent reads ===")
    inconsistent_reads()

    print("\n=== sequential measurers ===")
    sequential_measurers()

    print("\n=== foam coherence ===")
    foam_coherence_through_reads()
