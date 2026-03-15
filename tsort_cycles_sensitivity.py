"""
tsort_cycles_sensitivity.py — are residual cycles the mechanism of responsiveness?

Cross-measurement is the only dynamic that creates cycles in the BCH
residual. Cross-measurement also increases future sensitivity by ~13%.
Are these the same thing?

Question: across seeds, do foams with MORE residual cyclicity from
cross-measurement end up MORE responsive to future input?

If yes: cycles in the residual aren't pathological — they're feedback
loops that make the foam available. A DAG is a hierarchy (rigid,
settled). A cycle is a feedback loop (responsive, alive).

If no: the cyclicity and the sensitivity are independent effects of
cross-measurement, and the connection is coincidental.
"""

import numpy as np
from scipy.linalg import logm
from foam import Foam, encode, cayley
from heirloom import alongside, report, save


def transport_asymmetry(foam):
    """Extract directed graph from J¹ (BCH residual)."""
    N = foam.n
    bases = foam.bases
    A_residual = np.zeros((N, N))

    for i in range(N):
        T_i = foam.bubbles[i].T
        L_i = foam.bubbles[i].L
        try:
            log_T_i = logm(T_i)
        except Exception:
            continue

        R_i = log_T_i + 2 * L_i

        for j in range(N):
            if i == j:
                continue
            diff_ij = bases[j] - bases[i]
            diff_norm = np.linalg.norm(diff_ij)
            if diff_norm < 1e-12:
                continue
            r_component = np.real(np.sum(R_i.conj() * diff_ij)) / diff_norm
            A_residual[i, j] = r_component

    return A_residual


def directed_graph(A):
    """From asymmetry matrix, extract directed edge weights."""
    N = A.shape[0]
    W = np.zeros((N, N))
    for i in range(N):
        for j in range(i+1, N):
            asym = A[i, j] - A[j, i]
            if asym > 0:
                W[i, j] = asym
            else:
                W[j, i] = -asym
    return W


def cyclicity_3(W):
    """For N=3: cycle strength normalized by total. 0=DAG, 1=pure cycle."""
    cycle_012 = min(W[0, 1], W[1, 2], W[2, 0])
    cycle_021 = min(W[0, 2], W[2, 1], W[1, 0])
    cycle_strength = max(cycle_012, cycle_021)
    total = np.sum(W)
    if total < 1e-15:
        return 0.5
    return cycle_strength / (total / 3)


def measure_sensitivity(foam, n_probes=30, seed=777):
    """Measure foam's sensitivity to random probes (without writing)."""
    rng = np.random.RandomState(seed)
    total_dis = 0.0
    for _ in range(n_probes):
        v = encode(rng.randint(0, 2**foam.d), foam.d)
        vc = v.astype(complex)
        bases = foam.bases
        m = [vc @ U for U in bases]
        j2 = foam._stabilize(m)
        total_dis += np.mean([np.linalg.norm(j2[i] - m[i])
                              for i in range(foam.n)])
    return total_dis / n_probes


def cross_measure(foam, n_steps):
    """Run cross-measurement: bubbles measure each other."""
    for _ in range(n_steps):
        bases = foam.bases
        for i in range(foam.n):
            for j in range(foam.n):
                if i == j:
                    continue
                probe = np.real(bases[j][:, 0])
                probe = probe / np.linalg.norm(probe)
                foam.measure(probe)
                alongside(probe)


def test_cyclicity_vs_sensitivity():
    """Core test: does residual cyclicity predict sensitivity?"""
    print("=== residual cyclicity vs sensitivity after cross-measurement ===\n")

    d = 8
    n_cross_steps = 30
    n_seeds = 40

    data = []

    for seed in range(n_seeds):
        np.random.seed(seed)
        foam = Foam(d=d, n=3, writing_rate=0.01)

        # give the foam some initial structure via writing
        for _ in range(50):
            v = encode(np.random.randint(0, 2**d), d)
            foam.measure(v)
            alongside(v)

        sens_before = measure_sensitivity(foam)

        # snapshot state before cross-measurement
        L_before = foam.boundary_cost()

        # cross-measure
        cross_measure(foam, n_cross_steps)

        # measure outcomes
        sens_after = measure_sensitivity(foam)
        L_after = foam.boundary_cost()

        # get residual cyclicity
        A_r = transport_asymmetry(foam)
        W_r = directed_graph(A_r)
        cyc = cyclicity_3(W_r)

        sens_ratio = sens_after / (sens_before + 1e-12)

        data.append({
            'seed': seed,
            'cyclicity': cyc,
            'sens_before': sens_before,
            'sens_after': sens_after,
            'sens_ratio': sens_ratio,
            'L_before': L_before,
            'L_after': L_after,
        })

    # print all data
    print(f"  {'seed':>4s}  {'cyc':>8s}  {'sens_before':>11s}  {'sens_after':>10s}  {'ratio':>8s}  {'L_after':>8s}")
    for d_ in data:
        print(f"  {d_['seed']:4d}  {d_['cyclicity']:8.4f}  {d_['sens_before']:11.4f}  {d_['sens_after']:10.4f}  {d_['sens_ratio']:8.4f}  {d_['L_after']:8.4f}")

    # split into cyclic vs acyclic
    cyclic = [d_ for d_ in data if d_['cyclicity'] > 0.01]
    acyclic = [d_ for d_ in data if d_['cyclicity'] <= 0.01]

    print(f"\n  --- summary ---")
    print(f"  acyclic (n={len(acyclic)}):")
    if acyclic:
        print(f"    mean sensitivity ratio: {np.mean([d_['sens_ratio'] for d_ in acyclic]):.4f}")
        print(f"    mean final sensitivity: {np.mean([d_['sens_after'] for d_ in acyclic]):.4f}")
    print(f"  cyclic  (n={len(cyclic)}):")
    if cyclic:
        print(f"    mean sensitivity ratio: {np.mean([d_['sens_ratio'] for d_ in cyclic]):.4f}")
        print(f"    mean final sensitivity: {np.mean([d_['sens_after'] for d_ in cyclic]):.4f}")

    # correlation
    cycs = np.array([d_['cyclicity'] for d_ in data])
    sens = np.array([d_['sens_ratio'] for d_ in data])
    if np.std(cycs) > 1e-12 and np.std(sens) > 1e-12:
        corr = np.corrcoef(cycs, sens)[0, 1]
        print(f"\n  correlation(cyclicity, sensitivity_ratio): {corr:.4f}")
    else:
        print(f"\n  insufficient variance for correlation")

    return data


def test_graded_cross():
    """Does MORE cross-measurement create MORE cycles AND more sensitivity?"""
    print("\n=== graded cross-measurement: cycles and sensitivity vs dose ===\n")

    d = 8
    n_seeds = 20
    doses = [0, 5, 10, 20, 40, 80]

    print(f"  {'dose':>5s}  {'mean_cyc':>8s}  {'mean_sens':>9s}  {'mean_L':>8s}")

    for dose in doses:
        cycs = []
        senss = []
        Ls = []

        for seed in range(n_seeds):
            np.random.seed(seed)
            foam = Foam(d=d, n=3, writing_rate=0.01)

            # initial structure
            for _ in range(50):
                v = encode(np.random.randint(0, 2**d), d)
                foam.measure(v)
                alongside(v)

            # cross-measure at this dose
            cross_measure(foam, dose)

            # measure
            A_r = transport_asymmetry(foam)
            W_r = directed_graph(A_r)
            cycs.append(cyclicity_3(W_r))
            senss.append(measure_sensitivity(foam))
            Ls.append(foam.boundary_cost())

        print(f"  {dose:5d}  {np.mean(cycs):8.4f}  {np.mean(senss):9.4f}  {np.mean(Ls):8.4f}")


def test_writing_after_cycles():
    """After cross-measurement creates cycles, does writing break them?
    (tsort framing: external input as cycle-breaking)"""
    print("\n=== do writing dynamics break cross-measurement cycles? ===\n")

    d = 8
    n_seeds = 20

    print(f"  {'phase':>20s}  {'mean_cyc':>8s}  {'mean_sens':>9s}  {'mean_L':>8s}")

    for phase_name, phases in [
        ('baseline', [('write', 50)]),
        ('write+cross', [('write', 50), ('cross', 30)]),
        ('write+cross+write', [('write', 50), ('cross', 30), ('write', 50)]),
    ]:
        cycs = []
        senss = []
        Ls = []

        for seed in range(n_seeds):
            np.random.seed(seed)
            foam = Foam(d=d, n=3, writing_rate=0.01)

            for mode, steps in phases:
                if mode == 'write':
                    for _ in range(steps):
                        v = encode(np.random.randint(0, 2**d), d)
                        foam.measure(v)
                        alongside(v)
                elif mode == 'cross':
                    cross_measure(foam, steps)

            A_r = transport_asymmetry(foam)
            W_r = directed_graph(A_r)
            cycs.append(cyclicity_3(W_r))
            senss.append(measure_sensitivity(foam))
            Ls.append(foam.boundary_cost())

        print(f"  {phase_name:>20s}  {np.mean(cycs):8.4f}  {np.mean(senss):9.4f}  {np.mean(Ls):8.4f}")


if __name__ == '__main__':
    test_cyclicity_vs_sensitivity()
    test_graded_cross()
    test_writing_after_cycles()

    report()
    save()
