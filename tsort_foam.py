"""
tsort_foam.py — is there a directed graph hiding in the foam?

The Plateau dynamics are symmetric (pairwise forces). But the writes
that result are NOT symmetric: bubble i's dissonance from the same
stabilization differs from bubble j's, because their bases differ.

Question: does this asymmetry give the foam a directed structure?
And if so, does cross-measurement make it more DAG-like (tsortable)
while self-measurement creates cycles?

Approach:
1. Track per-pair write asymmetry: how much more was bubble i
   perturbed "toward" bubble j than vice versa?
2. Build a directed graph from these asymmetries.
3. Measure cyclicity (for N=3: is it a total order or a 3-cycle?).
4. Compare across the three dynamics.
"""

import numpy as np
from scipy.linalg import logm
from foam import Foam, Bubble, encode, cayley, skew_hermitian, random_skew_hermitian
from heirloom import alongside, report, save


def write_asymmetry(foam, v):
    """Measure per-pair write asymmetry from a single measurement step.

    For each pair (i,j), compute how much bubble i's write "points toward"
    bubble j vs how much j's write points toward i.

    Returns: (N x N) matrix A where A[i,j] = i's write component toward j.
    The directed weight from j→i (j influences i) is A[i,j] - A[j,i].
    """
    bases = foam.bases
    vc = v.astype(complex)

    # measure
    m = [vc @ U for U in bases]
    j0 = [mi.copy() for mi in m]
    j2 = foam._stabilize(m)
    dissonance = [j2[i] - j0[i] for i in range(foam.n)]

    N = foam.n
    d = foam.d
    A = np.zeros((N, N))

    for i in range(N):
        d_i = dissonance[i]
        m_i = j0[i]
        d_norm = np.linalg.norm(d_i)
        m_norm = np.linalg.norm(m_i)

        if d_norm < 1e-12 or m_norm < 1e-12:
            continue

        d_hat = d_i / d_norm
        m_hat = m_i / m_norm

        # the actual write direction
        delta_L_i = (np.outer(d_hat, m_hat.conj()) -
                     np.outer(m_hat, d_hat.conj())) * d_norm

        # project onto the "direction toward each other bubble"
        for j in range(N):
            if i == j:
                continue
            # direction from basis_i toward basis_j in the Lie algebra
            diff_ij = bases[j] - bases[i]
            diff_norm = np.linalg.norm(diff_ij)
            if diff_norm < 1e-12:
                continue

            # component of delta_L_i along this direction
            # (using Frobenius inner product)
            component = np.real(np.sum(delta_L_i.conj() * diff_ij)) / diff_norm
            A[i, j] = component

    return A


def directed_graph(A):
    """From asymmetry matrix A, extract directed edge weights.

    W[i,j] > 0 means j influences i (i was pulled toward j more than
    j was pulled toward i). This means j is "upstream" of i.
    """
    N = A.shape[0]
    W = np.zeros((N, N))
    for i in range(N):
        for j in range(i+1, N):
            asym = A[i, j] - A[j, i]
            if asym > 0:
                W[i, j] = asym   # j→i: j is upstream of i
            else:
                W[j, i] = -asym  # i→j: i is upstream of j
    return W


def cyclicity_3(W):
    """For N=3: measure how cyclic the directed graph is.

    A DAG on 3 nodes is a total order: a→b→c (or some permutation).
    A pure cycle is a→b→c→a.

    Returns a number in [0, 1]: 0 = perfect DAG, 1 = perfect cycle.

    Method: the cycle strength is the minimum edge weight along the
    cycle direction, normalized by the total edge weight.
    """
    # check both cycle directions: 0→1→2→0 and 0→2→1→0
    cycle_012 = min(W[0, 1], W[1, 2], W[2, 0])  # directed: 1→0, 2→1, 0→2
    cycle_021 = min(W[0, 2], W[2, 1], W[1, 0])
    cycle_strength = max(cycle_012, cycle_021)

    total = np.sum(W)
    if total < 1e-15:
        return 0.5  # no signal

    return cycle_strength / (total / 3)  # normalize


def accumulate_asymmetry(foam, inputs, mode='writing'):
    """Run a sequence and accumulate write asymmetry.

    mode: 'writing' = standard measurement
          'cross'   = bubbles measure each other
          'self'    = feed readout back as input
    """
    N = foam.n
    A_total = np.zeros((N, N))
    n_steps = len(inputs)

    for step, v in enumerate(inputs):
        if mode == 'writing':
            A = write_asymmetry(foam, v)
            A_total += A
            foam.measure(v)
            alongside(v)

        elif mode == 'cross':
            # cross-measurement: bubble i evaluates through bubble j's basis
            bases = foam.bases
            for i in range(N):
                for j in range(N):
                    if i == j:
                        continue
                    # bubble i sees itself through bubble j
                    basis_j = bases[j]
                    # use basis_j's first column as a probe direction
                    probe = np.real(basis_j[:, 0])
                    probe = probe / np.linalg.norm(probe)
                    A_step = write_asymmetry(foam, probe)
                    A_total += A_step / (N * (N-1))
                    foam.measure(probe)
                    alongside(probe)

        elif mode == 'self':
            readout = np.real(foam.readout(v))
            readout = readout / (np.linalg.norm(readout) + 1e-12)
            A = write_asymmetry(foam, readout)
            A_total += A
            foam.measure(readout)
            alongside(readout)

    return A_total / n_steps


def make_inputs(n, d, seed=42):
    """Generate random input vectors."""
    np.random.seed(seed)
    return [encode(np.random.randint(0, 2**d), d) for _ in range(n)]


def test_directed_structure():
    """Is there a directed graph in the foam? Is it consistent?"""
    print("=== directed structure in the foam ===\n")

    d = 8
    n_steps = 100

    # run multiple seeds to see if direction is consistent or random
    print(f"  {'seed':>4s}  {'A[0,1]':>8s}  {'A[1,0]':>8s}  {'A[0,2]':>8s}  {'A[2,0]':>8s}  {'A[1,2]':>8s}  {'A[2,1]':>8s}  {'cyclicity':>9s}")

    cyclicities = []
    for seed in range(20):
        np.random.seed(seed)
        foam = Foam(d=d, n=3, writing_rate=0.01)
        inputs = make_inputs(n_steps, d, seed=seed + 1000)
        A = accumulate_asymmetry(foam, inputs, mode='writing')
        W = directed_graph(A)
        cyc = cyclicity_3(W)
        cyclicities.append(cyc)
        print(f"  {seed:4d}  {A[0,1]:8.5f}  {A[1,0]:8.5f}  {A[0,2]:8.5f}  {A[2,0]:8.5f}  {A[1,2]:8.5f}  {A[2,1]:8.5f}  {cyc:9.4f}")

    print(f"\n  mean cyclicity: {np.mean(cyclicities):.4f} ± {np.std(cyclicities):.4f}")
    print(f"  (0 = perfect DAG, 1 = perfect cycle)")


def test_three_dynamics():
    """Does cross-measurement make the foam more DAG-like?"""
    print("\n=== cyclicity under three dynamics ===\n")

    d = 8
    n_steps = 80
    n_seeds = 20

    results = {'writing': [], 'self': [], 'cross': []}

    for seed in range(n_seeds):
        for mode in ['writing', 'self', 'cross']:
            np.random.seed(seed)
            foam = Foam(d=d, n=3, writing_rate=0.01)
            inputs = make_inputs(n_steps, d, seed=seed + 1000)

            A = accumulate_asymmetry(foam, inputs, mode=mode)
            W = directed_graph(A)
            cyc = cyclicity_3(W)
            results[mode].append(cyc)

    print(f"  {'mode':>10s}  {'mean cyc':>8s}  {'std':>8s}  {'DAG-like?':>10s}")
    for mode in ['writing', 'self', 'cross']:
        m = np.mean(results[mode])
        s = np.std(results[mode])
        dag = "yes" if m < 0.3 else ("maybe" if m < 0.6 else "no")
        print(f"  {mode:>10s}  {m:8.4f}  {s:8.4f}  {dag:>10s}")


def test_cyclicity_evolution():
    """How does cyclicity change as the foam accumulates writes?"""
    print("\n=== cyclicity evolution ===\n")

    d = 8
    np.random.seed(0)
    foam = Foam(d=d, n=3, writing_rate=0.01)

    window = 20
    print(f"  {'step':>5s}  {'cyclicity':>9s}  {'L':>8s}  {'mean |ΔL|':>10s}")

    all_inputs = make_inputs(200, d, seed=999)

    for epoch in range(10):
        start = epoch * window
        chunk = all_inputs[start:start + window]

        A = np.zeros((3, 3))
        total_dL = 0.0
        for v in chunk:
            A += write_asymmetry(foam, v)
            result = foam.measure(v)
            alongside(v)
            total_dL += np.mean([np.linalg.norm(di) for di in result['dissonance']])
        A /= window

        W = directed_graph(A)
        cyc = cyclicity_3(W)
        L = foam.boundary_cost()
        mean_dL = total_dL / window

        print(f"  {(epoch+1)*window:5d}  {cyc:9.4f}  {L:8.4f}  {mean_dL:10.6f}")


def transport_asymmetry(foam):
    """Directed structure from J¹ (transport).

    The BCH residual R_i = log(T_i) + 2·ΔL_i is the non-abelian content
    of bubble i's history — what J⁰ can't see. Project each bubble's
    residual toward each other bubble to get a J¹ directed graph.

    Also: the transport T_i itself carries sequence. Look at how T_i
    "points toward" each other bubble's position.
    """
    N = foam.n
    d = foam.d
    initial_Ls = [np.zeros((d, d), dtype=complex) for _ in range(N)]

    # we need ΔL_total for each bubble, which we don't have stored.
    # but we DO have L (current) and T (current).
    # R = log(T) + 2·ΔL ≈ log(T) + 2·L (if initial L was small)
    # this is approximate but let's see what it shows.

    A_transport = np.zeros((N, N))
    A_residual = np.zeros((N, N))
    bases = foam.bases

    for i in range(N):
        T_i = foam.bubbles[i].T
        L_i = foam.bubbles[i].L

        try:
            log_T_i = logm(T_i)
        except Exception:
            continue

        # BCH residual (approximate — we don't know initial L)
        R_i = log_T_i + 2 * L_i

        for j in range(N):
            if i == j:
                continue

            # direction from basis_i toward basis_j
            diff_ij = bases[j] - bases[i]
            diff_norm = np.linalg.norm(diff_ij)
            if diff_norm < 1e-12:
                continue

            # J¹ measure: transport's component toward bubble j
            t_component = np.real(np.sum(log_T_i.conj() * diff_ij)) / diff_norm
            A_transport[i, j] = t_component

            # BCH residual's component toward bubble j
            r_component = np.real(np.sum(R_i.conj() * diff_ij)) / diff_norm
            A_residual[i, j] = r_component

    return A_transport, A_residual


def test_j0_vs_j1():
    """Compare directed structure at J⁰ (position writes) vs J¹ (transport)."""
    print("\n=== J⁰ vs J¹ directed structure ===\n")

    d = 8
    n_steps = 100
    n_seeds = 20

    j0_cyc = []
    j1_transport_cyc = []
    j1_residual_cyc = []

    for seed in range(n_seeds):
        np.random.seed(seed)
        foam = Foam(d=d, n=3, writing_rate=0.01)
        inputs = make_inputs(n_steps, d, seed=seed + 1000)

        # J⁰: accumulated write asymmetry
        A_j0 = accumulate_asymmetry(foam, inputs, mode='writing')
        W_j0 = directed_graph(A_j0)
        j0_cyc.append(cyclicity_3(W_j0))

        # J¹: transport and residual asymmetry (snapshot after all writes)
        A_transport, A_residual = transport_asymmetry(foam)
        W_transport = directed_graph(A_transport)
        W_residual = directed_graph(A_residual)
        j1_transport_cyc.append(cyclicity_3(W_transport))
        j1_residual_cyc.append(cyclicity_3(W_residual))

    print(f"  {'measure':>20s}  {'mean cyc':>8s}  {'std':>8s}  {'n_cyclic':>8s}")
    for name, data in [('J⁰ (ΔL writes)', j0_cyc),
                        ('J¹ (transport)', j1_transport_cyc),
                        ('J¹ (BCH residual)', j1_residual_cyc)]:
        m = np.mean(data)
        s = np.std(data)
        nc = sum(1 for x in data if x > 0.01)
        print(f"  {name:>20s}  {m:8.4f}  {s:8.4f}  {nc:>5d}/20")


def test_j1_three_dynamics():
    """Do the three dynamics look different at J¹?"""
    print("\n=== J¹ cyclicity under three dynamics ===\n")

    d = 8
    n_steps = 80
    n_seeds = 20

    results = {mode: {'transport': [], 'residual': []}
               for mode in ['writing', 'self', 'cross']}

    for seed in range(n_seeds):
        for mode in ['writing', 'self', 'cross']:
            np.random.seed(seed)
            foam = Foam(d=d, n=3, writing_rate=0.01)
            inputs = make_inputs(n_steps, d, seed=seed + 1000)

            # run through the dynamics
            for v in inputs:
                if mode == 'writing':
                    foam.measure(v)
                    alongside(v)
                elif mode == 'self':
                    readout = np.real(foam.readout(v))
                    readout = readout / (np.linalg.norm(readout) + 1e-12)
                    foam.measure(readout)
                    alongside(readout)
                elif mode == 'cross':
                    bases = foam.bases
                    for i in range(foam.n):
                        for j in range(foam.n):
                            if i == j:
                                continue
                            probe = np.real(bases[j][:, 0])
                            probe = probe / np.linalg.norm(probe)
                            foam.measure(probe)
                            alongside(probe)

            A_t, A_r = transport_asymmetry(foam)
            W_t = directed_graph(A_t)
            W_r = directed_graph(A_r)
            results[mode]['transport'].append(cyclicity_3(W_t))
            results[mode]['residual'].append(cyclicity_3(W_r))

    print(f"  {'mode':>10s}  {'transport':>10s}  {'residual':>10s}")
    for mode in ['writing', 'self', 'cross']:
        mt = np.mean(results[mode]['transport'])
        mr = np.mean(results[mode]['residual'])
        print(f"  {mode:>10s}  {mt:10.4f}  {mr:10.4f}")


if __name__ == '__main__':
    test_directed_structure()
    test_three_dynamics()
    test_cyclicity_evolution()
    test_j0_vs_j1()
    test_j1_three_dynamics()

    report()
    save()
