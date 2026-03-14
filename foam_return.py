"""
foam_return.py — the Eckmann-Tlusty return mechanism in the foam.

The paper: walks in SO(3)/SU(2) return home when doubled and scaled.
The foam: T ≈ exp(-2ΔL). The transport IS the doubled-and-negated walk.
cayley(L) @ T composes position with its doubled inverse.

Questions:
1. Does cayley(L) @ T actually tend toward something?
   (Not identity — toward a FIXED POINT of the composed dynamics.)
2. Is the return mechanism what makes the self-tracking foam converge faster?
3. What's the "home" that the foam returns to?
"""

import numpy as np
from scipy.linalg import logm, expm
from foam_self import Foam, Bubble, skew_hermitian, cayley, enforce_skew_hermitian, encode


def return_test(seed=0):
    """
    Track the effective basis cayley(L) @ T.
    If the Eckmann-Tlusty mechanism is operating, the effective basis
    should tend toward identity (or some fixed point) faster than
    cayley(L) alone.
    """
    np.random.seed(seed)
    foam = Foam(d=8, n=3, writing_rate=0.01)

    print("  === distance from identity ===")
    print("  step  |U-I|    |T-I|    |UT-I|   |U|/|T|   L")

    for step in range(100):
        foam.measure(encode(np.random.randint(0, 256), 8))

        if step % 10 == 0:
            b = foam.bubbles[0]
            U = cayley(b.L)
            T = b.T
            UT = U @ T  # effective basis

            I = np.eye(8, dtype=complex)
            d_U = np.linalg.norm(U - I)
            d_T = np.linalg.norm(T - I)
            d_UT = np.linalg.norm(UT - I)

            print(f"  {step:4d}  {d_U:.4f}  {d_T:.4f}  {d_UT:.4f}  {d_U/d_T:.4f}   {foam.boundary_cost():.4f}")


def walk_and_double(seed=0):
    """
    Explicit test of the Eckmann-Tlusty mechanism.
    Take the sequence of writes as a walk in U(d).
    Traverse it once: product of cayley(ΔL_i).
    Traverse it twice with scaling: does it return?
    """
    np.random.seed(seed)
    foam = Foam(d=8, n=3, writing_rate=0.01)

    # collect the incremental writes
    deltas = []

    for step in range(50):
        # manually capture the writes
        v = encode(np.random.randint(0, 256), 8).astype(complex)
        bases = foam.bases
        m = [v @ U for U in bases]
        j0 = [mi.copy() for mi in m]
        j2 = foam._stabilize(m)
        dissonance = [j2[i] - j0[i] for i in range(foam.n)]

        step_deltas = []
        for i in range(foam.n):
            d_i = dissonance[i]
            m_i = j0[i]
            d_norm = np.linalg.norm(d_i)
            m_norm = np.linalg.norm(m_i)
            if d_norm < 1e-12 or m_norm < 1e-12:
                step_deltas.append(np.zeros((8, 8), dtype=complex))
                continue
            d_hat = d_i / d_norm
            m_hat = m_i / m_norm
            delta_L = foam.writing_rate * (
                np.outer(d_hat, m_hat.conj()) - np.outer(m_hat, d_hat.conj())
            ) * d_norm
            step_deltas.append(delta_L)

            # actually apply the write
            foam.bubbles[i].L = enforce_skew_hermitian(foam.bubbles[i].L + delta_L)
            foam.bubbles[i].T = foam.bubbles[i].T @ cayley(delta_L)

        deltas.append(step_deltas)

    # now test the return mechanism on bubble 0's walk
    print("  === Eckmann-Tlusty test on the foam's walk ===")

    walk_deltas = [d[0] for d in deltas]  # bubble 0's incremental writes

    # single traversal: product of cayley(ΔL_i)
    single = np.eye(8, dtype=complex)
    for dL in walk_deltas:
        single = single @ cayley(dL)

    # double traversal: product twice
    double = single @ single

    # double traversal with scaling: scale each ΔL by some factor, traverse twice
    I = np.eye(8, dtype=complex)
    print(f"\n  single traversal |W - I| = {np.linalg.norm(single - I):.4f}")
    print(f"  double traversal |W² - I| = {np.linalg.norm(double - I):.4f}")

    for scale in [0.5, 0.7, 0.8, 0.9, 1.0, 1.1]:
        scaled_product = np.eye(8, dtype=complex)
        for dL in walk_deltas:
            scaled_product = scaled_product @ cayley(dL * scale)
        doubled_scaled = scaled_product @ scaled_product
        print(f"  scale={scale:.1f}: |W_s² - I| = {np.linalg.norm(doubled_scaled - I):.4f}")

    # the foam's own version: T ≈ product of cayley(ΔL_i)
    # which is the single traversal. The effective basis is U @ T.
    # U ≈ cayley(Σ ΔL_i) ≈ the walk's endpoint in the Lie algebra.
    # T = the walk's product in the group.
    # U @ T = cayley(Σ ΔL_i) @ Π cayley(ΔL_i).
    # This is NOT exactly the doubled walk, but it's structurally related.

    b = foam.bubbles[0]
    U = cayley(b.L)
    T = b.T
    UT = U @ T

    print(f"\n  foam's effective basis:")
    print(f"  |U - I| = {np.linalg.norm(U - I):.4f}")
    print(f"  |T - I| = {np.linalg.norm(T - I):.4f}")
    print(f"  |U@T - I| = {np.linalg.norm(UT - I):.4f}")


def wave_particle_switch(seed=0):
    """
    Wave mode: feed repeated symbol, let foam stabilize.
    Particle mode: feed a burst of different symbols.
    Wave mode again: feed the original symbol.

    Track: does the foam find a new equilibrium that's coherent
    with the particle burst but different from the original wave?
    """
    np.random.seed(seed)
    foam = Foam(d=8, n=3, writing_rate=0.01)

    symbol_a = 42

    print("  === wave → particle → wave ===")
    print("  phase      step  L        |d|      phase_0   basis_cos_to_initial")

    v_a = encode(symbol_a, 8)

    # wave mode: establish equilibrium with symbol A
    initial_basis = None
    for step in range(40):
        result = foam.measure(v_a)
        if step == 0:
            initial_basis = foam.bubbles[0].basis.copy()

        if step % 10 == 0:
            dis = np.mean([np.linalg.norm(d) for d in result['dissonance']])
            phase = foam.bubbles[0].transport_phase
            cos = abs(np.trace(initial_basis.conj().T @ foam.bubbles[0].basis)) / 8
            print(f"  wave-1     {step:4d}  {result['L']:.4f}  {dis:.4f}  {phase:+.4f}   {cos:.4f}")

    pre_particle_basis = foam.bubbles[0].basis.copy()
    pre_particle_L = foam.boundary_cost()

    # particle mode: burst of different symbols
    print("  ---particle burst---")
    for step in range(10):
        s = np.random.randint(0, 256)
        result = foam.measure(encode(s, 8))
        dis = np.mean([np.linalg.norm(d) for d in result['dissonance']])
        phase = foam.bubbles[0].transport_phase
        cos_initial = abs(np.trace(initial_basis.conj().T @ foam.bubbles[0].basis)) / 8
        cos_pre = abs(np.trace(pre_particle_basis.conj().T @ foam.bubbles[0].basis)) / 8
        print(f"  particle   {40+step:4d}  {result['L']:.4f}  {dis:.4f}  {phase:+.4f}   {cos_initial:.4f}  (vs pre-particle: {cos_pre:.4f})")

    post_particle_basis = foam.bubbles[0].basis.copy()

    # wave mode again: same symbol A
    print("  ---resume wave---")
    for step in range(40):
        result = foam.measure(v_a)

        if step % 5 == 0:
            dis = np.mean([np.linalg.norm(d) for d in result['dissonance']])
            phase = foam.bubbles[0].transport_phase
            cos_initial = abs(np.trace(initial_basis.conj().T @ foam.bubbles[0].basis)) / 8
            cos_pre = abs(np.trace(pre_particle_basis.conj().T @ foam.bubbles[0].basis)) / 8
            cos_post = abs(np.trace(post_particle_basis.conj().T @ foam.bubbles[0].basis)) / 8
            print(f"  wave-2     {50+step:4d}  {result['L']:.4f}  {dis:.4f}  {phase:+.4f}   init={cos_initial:.4f}  pre={cos_pre:.4f}  post={cos_post:.4f}")


def retrodictive_coherence(seed=0):
    """
    After wave→particle→wave, is the new equilibrium retrodictively
    coherent? Meaning: does the foam in wave-2 respond to probes
    as if the particle burst was a natural part of its history?

    Test: compare probe responses of the post-switch foam to
    a foam that received the full sequence naturally (wave+particle+wave)
    vs a foam that received only wave-1 + wave-2 (no particle burst).
    """
    np.random.seed(seed)

    # foam A: wave → particle → wave (the actual path)
    foam_a = Foam(d=8, n=3, writing_rate=0.01)
    np.random.seed(42)
    init = [skew_hermitian(8) * 0.1 for _ in range(3)]
    for i in range(3):
        foam_a.bubbles[i].L = init[i].copy()
        foam_a.bubbles[i].T = np.eye(8, dtype=complex)

    for _ in range(40): foam_a.measure(encode(42, 8))     # wave 1
    for _ in range(10): foam_a.measure(encode(np.random.randint(0, 256), 8))  # particle
    for _ in range(40): foam_a.measure(encode(42, 8))     # wave 2

    # foam B: wave only (no particle burst, same total measurements of symbol 42)
    foam_b = Foam(d=8, n=3, writing_rate=0.01)
    for i in range(3):
        foam_b.bubbles[i].L = init[i].copy()
        foam_b.bubbles[i].T = np.eye(8, dtype=complex)

    for _ in range(80): foam_b.measure(encode(42, 8))     # wave only

    # probe both
    print("  === retrodictive coherence ===")
    print("  does the post-switch foam look like it had a natural history?")

    diffs = []
    for s in range(64):
        v = encode(s, 8)
        # no-write probes
        foam_a_probe = Foam(d=8, n=3, writing_rate=0.0)
        foam_b_probe = Foam(d=8, n=3, writing_rate=0.0)
        for i in range(3):
            foam_a_probe.bubbles[i].L = foam_a.bubbles[i].L.copy()
            foam_a_probe.bubbles[i].T = foam_a.bubbles[i].T.copy()
            foam_b_probe.bubbles[i].L = foam_b.bubbles[i].L.copy()
            foam_b_probe.bubbles[i].T = foam_b.bubbles[i].T.copy()

        ra = foam_a_probe.measure(v)
        rb = foam_b_probe.measure(v)

        j2_a = np.concatenate(ra['j2'])
        j2_b = np.concatenate(rb['j2'])
        diffs.append(np.linalg.norm(j2_a - j2_b))

    print(f"  probe response difference (wave+particle+wave vs wave-only):")
    print(f"    mean = {np.mean(diffs):.6f}")
    print(f"    max  = {np.max(diffs):.6f}")

    # now: does the post-switch foam's state make "retrodictive sense"?
    # check: is its L-T relationship still coherent (log(T) ≈ -2ΔL)?
    for label, foam in [("wave+particle+wave", foam_a), ("wave-only", foam_b)]:
        b = foam.bubbles[0]
        delta_L = b.L - init[0]
        try:
            log_T = logm(b.T)
            ratio = np.linalg.norm(log_T) / (np.linalg.norm(delta_L) + 1e-12)
            residual = np.linalg.norm(log_T + 2 * delta_L) / (np.linalg.norm(log_T) + 1e-12)
        except:
            ratio = float('nan')
            residual = float('nan')

        print(f"\n  {label}:")
        print(f"    |ΔL| = {np.linalg.norm(delta_L):.4f}  |logT| = {np.linalg.norm(log_T):.4f}  ratio = {ratio:.3f}  residual = {residual:.4f}")


if __name__ == '__main__':
    print("=== return test ===")
    return_test()

    print("\n=== Eckmann-Tlusty walk test ===")
    walk_and_double()

    print("\n=== wave → particle → wave ===")
    wave_particle_switch()

    print("\n=== retrodictive coherence ===")
    retrodictive_coherence()
