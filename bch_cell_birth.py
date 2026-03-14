"""
bch_cell_birth.py — can a foam manage its own degeneration by
instantiating a novel "unknown" bubble?

The settled foam (self-measured 200 steps) has low sensitivity.
Mutual measurement with a fresh foam doesn't help (session 10 finding).
But what about adding a new bubble to the foam itself?

Cell birth changes the topology:
- N increases (new Voronoi cell, new boundaries)
- Plateau target shifts (-1/(N-1) changes)
- New dissonance emerges from the existing equilibrium being disrupted
- No external input needed — the foam creates its own novelty

This is the "defocus epistemic fix" move: not measuring through
current bases harder, but adding capacity for dissonance by
forking awareness into a new measurement basis.
"""

import numpy as np
from scipy.linalg import logm
from foam import Foam, Bubble, encode, cayley, skew_hermitian, random_skew_hermitian


def sensitivity(foam, n_probe=50, seed=999):
    """Mean dissonance to random probes (without writing)."""
    np.random.seed(seed)
    total = 0.0
    for _ in range(n_probe):
        v = encode(np.random.randint(0, 256), foam.d)
        vc = v.astype(complex)
        bases = foam.bases
        m = [vc @ U for U in bases]
        j2 = foam._stabilize(m)
        total += np.mean([np.linalg.norm(j2[i] - m[i]) for i in range(foam.n)])
    return total / n_probe


def residual_summary(foam):
    """Quick residual geometry summary."""
    eff_ranks = []
    frobs = []
    for i in range(foam.n):
        try:
            log_T = logm(foam.bubbles[i].T)
        except:
            log_T = np.zeros_like(foam.bubbles[i].T)
        R = skew_hermitian(log_T + 2 * foam.bubbles[i].L)
        sv = np.linalg.svd(R, compute_uv=False)
        sv_n = (sv / (sv[0] + 1e-15)) ** 2
        sv_n = sv_n / (sv_n.sum() + 1e-15)
        eff_ranks.append(1.0 / (np.sum(sv_n ** 2) + 1e-15))
        frobs.append(np.linalg.norm(R))
    return np.mean(eff_ranks), np.mean(frobs)


def add_unknown_bubble(foam):
    """Add a fresh random bubble to the foam. Cell birth."""
    new_bubble = Bubble(foam.d)
    foam.bubbles.append(new_bubble)
    foam.n += 1
    return foam


def test_cell_birth(n_seeds=20, n_settle=200, n_post=50):
    """Settle a foam, then add an unknown bubble. Does sensitivity recover?

    Compare:
    1. settled foam (no treatment)
    2. settled + new bubble + continued measurement
    3. settled + continued self-measurement (control)
    4. settled + random input (control)
    """
    d = 8

    conditions = {
        'no_treatment': {'sens': [], 'L': []},
        'cell_birth': {'sens': [], 'L': []},
        'cell_birth_then_measure': {'sens': [], 'L': []},
        'more_self': {'sens': [], 'L': []},
        'random_input': {'sens': [], 'L': []},
    }

    for seed in range(n_seeds):
        # settle
        np.random.seed(seed)
        base = Foam(d=d, n=3, writing_rate=0.01)
        for step in range(n_settle):
            probe = encode(step % 256, d)
            readout = np.real(base.readout(probe))
            readout = readout / (np.linalg.norm(readout) + 1e-12)
            base.measure(readout)

        settled = [(b.L.copy(), b.T.copy()) for b in base.bubbles]
        settled_L = base.boundary_cost()

        for cond in conditions:
            foam = Foam(d=d, n=3, writing_rate=0.01)
            for i in range(3):
                foam.bubbles[i].L = settled[i][0].copy()
                foam.bubbles[i].T = settled[i][1].copy()

            if cond == 'no_treatment':
                pass

            elif cond == 'cell_birth':
                # just add the bubble, no further measurement
                np.random.seed(seed + 3000)
                add_unknown_bubble(foam)

            elif cond == 'cell_birth_then_measure':
                # add bubble, then let the foam process
                np.random.seed(seed + 3000)
                add_unknown_bubble(foam)
                for step in range(n_post):
                    foam.measure(encode(step % 256, d))

            elif cond == 'more_self':
                for step in range(n_post):
                    probe = encode(step % 256, d)
                    readout = np.real(foam.readout(probe))
                    readout = readout / (np.linalg.norm(readout) + 1e-12)
                    foam.measure(readout)

            elif cond == 'random_input':
                np.random.seed(seed + 7000)
                for step in range(n_post):
                    foam.measure(encode(np.random.randint(0, 256), d))

            conditions[cond]['sens'].append(sensitivity(foam))
            conditions[cond]['L'].append(foam.boundary_cost())

    print(f"=== cell birth vs controls ({n_seeds} seeds) ===\n")
    print(f"  settled foam: self-measured {n_settle} steps\n")
    print(f"  {'condition':>25s}  {'sensitivity':>12s}  {'L':>10s}")
    for cond, data in conditions.items():
        s = np.mean(data['sens'])
        L = np.mean(data['L'])
        print(f"  {cond:>25s}  {s:12.4f}  {L:10.4f}")


def test_cell_birth_trajectory(n_seeds=10, n_settle=200, n_post=100):
    """Track sensitivity over time after cell birth.
    Does the new bubble create sustained higher sensitivity?"""
    d = 8
    check_interval = 5
    n_checks = n_post // check_interval

    trajectories = {
        'cell_birth': np.zeros(n_checks),
        'no_birth': np.zeros(n_checks),
    }

    for seed in range(n_seeds):
        np.random.seed(seed)
        base = Foam(d=d, n=3, writing_rate=0.01)
        for step in range(n_settle):
            probe = encode(step % 256, d)
            readout = np.real(base.readout(probe))
            readout = readout / (np.linalg.norm(readout) + 1e-12)
            base.measure(readout)

        settled = [(b.L.copy(), b.T.copy()) for b in base.bubbles]

        # with cell birth
        foam_birth = Foam(d=d, n=3, writing_rate=0.01)
        for i in range(3):
            foam_birth.bubbles[i].L = settled[i][0].copy()
            foam_birth.bubbles[i].T = settled[i][1].copy()
        np.random.seed(seed + 3000)
        add_unknown_bubble(foam_birth)

        # without
        foam_no = Foam(d=d, n=3, writing_rate=0.01)
        for i in range(3):
            foam_no.bubbles[i].L = settled[i][0].copy()
            foam_no.bubbles[i].T = settled[i][1].copy()

        # feed same sequence to both
        np.random.seed(seed + 8000)
        for step in range(n_post):
            v = encode(np.random.randint(0, 256), d)
            foam_birth.measure(v)
            foam_no.measure(v)

            if (step + 1) % check_interval == 0:
                idx = step // check_interval
                trajectories['cell_birth'][idx] += sensitivity(foam_birth, n_probe=20, seed=idx)
                trajectories['no_birth'][idx] += sensitivity(foam_no, n_probe=20, seed=idx)

    for name in trajectories:
        trajectories[name] /= n_seeds

    print(f"\n=== cell birth sensitivity trajectory ({n_seeds} seeds) ===\n")
    print(f"  {'step':>5s}  {'with birth':>12s}  {'no birth':>12s}  {'ratio':>8s}")
    for idx in range(n_checks):
        step = (idx + 1) * check_interval
        b = trajectories['cell_birth'][idx]
        n = trajectories['no_birth'][idx]
        print(f"  {step:5d}  {b:12.6f}  {n:12.6f}  {b/n:8.4f}")


def test_cell_birth_residuals(n_seeds=20, n_settle=200, n_post=50):
    """Does cell birth change the BCH residual geometry of the
    ORIGINAL bubbles? Not the new bubble — the existing ones."""
    d = 8

    birth_data = {'eff_rank': [], 'frob': []}
    no_birth_data = {'eff_rank': [], 'frob': []}

    for seed in range(n_seeds):
        np.random.seed(seed)
        base = Foam(d=d, n=3, writing_rate=0.01)
        for step in range(n_settle):
            probe = encode(step % 256, d)
            readout = np.real(base.readout(probe))
            readout = readout / (np.linalg.norm(readout) + 1e-12)
            base.measure(readout)

        settled = [(b.L.copy(), b.T.copy()) for b in base.bubbles]

        for label, data, do_birth in [
            ('birth', birth_data, True),
            ('no_birth', no_birth_data, False),
        ]:
            foam = Foam(d=d, n=3, writing_rate=0.01)
            for i in range(3):
                foam.bubbles[i].L = settled[i][0].copy()
                foam.bubbles[i].T = settled[i][1].copy()

            init_Ls = [b.L.copy() for b in foam.bubbles]

            if do_birth:
                np.random.seed(seed + 3000)
                add_unknown_bubble(foam)

            np.random.seed(seed + 8000)
            for step in range(n_post):
                foam.measure(encode(np.random.randint(0, 256), d))

            # residuals of ORIGINAL 3 bubbles only
            for i in range(3):
                dL = foam.bubbles[i].L - init_Ls[i]
                try:
                    lT = logm(foam.bubbles[i].T)
                except:
                    lT = np.zeros((d, d), dtype=complex)
                R = skew_hermitian(lT + 2 * dL)
                sv = np.linalg.svd(R, compute_uv=False)
                sv_n = (sv / (sv[0] + 1e-15)) ** 2
                sv_n = sv_n / (sv_n.sum() + 1e-15)
                data['eff_rank'].append(1.0 / (np.sum(sv_n ** 2) + 1e-15))
                data['frob'].append(np.linalg.norm(R))

    print(f"\n=== original-bubble BCH residuals after cell birth ({n_seeds} seeds) ===\n")
    print(f"  {'':>15s}  {'eff_rank':>10s}  {'frob':>10s}")
    print(f"  {'with birth':>15s}  {np.mean(birth_data['eff_rank']):10.4f}  {np.mean(birth_data['frob']):10.4f}")
    print(f"  {'no birth':>15s}  {np.mean(no_birth_data['eff_rank']):10.4f}  {np.mean(no_birth_data['frob']):10.4f}")


if __name__ == '__main__':
    test_cell_birth()
    test_cell_birth_trajectory()
    test_cell_birth_residuals()
