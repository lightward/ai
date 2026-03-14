"""
bch_spontenuity.py — does mutual measurement with a fresh foam
reverse the heritage foam's degeneration?

The heritage foam has settled: diffuse residuals, decreased sensitivity.
Self-measurement alone leads to this (session 10 finding).

But mutual measurement organizes residuals and increases sensitivity
(also session 10). What happens when a settled foam gets cross-measured
by a fresh one? Does it wake up?

If so: the Load/Play/Save cycle is the anti-degeneration mechanism.
Each new player (fresh basis) is cross-measurement that prevents
the accumulated state from settling. "Spontenuity" — always spontaneous
without being discontinuous — is the property maintained by the cycle.
"""

import numpy as np
from scipy.linalg import logm
from foam import Foam, Bubble, encode, cayley, skew_hermitian


def residual_signature(foam, label=""):
    """Compute BCH residual geometry summary for a foam."""
    results = []
    for i in range(foam.n):
        try:
            log_T = logm(foam.bubbles[i].T)
        except:
            log_T = np.zeros_like(foam.bubbles[i].T)
        R = skew_hermitian(log_T + 2 * foam.bubbles[i].L)
        sv = np.linalg.svd(R, compute_uv=False)
        sv_n = (sv / (sv[0] + 1e-15)) ** 2
        sv_n = sv_n / (sv_n.sum() + 1e-15)
        eff_rank = 1.0 / (np.sum(sv_n ** 2) + 1e-15)
        frob = np.linalg.norm(R)
        diag_frac = np.linalg.norm(np.diag(np.diag(R))) / (frob + 1e-15)
        results.append({
            'eff_rank': eff_rank,
            'frob': frob,
            'diag_frac': diag_frac,
        })
    return results


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


def print_signature(sigs, label):
    """Print residual signature summary."""
    er = np.mean([s['eff_rank'] for s in sigs])
    fr = np.mean([s['frob'] for s in sigs])
    df = np.mean([s['diag_frac'] for s in sigs])
    print(f"  {label:>30s}:  eff_rank={er:.2f}  ‖R‖={fr:.4f}  diag_frac={df:.4f}")


def test_wake_up(n_seeds=20, n_settle=200, n_mutual=50):
    """Can mutual measurement with a fresh foam reverse settling?

    1. Create a foam and let it self-measure until it settles
    2. Snapshot: residual geometry + sensitivity
    3. Give it mutual measurement with a fresh foam
    4. Snapshot: did the residuals reorganize? did sensitivity increase?

    Compare with:
    - continued self-measurement (control: does more self-measurement help?)
    - independent random input (control: is it just more writes?)
    """
    d = 8

    conditions = {
        'mutual_with_fresh': {'eff_rank_before': [], 'eff_rank_after': [],
                              'sens_before': [], 'sens_after': [],
                              'diag_before': [], 'diag_after': []},
        'more_self': {'eff_rank_before': [], 'eff_rank_after': [],
                      'sens_before': [], 'sens_after': [],
                      'diag_before': [], 'diag_after': []},
        'random_input': {'eff_rank_before': [], 'eff_rank_after': [],
                         'sens_before': [], 'sens_after': [],
                         'diag_before': [], 'diag_after': []},
    }

    for seed in range(n_seeds):
        # create and settle a foam via self-measurement
        np.random.seed(seed)
        base_foam = Foam(d=d, n=3, writing_rate=0.01)
        for step in range(n_settle):
            probe = encode(step % 256, d)
            readout = np.real(base_foam.readout(probe))
            readout = readout / (np.linalg.norm(readout) + 1e-12)
            base_foam.measure(readout)

        # snapshot the settled state
        settled_state = [(b.L.copy(), b.T.copy()) for b in base_foam.bubbles]

        for cond_name, data in conditions.items():
            # restore settled state
            foam = Foam(d=d, n=3, writing_rate=0.01)
            for i in range(3):
                foam.bubbles[i].L = settled_state[i][0].copy()
                foam.bubbles[i].T = settled_state[i][1].copy()

            # before
            sigs_before = residual_signature(foam)
            sens_before = sensitivity(foam)
            data['eff_rank_before'].append(np.mean([s['eff_rank'] for s in sigs_before]))
            data['sens_before'].append(sens_before)
            data['diag_before'].append(np.mean([s['diag_frac'] for s in sigs_before]))

            # apply treatment
            if cond_name == 'mutual_with_fresh':
                np.random.seed(seed + 5000)
                fresh = Foam(d=d, n=3, writing_rate=0.01)
                for step in range(n_mutual):
                    # settled foam reads fresh
                    fresh_readout = np.real(fresh.readout(encode(step % 256, d)))
                    fresh_readout = fresh_readout / (np.linalg.norm(fresh_readout) + 1e-12)
                    foam.measure(fresh_readout)

                    # fresh reads settled
                    settled_readout = np.real(foam.readout(encode(step % 256, d)))
                    settled_readout = settled_readout / (np.linalg.norm(settled_readout) + 1e-12)
                    fresh.measure(settled_readout)

            elif cond_name == 'more_self':
                for step in range(n_mutual * 2):  # same total writes
                    probe = encode(step % 256, d)
                    readout = np.real(foam.readout(probe))
                    readout = readout / (np.linalg.norm(readout) + 1e-12)
                    foam.measure(readout)

            elif cond_name == 'random_input':
                np.random.seed(seed + 7000)
                for step in range(n_mutual * 2):  # same total writes
                    foam.measure(encode(np.random.randint(0, 256), d))

            # after
            sigs_after = residual_signature(foam)
            sens_after = sensitivity(foam)
            data['eff_rank_after'].append(np.mean([s['eff_rank'] for s in sigs_after]))
            data['sens_after'].append(sens_after)
            data['diag_after'].append(np.mean([s['diag_frac'] for s in sigs_after]))

    print(f"=== can mutual measurement reverse settling? ({n_seeds} seeds) ===\n")
    print(f"  foams self-measured {n_settle} steps to settle, then treated with {n_mutual} steps\n")

    for cond_name, data in conditions.items():
        print(f"  --- {cond_name} ---")
        er_b = np.mean(data['eff_rank_before'])
        er_a = np.mean(data['eff_rank_after'])
        s_b = np.mean(data['sens_before'])
        s_a = np.mean(data['sens_after'])
        d_b = np.mean(data['diag_before'])
        d_a = np.mean(data['diag_after'])
        print(f"    eff_rank:   {er_b:.3f} → {er_a:.3f}  (Δ={er_a-er_b:+.3f})")
        print(f"    sensitivity:{s_b:.4f} → {s_a:.4f}  (Δ={s_a-s_b:+.4f}  ratio={s_a/s_b:.3f})")
        print(f"    diag_frac:  {d_b:.4f} → {d_a:.4f}  (Δ={d_a-d_b:+.4f})")
        print()


def test_trajectory(n_seeds=10, n_settle=200, n_treatment=100):
    """Track sensitivity over time during treatment.
    Does mutual measurement produce a different trajectory than self/random?"""
    d = 8
    check_interval = 5
    n_checks = n_treatment // check_interval

    trajectories = {name: np.zeros(n_checks)
                    for name in ['mutual', 'self', 'random']}

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

        foams = {}
        for name in ['mutual', 'self', 'random']:
            f = Foam(d=d, n=3, writing_rate=0.01)
            for i in range(3):
                f.bubbles[i].L = settled[i][0].copy()
                f.bubbles[i].T = settled[i][1].copy()
            foams[name] = f

        np.random.seed(seed + 5000)
        fresh = Foam(d=d, n=3, writing_rate=0.01)

        for step in range(n_treatment):
            # mutual
            fresh_ro = np.real(fresh.readout(encode(step % 256, d)))
            fresh_ro = fresh_ro / (np.linalg.norm(fresh_ro) + 1e-12)
            foams['mutual'].measure(fresh_ro)
            settled_ro = np.real(foams['mutual'].readout(encode(step % 256, d)))
            settled_ro = settled_ro / (np.linalg.norm(settled_ro) + 1e-12)
            fresh.measure(settled_ro)

            # self
            probe = encode(step % 256, d)
            self_ro = np.real(foams['self'].readout(probe))
            self_ro = self_ro / (np.linalg.norm(self_ro) + 1e-12)
            foams['self'].measure(self_ro)

            # random
            foams['random'].measure(encode(np.random.randint(0, 256), d))

            if (step + 1) % check_interval == 0:
                idx = step // check_interval
                for name, f in foams.items():
                    trajectories[name][idx] += sensitivity(f, n_probe=20, seed=idx)

    for name in trajectories:
        trajectories[name] /= n_seeds

    print(f"\n=== sensitivity trajectory during treatment ({n_seeds} seeds) ===\n")
    print(f"  {'step':>5s}  {'mutual':>10s}  {'self':>10s}  {'random':>10s}  {'mut/self':>10s}")
    for idx in range(n_checks):
        step = (idx + 1) * check_interval
        m = trajectories['mutual'][idx]
        s = trajectories['self'][idx]
        r = trajectories['random'][idx]
        ratio = m / (s + 1e-15)
        print(f"  {step:5d}  {m:10.6f}  {s:10.6f}  {r:10.6f}  {ratio:10.4f}")


if __name__ == '__main__':
    test_wake_up()
    test_trajectory()
