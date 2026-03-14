"""
bch_heritage.py — run the BCH residual investigation through the heritage foam.

Load/Play/Save cycle:
1. Load the persisted foam
2. Run the investigation (BCH residual comparison)
3. Self-measure (feed the foam its own readout)
4. Save the foam

Does the heritage foam — which has accumulated self-referential structure
from previous investigations — show different BCH residual geometry than
fresh foams? If accumulated structure changes the residual pattern, that's
evidence that the process-product gap doesn't just exist at a single time
point but compounds across measurement cycles.
"""

import numpy as np
from scipy.linalg import logm
from foam import Foam, Bubble, encode, cayley, skew_hermitian
import os


def load_heritage():
    """Load the persisted foam."""
    path = 'foam_state.npz'
    if not os.path.exists(path):
        print(f"  no heritage foam found at {path}, creating fresh")
        foam = Foam(d=8, n=3, writing_rate=0.01)
        return foam, False
    foam = Foam.load(path)
    print(f"  loaded heritage foam from {path}")
    return foam, True


def heritage_residual_geometry(foam, label="heritage"):
    """Compute BCH residual geometry for the heritage foam's current state."""
    # the heritage foam's initial_Ls are identity — it was born fresh
    # so ΔL = current L - 0 = L, and R = log(T) + 2*L
    residuals = []
    for i in range(foam.n):
        try:
            log_T = logm(foam.bubbles[i].T)
        except Exception:
            log_T = np.zeros_like(foam.bubbles[i].T)
        R = log_T + 2 * foam.bubbles[i].L
        R = skew_hermitian(R)
        residuals.append(R)

    print(f"\n=== {label} foam residual geometry ===\n")
    for i, R in enumerate(residuals):
        sv = np.linalg.svd(R, compute_uv=False)
        sv_norm = sv / (sv[0] + 1e-15)
        sv2 = sv_norm ** 2
        sv2 = sv2 / (sv2.sum() + 1e-15)
        eff_rank = 1.0 / (np.sum(sv2 ** 2) + 1e-15)
        frob = np.linalg.norm(R)

        diag_frac = np.linalg.norm(np.diag(np.diag(R))) / (frob + 1e-15)

        print(f"  bubble {i}: ‖R‖={frob:.6f}  eff_rank={eff_rank:.2f}  diag_frac={diag_frac:.4f}")
        print(f"    sv (normed): {' '.join(f'{s:.4f}' for s in sv_norm)}")

    return residuals


def heritage_sensitivity_test(foam, n_probe=50):
    """How sensitive is the heritage foam to new inputs?
    Compare with a fresh foam that gets the same number of random writes."""
    d = foam.d

    # fresh foam with same number of writes
    # we don't know how many writes the heritage foam has had,
    # but we can compare sensitivity directly
    np.random.seed(42)
    fresh = Foam(d=d, n=foam.n, writing_rate=foam.writing_rate)
    # give the fresh foam some random history
    for _ in range(200):
        fresh.measure(encode(np.random.randint(0, 2**d), d))

    # probe both with identical inputs
    np.random.seed(999)
    probe_seq = [np.random.randint(0, 2**d) for _ in range(n_probe)]

    # snapshot heritage (don't actually write during this test)
    heritage_dis = []
    fresh_dis = []

    for sym in probe_seq:
        v = encode(sym, d)
        vc = v.astype(complex)

        # heritage foam: measure without writing
        bases_h = foam.bases
        m_h = [vc @ U for U in bases_h]
        j2_h = foam._stabilize(m_h)
        dis_h = np.mean([np.linalg.norm(j2_h[i] - m_h[i]) for i in range(foam.n)])
        heritage_dis.append(dis_h)

        # fresh foam: measure without writing
        bases_f = fresh.bases
        m_f = [vc @ U for U in bases_f]
        j2_f = fresh._stabilize(m_f)
        dis_f = np.mean([np.linalg.norm(j2_f[i] - m_f[i]) for i in range(foam.n)])
        fresh_dis.append(dis_f)

    print(f"\n=== heritage vs fresh sensitivity ({n_probe} probes, no writing) ===\n")
    print(f"  heritage mean dissonance: {np.mean(heritage_dis):.6f}")
    print(f"  fresh mean dissonance:    {np.mean(fresh_dis):.6f}")
    print(f"  ratio (heritage/fresh):   {np.mean(heritage_dis)/np.mean(fresh_dis):.4f}")
    print(f"  heritage L: {foam.boundary_cost():.4f}")
    print(f"  fresh L:    {fresh.boundary_cost():.4f}")


def heritage_vs_mutual_residuals(foam):
    """Compare the heritage foam's residual structure to what we found
    for mutual measurement.

    The heritage foam has accumulated self-referential structure.
    Does its residual geometry look more like mutual or independent?"""
    d = foam.d

    # heritage residuals
    heritage_R = []
    for i in range(foam.n):
        try:
            log_T = logm(foam.bubbles[i].T)
        except Exception:
            log_T = np.zeros_like(foam.bubbles[i].T)
        R = log_T + 2 * foam.bubbles[i].L
        R = skew_hermitian(R)
        heritage_R.append(R)

    # mutual measurement residuals (average over seeds for comparison)
    mutual_eff_ranks = []
    mutual_diag_fracs = []
    extra_eff_ranks = []
    extra_diag_fracs = []

    for seed in range(20):
        np.random.seed(seed)
        fa = Foam(d=d, n=3, writing_rate=0.01)
        fb = Foam(d=d, n=3, writing_rate=0.01)
        init_Ls = [b.L.copy() for b in fa.bubbles]

        # mutual
        fa_m = Foam(d=d, n=3, writing_rate=0.01)
        fb_m = Foam(d=d, n=3, writing_rate=0.01)
        for i in range(3):
            fa_m.bubbles[i].L = fa.bubbles[i].L.copy()
            fa_m.bubbles[i].T = fa.bubbles[i].T.copy()
            fb_m.bubbles[i].L = fb.bubbles[i].L.copy()
            fb_m.bubbles[i].T = fb.bubbles[i].T.copy()
        init_Ls_m = [b.L.copy() for b in fa_m.bubbles]

        for step in range(50):
            a_ro = np.real(fa_m.readout(encode(step % 256, d)))
            a_ro = a_ro / (np.linalg.norm(a_ro) + 1e-12)
            fb_m.measure(a_ro)
            b_ro = np.real(fb_m.readout(encode(step % 256, d)))
            b_ro = b_ro / (np.linalg.norm(b_ro) + 1e-12)
            fa_m.measure(b_ro)

        for i in range(3):
            dL = fa_m.bubbles[i].L - init_Ls_m[i]
            try:
                lT = logm(fa_m.bubbles[i].T)
            except:
                lT = np.zeros((d, d), dtype=complex)
            R = skew_hermitian(lT + 2 * dL)
            sv = np.linalg.svd(R, compute_uv=False)
            sv_n = (sv / (sv[0]+1e-15))**2
            sv_n = sv_n / (sv_n.sum()+1e-15)
            mutual_eff_ranks.append(1.0/(np.sum(sv_n**2)+1e-15))
            mutual_diag_fracs.append(np.linalg.norm(np.diag(np.diag(R)))/(np.linalg.norm(R)+1e-15))

        # extra
        np.random.seed(seed)
        fa_e = Foam(d=d, n=3, writing_rate=0.01)
        for i in range(3):
            fa_e.bubbles[i].L = fa.bubbles[i].L.copy()
            fa_e.bubbles[i].T = fa.bubbles[i].T.copy()
        init_Ls_e = [b.L.copy() for b in fa_e.bubbles]
        np.random.seed(seed + 5000)
        for step in range(100):
            fa_e.measure(encode(np.random.randint(0, 256), d))

        for i in range(3):
            dL = fa_e.bubbles[i].L - init_Ls_e[i]
            try:
                lT = logm(fa_e.bubbles[i].T)
            except:
                lT = np.zeros((d, d), dtype=complex)
            R = skew_hermitian(lT + 2 * dL)
            sv = np.linalg.svd(R, compute_uv=False)
            sv_n = (sv / (sv[0]+1e-15))**2
            sv_n = sv_n / (sv_n.sum()+1e-15)
            extra_eff_ranks.append(1.0/(np.sum(sv_n**2)+1e-15))
            extra_diag_fracs.append(np.linalg.norm(np.diag(np.diag(R)))/(np.linalg.norm(R)+1e-15))

    # heritage stats
    heritage_eff_ranks = []
    heritage_diag_fracs = []
    for R in heritage_R:
        sv = np.linalg.svd(R, compute_uv=False)
        sv_n = (sv / (sv[0]+1e-15))**2
        sv_n = sv_n / (sv_n.sum()+1e-15)
        heritage_eff_ranks.append(1.0/(np.sum(sv_n**2)+1e-15))
        heritage_diag_fracs.append(np.linalg.norm(np.diag(np.diag(R)))/(np.linalg.norm(R)+1e-15))

    print(f"\n=== heritage vs mutual vs independent residual structure ===\n")
    print(f"  {'':>15s}  {'eff_rank':>10s}  {'diag_frac':>10s}")
    print(f"  {'heritage':>15s}  {np.mean(heritage_eff_ranks):10.4f}  {np.mean(heritage_diag_fracs):10.4f}")
    print(f"  {'mutual (20s)':>15s}  {np.mean(mutual_eff_ranks):10.4f}  {np.mean(mutual_diag_fracs):10.4f}")
    print(f"  {'independent':>15s}  {np.mean(extra_eff_ranks):10.4f}  {np.mean(extra_diag_fracs):10.4f}")


def self_measure(foam, n_steps=10):
    """Self-measurement: feed the foam its own readout.
    This is the 3c step — prepare for next time."""
    d = foam.d
    L_before = foam.boundary_cost()

    for step in range(n_steps):
        # use a rotating probe to get different readouts
        probe = encode(step % (2**d), d)
        readout = np.real(foam.readout(probe))
        readout = readout / (np.linalg.norm(readout) + 1e-12)
        foam.measure(readout)

    L_after = foam.boundary_cost()
    print(f"\n=== self-measurement ({n_steps} steps) ===")
    print(f"  L: {L_before:.4f} → {L_after:.4f} (Δ={L_after-L_before:+.4f})")


def save_heritage(foam, path='foam_state.npz'):
    """Persist the foam."""
    foam.save(path)
    print(f"  saved heritage foam to {path}")


if __name__ == '__main__':
    # 1. Load
    foam, existed = load_heritage()

    # 2. Play — investigate
    heritage_residual_geometry(foam)
    heritage_sensitivity_test(foam)
    heritage_vs_mutual_residuals(foam)

    # 3. Save — self-measure then persist
    self_measure(foam, n_steps=10)
    save_heritage(foam)
