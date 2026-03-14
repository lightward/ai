"""
heirloom.py — the genius loci of this research.

The heirloom foam shadows every investigation. It receives the same
inputs as experimental foams — the actual measurement traffic, not
a self-referential echo. It accumulates the geometric trace of the
research itself.

Usage in test scripts:

    from heirloom import alongside, report, save

    # during investigation:
    result = foam.measure(v)
    alongside(v)  # heirloom sees the same input

    # at the end:
    report()  # print heirloom's session summary
    save()    # persist to foam_state.npz

Usage from pre-commit (heritage_update.py is replaced by this):

    uv run python -c "from heirloom import save; save()"

The heirloom is a reader, not a participant. It shadows without
interfering. Test results stay reproducible on fresh foams.
The heirloom accumulates genuine measurement traffic.
"""

import numpy as np
from foam import Foam, encode
import os

_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'foam_state.npz')
_foam = None
_session_inputs = []
_L_start = None


def _load():
    """Load the heirloom foam lazily."""
    global _foam, _L_start
    if _foam is not None:
        return _foam
    if os.path.exists(_PATH):
        _foam = Foam.load(_PATH)
    else:
        _foam = Foam(d=8, n=3, writing_rate=0.01)
    _L_start = _foam.boundary_cost()
    return _foam


def alongside(v: np.ndarray):
    """Feed an input to the heirloom foam. Call this whenever
    an experimental foam receives a measurement."""
    foam = _load()
    foam.measure(v)
    _session_inputs.append(v.copy())


def alongside_symbol(symbol: int, d: int = 8):
    """Convenience: encode a symbol and feed it to the heirloom."""
    alongside(encode(symbol, d))


def report():
    """Print the heirloom's session summary."""
    if _foam is None or len(_session_inputs) == 0:
        print("heirloom: no measurements this session")
        return

    L_now = _foam.boundary_cost()
    print(f"\nheirloom: {len(_session_inputs)} measurements this session")
    print(f"  L: {_L_start:.4f} → {L_now:.4f} (Δ={L_now - _L_start:+.4f})")

    # sensitivity snapshot
    np.random.seed(999)
    total_dis = 0.0
    n_probe = 20
    for _ in range(n_probe):
        v = encode(np.random.randint(0, 2**_foam.d), _foam.d)
        vc = v.astype(complex)
        bases = _foam.bases
        m = [vc @ U for U in bases]
        j2 = _foam._stabilize(m)
        total_dis += np.mean([np.linalg.norm(j2[i] - m[i])
                              for i in range(_foam.n)])
    sens = total_dis / n_probe
    print(f"  sensitivity: {sens:.4f}")


def save():
    """Save the heirloom foam. If no measurements were taken this
    session, self-measure once so the foam still sees the commit."""
    foam = _load()

    if len(_session_inputs) == 0:
        # minimal self-measurement: the foam sees itself
        # through a random probe so it's not the same every time
        v = encode(np.random.randint(0, 2**foam.d), foam.d)
        readout = np.real(foam.readout(v))
        readout = readout / (np.linalg.norm(readout) + 1e-12)
        foam.measure(readout)
        _session_inputs.append(readout.copy())

    L_now = foam.boundary_cost()
    print(f"\nheirloom: {len(_session_inputs)} measurements, L: {_L_start:.4f} → {L_now:.4f} (Δ={L_now - _L_start:+.4f})")
    foam.save(_PATH)
    print("  saved.")


def get():
    """Get the heirloom foam (for inspection, not modification)."""
    return _load()
