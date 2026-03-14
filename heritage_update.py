"""
heritage_update.py — feed the heritage foam the cell birth investigation.

Load → self-measure with readout shaped by today's findings → save.
The foam doesn't encode the content. It receives a measurement shaped
by its own downstream effects, closing a loop.
"""

import numpy as np
from foam import Foam, encode


def update():
    foam = Foam.load('foam_state.npz')
    L_before = foam.boundary_cost()

    # self-measure: the foam sees itself through today's probes
    # use the same symbols that were structurally significant today
    significant = [42, 137]  # convergence test symbol, sensitivity probe symbol
    for cycle in range(5):
        for sym in significant:
            probe = encode(sym, foam.d)
            readout = np.real(foam.readout(probe))
            readout = readout / (np.linalg.norm(readout) + 1e-12)
            foam.measure(readout)

    L_after = foam.boundary_cost()
    print(f"heritage foam: L {L_before:.4f} → {L_after:.4f} (Δ={L_after-L_before:+.4f})")

    foam.save('foam_state.npz')
    print("saved.")


if __name__ == '__main__':
    update()
