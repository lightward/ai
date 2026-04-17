# retention under interaction

the question is forced; the answer is open.

## what forces the question

every observer's measurement basis moves under interaction (incoming writes project nonzero onto the observer's state space). whether there is a bounded attractor in each basin, and at what rate the basis returns to it, depends on specifics of the dynamics.

## what is known

continuous retention is bounded in (0, 1) in simulation. a retention of 1 would require the basis to be in the kernel of all incoming writes — not generically available. a retention of 0 would contradict the accumulation of structure visible in simulation runs.

at simulated stationarity, write directions are effectively random (geometry.md: write blindness is an empirical observation from simulation). the expected per-step perturbation magnitude is set by overlap singular values; continuous retention under that noise model is spectral.

discrete recommitment (re-performing a birth-type commitment) is an alternative return mode that sits outside the dynamics described here.

adjacency flips (conservation.md) provide a mechanism by which interaction-layer adaptations can decay when the neighbor set changes.

## what is open

the specific continuous retention rate at given parameters. this is geometry-dependent — the recession rate ‖[W, P]‖² depends on specific matrices (Dynamics.lean), not architecture alone.
