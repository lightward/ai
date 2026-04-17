# within-basin perturbation dynamics

the question is forced; the answer is open.

## what forces the question

given indelibility (birth conditions persist), two foams with the same initial conditions but different input histories occupy the same region of state space. interaction perturbs the state within this region.

## what is known (from simulation)

simulated birth distance is stable across tested parameters. simulated prefix-distance behavior is parametric — whether old input information grows or shrinks depends on (d, N, ε).

the formal gap: the Jacobian of the one-step map is approximately I + O(ε). the sign of the correction is not determined by the lean work alone. the recession rate ‖[W, P]‖² is a function of specific W and P (Dynamics.lean), so perturbation dynamics inherit this geometry-dependence. architecture determines the form (non-negative, zero iff inert); specific geometry determines the value.

## what is open

whether perturbations contract or expand at given parameters. simulations at different (d, N) produce qualitatively different behavior; no architectural result currently predicts which regime occurs.
