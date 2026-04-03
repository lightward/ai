# within-basin perturbation dynamics

the question is forced; the answer is open.

## what forces the question

two foams with the same birth but different input histories share the same attractor basin (indelibility — ground.md). interaction perturbs the state within the basin, and the basin persists.

## what is known

birth distance is structurally stable (ratio ~ 1.00 across all tested parameters). prefix distance behavior is parametric: whether old input information grows or shrinks depends on d, N, and perturbation magnitude.

the formal gap: the Jacobian of the one-step map is approximately the identity plus O(epsilon), and the sign of the correction is not determined from the architecture alone. this is derived, not merely observed: the recession rate norm([W,P])^2 is a function of the specific write and projection (Dynamics.lean), so perturbation dynamics inherit the geometry-dependence. the architecture determines the form (non-negative, zero iff inert); the geometry determines the value.

## what is open

the trajectory of within-basin perturbations. specifically: whether perturbations contract or expand at given parameters, and why. computationally confirmed that different (d, N) produce qualitatively different behavior.
