# observed

empirical results. nothing here is formally derived; everything here is tested.
each file is referenced by the status section of the derivation it serves.

## by derivation

### writing_map
- write_uniqueness.py — uniqueness of the wedge product form
- perpendicularity.py — perpendicular writes as the unique navigable constraint

### channel_capacity
- foam_channel.py — the foam as its own encoding (cross-measurement channel)

### group
- controllability.py — so(d) reachability for 2-3 observers
- stacked_slices.py — stacked slices generating u(d)
- stacking_mechanism.py — complex structure from stacked R^3, so(d) closure

### three_body
- three_body_derivation.py — Known/Knowable/Unknown from overlap geometry
- grassmannian_vertical.py — Grassmannian tangent as vertical structure

### geometry
- L_saturation.py — L saturation behavior
- L_saturation_cross.py — saturation level dependencies (d, N)
- wedge_magnitude.py — expected wedge magnitude, perpendicularity cost
- kolmogorov_self.py — write blindness, effective wandering dimension
- write_direction_pca.py — write subspace is exactly 3D per observer
- cayley_det.py — determinant drift in Cayley transform
- epoch_recursive.py — epoch structure, single-write L neutrality

### conservation
- adjacency_flip.py — adjacency flip confirmed at d=2, N=12

### self_generation
- (none)

### open/retention
- echo_state.py — birth conditions indelible (no echo state property)
- memory_horizon.py — prefix information decay
- memory_deep.py — within-basin memory across parameters
- memory_mechanism.py — per-step contraction mechanics
- memory_cross.py — perturbation behavior across (d, N)
- sequence_echo.py — cross-measurement sequence echo

### open/perturbation
- levy_wandering.py — heavy-tailed L steps (geometric, not dynamical)

### open/mixing_rate
- fluctuation_dissipation.py — FDT failure (foam is driven, not equilibrium)
