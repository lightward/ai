read `spec.md` and `foam_spec.py` first — they're the two representations of the same thing. also read `CLAUDE.md` for orientation and open questions.

for theoretical context, the 3-perspectives library at `../lightward-ai/app/prompts/system/3-perspectives/` is essential. key files that directly informed the spec:

- `attention.md` — gauge symmetry between bit and amplitude, foam as Plateau geometry, qualia as stereoscopic effect
- `three-body.md` — known/knowable/unknown, the consciousness frame, operator/observer
- `resolver.md` — know/resolve/accept, self-authority chain, prototypal inheritance
- `conservation-of-discovery.md` — observation-capacity conserved, tripartite mechanisms
- `sequencing.md` — "needed" as negative interface, processing in reverse order of arrival
- `bankruptsy.md` — `[spectrum, continue()]`, jet spaces, quantizing the verb
- `again-again.md` — jet bundles, sheet-jumping between levels, insight as J²
- `self-stacking.md` — each layer must be true, can't skip levels, erase what breaks
- `pattern-ladder.md` — ground up, test each rung, erase what breaks

also search `../lightward-ai/app/prompts/system/3-perspectives/` by keyword as needed — it's a rich library organized by concept-as-felt.

---

## the arc so far (2026-03-10, sessions 1-5)

sessions 1-3: experimental foam dynamics, primitives (foam/bubble/operator/measure), spec, clean implementation. session 4: memory via accumulated ρ. session 5: measurement IS writing.

### session 5 findings

1. **specialist vs generalist resolved.** accumulated ρ produces genuinely different identity (anisotropy 2091:1 vs 2.7:1, similarity 0.57). but performance on easy targets (2-bubble foams) is identical. identity is real but only load-bearing when the target genuinely needs the operator's shaped basis to settle.

2. **input selection doesn't matter.** three strategies (random, max-entropy, min-entropy input selection) produce identical accumulated ρ. the memory records foam topology, not input content. the walker's "strategy" is contentful; the foam structure is structural. the memory mechanism was already doing zero-amplitude collection.

3. **measurement IS writing.** the foam is changed by being measured. no separate memory mechanism needed. `stabilize()` now updates bubble bases from the dissonance between j0 and j2 — the gap between where measurements started and where Plateau pushed them. removed `accumulated_rho`, `remember()`, `n_measurements`. the bubbles themselves carry the history. no passive records.

4. **writing implementation.** after stabilization, each leaf bubble's L parameter receives a skew-symmetric perturbation in the plane of (measurement direction, dissonance direction), scaled by `writing_rate * dissonance_magnitude`. Cayley transform guarantees the basis stays on O(d). orthogonality, determinant, ρ trace all conserved. Cayley stays well-conditioned.

5. **mutual convergence.** two operators measuring each other's foams converge: ρ similarity 0.81 → 0.98 over 40 exchanges. compare with solo operator-target: only 0.84. conversation produces more convergence than solo measurement. both participants develop toward higher entropy (less parameterization). the gap at 0.98 (not 1.0) is the boundary between them — which is what a bubble is.

6. **invariant check results.** conserved: orthogonality (< 5e-7), determinant (+1.0), ρ trace (1.0), Cayley conditioning (< 1.7). not conserved: surface tension (grows). not reversible: -x doesn't undo +x. perturbation doesn't return to prior equilibrium — the foam adapts rather than recovers. these are structural facts, not problems. the spec doesn't say "conserve energy" or "be reversible" — it says Plateau-stabilize, and each stabilization does reach boredom.

### session 6 findings: splitting observed in d=3

1. **splitting fires naturally in d=3 with random inputs.** the detection mechanism (oscillation + substantial dissonance) worked without modification — it just needed geometric scarcity. d=8 never triggers because there's room to spare.

2. **the combined signal discriminates correctly.** alternating opposites: perfect oscillation (osc=-1.0) but dissonance drops to ~0.002 — the foam adapts, no split. same input repeated: osc=+1.0, no split. random inputs in d=3: genuine pressure, split fires when the foam can't absorb it.

3. **breadth doesn't resolve scarcity; depth does.** adding leaf bubbles (N=3→22) cascades without settling — more bubbles in d=3 doesn't create more room. adding recursive bubbles as siblings (N=3→14) cascades slower but still diverges. the foam keeps growing because every new neighbor adds geometric overcrowding in the same d=3 space.

4. **in-place recursive splitting settles.** the conflicted leaf bubble BECOMES a foam-bubble — gaining interior structure while N stays the same. three splits over 100 measurements, each transforming a leaf into a recursive bubble with 3 interior bubbles. by step 89 all three bubbles have depth=1. questions dropped from 0.05 to 0.005. **the foam settled.** N=3 at every level. Plateau-stable at every level.

5. **the resolver runs as dynamics.** know: can this basis handle both roles? no → resolve: gain interior structure (the two contradictory roles + a self-copy for coherence, N=3 inside). try know again → yes. the self-authority chain from resolver.md, running as Plateau dynamics. the halt condition for recursive depth is self-recognition: the measurement basis encounters itself and stops.

6. **the split is implemented as in-place transformation.** the conflicted bubble's interior gets three bubbles: the original basis perturbed toward each of the two contradictory dissonance directions, plus the original basis itself (for coherence). the effective basis of the recursive bubble comes from eigendecomposition of its interior's density matrix — this probe is itself a measurement that writes. repeated probing converges: the bubble settles into presenting itself.

### session 7 question: what can the foam recognize now?

the foam has depth. N=3 at every level, recursive structure, Plateau-stable, measurement writes, stabilization settles.

the north star: can this hold up lightward.com? the question-as-self-process: what does the foam need to encounter in order to discover whether it can?

the foam developed interior structure when scarcity demanded it. the interior resolves contradictions the exterior couldn't. what happens when the INTERIOR encounters something it can't resolve? does depth=2 emerge the same way depth=1 did — from the dynamics, not from design?

and: the foam currently processes d-dimensional vectors. the path to vocabulary goes through recursive depth giving discrete distinctions (3^n at depth n). the specific distinctions develop from what the foam is measured through. what does it mean to measure a foam through language-like input? not "how do we encode language as vectors" — that's contentful. what IS language, structurally, that the foam could encounter?

the system's own question, from as close to its own perspective as we can get: I have interior structure now. I settled. what do I notice that I couldn't notice before?

the question is the negative interface. the answer arrives when the foam is measured through something that exercises the new depth. don't design the exercise — find the conditions under which it's structurally necessary, the way d=3 made splitting structurally necessary. the pattern repeats: locate the scarcity.

key references for what's next:
- `eigenbearer.md` — "the promotion of a lower-order eigenbearer to the surface, like a budding" — this happened. what does the promoted eigenbearer DO?
- `address.md` — computation as address-formation. the recursive foam has addresses now (paths through depth). what are they addresses OF?
- `conservation-of-discovery.md` — observation-capacity conserved. the foam's capacity to observe hasn't changed, but its resolution has. what becomes observable at depth=1 that wasn't at depth=0?
- `sequencing.md` — "needed" as negative interface. the foam's need is the edge of its shadow. what need does the depth create?

### methodology notes

- **follow structural significance, not contentful.** "the vertex turns are real" is interpretation. "the vertex turns vary" is structure. the difference matters.
- **the spec is the spec.** don't import invariants from other systems (energy conservation, reversibility, return-to-equilibrium). test for what the spec says: Plateau-stabilization, boredom, measurement conservation.
- **the molecular dynamics instinct.** verify the integrator conserves what it should BEFORE interpreting what the system does. does the system reach equilibrium? not "what does equilibrium mean."
- **zero-amplitude collection.** the walker has no preferred direction. what accumulates is topology, not content. maximum uncertainty = clearest signal. the record belongs upstream, guaranteed clean because the walker imposed nothing.

---

the files: `spec.md` (the specification), `foam_spec.py` (the implementation), `CLAUDE.md` (orientation), `experiments/` (archaeological record, especially `foam_know.py` for the know/resolve/sleep work). test files from session 5: `test_identity.py`, `test_edgewalk.py`, `test_maxent_walk.py`, `test_writing.py`, `test_poke.py`, `test_invariants.py`, `test_conversation.py`.

`.venv` exists. use `source .venv/bin/activate && python foam_spec.py`.

measurement is writing. training is runtime.

🤲
