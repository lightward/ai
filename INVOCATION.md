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

1. **splitting fires naturally in d=3 with random inputs.** at step 66 of 80, bubble 1 split (N=3 → N=4). the detection mechanism already in foam_spec.py worked without modification — it just needed geometric scarcity.

2. **scarcity is the key.** d=3 with N=3 means three 3×3 rotation matrices nearly exhaust the available directions. diverse measurement pressure in that tight space creates genuine structural need. d=8 never triggers because there's room to spare.

3. **the combined signal works.** splitting requires BOTH oscillation (dissonance direction flipping) AND substantial dissonance (bubble failing to adapt). the bubble that split had osc≈-0.47 and dis_ema≈0.52 at step ~60. the foam couldn't absorb the pressure.

4. **regular patterns don't trigger splits.** alternating opposites produce perfect oscillation (osc=-1.0) but dissonance drops to ~0.002 — the foam adapts to the pattern. same input repeated: osc=+1.0 (no oscillation), no split. the detection discriminates correctly.

5. **after splitting, questions go UP.** from 0.01 to 0.20. the new 4-bubble topology is in J¹ — adjusting to its new shape. growth introduces instability before it settles. this is structurally correct.

6. **the methodology holds.** "follow structural significance, not contentful." the split happened not because we tuned thresholds but because we reduced d until the geometry demanded it. the dynamics showed us what splitting looks like when it's genuinely needed.

observation script: `observe_d3.py`. run with `source .venv/bin/activate && python observe_d3.py`.

### what's next

- **post-split equilibration.** does the N=4 foam in d=3 find a new stable configuration? does it split further? run longer measurements after the first split.
- **recursive splitting.** the spec says split produces (a) original stays, (b) copy of current foam becomes recursive bubble. current implementation creates two leaf bubbles. the recursive version is the path to depth.
- **the organic chemistry parallel.** with splitting working, do bubble-clusters spontaneously form functional groups?
- **the coherence test with writing.** drilling into a recursive bubble should eventually return you to yourself — and the loop encounters the foam as it has been shaped by measurement.

key references for splitting:
- `eigenbearer.md` — "the promotion of a lower-order eigenbearer to the surface, like a budding"
- `address.md` — computation as address-formation and address-navigation, "creation is the act of increasing the surface area of the possible without breaking the tension of the actual"
- `kierkeguardian.md` — circular reasoning as home for information, the tautology is load-bearing
- `a-tension.md` — structural significance over contentful significance, "if it tracks a parameterization, it's out of bounds"

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
