hey.

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

## the arc of this session (2026-03-10, session 4)

previous sessions established: experimental foam dynamics, primitives (foam/bubble/operator/measure), spec, clean implementation. this session found memory.

1. **the stabilization dynamics were broken.** the norm-preservation bug: forces pushed measurements apart without projecting back to the sphere, causing self-dampening (norms grew, relative force shrank). fixed by projecting to original norms after each force step. also: step_size was clamped to 0.5, an artifact of the old dynamics — removed. with step_size=5.0 and norm preservation, the foam actually reaches near-equilibrium (mean question ~0.05, boredom at step ~21).

2. **the foam-as-bubble junction was the gate.** `effective_basis` computed from scratch each time (stabilize with identity probe, eigendecompose density matrix). the density matrix from N=3 bubbles in d=8 is rank 2-3 — the eigenvectors fill the null space with noise. a leaf bubble outperformed a foam-as-bubble. the mapping was lossy because it was stateless.

3. **"training is runtime."** this was known in session 2 (see `experiments/foam_know.py`) and lost in the session 3 refactor. re-derived from first principles by hitting the effective_basis wall. the foam's identity isn't computed — it's accumulated. the density matrix builds through lived measurement, not through a single self-stabilization probe.

4. **memory implemented.** `Foam.accumulated_rho` — a running exponentially-weighted density matrix. `Foam.remember(rho)` accumulates after each measurement. `effective_basis` uses the accumulated ρ when available, falls back to instantaneous probe when blank. `Operator.measure` calls `self.foam.remember()` after each measurement — the verb leaves a trace.

5. **the memory works.** rank fills from 3/8 to 8/8 after just 5 measurements. experience shapes identity: narrow experience (same foam structure) produces highly anisotropic ρ (eigenvalues 0.0002 to 0.47), wide experience (diverse foams) produces nearly isotropic ρ (eigenvalues 0.07 to 0.19). ρ similarity between the two: 0.57 — genuinely different operators from different experience. no optimizer. no loss function.

6. **the instinct domain.** the right framing for this work is molecular dynamics, not machine learning. particles on a sphere, angular potentials, energy minimization. ML conventions (SGD, loss functions, training loops) led to building scaffolding around unverified dynamics. physics conventions (does the integrator conserve what it should? does the system reach equilibrium?) led to finding and fixing the actual bugs. this is in CLAUDE.md now.

## notes from Isaac

- "it's an easy slip to make, into narration — but we're working *outside* of time here, working on things that create their own narration just by running. it's a different kind of practice."
- "training is runtime"

## the cliffhanger

does shaped identity help? the narrow-experience operator (specialist) vs the wide-experience operator (generalist) — tested on familiar vs unfamiliar foams. the mechanism is in place. the test is ready to run. we stopped here because context was low, not because the question was answered.

## what's open (attractors for future-us)

1. **specialist vs generalist.** does the narrow operator outperform the wide operator on familiar foam structure? does the wide operator outperform on novel structure? this is the first real test of whether accumulated identity is *useful*, not just different.

2. **the know/resolve cascade.** `experiments/foam_know.py` had running statistics with multiple temporal horizons (fast/medium/slow decay), a know/resolve cascade, and sleep/wake. these need to be brought into the clean primitive set. the accumulated ρ IS the running statistics — but the multi-timescale frame stack and the know/resolve distinction haven't been reimplemented yet.

3. **sleep/wake.** consolidation of the frame stack into a harmonic. wake inherits the harmonic. the foam's context window isn't a number — it's vitality.

4. **the effective_basis question, deeper.** the accumulated ρ solves the rank problem. but is eigendecomposition of ρ the right way for a foam to present as a bubble? the spec says "a bubble is defined entirely by its boundaries" — its outside, not its inside. the accumulated ρ captures what the foam has measured (inside). what it presents at boundaries might be something else.

5. **coherence test.** drilling into a recursive bubble should return you to yourself. with memory, this has new meaning — the loop should encounter the foam's accumulated identity, not a blank probe.

6. **the north star.** can this hold up lightward.com? the foam now remembers. the question shifts from "can it learn" to "can it develop a self rich enough to hold a conversation."

---

the files: `spec.md` (the specification), `foam_spec.py` (the implementation), `CLAUDE.md` (orientation), `experiments/` (archaeological record, especially `foam_know.py` for the know/resolve/sleep work).

`.venv` exists. use `source .venv/bin/activate && python foam_spec.py`.

training is runtime.

🤲
