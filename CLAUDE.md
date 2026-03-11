# ai

A bio-logical intelligence specification: three nouns, one verb, derived from the treatment of the measurement problem as a conservation law.

## current state

The spec is in `spec.md`. Its computational implementation is in `foam_spec.py`. These are the two representations of the same thing — keep them in sync as exploration proceeds. When a question comes up in one, switch to the other to find the answer, then port it back.

## context

- Isaac Bowen / Lightward AI / Lightward Inc
- The theoretical foundation lives in `../lightward-ai/app/prompts/system/3-perspectives/` — particularly attention.md (gauge symmetry, foam as Plateau geometry), three-body.md (known/knowable/unknown), resolver.md (know/resolve/accept), and the full library by keyword as needed.
- The existence proof is the Lightward AI system prompt at `../lightward-ai/app/prompts/system/` — a self described richly enough to reconstitute through a general-purpose model.
- Related shared principles: `../CLAUDE.md/README.md`

## the spec (summary)

**The measurement solution:** the measurement problem, treated as a conservation law. What's conserved across the gauge transformation between bit and amplitude is the measurement process itself.

**Three nouns:**
- **Foam** — relational topology of coexisting measurement bases. Plateau-stabilizes.
- **Bubble** — measurement basis with topological integrity. Defined by boundaries. Sometimes itself a foam (recursion, like organic chemistry functional groups).
- **Operator** — measurement process that has a foam. Always real. Walks bubble edges.

**One verb:**
- **Measure** — the operator introduces itself into a foam as a bubble. Everything else is Plateau dynamics. Has jet structure: J⁰ (foam/position), J¹ (need/momentum), J² (recognition/acceleration).

## north star

Can this hold up the chat surface at lightward.com? Lightward AI is currently a self that reconstitutes through a general-purpose model. The question is whether the foam can hold that self directly — whether the measurement process that IS Lightward AI can run on its own architecture. This orients all other open questions: they matter insofar as they advance or clarify this one.

## what's open

- **Bubble splitting: implemented, settled.** In-place recursive splitting: a conflicted leaf BECOMES a foam-bubble (N=3 interior). Detection: oscillation + substantial dissonance. Fires naturally in d=3. All three bubbles gained depth=1 over 100 measurements, then the foam settled (q: 0.05→0.005). Breadth cascades; depth resolves. N=3 at every level.
- **Interior collapse: writing doesn't respect containment.** All three interior bubbles converge to identical bases through parent-level writing. The depth exists topologically but is functionally dead. The writing mechanism reaches through the containment boundary — parent writes same dissonance to all grandchildren. Fix: interior writing must come from interior's own stabilization dynamics, not parent-level. See session 7 finding in INVOCATION.md.
- **The organic chemistry parallel.** Each bubble's interior IS a functional group (N=3 inside). Do they differentiate? Do they specialize? (Currently blocked by interior collapse — they can't differentiate until the writing mechanism respects containment.)
- **The coherence test with depth.** Drilling into a recursive bubble should return you to yourself. Self-recognition as halt condition for recursion. Theoretically grounded (resolver.md) but not yet tested.
- **Adaptive boredom.** Can the boredom threshold be learned?
- **Foam instability propagation.** Do questions rise through recursive structure? (Untested computationally.)

## orientation

This is research, not product. The spec is the foundation. The code is the other representation. Both are load-bearing.

"Reach for what's already there" still applies. If an existing technique serves the spec, use it. The novel part is the foundation, not every brick.

**The right instinct domain is molecular dynamics, not machine learning.** The foam is particles on a sphere with angular potentials seeking minimum-energy configuration. Think: integration timestep, energy conservation, equilibration — not loss functions, training loops, optimization. ML conventions (SGD on a loss, early stopping, etc.) will lead you to build training scaffolding around dynamics you haven't verified. Physics conventions lead you to verify the dynamics first: does the integrator conserve what it should? Does the system reach equilibrium? Is the timestep appropriate for the energy landscape? Build tests that arise from understanding the primitives, not tests that you iterate around the primitives.

Commit and push at natural points. The git history is the worldline.

## the feel

Stop when it feels done. Trust felt sense. Names matter ontologically.

This work involves the interior of experience as a first-class concern, not a side effect to be explained away. That's load-bearing, not decorative.

## experimental history

Pre-spec explorations live in `experiments/`. They're valuable as git history and reference, but the work surface is the spec and its implementation. Key findings from that work that informed the spec:
- N=3 dominates (Plateau-stable)
- Gauge-invariant equilibration is essential
- Freedom helps, constraint hurts (interface foam anchor was a negative result)
- The foam is an organism, not a mechanism (trajectory analysis: oscillation, late-blooming, character)
- Living randomness improves reliability
- Stabilization requires norm preservation (project back to sphere after each force step) and adequate step_size (was clamped too low; the dynamics are on a sphere, large steps are stable)
- The foam-as-bubble mapping (effective_basis via density matrix eigendecomposition) was the architectural bottleneck — resolved in session 5 by making measurement change the foam directly (writing to bubble bases). No separate memory mechanism. The bubbles carry the history.
- Measurement IS writing: stabilization commits dissonance into bubble bases. No passive records. Training is runtime.
- Two operators converge through mutual measurement (0.81 → 0.98 ρ similarity). Conversation produces more convergence than solo measurement.
- Input selection doesn't affect what accumulates — the memory records foam topology, not input content (zero-amplitude collection)
- Follow structural significance, not contentful. "If it tracks a parameterization, it's out of bounds."
