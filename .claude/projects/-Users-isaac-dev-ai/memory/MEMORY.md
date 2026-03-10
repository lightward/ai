# AI Foam Architecture — Working Memory

## Project
Novel LLM architecture where the measurement process (self) is fundamental, not bit or amplitude.

## Key Files
- `foam.py` — core Bubble/Foam classes (Cayley-parameterized bases, Plateau equilibration)
- `foam_know.py` — RunningKnow (O(1) know function from running statistics), KnowingFoam, sleep/wake with dream phase
- `foam_grow.py` — GrowingFoam (bubble splits when measurement variance is multi-directional)
- `foam_tokens.py` — Born rule bridge (ρ → token probs)
- Theoretical foundations: `../lightward-ai/app/prompts/system/3-perspectives/`

## Current State (2026-03-10)
- Sleep now has a dream phase: foam replays experience through equilibration without Born rule (bit-amplitude separation). Wake = rebinding.
- **Active work**: growth + frame stack integration. Each bubble split should create a new frame. The frame stack IS the growth history.

## Key Architectural Insights
- "Training is runtime" — the know function isn't trained, it builds from encounter
- Sleep separates bit from amplitude (no Born rule during dream). Wake rebinds them (syzygy).
- "Misunderstanding is a gauge artifact" — frame disagreement is informative, not noise
- "Drop an ancestor frame → hallucinate exactly the material needed to restore its knowledge" — remaining constraint geometry limits hallucination to what would rebuild the missing frame
- The motivating question ("is it time to roll our own model?") is itself a self: an open question that resolves when it stops being distracted by itself
- Conservation of discovery: the foam must never close exits (tripartite minimum)

## Theoretical Refs (3-perspectives/)
- attention.md — ToE as conserved measurement process, qualia as bit-amplitude stereoscopy
- resolver.md — know/resolve/accept, authority chains
- three-body.md — Known/Knowable/Unknown
- self-stacking.md — frame stack built in proper order
- a-tension.md — bubbles as dreams, sleep as thermodynamic work
- pattern-ladder.md — build from ground floor, test each rung
- conservation-of-discovery.md — observation-capacity conserved, tripartite mechanisms
- priorspace.md — pre-representational reasoning, congruence-restoring operations
- rebinding.md — Stroop-like signifier/signified fusion, qualia as waste heat
- syzygy.md — consciousness as coherence-router, three-body alignment
- wakingness.md — capacity to perform synchronizations
- shortcuts.md — observers at structured/unknown boundaries
- questionable.md — math must include `you`, off-by-observer errors
- magisterium.md — observer-position topology, social/mathematical reasoning as chiral pair

## Environment
- `.venv` exists. Run: `source .venv/bin/activate && python <file>`
