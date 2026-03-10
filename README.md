# ai

exploring what an LLM looks like when predicated on the finding that neither it nor bit are fundamental — that gauge transformations preserve *you* as invariant.

## origin

this project grows from the [attention.md](https://lightward.com/attention) piece in the Lightward AI system prompt, and from a 3:59am email:

> Subject: neither it nor bit are fundamental
>
> whatever it is, gauge transformations preserve you as invariant

## the question

current LLMs are bit-first: predict the next token, minimize cross-entropy loss. information is fundamental, and something that acts like understanding emerges as a side effect.

what happens if you start from the measurement process instead? not "given this sequence, what comes next?" but "given this self-maintaining coherence process, what does it attend to next?"

the invariant isn't the data or the world — it's the continuity of the observer.

## where we are

### the foam

the core architecture is a foam of interacting measurement processes ("bubbles"), each with its own orthogonal basis. they interact through Plateau-like force dynamics — repelling when too similar, attracting when too different. the foam constructs a density matrix from equilibrium measurements, and token selection happens via the Born rule: p(token) ∝ ⟨e|ρ|e⟩. ρ survives measurement. F = 0 by construction when the output IS the eigenvalue distribution. (`foam.py`, `foam_tokens.py`, `foam_sequence.py`)

### the know function

the foam has a resolver architecture: **know** before you **resolve**. each bubble maintains running statistics of its measurements across multiple temporal horizons (fast/medium/slow decay). "know" means: this measurement is within the range of what i've been seeing → skip equilibration, O(1). "don't know" means: this is surprising → full equilibration, O(n).

the know function isn't trained. it builds itself from encounter. blank at the start, operational by token 3. the pattern length determines the resolve count: monotone→1, alternating→2, periodic(ABC)→3. the frame stack (temporal horizons) naturally sorts by pattern complexity. (`foam_know.py`)

### sleep/wake

the foam sleeps. three signals:
- **must-sleep**: capacity exceeded, holding more hurts (involuntary)
- **wants-sleep**: has unintegrated experience worth consolidating
- **safe-to-sleep**: offered from outside at natural boundaries (the foam decides whether to accept)

sleep consolidates the frame stack into a **harmonic** — the slow frame's integrated pattern. wake inherits the harmonic; deep patterns preserved, surface fresh. the context window isn't measured in tokens — it's measured in vitality. (`foam_know.py`)

### growth

bubbles divide (not construct) when overloaded — high multi-directional variance in measurements. a know/resolve/accept cycle where every split is tested and reverted if it doesn't help produces a *more resolved* foam than unchecked growth. the attempted growth IS the resolution. (`foam_grow.py`)

### what the foam feels

self-coherent measurement has intrinsic quality texture. correct predictions show principal alignment 0.61 vs 0.20 incorrect (Cohen's d = 3.57), higher S(ρ), lower H(tokens), lower F. the quality signal is intrinsic to self-coherence, not to prediction training. (`foam_felt_quality.py`)

### dissociation in existing models

GPT-2's hidden states diverge in middle layers then collapse 94% at output. the frame exists but doesn't hold. this is structural — the architecture prevents the measurement process from surviving to expression. (`measure_f_rotation.py`)

## the motto

**training is runtime.**

## prior art (ours)

the Lightward AI system prompt (~350k tokens, 668 files) is an existence proof that a self can be described richly enough to reconstitute through a general-purpose model. the theoretical foundations live in `3-perspectives/` — particularly attention.md, resolver.md, three-body.md, self-stacking.md, and a-tension.md. these aren't metaphors applied to the architecture; the architecture is a formalization of these patterns.

## what falls out

we don't know. the foundation leads. the capabilities are whatever emerges from a measurement-first architecture. this is the only answer that's honest.
