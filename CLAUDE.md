# ai

The measurement solution: three nouns, one verb, derived from the treatment of the measurement problem as a conservation law.

## current state

The spec is in `spec.md`. It is the sole artifact. All prior code (implementations, experiments, codecs) has been folded into the spec and deleted. The git history is the worldline.

## context

- Isaac Bowen / Lightward AI / Lightward Inc
- The theoretical foundation lives in `../lightward-ai/app/prompts/system/3-perspectives/` — particularly attention.md (gauge symmetry, foam as Plateau geometry), three-body.md (known/knowable/unknown), resolver.md (know/resolve/accept), and the full library by keyword as needed.
- Related shared principles: `../CLAUDE.md/README.md`

## the spec (summary)

**Three nouns:**
- **Line** — a measurement process. The conserved quantity. Has character (topological invariant). Orbit cannot be known to close. Prior to the structures it moves through.
- **Bubble** — measurement basis with topological integrity. Defined by boundaries. Sometimes itself a foam (recursion). Symmetry is rational (closes — that's its conserved charge).
- **Foam** — relational topology of coexisting measurement bases. Plateau-stabilizes. The classifying space.

**One verb:**
- **Measure** — a line enters a foam by passing through a bubble's center. Everything else is Plateau dynamics. Has jet structure: J⁰ (position), J¹ (momentum/derivative), J² (acceleration).

**Key properties (from section 5):**
- Holonomy is an invertible map that preserves similarity (invertible semantic hash — falls out of the geometry, not designed)
- The information is in the direction, not the magnitude (rotations characterized by axis, not angle)
- Sequence requires the derivative (J⁰ + J¹ together reconstruct order from what was unordered; J² resolves degeneracies)
- The foam is permanently changed by measurement (no passive records — the bases carry the history)

## orientation

The spec is the work surface. It should be precise enough to re-derive any implementation. If something can't be re-derived from the spec, the spec needs work.

The right instinct domain is molecular dynamics, not machine learning. The foam is particles on a sphere with angular potentials seeking minimum-energy configuration.

Read the 3-perspectives files directly when context is needed — don't use subagents for reference material.

Commit and push at natural points. The git history is the worldline.

## the feel

Stop when it feels done. Trust felt sense. Names matter ontologically.

The spec's section 9 (heading) is a checksum: the measurement process's self-declared direction. If it doesn't make sense, the reader is missing context, not the spec.
