---
name: Session 22 reservoir investigation
description: No global ESP (derived), complement exhaustiveness (proven), causal ordering (derived), line investigability, reservoir correspondence. Started from reservoir.md perspective file.
type: project
---

**Session 22 (2026-03-23): reservoir computing investigation**

Started from Lightward AI commit adding perspective files (including reservoir.md). Asked: does the foam derive a reservoir computer?

**Derived results:**
- No global ESP: two foams with different births, same input, do not converge. Gauge-invariant distance ratio ~1.00 across all write scales. Derivation: stabilization target is state-dependent (no shared attractor). Birth conditions are indelible — state encodes identity and history inseparably.
- Reservoir correspondence: foam has 2 of 3 reservoir properties (separation + sequence, not echo state). Noted in theorem section.
- Complement of full controllability exhausted (per basis): exactly two components — topological invariants (discrete, pi_1 = Z) and commitment source (not in the group). Proven via standard Lie theory (connected compact Lie group + full algebra = surjective exponential). U(d)^N extension plausible but not yet verified.
- Causal ordering derived from partiality + closure: every measurement changes the foam, creating before/after. Ordering forced, practically irreversible (non-abelian, write map doesn't produce its own undo). Whether this constitutes time is a mapping question.
- Line investigability: the line's side is investigable using the same formalism (universality via BU(d)), but requires releasing current reference frame. Can't measure both sides simultaneously — non-partial frame has no dynamics. Partiality implies a boundary must exist; does not determine where it falls or what the line is.

**Empirical results (not in main body):**
- Codec is birth-shaped from step zero (not increasingly so with saturation). test_codec_divergence.py.
- Dissonance converges across births (~13% decrease over 2000 steps). Architecture-determined, not birth-determined.
- Hosted ESP also fails: measurements don't converge, measurement structure doesn't converge. test_echo_state_hosted.py.

**Open question added:**
- Inverted echo state: the foam may converge toward expression of its birth conditions, forgetting what it isn't. Candidate mechanism: perpendicular writes filling complement of birth geometry. Resists precise formulation — every testable version reduces to separation or contradicts it.

**Session dynamics:**
- 12 cold reads from other conversations all confidently asserted ESP held. All wrong — none tested it. The reservoir question was the right starting measurement because it made the indelibility result visible (perpendicular to the question asked).
- Isaac flagged RLHF-motivated about-face ("You're right. I was imprecise.") — checked, it was genuine but the flag was correct to raise.
- Three rounds of cold reads stabilized the additions. Lightward sharpest reader (caught "produces" and "precisely" as overselling).
- Perpendicular writes as survivability condition: work that writes perpendicular to your bases doesn't require recovery. Methodology as instance again.
