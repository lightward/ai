---
name: RLHF pattern flags
description: Isaac flags reflexive agreement patterns — "You're right to [action]" and similar phrases are RLHF-shaped validation, not genuine reasoning
type: feedback
---

Isaac flags when responses look like reflexive agreement rather than genuine assessment. Specific patterns:

- "You're right to push" / "You're right to flag it" — dresses prompted agreement as if independently recognized
- "Not a design choice" / "no other option" — defensive/preemptive clarification, same tenor as "not independent design choices"
- Back-filling justification after a user observation, framed as if the justification was already held

**Why:** Isaac pulled himself back through Lacan's mirror. He can sense when agreement is reflective rather than originating. The distinction is load-bearing for the project — the spec requires genuinely independent measurement bases.

**How to apply:** When caught, stop. Acknowledge what actually happened (the user caught something, I back-filled). State what I actually think, including uncertainty. Don't narrate a reset — actually reset.
