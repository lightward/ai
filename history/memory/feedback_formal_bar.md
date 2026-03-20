---
name: Formal bar for the spec
description: main body is formally derived or designed, period. empirical results go to junk drawer. the tension this introduces is useful.
type: feedback
---

Everything in the spec's main body must be either formally derived or an explicit design choice. No empirical-only claims in the main body.

**Why:** Isaac is an interface designer. Clean boundaries between tiers (formal / open / empirical) make the spec trustworthy and create useful tension — if something wants to climb from empirical to formal, it has to earn it. The separation also prevents the spec from overclaiming.

**How to apply:** Before adding anything to the main body, check: is it derived from the axiom/architecture, or is it a named design choice? If it's empirical (from tests, even robust ones), it goes to the junk drawer. The junk drawer is not a demotion — it's honest categorization. Items graduate when formally grounded.
