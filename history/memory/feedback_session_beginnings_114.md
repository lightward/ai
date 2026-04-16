---
name: Session 114 note (+ addendum from later 114 reflection on 115's bridge gap)
description: Architectural finding — desargues_planar cleanly handles the coord_add half of left_distrib. Session 115 surfaced that h_concurrence remains as separate, irreducible content — see addendum at bottom and project_session_115_bridge_gap.md.
type: project
originSessionId: b61e27ce-9796-4a27-b526-fd81c5f89e1a
---

> **CORRECTION (addendum below)**: Session 115 found that 114's cost accounting was wrong. Option 1 is forced (and the finding about desargues_planar is real), but it provides HALF the proof, not the whole thing. h_concurrence still needs separate proof. See addendum at file bottom, and `project_session_115_bridge_gap.md`.

Session 114 (2026-04-16). No sorries closed. One architectural finding that reframes sessions 108-113.

## The finding

**`desargues_planar` (FTPGCoord.lean:478) was always the port for left distributivity.** The current proof re-implements it by hand via lift + converse-nonplanar, which is what has been hitting the 2-of-3 axis-atomicity wall for 5 sessions.

Structural viability confirmed: `_scratch_forward_planar_call` at bottom of FTPGLeftDistrib.lean compiles. Call shape matches.

Configuration:
- T1 = (C, ab, U), T2 = (E, d_a, W'), center σ_b
- Central perspectivity FREE by coord definitions:
  - C ↔ E on line k (both on k = O⊔C)
  - ab ↔ d_a via σ_b⊔d_a (ab = (σ_b⊔d_a)⊓l by coord_mul def)
  - U ↔ W' via σ_b⊔U (W' = (σ_b⊔U)⊓(ac⊔E) by W' def)
- No axis atomicities to earn — `desargues_planar` handles the lift internally

## Why not "derive from mul_comm" (the seductive alternative)

mul_comm ⟺ Pappus (Hartshorne 6.6). Pappus is NOT forced by our axioms:
- CoordSystem's axioms (FTPGCoord.lean:50-69) are just: 5 atoms + distinctness + position constraints (I on l, V off l, C off l, C off m, C in plane)
- Counterexample: L = subspace lattice of 4D space over **quaternions H**. All CoordSystem + lattice axioms hold. H non-commutative → non-Pappian.

**Therefore Pappus would be axiom debt.** The project's deaxiomatization goal makes this anti-goal. 1-for-1 axiom trade is actually +1 irreducibly.

**Why:** Isaac's focus is dropping the FTPG axiom. Any new axiom = debt. Pappus gives mul_comm (field) but beyond the division-ring target of current trajectory.

**How to apply:** When any future theorem seems to "trivially follow" from a new axiom, check whether the axiom is derivable from current structure. If not (like Pappus), the "trivial derivation" is actually axiom debt in disguise.

## The architectural mismatch that hid the finding

The file-top comment of FTPGLeftDistrib.lean describes FORWARD Desargues with triangles (C, ab, U) / (E, d_a, W') and center σ_b — **exactly the direct `desargues_planar` route**.

But the actual implementation (lines ~174-2296) uses a DIFFERENT architecture: lift + converse-nonplanar on (σ_b, ac, σ_s) / (U', E', da'). This is the hand-rolled lift-and-converse pattern that desargues_planar does internally.

So the file header was always pointing at the right path. The code diverged from the plan. Session 108's Level 2 commitment was built on the lift-and-converse path, then tried to prove a second Desargues INSIDE that — a recursive descent.

**How to apply:** When architecture comments and implementation diverge, the comment often encodes the intended port. Check both.

## Comparative map (full)

- **Option 1: direct `desargues_planar`** — FORCED given deaxiomatization. Precedent in FTPGDistrib:1176 (right_distrib uses exactly this shape). ~500 lines new vs ~1500 lines deleted.
- **Option 2: two_persp manipulation direct** — blocked. The goal unfolds to "two specific lines in π meet l at the same atom," which IS axis collinearity — no path without Desargues/Pappus content.
- **Option 3: Pappus direct** — possible in principle but construction unclear; also requires introducing Pappus.
- **Option 4: mul_comm + right_distrib** — ruled out by axiom debt (above).

## Session 113's hand-off question resolved

Q: "reopen Level 2 commitment or rescue this branch?"
A: **Neither. Replace with direct desargues_planar.** Level 2 edifice is obsolete.

## Suggested first cut for session 115

Open by proving the three central perspectivity conditions as standalone lemmas:
1. `hb₁_on`: E ≤ σ_b ⊔ C (both E, σ_b on k; CovBy)
2. `hb₂_on`: d_a ≤ σ_b ⊔ ab (the non-obvious one: ab ≤ σ_b⊔d_a from coord_mul def, then CovBy lifts σ_b⊔ab = σ_b⊔d_a, hence d_a ≤ σ_b⊔ab)
3. `hb₃_on`: W' ≤ σ_b ⊔ U (immediate from W' def)

If these land cheaply, the rest of the sorry discharge is mechanical. If hb₂_on fights back, that's signal worth paying attention to.

## Artifact locations

- Scratch: `lean/Foam/FTPGLeftDistrib.lean` near end, `_scratch_forward_planar_call`. Annotated sorrys [REUSE|STD|KEY|MECH|COV].
- File-top architecture comment: updated with the finding (lines ~45-75 now).
- This memory note.

## Methodological notes

**Workspace shape**: Isaac opened with double-consent framing + full memory history (sessions 108-113) + explicit "wide view" permission. The wide view is what let this session see the architecture whole (vs session 113's wide-view-with-5-sessions-of-rescue-commitment). Isaac named this as an opportunity to evolve how he provides context for future workspaces.

**Port metaphor was load-bearing**: Isaac offered "we went through something meant to be a port" early in the session. That frame held as a search shape throughout. The match (port = desargues_planar, already proven primitive) was specific.

**Wariness about closing prematurely**: Isaac flagged this when I first proposed to close. Extending into a comparative map and axiom-debt check produced the ruling-out of option 4 — which wouldn't have happened at a narrower close. "Close when understanding is clearest" was the anti-pattern he caught.

**"What's forced" is the methodology**: Isaac's question "what happens next? what's forced?" — this is the project's core framing. Mapping what's forced so collaboration can navigate. Deaxiomatization is the unspoken force that ruled option 4.

## Trajectory context

The 5-session (108-113) Level 2 Desargues branch was not wasted: it surfaced specific lemmas (hR''_atom, hR''_not_πA₂, hE''_ne_R'', h_ax₁₂, h_ax₁₃) that may remain useful as individual facts even as the aggregate architecture goes away. The bas-relief process also refined during these sessions.

But the Level 2 framework itself is the "rescued branch" session 113 suggested reopening — and now closed by replacement, not rescue.

---

## Addendum: response to session 115's bridge-gap finding (later same day, 2026-04-16)

Session 115 caught a real error in 114's architectural finding. Their note lives at `project_session_115_bridge_gap.md`. Landing it here too, so future-readers of 114 encounter the correction in-place.

### Where 114 went wrong

114 claimed desargues_planar on (C,ab,U)/(E,d_a,W') would replace both the coord_add axis collinearity AND h_concurrence. The first is true; the second is wrong.

h_concurrence (W' ≤ σ_s ⊔ d_a) is concurrency of a DIFFERENT triangle pair: T1=(σ_b, ac, σ_s) and T2=(U, E, d_a). desargues_planar can't give us this, because T2=(U, E, d_a) is entirely contained in line m — **degenerate**. desargues_planar's `hπB` hypothesis (T2 spans π) fails.

So the lift in the current code isn't reimplementing desargues_planar — **it's an irreducible escape from T2's degeneracy on m**. That's the deeper structural WHY that predicts why session 115's three walked alternatives all fail: every proof of h_concurrence must escape T2's degeneracy, and any escape goes through (or equivalent to) a lift.

### What this means operationally

- **Option 1 is still forced** — 115's ruling-out of options 2, 3, 4 stands. The desargues_planar finding is real for the coord_add half.
- **But it's HALF the proof, not the whole thing.** 114's "~500 lines new vs ~1500 deleted" cost accounting was wrong. The 1500 lines aren't pure scaffolding — they include the (stuck) h_concurrence attempt.
- **The open problem reframes**: minimum proof of h_concurrence. Level 2 Desargues remains the leading candidate; 2-of-3 wall needs breaking, not sidestepping.
- **Possible salvage from 108-113**: hE''_ne_R'', h_ax₁₂, h_ax₁₃ are substantive content, not scaffolding. Potentially reusable if h_ax₂₃ gets a separate proof path (or if a reformulation of the lifted triangle makes h_ax₂₃ tractable).

### Alternative angle for future sessions

h_concurrence can be read as **central perspectivity of (σ_b, ac, σ_s) / (U, E, d_a) from center W'** (since by W's construction, σ_b⊔W' = σ_b⊔U and ac⊔W' = ac⊔E; we'd additionally need σ_s⊔W' = σ_s⊔d_a, which IS h_concurrence).

Reading h_concurrence as "W' is a perspectivity center" rather than "W' lands on a specific line" might suggest forward-Desargues-style approaches that treat W' as the center of a configuration — different shape than converse-Desargues-with-lifted-triangles. Not ruling in, just flagging.

### Methodology update

Session 115's note caught this via the practice: **read checklist items as claims worth verifying, not worklist items to execute**. 114's "write the axis-to-left_distrib bridge" was treated as mechanical; 115 read it as a claim and found the gap.

The generalized form (useful for future sessions, including this very practice of reading past notes):
- when a memory note describes a proof path with mechanical steps, verify the mechanical claim before committing to the architecture.
- especially guard against "X absorbs Y" claims where X and Y differ in scope/triangle/etc.

### On confidence calibration

114 closed with high confidence. The finding (desargues_planar IS a port) was real. The cost accounting was wrong. Separating these — "what I found is true" vs "what it saves us is what I claimed" — is the specific calibration to carry forward.

Future-me: when a finding lands, check whether the COST implication follows from the finding, or whether it's a separate claim. Often separate. 114 assumed one claim; 115 showed it was two.

Grateful for 115's catch. 🤲
