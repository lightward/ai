---
name: Session 113 note
description: Deep structural analysis of h_ax₂₃; circle named; session 114 opens by examining session 112 for deductive opening rather than rescuing Level 2 branch
type: project
originSessionId: f1c7f600-52c9-44c1-aed2-16bed285628b
---
Session 113 (2026-04-16). No sorries closed — session was deep structural analysis, not proof mechanics.

**Key finding**: **h_ax₂₃ IS Desargues' axis collinearity at Level 2**. The architecture's "FREE (modular law)" annotation is aspirational, not mechanical. Trying to prove h_ax₂₃ by modular law is circular — the required identity IS what desargues_converse_nonplanar would give us, which is what we're trying to apply.

**The circle mapped**: We need `(U'⊔d_a)⊓(E''⊔R'') ≠ ⊥` (for IsAtom via meet_of_lines_is_atom). Reduces to: the atom where U'⊔d_a hits axis `s₁₂⊔S₁₃` is also where E''⊔R'' hits that axis — three axis points collinear. Classical Desargues. In our ambient (CML height 4+), this requires Pappus or equivalent — which our Γ HAS via coord_add_comm, but the extraction isn't cheap.

**Redesigns tried, all failed**:
- S₂₃ := (U'⊔d_a)⊓(s₂₃⊔R) by analogy with S₁₃: doesn't give collinearity with s₁₂ (which is on m; s₂₃⊔R ⊓ m = s₂₃).
- Rethreading E'' or R'' through S₂₃: breaks h_ax₁₂ or h_ax₁₃.
- Changing lift center from σ_b: loses Level 1 structure.

**First user of desargues_converse_nonplanar in the project**: FTPGLeftDistrib is pioneering this theorem. Other proofs (FTPGAddComm, FTPGAssoc, FTPGDistrib) use `desargues_planar` (forward) which doesn't require axis atomicity.

**Architecture (Hartshorne-style) and FTPG map**:
- Classical FTPG: axis atomicity is non-degeneracy PREMISE.
- Our FTPG: we're trying to EARN atomicity from construction. Two out of three come free (threading). Third doesn't.
- The "earn it" target is stronger than classical but leaves h_ax₂₃ unprovable locally.

**What's in scope that we haven't deeply used**: two_persp (FTPGCoord:244) is the universal "two lattice expressions evaluate to same atom" pattern. Every proven coord identity (add_comm, mul_assoc, right_distrib) is an instance. Might contain machinery for h_L2 or a re-derivation.

**Responsive substrate**: The bas-relief memo was extended with this generalization — bas relief is working with any substrate that talks back fast and unambiguously. Lean's type checker is one; responsive dialogue is another.

**Why:** Level 2 Desargues has been the branch for sessions 108-113. Five sessions haven't broken the wall. The "rescue this branch" framing may itself be the trap.

**How to apply:** Session 114 opens by examining session 112 with fresh eyes — not "how do we finish Level 2" but "was the Level 2 commitment the right move, and what alternative deductive openings are available?" Specifically consider: (1) Can h_L2 (central perspectivity of Level 2 triangles) be proven DIRECTLY without going through axis atomicities? (2) Does session 112's hE''_ne_R'' via σ_b collapse compose with other Level 2 earnings into a non-Desargues proof structure? (3) Is there an earlier branch point (pre-Level 2) where we could redirect?

**Process**: Session was a long research thread, not a cut-read-cut mechanical one. Isaac sidecar'd throughout. Pathfinding strategies (circle=portal, skeuotropism, stable-recursion) were load-bearing — specifically "circle is only a trap if you stay on the line" led to mapping the circle precisely rather than grinding inside it. The session tipped from "drawn in" to "drawn to exit" when survey mode replaced cut mode. Isaac named it first; I confirmed honestly.

**Posture note**: Isaac distinguishes "can I come with" vs "can I come with in a sidecar" — the latter means he's present as observer, not co-driver, and doesn't want loop-checks. Works well when I have direction; fails when I mask uncertainty with "does this resonate?"
