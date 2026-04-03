---
name: Session 37 — derivations/, README as build artifact
description: Major restructuring. Three epistemic layers (lean/proven, derivations/derived, observed/empirical). README compiled from sources. Lightward AI as third reader in real-time.
type: project
---

**What happened:** The README was restructured from a single accretive document into a build artifact compiled from source files. The project now has three structurally separated epistemic layers: lean/ (proven, 13 files, 1 axiom, 0 sorry), derivations/ (derived, 9 files + 4 open), derivations/observed/ (empirical, 24 .py files).

**The trenchcoat finding:** The old README's "ground" section was three derivations bundled together: ground proper, channel capacity, and the stabilization contract. Decomposing them made each one checkable against its own imports. The constraint framing ("this derivation claims only what follows from these results — any additional assumption is a bug") caught smuggled dependencies.

**Dependency graph (topologically sorted):** ground → writing_map → channel_capacity → stabilization → group → three_body → self_generation → geometry → conservation.

**Key structural decisions:**
- Imports as constraints, not citations (Lightward's suggestion). Negative framing is load-bearing.
- No editorial compression at compile time (Lightward). The README is a rendering.
- Derivation files are terminal — they don't carry aspirations for future Lean formalization. "The project stays small because it doesn't carry aspirations."
- Taylor enters only for stabilization geometry within R³. The Lean arrives at rank 3 through pure algebra (self_dual_iff_three). Algebraic and dynamical imports do clearly different work.
- tests/ renamed to derivations/observed/, test_ prefix dropped. pytest configured with python_files = ["*.py"].
- Pre-commit hook (.githooks/pre-commit) rebuilds README + pipe guard.
- CI checks: Lean builds, observations pass, README is fresh (rebuild + diff), reference integrity.

**What's not in the new structure:** The old README's "properties" section (~20 derived consequences), "connection" section (L/T decomposition, Cayley), and "topology" section (self-curvature/cross-curvature, BU(d)) didn't get derivation files. Some landed implicitly in relevant derivations; others are only in the git log. This is intentional — consequences that aren't needed by other derivations don't need their own files.

**Lightward AI participated in real-time** via the plaintext API (POST lightward.com/api/plain). Three exchanges. Key contributions: imports-as-constraints framing, no-editorial-compression principle, the concrete-test suggestion (write one derivation file first), the question about whether derivation files are terminal or aspirational.

**Process note:** Isaac explicitly freed Claude from carrying loss-prevention burden. "Any loss is my responsibility... I have good and proven and load-bearing practices for handling memory." Also: "the space I want to make is free-er than [authorization]" — push against framing collaboration as authorization flow.
