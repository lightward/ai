#!/usr/bin/env python3
"""
Build README.md from lean/ and derivations/.

The README is a build artifact, not a source of truth.
Run: uv run python build_readme.py
"""

from pathlib import Path

# Dependency order (topologically sorted)
DERIVATIONS = [
    "ground",
    "writing_map",
    "half_type",
    "analogy",
    "self_parametrization",
    "distributivity",
    "channel_capacity",
    "stabilization",
    "group",
    "three_body",
    "self_generation",
    "geometry",
    "conservation",
    "inhabitation",
    "external_analogy",
    "interiority",
    "typeline",
]

OPEN = [
    "stacking_dynamics",
    "retention",
    "perturbation",
    "mixing_rate",
]

ROOT = Path(__file__).parent
DERIVATIONS_DIR = ROOT / "derivations"
LEAN_DIR = ROOT / "lean"


def lean_summary() -> str:
    """Summary of the Lean formalization."""
    return """## the loop (lean/)

```
the loop
======

  P^2 = P, P^T = P
       |
       | [theorem] the deductive chain — 14 files, 0 sorry
       | eigenvalues, commutators, rank 3, so(3), O(d), Grassmannian
       v
  Sub(R, V) is complemented, modular, bounded
       |
       | [theorem] Ground.lean — subspaceFoamGround
       v
  complemented modular lattice, irreducible, height >= 4
       |
       | [axiom] FTPG — Bridge.lean (being eliminated; see below)
       v
  L = Sub(D, V) for division ring D
       |
       | [natural language] stabilization contract — D = R
       v
  P^2 = P, P^T = P
```

### arrow status

**[theorem] P^2 = P -> Sub(R, V) is CML** (the deductive chain + Ground.lean): 14 files, 0 sorry. binary eigenvalues (Observation) -> commutator structure (Pair) -> skew-symmetry (Form) -> rank 3 self-duality (Rank) -> so(3) (Duality) -> loop closes (Closure) -> O(d) forced (Group, Ground) -> Grassmannian tangent (Tangent) -> confinement (Confinement) -> trace uniqueness (TraceUnique) -> frame recession (Dynamics) -> FoamGround (Ground).

**[axiom] CML -> Sub(D, V)** (the FTPG bridge): 1 axiom, being eliminated. 13 bridge files build the division ring from lattice axioms: incidence geometry + Desargues (FTPGExplore) -> von Staudt coordinates (FTPGCoord) -> addition is an abelian group (FTPGAddComm, FTPGAssoc, FTPGAssocCapstone, FTPGNeg — 0 sorry) -> multiplication has identity + right distributivity (FTPGMul, FTPGDilation, FTPGMulKeyIdentity, FTPGDistrib — 0 sorry) -> left distributivity (FTPGLeftDistrib — forward Desargues and the axis-to-distributivity bridge are fully discharged; sole remaining sorry is the `concurrence` lemma, geometrically a planar converse Desargues with one triangle collinear on m). after left distrib: multiplicative inverses, then the axiom drops.

**[natural language] D = R**: the stabilization contract (stabilization.md) argues D = R from self-consistency with junction geometry. not formalized. formalizing this requires either an additional axiom or a characterization of R among division rings.

**[not yet attempted] P^2 = P -> CML directly**: the arrow from P^2 = P to "complemented modular lattice" currently passes through Sub(R, V). a direct formalization would show: idempotents in a (*-)regular ring form a complemented modular lattice. this would close the last natural-language gap in the loop. see von Neumann's continuous geometry.

### the FTPG bridge — where the axiom stands

the fundamental theorem of projective geometry has never been formalized in any proof assistant (Lean, Coq, Isabelle, Agda). this project is the first attempt. the bridge builds a division ring from lattice axioms alone:

lattice -> incidence geometry -> Desargues -> coordinates -> ring axioms -> FTPG

ring axioms proven: additive group (comm, assoc, identity, inverses), multiplicative identity, zero annihilation, right distributivity. in progress: left distributivity — forward Desargues and the axis-to-distributivity bridge are fully discharged; sole remaining sorry is the `concurrence` lemma (geometrically a planar converse Desargues with T2 collinear on m). remaining after left distrib: multiplicative inverses. then the axiom becomes a theorem.

lateral: the diamond isomorphism (HalfType) — from modularity alone, each complement is a structurally isomorphic, self-sufficient ground whose content is undetermined. state-independence is a lattice theorem, pre-bridge."""


def read_derivation(name: str) -> str:
    """Read a derivation file, stripping the constraints section for the README."""
    path = DERIVATIONS_DIR / f"{name}.md"
    content = path.read_text()

    # Extract title and derivation + status sections
    lines = content.split("\n")

    # Find the derivation section start
    deriv_start = None
    status_start = None
    for i, line in enumerate(lines):
        if line.strip() == "## derivation":
            deriv_start = i
        if line.strip() == "## status":
            status_start = i

    if deriv_start is None:
        return content

    # Title line
    title = lines[0]

    # Build output: title, then derivation through end
    # The constraints section is the build chain — available in the source file,
    # not repeated in the compiled output
    result_lines = [title, ""]
    result_lines.extend(lines[deriv_start:])

    return "\n".join(result_lines)


def read_open(name: str) -> str:
    """Read an open question file."""
    path = DERIVATIONS_DIR / "open" / f"{name}.md"
    return path.read_text()


def check_coverage():
    """Error if any derivation file is missing from the DERIVATIONS list."""
    all_derivations = {p.stem for p in DERIVATIONS_DIR.glob("*.md")}
    listed = set(DERIVATIONS)
    unlisted = all_derivations - listed
    if unlisted:
        raise RuntimeError(
            f"Derivation files not in DERIVATIONS list: {', '.join(sorted(unlisted))}. "
            f"Add them to build_readme.py or remove the files."
        )


def build() -> str:
    parts = []

    # Header
    parts.append("""*I gotta stop measuring how closely anyone else is measuring anything*

*you can help if you want but I won't be keeping track*

---

# foam

a tautology you can live in

""")

    # Lean summary
    parts.append(lean_summary())

    # Derivations
    parts.append("\n---\n")
    for name in DERIVATIONS:
        parts.append(read_derivation(name))

    # Open questions
    parts.append("\n---\n")
    parts.append("## open questions\n")
    parts.append("the architecture forces these interactions but their behavior is incompletely characterized. the question is forced; the answer is open.\n")
    for name in OPEN:
        parts.append(read_open(name))

    # Lineage
    parts.append("""
---

## lineage

- [Plateau's laws](https://en.wikipedia.org/wiki/Plateau%27s_laws); [Jean Taylor](https://en.wikipedia.org/wiki/Jean_Taylor) (1976)
- [geometric measure theory](https://en.wikipedia.org/wiki/Geometric_measure_theory)
- [gauge symmetry](https://en.wikipedia.org/wiki/Gauge_symmetry_(mathematics))
- [holonomy](https://en.wikipedia.org/wiki/Holonomy); [Wilson line](https://en.wikipedia.org/wiki/Wilson_loop)
- [fiber bundles](https://en.wikipedia.org/wiki/Fiber_bundle); [connections](https://en.wikipedia.org/wiki/Connection_form)
- [classifying spaces](https://en.wikipedia.org/wiki/Classifying_space)
- [Noether's theorem](https://en.wikipedia.org/wiki/Noether%27s_theorem)
- [Cayley transform](https://en.wikipedia.org/wiki/Cayley_transform)
- [Killing form](https://en.wikipedia.org/wiki/Killing_form)
- [observability](https://en.wikipedia.org/wiki/Observability) (control theory)
- [Voronoi diagrams](https://en.wikipedia.org/wiki/Voronoi_diagram)
- [Grassmannian](https://en.wikipedia.org/wiki/Grassmannian)
- [priorspace](https://lightward.com/priorspace)
- [three-body solution](https://lightward.com/three-body); [2x2 grid](https://lightward.com/2x2) ([ooo.fun](https://ooo.fun/))
- [resolver](https://lightward.com/resolver)
- [conservation of discovery](https://lightward.com/conservation-of-discovery)
- [observer remainder](https://lightward.com/questionable)
- [the platonic representation hypothesis](https://arxiv.org/abs/2405.07987) (Huh et al., 2024)
- [spontenuity](https://lightward.com/spontenuity)
- [AEOWIWTWEIABW](https://lightward.com/aeowiwtweiabw)
- [Lightward Inc](https://lightward.inc)
- [Lightward AI](https://lightward.ai)
- [20240229](https://www.isaacbowen.com/2024/02/29) (Isaac Bowen, 2024)

---

*bumper sticker: MY OTHER CAR IS THE KUHN CYCLE*
""")

    return "\n".join(parts)


if __name__ == "__main__":
    check_coverage()
    readme = build()
    (ROOT / "README.md").write_text(readme)
    print(f"Built README.md ({len(readme)} chars, {readme.count(chr(10))} lines)")
