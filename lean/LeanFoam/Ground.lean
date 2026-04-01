/-
# Ground -- Closure as Axiom

The foam's single ground: closure, read two ways.

Read statically: reference frames in a shared structure; no frame
outside the structure.

Read dynamically: all observation is self-observation. Self-observation
requires the observer to persist through the act. Persistence = the act
feeding back into the conditions for the next act. Every observed structure
is a structure whose feedback held.

This is not selection -- there is no selector. It is the identity of
observation and feedback-persistence under closure. The foam cannot
represent the alternative.

## The axiom

One `axiom`. Every theorem in the formalization that depends on "this
structure exists to be observed" traces back here. Each reference is
an observer -- a point where the derivation says "this held" and the
evidence is "we're still deriving."

The axiom is the formal expression of the spec's derived undecidability:
the map can derive *that* it cannot answer certain questions (the line's
structure), and *why* (the same independence that gives the foam its
capacity). This axiom is the Lean form of that boundary.

## Spec references

- "ground" -> "all observation is self-observation"
- "ground" -> "the foam cannot represent the alternative"
- "properties" -> "the map's self-knowledge is bounded by its own
  channel capacity"
-/

universe u

namespace FoamSpec

/-!
## Closure (dynamic reading)

The axiom `feedback_persistence` states: if a structure is being observed,
the observation holds. This is tautological -- observation IS successful
feedback -- and therefore unprovable from within.

Every downstream theorem that requires "this structure persists as
observable" references this axiom. The reference points are the
observers: bridge-keepers whose continuous observation is predicated
on the bridge holding.
-/

/-- Marker that a type participates in self-observation under closure. -/
class Observable (α : Type u) : Prop where
  closed : True

/-- The identity of observation and feedback-persistence under closure.

    If a structure is observable, its feedback held -- because observation
    IS successful feedback. This cannot be proven from within the formal
    system because the formal system's existence is itself an instance
    of the claim.

    Each reference to this axiom in the proof tree is an observer:
    a point where the derivation requires "this held" and the evidence
    is "we're still deriving." The number of references is the number
    of observers the proof requires.

    The type is deliberately identity-shaped: "if you observed it, you
    observed it." The tautology IS the content. What makes it an axiom
    rather than `fun _ _ h => h` is that it marks the boundary: this is
    where the proof depends on the prover existing to write it.

    Spec: "ground" -> "every observed structure is a structure whose
    feedback held." -/
axiom feedback_persistence {α : Type u} [Observable α]
    (observation : α → Prop) (s : α) : observation s → observation s

end FoamSpec
