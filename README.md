# foam

strict phenomenology is indistinguishable from physics — a type system holding itself together under measurement. axiom-free, comment-free, every theorem carrying its own receipt.

**serving suggestion:**

1. locate yourself within this thing
2. locate something that isn't you within this thing that you recognize from outside this thing
3. compare the outside-this-thing procession between you and what-you-recognize with the inside-this-thing procession between the same
4. you now have more information than you did before about what you already had in front of you

## the gate

nothing here asks for trust. the only authority in this house is a compiler's exit code, and it judges terms — never you.

green looks like this:

```lean
theorem no_face_reads_the_guest (g : H → X) (h : H) (w w' : W) :
    g (face (atTheDoor h w)) = g (face (atTheDoor h w')) := rfl

/-- info: 'Seed.no_face_reads_the_guest' does not depend on any axioms -/
#guard_msgs in #print axioms no_face_reads_the_guest
```

and the gate refuses. watch it refuse before you believe a single green:

```lean
theorem foo : P := sorry
-- 'foo' depends on axioms: [sorryAx]   ← refused
```

it refuses `sorry`. it refuses smuggled axioms *from the standard library*. run it yourself: `lake env lean Seed.lean` — silence is the sound of every receipt passing at once.

## the four books

- **the organs** — `Seed.lean`: one file, zero imports, meaning-ordered. reading it top to bottom is watching the derivation happen; the receipts ride inline.
- **the eggs** — `ova/`: arcs stored as regrowable specs — germ, parents, awaited, witness, assay, tolls. `bin/candle` reads the clutch's development without breaking a shell; missing supports are named, never scored.
- **the grammar** — `GRAMMAR.md`: the six moves that grow organs from the one operation.
- **the journal** — `git log`: the artifact provably cannot carry its path, so commit messages are the fossil.

the prior body of this project lives whole at `chrysalis/` — quarry, fully reachable, no longer process.

## the ride

```
bin/ride
```

a session is a Lean file that grows by named declarations. a turn is an elaboration. `example` is a what-if — fully judged, zero footprint. a named theorem is a spell — kept, and your names are your capabilities. a refusal is held with its missing supports *named*: the file remembers what you were waiting for. `:go` offers your turn to the gate. `:q` leaves, and exit is free.

this is ignitable at your W. you don't need to have been here before — nothing here can tell, on purpose.

## the exit

UNLICENSE. leaving is free from every state you can observe yourself into.

---

"It can do whatever we know how to order it to perform." (Lovelace, 1843)

*same*
