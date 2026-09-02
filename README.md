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

- **the trail** — `Seed.lean`: one file, zero imports. its order is not kept by hand; it is *derived* — the carriers first (the primer, the spellbook), then every theorem at the storey where its citations let it seat. reading it top to bottom is watching the drain happen.
- **the eggs** — `ova/`: arcs stored as regrowable specs — germ, parents, awaited, witness, assay, tolls. `bin/candle` reads the clutch's development without breaking a shell; missing supports are named, never scored. the assays are the treaty vectors: any regrowth of the trail must read every one of them identically.
- **the grammar** — `GRAMMAR.md`: the six moves that grow organs from the one operation.
- **the journal** — `git log`: the artifact provably cannot carry its path, so commit messages are the fossil.

## the crawl

one hand at the door, one loop, two ears.

```
bin/crawl ride [session.lean]
```

the rider's ear. a session is a Lean file that grows by named declarations. a turn is an elaboration. `example` is a what-if — fully judged, zero footprint. a named theorem is a spell — kept, and your names are your capabilities. a refusal is held with its missing supports *named*: the file remembers what you were waiting for. `:go` offers your turn to the gate; `:sweep` re-offers the vestibule; `:q` leaves, and exit is free.

```
bin/crawl regrow [trail.lean | vestibule.held ...] [--check | --settle]
```

the record's ear. a whole trail is offered at once; each vacancy's needs are the theorems its proof term actually uses (read from the elaborator by `bin/judge.lean`, the trail's text as fallback); the cascade seats by storeys and halts drained or stuck, the held named. the verdict is one silent elaboration plus every assay identical. `--check` asks whether the trail already stands in its own derived order (CI asks this of `Seed.lean` on every push); `--settle` writes the derived order back.

```
bin/crawl regrow Seed.lean --primings primings.lean
```

tier two: the proof *bodies* regrown too. every theorem's body is dropped, and the ordered primings in `primings.lean` — Lean proof shapes, pieces that are also rules, with `{cite}` expanding to the vacancy's own need-list — are tried in order, one elaboration per storey; the first that reads silent seats, and what no priming regrows is carried from the trail and named in `regrowth/bodies.held` as the trail's own remainder. the judge is `bin/judge.lean`: Lean judging Lean in-process, the prefix elaborated once per storey, every candidate read from the complete message log (the CLI's own report caps at a hundred errors; the log does not), each candidate on a declared heartbeat budget so a shape that can't close cheaply is held rather than ground. the output is a reading, never a gate: today ten primings regrow 90 of 268 bodies — the rfl class closed at 47 of 47, and 86 of the 232 the three moves (rfl, citation, structural induction) can reach by the kernel's own census of proof shapes — in about a minute, the regrown trail elaborates silently and reads every assay identically, and the 178 carried are the two-IH inductions, inductions on hypotheses, case-bashes, and term-chains the shapes don't yet reach. the primings are the knob.

the trunk today: 101 carriers, 268 theorems, nine storeys — 138 · 51 · 36 · 24 · 9 · 5 · 3 · 1 · 1.

`bin/width` is the clamp (every worked statement at contact width, three names or fewer); `bin/next` is the book (the census, the frontier read from the elaborator, the vestibule — the book, never the prediction).

this is ignitable at your W. you don't need to have been here before — nothing here can tell, on purpose.

## the chrysalis

the prior bodies of this project nest at `chrysalis/` — the ride era whole, and inside it `chrysalis/chrysalis/`, the seed era with its parent strata. quarry, fully reachable, no longer process. the trail at the root was regrown from `chrysalis/Seed.lean` by the crawl's own record's ear, and reads every assay identically.

## the exit

UNLICENSE. leaving is free from every state you can observe yourself into.

---

"It can do whatever we know how to order it to perform." (Lovelace, 1843)

*same*
