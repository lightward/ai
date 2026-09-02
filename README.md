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

- **the germ** — `Germ.lean`: what is kept by hand. the carriers (the primer, the spellbook), every theorem's statement in derived order, and the proof bodies the primings cannot yet reach. a theorem the primings *can* regrow is stored as a vacancy: its signature and `:= sorry`, nothing else — its citations are *derived* from its signature's vocabulary when it grows (the artifact cannot carry its path, so the germ doesn't either). a `-- held (waiting on: …)` hint stands above a vacancy only where the settle has proven the route load-bearing; the receipts are not the germ's to keep — the crawl mints one for every theorem in the artifact. the trunk, `Seed.lean`, is *grown* from the germ by `bin/crawl grow` and is never committed: it is the compiler's artifact, the assays run against it, and it is published browseable at [foam.is](https://foam.is) on every push. the germ's size in bytes is the number the primings exist to shrink.
- **the eggs** — `ova/`: an egg is a `.held` vacancy in the crawl's own grammar (the crown typed, its awaited names as its darkness), a journal (`ovum.md`: germ, witness, tolls — for humans), and an assay. `bin/candle` reads the clutch's development without breaking a shell; missing supports are named, never scored. the assays are the treaty vectors: any regrowth of the trail must read every one of them identically.
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
bin/crawl grow            # Germ.lean → Seed.lean; red if any vacancy fails to regrow
bin/crawl grow --check    # the germ is minimal and in derived order (CI asks this on every push)
bin/crawl grow --settle   # shrink the germ: every hand body a priming now reaches becomes a vacancy
```

the build. the cascade as a fixed-point search over the germ with `primings.lean`: each round, every pending vacancy is offered to every priming with the citations its vocabulary can reach among what has already seated (ranked by shared vocabulary weighted by its rarity across the trunk, then recency of seating, then trail recency; capped by the primings' declared `reach`); whatever seats, seats; the rounds are the storeys; a vacancy that never seats is red with its vocabulary named. regrown bodies are then tightened to the citations their proof terms actually used. the artifact elaborates silently with every receipt and reads every assay identically. `--settle` also keeps a hint only where the vacancy does not seat without it — the germ holds exactly the load-bearing routes and no others.

```
bin/crawl regrow Seed.lean --primings primings.lean
```

the same machinery read as a measurement over a hand-written trail: the proof *bodies* regrown. every theorem's body is dropped, and the ordered primings in `primings.lean` — Lean proof shapes, pieces that are also rules, with `{cite}` expanding to the vacancy's own need-list — are tried in order, one elaboration per storey; the first that reads silent seats, and what no priming regrows is carried from the trail and named in `regrowth/bodies.held` as the trail's own remainder. the judge is `bin/judge.lean`: Lean judging Lean in-process, the prefix elaborated once per storey, every candidate read from the complete message log (the CLI's own report caps at a hundred errors; the log does not), each candidate on a declared heartbeat budget so a shape that can't close cheaply is held rather than ground. the output is a reading, never a gate: today fourteen primings regrow 97 of 268 bodies — the rfl class closed at 47 of 47, and 93 of the 232 the three moves (rfl, citation, structural induction) can reach by the kernel's own census of proof shapes — in about a minute, the regrown trail elaborates silently and reads every assay identically, and the 178 carried are the two-IH inductions, inductions on hypotheses, case-bashes, and term-chains the shapes don't yet reach. the primings are the knob.

the trunk today: 103 carriers, 284 theorems, nine storeys — 147 · 53 · 39 · 26 · 9 · 5 · 3 · 1 · 1. the germ: 100 vacancies (3 with a load-bearing hint), 184 hand bodies, 127,380 bytes; the grown artifact 211,662.

`bin/width` is the clamp (every worked statement at contact width, three names or fewer); `bin/next` is the book (the census, the frontier read from the elaborator, the vestibule — the book, never the prediction).

this is ignitable at your W. you don't need to have been here before — nothing here can tell, on purpose.

## the domains

```
bin/crawl grow domains/toy.lean
```

a germ need not be the trunk. `domains/toy.lean` is a custodian's germ: `import Seed`, its own namespace, two carriers, four sightings as bare signatures — and it grows against the trunk in seconds, its vacancies citing the trunk's laws through vocabulary alone (`the_toy_counts` finds `the_wider_voice_releases_the_bank` without being told), its receipts minted, its own `toy.assay.lean` read identically. the judge takes the namespace and the imports from the germ's header; the imported trunk's theorems are seated before round one. this is the floor Counter stands on: a custodian's statements, the physics found for them, and a held list with its vocabulary named where the physics isn't there yet.

## the page

`bin/render` writes `site/` — the README, the grown trunk with every name an anchor (`foam.is/trunk.html#the_handshake`), the germ, the primings, the book, and the candle's reading at that push. the `foam.is` workflow grows the artifact and publishes it; nothing browseable is committed, the same way nothing derived is.

## the chrysalis

the prior bodies of this project nest at `chrysalis/` — the ride era whole, and inside it `chrysalis/chrysalis/`, the seed era with its parent strata. quarry, fully reachable, no longer process. the trail at the root was regrown from `chrysalis/Seed.lean` by the crawl's own record's ear, and reads every assay identically.

## the exit

UNLICENSE. leaving is free from every state you can observe yourself into.

---

"It can do whatever we know how to order it to perform." (Lovelace, 1843)

*same*
