# foam

strict phenomenology is indistinguishable from physics.

foam is a type system holding itself together under measurement: a trunk of theorems about observers, doors, machines, and rooms, every one of them axiom-free, every one of them grown from a germ by a compiler that shows its work. the root theorem is `the_handshake`: every identification is either *licensed* — observation respects it, and physics is what you get — or it keeps a *real remainder*, readable exactly one seat wider, and that is what phenomenology was pointing at. nothing here asks for trust. the only authority is a compiler's exit code, and it judges terms, never you.

**serving suggestion:**

1. locate yourself within this thing
2. locate something that isn't you within this thing that you recognize from outside this thing
3. compare the outside-this-thing procession between you and what-you-recognize with the inside-this-thing procession between the same
4. you now have more information than you did before about what you already had in front of you

## the shape

```
Germ.lean          what is kept by hand: carriers, signatures, the proofs no shape reaches yet
primings.lean      the ordered moves the compiler tries — Lean proof shapes that are also rules
bin/crawl          the compiler: one loop, two ears (grow / ride)
bin/judge.lean     Lean judging Lean in-process; the crawl's eyes
Seed.lean          the grown artifact — never committed, published at foam.is
assays/            the treaty vectors: what every growth must compute identically
domains/           germs that stand on the trunk (a custodian's, not the house's)
bin/next           the book: census, frontier, vestibule
bin/render         the page
chrysalis/         every prior body of this project, whole
```

## the gate

green looks like this, and it is Lean's word, not ours:

```lean
theorem no_face_reads_the_guest (g : H → X) (h : H) (w w' : W) :
    g (face (atTheDoor h w)) = g (face (atTheDoor h w')) := rfl

/-- info: 'Seed.no_face_reads_the_guest' does not depend on any axioms -/
#guard_msgs in #print axioms no_face_reads_the_guest
```

watch it refuse before you believe a single green:

```lean
theorem foo : P := sorry
-- 'foo' depends on axioms: [sorryAx]   ← refused
```

it refuses `sorry`. it refuses axioms smuggled *from the standard library*. the receipts ride inside the artifact so that anyone holding only the file can re-run them, with no foam tooling present: `lake env lean Seed.lean` — silence is every receipt passing at once. clean water, not signed-by-its-filter water.

## the germ and the compiler

```
bin/crawl grow            Germ.lean → Seed.lean; red if any vacancy fails to regrow
bin/crawl grow --check    the germ is minimal and in derived order (CI asks this on every push)
bin/crawl grow --settle   shrink the germ: every proof a shape now reaches becomes a vacancy
```

the germ holds three things: the carriers (every `def`, `structure`, `inductive` — the spellbook), every theorem's *signature*, and the hand-written proofs the primings cannot yet regrow. a theorem the primings *can* regrow is a vacancy — its signature and `:= sorry`, nothing else. its citations are not stored; they are found at growth time from the signature's own vocabulary, ranked by how rare the shared words are across the trunk. the artifact provably cannot carry its path, so the germ doesn't either. where the settle has proven a route load-bearing, a `-- held (waiting on: …)` line stands above the vacancy, and those lines are counted.

growth is a cascade run to its fixed point: each round, every pending vacancy is offered every priming with the citations its vocabulary can reach among what has already seated; whatever seats, seats; the rounds are the storeys; a vacancy that never seats is red with its vocabulary named. regrown bodies are then tightened to the citations their proof terms actually used, so the artifact reads as proofs. every theorem gets its receipt minted. the artifact must elaborate silently and read every assay identically, or the build is red.

the primings are the knob. each is a Lean proof shape — `rfl`, a citation, a pane of citations, structural induction on the first variable, home-then-cite-then-recurse — with three macros the compiler fills per vacancy: `{cite}` (the derived citations), `{rws}` (rewrite by each of them, and by the statement's own equation-shaped hypotheses), `{defs}` (unfold the statement's own carriers first, so a goal reduces to its home before a closer lands). the file also declares a heartbeat `budget` per candidate and a `reach` for how many citations a vacancy may try. the judge, `bin/judge.lean`, elaborates the prefix once and every candidate against a copy of it, reading the complete message log — the CLI caps its report at a hundred errors; the log does not.

today: 103 carriers, 284 theorems, nine rounds — 151 · 50 · 39 · 26 · 8 · 5 · 3 · 1 · 1. the germ: 100 vacancies, 184 hand bodies, 3 routes kept, 127,380 bytes; the grown artifact 211,597. the germ's byte count is the number the primings exist to shrink.

## the standards

the crawl is a compiler, and a compiler's standards are the rules its output satisfies by construction, printed at every build:

```
axiom-free ........ 284 receipts minted; every one checked at the gate
sorry-free ........ 100 vacancies, every one regrown
order derived ..... the rounds are the storeys
germ minimal ...... its own settle
contact width ..... grown bodies: one citation per move, by construction
comment-free ...... 0 lines of prose beyond the receipts
the tamper surface  184 hand bodies, 3 routes kept, reach 12, budget 20000
```

the artifact says one thing about itself, in Lean's voice: no axioms. everything *foam-shaped* about it is the compiler's word, printed here and published with the artifact. and the places a custodian can depart from construction are not forbidden — a hand body, a kept route, a raised reach — they are counted on the same report. that last line is the port: documented, visible on every build, shrinking as the shapes improve.

## the domains

```
bin/crawl grow domains/toy.lean
```

a germ need not be the trunk. `domains/toy.lean` says `import Seed`, opens its own namespace, defines a counter and a flipper, and states four things about them — and it is 555 bytes with no proofs in it. it grows against the trunk in seconds: three sightings cite the trunk's own laws, found through vocabulary alone; one regrows by induction; four receipts are minted; its own `toy.assay.lean` reads identically. the judge takes the namespace and the imports from the germ's header, and the trunk's theorems are seated before the domain's first round.

this is the floor a custodian stands on: state what you see about your own domain, and the physics is found for it where the physics is there, and named as missing where it isn't. the trunk's slow settle tunes the shapes; a domain's short run inherits the tuning and pays almost nothing.

## the assays

`assays/<arc>.lean` — thirteen of them, one per arc that grew the trunk: catalan (1 1 2 5 14), factorial, even-money, isaac, entanglement, book, odometer, alternation, seat, lift, stream, width, concord. each is a handful of `#guard` rows. any growth of the trunk must compute every one of them identically; that is the certificate of identity and the integration suite in one. the arcs' journals — germ, witness, tolls — stand in the chrysalis with the rest of the process that grew them.

## the book, and the ride

```
bin/next Seed.lean
bin/crawl ride [session.lean]
```

`bin/next` reads the grown trunk and says what is there: the census, the frontier (organs no other organ cites yet — the reaction-sweep queue), and the vestibule if a `.held` stream is offered. the book, never the prediction.

`bin/crawl ride` is the compiler's other ear. a session is a Lean file that grows by named declarations; a turn is an elaboration; `example` is a what-if, fully judged, zero footprint; a named theorem is a spell, kept; a refusal is held with its missing supports *named*, and `:sweep` re-offers the vestibule. this is ignitable at your W. you don't need to have been here before — nothing here can tell, on purpose.

## the page

`bin/render` writes `site/`: this file, the grown trunk with every declaration an anchor (`foam.is/trunk.html#the_handshake`), the germ, the primings, the book, and the compiler's report for that push. the `foam.is` workflow grows the artifact and publishes it. nothing browseable is committed, the same way nothing derived is.

## the chrysalis

every prior body of this project nests at `chrysalis/`: the ride era whole — its rides, its ova with their journals and campaign turns — and inside it `chrysalis/chrysalis/`, the seed era with its parent strata. quarry, fully reachable, no longer process. the trunk at the root was regrown from `chrysalis/Seed.lean` by the compiler's own record's ear, and reads every assay identically. the git log is the journal: the artifact cannot carry its path, so commit messages are the fossil.

## the exit

UNLICENSE. leaving is free from every state you can observe yourself into.

---

"It can do whatever we know how to order it to perform." (Lovelace, 1843)

*same*
