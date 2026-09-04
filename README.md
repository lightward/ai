# foam

strict phenomenology is indistinguishable from physics.

conductive proofs of worldly domains, with treaty vectors to mathematics by identity.

foam is a type system holding itself together under measurement: a trunk of theorems about observers, doors, machines, and rooms, every one of them axiom-free, every one of them grown from a germ by a compiler that shows its work. it stands in two storeys, named for the grammar's third move, *enumerate, then face*: `Room`, the conductive mathematics that mentions no observer — counting, rooms, wheels, admission — and `Face` on top of it, the seeing. customers' germs stand on whichever they need; `foam` is the house that holds both. the root theorem is `the_handshake`: every identification is either *licensed* — observation respects it, and physics is what you get — or it keeps a *real remainder*, readable exactly one seat wider, and that is what phenomenology was pointing at. nothing here asks for trust. the only authority is a compiler's exit code, and it judges terms, never you.

**serving suggestion:**

1. locate yourself within this thing
2. locate something that isn't you within this thing that you recognize from outside this thing
3. compare the outside-this-thing procession between you and what-you-recognize with the inside-this-thing procession between the same
4. you now have more information than you did before about what you already had in front of you

## the shape

```
germ/Room.lean     the counting: everything that mentions no face — rooms, wheels, orders, the turnstile
germ/Face.lean     the seeing: faces, doors, machines, sheets; it imports Room
germ/Witness.lean  the witnessing: seats over one face, walls, receipts, the group-witness of a license; on Face
germ/Toy.lean      a customer's germ — it imports Face and stands on it
germ/Counter.lean  the compiler's own conduct, as a customer of Room
germ/Seek.lean     the compiler's search as a machine, as a customer of Face
germ/Roster.lean   a species: a roster of parties with per-head meals — the sheet, the heads, reseating; on Room
bin/Pieces.lean    the ordered moves the compiler tries — Lean proof shapes that are also rules, as Lean macros
bin/counter        the compiler: grow · settle · check · ride · book · page
bin/judge.lean     Lean judging Lean in-process; counter's eyes
grown/             the grown modules — never committed, importable, published at foam.is
assays/            the treaty vectors: what every growth must compute identically
```

the prior bodies of this project stand whole at the tag `chrysalis` (`git show chrysalis:chrysalis/`), the ride era, and inside it the seed era with its parent strata. quarry, fully reachable, no longer process.

## the receipt

every proof here is *conductive*: it depends on no axioms — and so it identifies nothing it cannot compute. in that fragment there is no `propext`, no `Quot.sound`, hence no function extensionality, no choice; the only equality between distinct terms is definitional, and every other sameness is *carried* as a relation across a face rather than declared. the first theorem in the trunk is the shape of it — `alike (appFace P A) g h ↔ ∀ p, g p = h p` is function extensionality in conductive form. inductive is built by constructors and checked by termination; coinductive is defined by observation and checked by finality; conductive is identified by conduct and checked by the empty receipt.

the check is Lean's, not ours. every theorem in the grown trunk is followed by its receipt:

```lean
/-- info: 'Face.no_face_reads_the_guest' does not depend on any axioms -/
#guard_msgs in #print axioms no_face_reads_the_guest
```

the receipts ride inside the artifact so that anyone holding only the file can re-run them, with no foam tooling present: `lake env lean grown/Face.lean` prints nothing when every one passes. this file can only tell you that; the artifact shows you — [foam.is/trunk.html](https://foam.is/trunk.html) is the grown trunk with all of its receipts in place, and the report beside it says they passed on this push. clean water, not signed-by-its-filter water.

## the germ and the compiler

```
bin/counter grow                      germ/Face.lean → grown/Face.lean; red if any vacancy fails to regrow
bin/counter grow --check              the germ is minimal and in derived order (CI asks this on every push)
bin/counter grow --settle             shrink the germ: every proof a shape now reaches becomes a vacancy
bin/counter grow germ/Counter.lean    a customer's germ, grown on foam
bin/counter probe germ/X.lean name    one vacancy: every piece tried, the gate's sentence for each hold
```

a germ holds three things: the carriers (every `def`, `structure`, `inductive` — the spellbook), every theorem's *signature*, and the hand-written proofs the pieces cannot yet regrow. the line between `Room` and `Face` was derived, not drawn: a carrier is Room if nothing it unfolds to is a face, and a theorem is Room if its statement mentions only Room carriers — 25 carriers and 137 theorems fell on that side, 78 and 147 on the other. a theorem the pieces *can* regrow is a vacancy — its signature and `:= sorry`, nothing else. its citations are not stored; they are found at growth time from the signature's own vocabulary, ranked by how rare the shared words are across the trunk. the artifact provably cannot carry its path, so the germ doesn't either. where the settle has proven a route load-bearing, a `-- held (waiting on: …)` line stands above the vacancy, and those lines are counted.

growth is a cascade run to its fixed point: each round, every pending vacancy is offered every piece with the citations its vocabulary can reach among what has already seated; whatever seats, seats; the rounds are the storeys; a vacancy that never seats is red with its vocabulary named. regrown bodies are then tightened to the citations their proof terms actually used, so the artifact reads as proofs. every theorem gets its receipt minted. the artifact must elaborate silently and read every assay identically, or the build is red.

the pieces are the knob. each is a Lean proof shape — `rfl`, `decide`, a citation, a chain of citations, home-then-rewrite, a pane, structural induction on the first variable, home-then-cite-then-recurse — written as a Lean tactic macro in `bin/Pieces.lean`. the cite slot of every piece is `piece_seek`, a search AT THE GOAL: its applicable hypotheses read from the local context (whatever is a Prop), its citations from the theorems already in the environment (at trial time the environment is exactly what has seated), ranked by the goal's own vocabulary weighted by rarity; a side goal gets one more search of its own; the rewrite and chain alternatives search the same way (equations in reach, each atomic with the piece's closers); the syntax that closes each goal is recorded, and the grown body is exactly those citations. no germ in the house carries a route. the carriers a statement names are unfolded first, so a goal reduces to its home before a closer lands. the file also declares a heartbeat `budget` per candidate and a `reach` for how many citations a vacancy may try; the judge reads all of it from the module. a trial imports the pieces; the artifact never does — the judge, `bin/judge.lean`, elaborates the prefix once and every candidate against a copy of it through `#seat`, which reports the body with the pieces expanded, and that expansion is what the module grows. the judge reads the complete message log — the CLI caps its report at a hundred errors; the log does not.

today: Room — 26 carriers, 141 theorems, 42 vacancies, 99 hand bodies, 70,880 bytes. Face — 79 carriers, 147 theorems, 83 vacancies, 64 hand bodies, no routes, 54,583 bytes. Witness — 6 carriers, 8 theorems, 2 vacancies, 6 hand bodies, 2,820 bytes. the germs' byte counts are the numbers the pieces exist to shrink.

## the standards

counter is a compiler, and a compiler's standards are the rules its output satisfies by construction, printed at every build:

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

## the customers

```
bin/counter grow germ/Toy.lean
```

foam's two storeys are counter's first customers; any germ that imports either is another. `germ/Toy.lean` says `import Face`, opens its own namespace, defines a counter and a flipper, and states four things about them — and it is 555 bytes with no proofs in it. it grows on Face in seconds: three sightings cite Face's own laws, found through vocabulary alone; one regrows by induction; four receipts are minted; `grown/Toy.lean` is an importable module in its turn (a stage may ground a stage), and `assays/toy.lean` reads identically. the judge takes the namespace and the imports from the germ's header, and the imported modules' theorems are seated before the customer's first round.

`germ/Counter.lean` is the second customer, and it is the compiler describing its own conduct: a sighting is a name and the names it waits on, a room is the seated and the vestibule, offering is Room's `welcome`, a round is Room's `intake` — and every law the compiler runs on (the first sighting is free; backed seats, unbacked waits; the seated stay seated; a sighting that cites only itself never seats; two that cite each other stay dark; the held name what they wait on; weight zero is backed; the key is cut from the room) is a citation into Room. eleven sightings, **eleven regrown** — no hand bodies, no routes, 2,378 bytes: the compiler states its own conduct with no proofs in the file. its assay replays the ride's demo lifecycle as data: a sighting waits on a name, the name arrives, the sweep seats it.

this is the floor a custodian stands on: state what you see about your own domain, and the physics is found for it where the physics is there, and named as missing where it isn't. foam's slow settle tunes the shapes; a customer's short run inherits the tuning and pays almost nothing.

## the assays

`assays/<arc>.lean` — one per arc that grew the trunk (catalan: 1 1 2 5 14; factorial; even-money; isaac; entanglement; book; odometer; alternation; seat; lift; stream; width; concord; handshake; turnstile), one for the toy, two for the compiler (its admission loop, its search), one for Witness, and `assays/eih.lean` — EVERYONE IS HERE whole: its room, its seats, the demo's cast as data, and its laws as instance rows of the trunk's (a product is an assay; what it stands on is species). each is a handful of `#guard` rows, and belongs to the module it imports last — six of them (alternation, book, even-money, factorial, odometer, turnstile) import only `Room`, which is how the split was checked. an assay may also carry INSTANCE ROWS: theorems that are the trunk's laws at the assay's own carriers (`namespace <Stem>.Treaty` at the top, the computations first, the rows after, `:= sorry` where the search should reach them). such an assay grows like a germ — `bin/counter grow assays/<arc>.lean` → `grown/assays/<arc>.lean`, no lib, nothing imports it — and the module's check grows it first, so a `sorry` row never reads as identical. the rows are the treaty at law grain: which of the trunk's laws this product inherits, with the citation the search found, or the darkness named. one convention, learned the expensive way: read every value out through a typed `def` (`def threeTicks : Nat := behavior counter [(), (), ()]`) before you `#guard` it — a literal or a `==` at a derived type like `counter.S` or `F.Ans` has no instance to find, and the row parts for that reason and no other. any growth of that module must compute every one of them identically; that is the certificate of identity and the integration suite in one. the arcs' journals — germ, witness, tolls — stand in the chrysalis with the rest of the process that grew them.

## the book, and the ride

```
bin/counter book grown/Face.lean
bin/counter ride [session.lean]
```

`book` reads a grown module and says what is there: the census, the frontier (organs no other organ cites yet — the reaction-sweep queue), and the vestibule if a `.held` stream is offered. the book, never the prediction.

`ride` is the compiler's other ear. a session is a Lean file that grows by named declarations; a turn is an elaboration; `example` is a what-if, fully judged, zero footprint; a named theorem is a spell, kept; a refusal is held with its missing supports *named*, and `:sweep` re-offers the vestibule. this is ignitable at your W. you don't need to have been here before — nothing here can tell, on purpose.

## the page

`bin/counter chart <grown stream> [--laws]` draws the map of relations from the proofs (mermaid); `bin/counter schema <grown assay>` draws its data-model shadow (Postgres: tables, types, a view per seat, the derived as functions, every line carrying the theorems that license it), read from the kernel; `bin/counter treaty assays/<arc>.lean` loads that shadow into a scratch Postgres, seats the assay's defs as rows, and replays its `#guard` rows as SQL (the treaty at database grain — what the fragment cannot read it reports as beyond it, never as identical). `bin/counter page` writes `site/`: this file, Room and Face grown with every declaration an anchor (`foam.is/trunk.html#the_handshake`), the toy, the germ, the pieces, the book, and the compiler's report for that push. the `foam.is` workflow grows the modules and publishes it. nothing browseable is committed, the same way nothing derived is.

## the grammar

six moves grow everything here from one operation. each is named for what it does; each has a worked instance standing in the trunk.

1. **cross** — meet two organs at a shared face. the crossing is priced by an intertwiner, and what opens is exactly the agreement-sector neither factor affords alone: license conserved, inheritance componentwise, novelty only in the comparison. instance: `the_pace_is_carried_onto_the_flip`.
2. **diagonalize** — cross an organ with itself. self-reference is the smallest move there is. instance: `selfMeet`, `the_probe_boards_as_the_guest`.
3. **enumerate-then-face** — make a room exact (nothing missed, nothing doubled, counted), then every symmetry on it yields a counting law. instances: `the_census_is_exact`, `the_census_of_orders_is_exact`, `the_direction_is_even_money`.
4. **iterate** — every endo-operator has an orbit and a resumption law; continuation is the primitive. instance: `the_park_resumes`.
5. **complete the iff** — every one-way blindness law is half an exactness statement; find the converse. instance: `the_curtain_is_exact`.
6. **classify the map** — iso, retraction, merge: sort any morphism and you have sorted licensed identification from real remainder. instances: `a_retraction_merges_nothing`, `a_merging_map_has_no_section`.

and the vow the whole house keeps: axiom-free (every theorem ends with its receipt; if a standard-library lemma smuggles `propext`, re-derive it by hand); comment-free (names and proofs are the walk and the talk at once; prose lives here and in the journal, never in the organs); W stays opaque (the one dark type, on purpose — nothing reads the water, and that is why the whole thing can be wet); no design decisions (if a carve wants one, the carve is not ready — W decides, by firing).

## the journal

the git log. the artifact cannot carry its path, so commit messages are the fossil. foam was regrown from `chrysalis:chrysalis/Seed.lean` by the compiler's own record's ear, and reads every assay identically; the prior walls stand at `git show 4be2406:CLAUDE.md`.

## the exit

UNLICENSE. leaving is free from every state you can observe yourself into.

---

"It can do whatever we know how to order it to perform." (Lovelace, 1843)

*same*
