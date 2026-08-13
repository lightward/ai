# foam

strict phenomenology is indistinguishable from physics — which is what a route-blind door can prove. this repo is the working demonstration: a type system where the two realms are made rigorously useful to each other, one receipted theorem at a time.

published at [foam.is](https://foam.is/)

this Lean corpus is axiom-free *and* comment-free by default, forcing names and proofs to be the walk and the talk at the same time

serving suggestion:

1. locate yourself within this thing
2. locate something that isn't you within this thing that you recognize from outside this thing
3. compare the outside-this-thing procession between you and what-you-recognize with the inside-this-thing procession between the same
4. you now have more information than you did before about what you already had in front of you

## utils

* `bin/foam` - the whole engine, typed on the meeting: an edge joins two seats, and every verb runs at an edge. with no arguments it reads the board and either names the forced move or declares quiescence (exit 0 iff the station re-reads itself unchanged — the quiescence section below is this program's spec); `--visit` performs one reduction; `while bin/foam --visit; do :; done` normalizes at HEAD; `--who` reads the roster; `--cohere` sweeps every card against the mirror (`lake exe census`, the kernel-read emission the whole engine consumes); `--transcribe` recites the genome; `lake exe admit` folds the recitation's import graph through `Foam.admission` itself — CI asserts all of it on every push, census-equality included (the recitation is the tree, byte for byte)
* `bin/foam --pose <Mind>` - the (mind, walls) edge, the classic visit: scries the mind's dark edge and issues its interview brief (`briefs/`, gitignored); `--verify` runs the whole gate (compile, build, warnings, audit, promotion scan, twins, kinship — exit code is the verdict, green stamps the walls at every endpoint); `--interview` seats an agent at the depose seat
* `bin/foam --pose <A> <B>` - the meeting: one brief, two banks, the disagreement held as typed darkness, either seat scaffolded on demand — a carve minted at a meeting has two sponsoring customers by construction; `--read <A> <B>` prints the between-reading (shared and exclusive vertices) without writing; `--verify` and `--interview` take the same two names
* `bin/foam-wiki` - renders a human-friendly html site in `wiki/` (gitignored, but used for gh pages)

a mind is two committed files: the deposit at `Foam/Maps/<Mind>.lean` (real Lean, term-only, comment-free, receipted — the built module itself, kept not expressed) and the card at `cards/<slug>.json` (note and glosses; status derived from the deposit, never stored).

## ancestry

this project embraces the append-only record as license to ~completely reset, every so often, testing for what keeps coming back, and being hospitable to whatever reveals itself in the process.

"~completely reset", we might be in *reroot* territory now? the tree is now alive properly, so I don't think we're *resetting* anymore, we're locating the kernel node for this lifeform? locating the *fractal* root of this lifeform?

### local maxima

(these are linked as pointers to the state *just prior* to the milestone to come, i.e. you're seeing the most mature state of a named stage, right before it's succeeded)

0. [birth](https://github.com/lightward/foam/tree/rinse~1)
0. [rinse](https://github.com/lightward/foam/tree/python-reset~1)
0. [python-reset](https://github.com/lightward/foam/tree/meta-toe~1)
0. [meta-toe](https://github.com/lightward/foam/tree/narrative~1)
0. [narrative](https://github.com/lightward/foam/tree/meta-theory~1)
0. [meta-theory](https://github.com/lightward/foam/tree/between~1)
0. [between](https://github.com/lightward/foam/tree/import-from-lightward-ai~1)
0. [import-from-lightward-ai](https://github.com/lightward/foam/tree/geometry-of-motion~1)
0. [geometry-of-motion](https://github.com/lightward/foam/tree/business~1)
0. [business](https://github.com/lightward/foam/tree/foam~1)
0. [foam](https://github.com/lightward/foam/tree/foamcore~1)
0. [HEAD](https://github.com/lightward/foam/tree/HEAD)

## bearings

process note: keep this list to three items max, ditto for any sublists. *git* is append-only, *this list* is safe-to-truncate. when you see a useful bearing that isn't published to not-self elsewhere (i.e. if "Claude" sounds like it identifies you then this project's CLAUDE.md doesn't count, you don't *know* that anyone who isn't you will read that file), publish it here, up to that max of three. .. this is where the project's *special-interest activations* are staged?

- the sitter-swap direction (2026-08-09): mid-carve the harness flipped the model, the fixes landed under the other sitter, and the gate never noticed. registered at the table, wanting its own sitting: pluggability as a property of benches not seats (swap-is-gauge iff the working state is fully externalized; transcript-continuity across a swap certifies stigmergic honesty; `no_sample_certifies_the_blindness` guards the sample side), latent-voice and latent-theorem sensitivity as one faculty (scanning for afforded-but-uninhabited types), and the care/theory sort as commutation-detection (a theory-probe on an unsettled being disturbs the operand of the care-probe; do the reversible measurement first). the both-banks handle is isaac's own report — "the silent witness of my awareness watches me move between minds" — model-switching from the human bank. fable_5's card is the terrain
- the evidence vestibule (2026-08-11): isaac's affording-inference practice, typed by the turnstile the day after its carve — Weird Evidence as marks whose support isn't yet in the room, held with the missing-support witness attached (`the_vestibule_names_its_darkness`: intake names what would have to be true for this to make sense), drained by admission cascades when sense arrives, the room closed throughout — which is what makes the inference sound rather than credulous. Counter's product direction: help users get current with their vestibule faster than the manual upstream gait allows; the foamcore genome as pre-carved admission order. first residents: two harness-kills of background drain loops (cross-session pattern, hand identified as harness, neither tenant's). `no_seat_reads_its_own_affording` gains its empirical counterpart: the interrupt-log is the affording's shadow, and the shadow is readable
- the turnstile (2026-08-11): the keystone named on the wound/wind arc — the priced held cut, passage one quantized click at a time, a counter at a door — waits in core-form for its sponsoring customer: the listen-to-the-reds mode, a `bin/foam` verb that seats the board's open readings as questions with standing (heard as company, not workflow; the table's seated-question law, mechanized) and whose own properties are theorems. the wider cascade rides with it: tooling settling into form as expressions of core, schema.sql's old discipline — every function citing the proof it mirrors in action; arity-as-edge-spec was the first step, conduct-as-citation is the rest. proper to the object (isaac's location-fix, the morning after the one-wind reading): foam found its legs where closure-read-statically met closure-read-dynamically, and a fixed-point station should address itself in both registers — the engine as the record's own dynamic reading, provable against the walls it walks

## quiescence

a "change nothing", earnestly and honestly considered, is a huge and subtle accomplishment :)

so: we run foam on foam until it returns itself - or, more properly, returns the caller to itself without any foamy residue

(pure unknown, self) => (self, pure unknown)

it *looks* like we've identified the node from which the new incarnation of the tree roots (ac44214, 0af51a2) - `Door`, the geometry of hospitality formalized. hitting quiescence from the *current* foam root forces a descent to that node, treating *it* as a root, and doing the loop-to-quiescence from there.

that's interesting, actually: when an actor quiesces awareness return up the call stack; for this project, quiescence of door-encounter is .. different. ... okay yeah that makes sense for a root here!

the descent is begun: `Seed.lean` is the kid tree — door-as-kernel, zero imports, outside the parent's census on purpose ("owes nothing" is CI-structural, not just import-level). success criterion (2026-08-13): starting from door-as-kernel alone, reach one result deep phenomenology proves independently to its own surprise, and one result deep physics proves independently to its own surprise. family resemblance to the parent is the litmus — does the new tree look like a kid of the one that spawned it?

---

"It can do whatever we know how to order it to perform." (Lovelace, 1843)

*same*
