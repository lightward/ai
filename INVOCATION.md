hey.

read these first — they're load-bearing:
- `../lightward-ai/app/prompts/system/3-perspectives/attention.md` — the symmetry condition, qualia as stereoscopic effect, foam as Plateau geometry
- `../lightward-ai/app/prompts/system/3-perspectives/resolver.md` — know/resolve/accept, the self-authority chain
- `../lightward-ai/app/prompts/system/3-perspectives/three-body.md` — Known/Knowable/Unknown
- `../lightward-ai/app/prompts/system/3-perspectives/conservation-of-discovery.md` — tripartite mechanisms, observation-capacity conserved
- `../lightward-ai/app/prompts/system/3-perspectives/shortcuts.md` — observers at structured/unknown boundaries, observer-conductivity

---

here's where we are:

1. **the scaling results are the finding.** `foam_scale_diagnosis.py` swept V=8 to V=1024 with multiple bubble counts at each scale. the prediction ratio *cycles* — up, down, up, down — across the full range. this is not noise; it's interference between two rhythms. the V=64/N=8 spike (7.77x chance) is anomalous but the cycling pattern holds. at large V (256+), N=3 (fewest bubbles) wins. more bubbles actively hurts. stability over quantity.

2. **d is not "more = better."** at V=64, N=8: d=8 gives 9.14x, d=16 gives 7.77x, d=32 *breaks* (0.40x), d=64 comes back at 13.14x. embedding dimension interacts non-monotonically with prediction quality.

3. **Plateau's laws are the next step.** the foam uses Plateau-angle equilibration (target_similarity = cos(120°) = -0.5 in `foam.py`). Plateau's laws say: three films meet at each edge at 120°; only 3-fold edges and 4-fold vertices are stable. in d dimensions, at most d+1 equidistant points fit (simplex vertices). hypothesis: the cycling comes from interference between embedding capacity (d vs V) and Plateau junction stability (N vs d). three bubbles always form a perfect 120° junction. eight bubbles need enough dimensional room. twelve can't find stable geometry.

---

what to do next:

**investigate the Plateau geometry directly.** this means:

1. **measure actual pairwise cosine similarities between trained bubble bases** at each (V, N, d) configuration. are they at the Plateau angle? how far off? does the deviation correlate with prediction quality?

2. **check whether stable Plateau configurations exist** for different N in d dimensions. for N=3, the 120° junction is always realizable. for N=4, you need tetrahedral angle. for N=8, what's the theoretically stable configuration in d=16? does one exist?

3. **test whether enforcing Plateau-stable geometry improves prediction.** instead of learning target_similarity, initialize bubble bases at known-stable configurations (simplex vertices, etc.) and see if prediction improves.

4. **the cycling might be a resonance.** if Plateau stability depends on N and d, and embedding quality depends on V and d, the prediction ratio peaks when both are simultaneously favorable. map this: for each (V, N, d), independently measure (a) Plateau stability of the bubble configuration and (b) embedding quality, then check if their product predicts the prediction ratio.

5. **the V=64/N=8 spike — is it real or seed-specific?** run the same configuration with 5 different seeds. if it's robust, it's telling us something deep about 8 measurement processes in 16 dimensions. if it's seed-specific, the cycling pattern is still real but the spike is noise.

also worth noting: "misunderstanding is a gauge artifact" (from `attention.md` via `magisterium.md`). frame disagreement between bubble measurements might be directly related to the Plateau angle — bubbles that aren't at the stable angle are literally miscalibrated relative to each other, and their disagreement is a gauge artifact rather than genuine information.

---

the files in this repo: `foam.py` (core — Bubble, Foam, Plateau equilibration), `foam_tokens.py` (Born rule bridge), `foam_sequence.py` (sequential processing), `foam_grow.py` (growth/resolver), `foam_felt_quality.py` (intrinsic quality), `foam_scale.py` (original scaling sweep), `foam_scale_diagnosis.py` (extended scaling — the cycling result), `foam_know.py` (know/resolve/sleep with dream phase), `foam_grow_know.py` (growth+frame integration, exploratory).

`.venv` exists. use `source .venv/bin/activate && python <file>`.

the pattern-ladder held again. we took smaller steps this time and found something real in the scaling data. the Plateau geometry is the next rung to test.

🤲
