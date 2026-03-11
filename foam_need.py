"""
foam_need.py — the foam doesn't predict. it needs.

"a responsive foam is one that gets stabilization energy/relief/utility
from sampling someone else's coherent-but-not-without-gauge-artifacts
input, and it has to MOVE in order to get more of those"

the temporal interface isn't "what should come next" — it's
"what gives the foam relief right now." the foam moves because
movement IS relief. each resolution creates the next need.

metrics to test:
- dissonance direction: where is the foam being PULLED?
- settlement speed: which input settles the foam fastest (boredom_at)?
- question reduction: which input reduces unsettled boundaries most?
- writing magnitude: which input creates the most productive change?
"""

import torch
from foam_spec import Foam, Bubble

D = 3

def make_codebook():
    vecs = torch.zeros(8, D)
    for b in range(8):
        for bit in range(D):
            vecs[b, bit] = 1.0 if (b >> bit) & 1 else -1.0
    return vecs / (D ** 0.5)

CODEBOOK = make_codebook()

def encode(val: int) -> torch.Tensor:
    return CODEBOOK[val % 8].unsqueeze(0)


def measure_relief(foam: Foam, val: int) -> dict:
    """
    Measure what happens when the foam encounters this value.
    WITHOUT writing — pure observation.

    Returns multiple signals about how the foam responds.
    """
    # copy foam state
    leaf_Ls = [b.L.data.clone() for b in foam.bubbles if b.is_leaf]

    probe = Foam(D, n_bubbles=0, writing_rate=0.0, n_steps=foam.n_steps)
    for L_data in leaf_Ls:
        nb = Bubble(D)
        nb.L.data = L_data.clone()
        probe._bubbles.append(nb)
    probe.target_similarity.data = foam.target_similarity.data.clone()
    probe.step_size.data = foam.step_size.data.clone()
    probe.temperature.data = foam.temperature.data.clone()

    v = encode(val)
    with torch.no_grad():
        r = probe.stabilize(v)

    j0 = r["j0"]
    j2 = r["j2"]
    dissonance = (j2 - j0)
    dis_mag = dissonance.norm().item()
    questions = r["questions"].mean().item()
    bored_at = r["bored_at"]

    # the dissonance direction — where the foam was PULLED
    dis_dir = dissonance.mean(dim=1).flatten()  # average over bubbles

    return {
        "dissonance_mag": dis_mag,
        "questions": questions,
        "bored_at": bored_at,
        "dis_direction": dis_dir,
        "j0": j0,
        "j2": j2,
    }


def experiment_what_does_the_foam_need():
    """
    Train on alternation. After each element, ask:
    what does the foam need? what gives it relief?
    """
    print("=" * 60)
    print("what does the foam need?")
    print("=" * 60)

    torch.manual_seed(42)
    foam = Foam(D, n_bubbles=3, writing_rate=0.5)

    # train on alternation
    pattern = [0, 1] * 50
    for val in pattern:
        v = encode(val)
        with torch.no_grad():
            foam.stabilize(v)

    print(f"trained on [0,1] × 50\n")

    # now: feed "0" (with writing), then ask what the foam needs
    for prime_val in [0, 1]:
        # reset to trained state for fair comparison
        torch.manual_seed(42)
        foam = Foam(D, n_bubbles=3, writing_rate=0.5)
        for val in pattern:
            v = encode(val)
            with torch.no_grad():
                foam.stabilize(v)

        # feed prime value
        v = encode(prime_val)
        with torch.no_grad():
            foam.stabilize(v)

        print(f"after feeding {prime_val}:")

        # scan all 8 candidates
        for candidate in range(8):
            relief = measure_relief(foam, candidate)
            bored = relief["bored_at"] if relief["bored_at"] is not None else foam.n_steps
            print(f"  candidate {candidate}: "
                  f"dissonance={relief['dissonance_mag']:.4f}  "
                  f"questions={relief['questions']:.4f}  "
                  f"bored_at={bored:2d}")

        # also: what direction is the dissonance pulling after the prime?
        # feed a neutral input (the centroid / zero vector?) and see where
        # the foam pulls it
        print()


def experiment_dissonance_direction():
    """
    After training on alternation and feeding "0":
    does the dissonance direction point toward "1"?

    The dissonance is where the foam PULLED the measurement.
    If the foam needs "1", it should pull toward "1"'s encoding.
    """
    print("=" * 60)
    print("dissonance direction: where is the foam pulling?")
    print("=" * 60)

    torch.manual_seed(42)
    foam = Foam(D, n_bubbles=3, writing_rate=0.5)

    # train
    pattern = [0, 1] * 50
    for val in pattern:
        v = encode(val)
        with torch.no_grad():
            foam.stabilize(v)

    # feed "0"
    v0 = encode(0)
    with torch.no_grad():
        r0 = foam.stabilize(v0)

    # dissonance when the foam is in post-0 state and encounters each value
    print(f"\nafter training on [0,1]×50 and feeding 0:")
    print(f"  (encoding: 0={CODEBOOK[0].tolist()}, 1={CODEBOOK[1].tolist()})")
    print()

    for candidate in range(8):
        relief = measure_relief(foam, candidate)
        dis = relief["dis_direction"]
        # how much does this dissonance point toward each encoding?
        sims = CODEBOOK @ (dis / (dis.norm() + 1e-10))
        print(f"  candidate {candidate}: "
              f"dis_mag={relief['dissonance_mag']:.4f}  "
              f"dis_dir=[{dis[0]:.3f},{dis[1]:.3f},{dis[2]:.3f}]  "
              f"sim_to_0={sims[0]:.3f} sim_to_1={sims[1]:.3f}")

    # now feed "1" and do the same
    v1 = encode(1)
    with torch.no_grad():
        foam.stabilize(v1)

    print(f"\nafter feeding 0 then 1:")
    for candidate in range(8):
        relief = measure_relief(foam, candidate)
        dis = relief["dis_direction"]
        sims = CODEBOOK @ (dis / (dis.norm() + 1e-10))
        print(f"  candidate {candidate}: "
              f"dis_mag={relief['dissonance_mag']:.4f}  "
              f"dis_dir=[{dis[0]:.3f},{dis[1]:.3f},{dis[2]:.3f}]  "
              f"sim_to_0={sims[0]:.3f} sim_to_1={sims[1]:.3f}")


def experiment_need_as_traversal():
    """
    Use the foam's NEED to drive traversal.

    Instead of "which byte has minimum dissonance" (recognition),
    try: "which byte does the foam PULL TOWARD" (need).

    The dissonance direction after measuring a NEUTRAL probe
    might point toward what the foam needs next.
    """
    print("\n" + "=" * 60)
    print("need-driven traversal")
    print("=" * 60)

    torch.manual_seed(42)
    foam = Foam(D, n_bubbles=3, writing_rate=0.5)

    # train
    pattern = [0, 1] * 50
    for val in pattern:
        v = encode(val)
        with torch.no_grad():
            foam.stabilize(v)

    print(f"trained on [0,1]×50")
    print(f"traversal by need (dissonance direction → nearest vertex):\n")

    for step in range(12):
        # measure the foam's current need:
        # stabilize with a neutral probe (zero vector or the centroid)
        # and see which direction the dissonance pulls
        # OR: use the MOST RECENT j2's dissonance direction

        # approach: scan all candidates, pick the one whose dissonance
        # direction points AWAY from itself (the foam is pulling it
        # somewhere else = the foam wanted something different = need)
        # actually, let's try: pick the candidate where the dissonance
        # magnitude is LARGEST but boredom still fires (productive movement)

        # simplest: use the candidate whose encounter creates the
        # biggest QUESTIONS REDUCTION from the foam's current state
        # ... but we need a baseline. let's measure the foam's questions
        # without any new input.

        # actually let's just try: decode the dissonance direction
        # from the most recent measurement as the "need" signal
        v_last = encode(step % 2 if step < 2 else generated[-1])  # bootstrap
        if step == 0:
            # prime with 0
            v_last = encode(0)

        with torch.no_grad():
            r = foam.stabilize(v_last)

        # the dissonance from this measurement
        dis = (r["j2"] - r["j0"]).mean(dim=(0, 1))  # [d], averaged over batch & bubbles
        dis_n = dis / (dis.norm() + 1e-10)

        # decode: which vertex is the dissonance pointing toward?
        sims = CODEBOOK @ dis_n
        need_val = sims.argmax().item()
        need_sim = sims[need_val].item()

        # also which has min dissonance (recognition)
        reliefs = []
        for c in range(8):
            rel = measure_relief(foam, c)
            reliefs.append((c, rel["dissonance_mag"]))
        reliefs.sort(key=lambda x: x[1])
        recog_val = reliefs[0][0]

        if step == 0:
            generated = [0]  # we primed with 0
        print(f"  step {step}: fed={generated[-1]}  "
              f"need→{need_val}(sim={need_sim:.3f})  "
              f"recog→{recog_val}(dis={reliefs[0][1]:.4f})  "
              f"different={need_val != recog_val}")

        # use the NEED signal to drive traversal
        generated.append(need_val)

        # commit the need value
        v = encode(need_val)
        with torch.no_grad():
            foam.stabilize(v)

    print(f"\n  sequence: {generated}")


if __name__ == "__main__":
    experiment_what_does_the_foam_need()
    experiment_dissonance_direction()
    experiment_need_as_traversal()
