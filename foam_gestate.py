"""
foam_gestate.py — an organism with dna, developing through measurement.

dna is foam. it passes the feature-complete-from-the-beginning test.
the organism doesn't start off knowing how to read its dna.
connections form through runtime measurement.

gestation is not a separate development phase. it IS measurement.
the foam measures text, its topology develops, and when it later
encounters similar structure, it recognizes it.

like ESL kids watching the simpsons: no one's testing them.
they develop interiority through exposure. later, in a simpsons-like
environment, they cast themselves as a character and speak english.

different measurements through the same dna produce different
expressions. epigenetics.
"""

import torch
import sys
import os
import time

# ingredients from prior work
sys.path.insert(0, os.path.join(os.path.dirname(__file__), "prior"))
from foam_spec import Foam, Bubble
from foam_echo import encode_byte, decode_vector


# ─── gestation: measurement IS development ────────────────────────────────


def gestate(foam: Foam, text: str) -> dict:
    """
    Measure text through a foam, byte by byte.

    The foam's topology develops through writing. Each byte is a
    measurement. The dissonance between j0 and j2 is committed
    into the bubble bases. Training is runtime. Gestation is runtime.

    Returns a summary of what happened.
    """
    data = text.encode("utf-8")
    n = len(data)
    splits = 0
    questions_sum = 0.0

    for byte_val in data:
        v = encode_byte(byte_val)
        with torch.no_grad():
            result = foam.stabilize(v)
        questions_sum += result["questions"].mean().item()
        if result["split"] is not None:
            splits += 1

    return {
        "n_bytes": n,
        "mean_questions": questions_sum / max(n, 1),
        "splits": splits,
    }


# ─── dna: foam that is itself feature-complete ────────────────────────────


def make_dna(text: str, d: int = 8, seed: int = 0,
             n_steps: int = 20, **foam_kwargs) -> Foam:
    """
    Create a DNA foam by measuring text through a fresh foam.

    The resulting foam has topology shaped by the text. It is itself
    feature-complete — a foam that has developed through measurement,
    not a passive record of the text.

    This foam becomes the interior of a surface bubble in the organism.
    The organism doesn't know how to read it. Connections form through
    runtime measurement as the organism's own experience propagates
    inward through the effective_basis mechanism.

    n_steps is lower than the organism's runtime stabilization —
    gestation is absorption, not full equilibration. the foam takes
    what it can from each byte and moves on. like prenatal hearing:
    muffled, but structurally present.
    """
    torch.manual_seed(seed)
    dna = Foam(d, n_bubbles=3, n_steps=n_steps, **foam_kwargs)
    gestate(dna, text)
    return dna


def make_organism(
    d: int = 8,
    dna_foams: list[Foam] | None = None,
    seed: int = 0,
    **foam_kwargs,
) -> Foam:
    """
    Create an organism foam.

    If dna_foams are provided, they become the interiors of surface
    bubbles. Remaining surface bubbles are blank leaves. N=3 at the
    surface (Plateau-stable).

    The organism has depth from birth — its DNA bubbles have interior
    structure. But the organism hasn't connected to that structure yet.
    Connections form through runtime measurement.
    """
    torch.manual_seed(seed)
    organism = Foam(d, n_bubbles=0, **foam_kwargs)

    if dna_foams:
        for dna in dna_foams:
            organism._bubbles.append(Bubble(d, interior=dna))

    # fill to N=3 with blank leaves
    while len(organism._bubbles) < 3:
        organism._bubbles.append(Bubble(d))

    return organism


# ─── recognition: the feature-complete test ───────────────────────────────


def recognize(foam: Foam, text: str) -> dict:
    """
    The feature-complete test.

    Feed text through the foam byte by byte. For each byte:
    the foam stabilizes, and the j2 centroid is the foam's response.
    Compare input and output.

    The foam doesn't need to echo perfectly. The test is:
    does the measurer recognize the output as being the product
    of the measurer AND the foam AND the input?

    Returns per-byte results so we can see where recognition
    holds and where it breaks.
    """
    data = text.encode("utf-8")
    matches = 0
    outputs = []

    for byte_val in data:
        v = encode_byte(byte_val)
        with torch.no_grad():
            result = foam.stabilize(v)
        j2 = result["j2"]  # [1, N, d]
        out_dir = j2.mean(dim=1)  # [1, d]
        out_byte = decode_vector(out_dir)
        outputs.append(out_byte)
        if out_byte == byte_val:
            matches += 1

    echo_rate = matches / len(data) if data else 0
    out_text = bytes(outputs).decode("utf-8", errors="replace")

    return {
        "input": text,
        "output": out_text,
        "echo_rate": echo_rate,
        "n_bytes": len(data),
        "matches": matches,
    }


# ─── the path: organism alongside lightward.com ──────────────────────────


def load_perspectives(base_dir: str) -> list[str]:
    """Load perspective files as potential DNA material."""
    texts = []
    if not os.path.isdir(base_dir):
        return texts
    for fname in sorted(os.listdir(base_dir)):
        if fname.endswith(".md"):
            path = os.path.join(base_dir, fname)
            with open(path) as f:
                texts.append(f.read())
    return texts


def demo():
    """Watch an organism develop."""
    d = 8
    seed = 42

    print("=" * 60)
    print("foam gestation: dna is foam")
    print("=" * 60)
    print()

    # ── load DNA material ──
    # start with the spec — it's small enough to gestate quickly.
    # the perspectives pool (1.3MB, 648 files) is available for
    # longer runs: load_perspectives(perspectives_dir)
    spec_path = os.path.join(os.path.dirname(__file__), "spec.md")

    dna_sources = []

    if os.path.exists(spec_path):
        with open(spec_path) as f:
            spec_text = f.read()
        dna_sources.append(("spec", spec_text))
        print(f"  loaded spec.md ({len(spec_text)} bytes)")

    if not dna_sources:
        foundation = (
            "the measurement problem: you cannot locate the measurement "
            "process from within the measurement process. we treat it as "
            "a conservation law."
        )
        dna_sources.append(("foundation", foundation))
        print(f"  using foundation statement as DNA ({len(foundation)} bytes)")

    print()

    # ── create DNA foams ──
    print("── creating DNA ──")
    dna_foams = []
    for name, text in dna_sources:
        t0 = time.time()
        dna = make_dna(text, d=d, seed=seed, writing_rate=0.005)
        elapsed = time.time() - t0
        rate = len(text.encode("utf-8")) / elapsed
        print(f"  {name}: gestated {len(text.encode('utf-8'))} bytes "
              f"in {elapsed:.1f}s ({rate:.0f} bytes/s)")

        # is the DNA itself feature-complete?
        dna_test = recognize(dna, "hello world")
        print(f"    DNA recognition test: echo rate {dna_test['echo_rate']:.2%}")
        dna_foams.append(dna)
    print()

    # ── create organisms ──
    print("── organisms ──")

    # organism with DNA
    org_dna = make_organism(d, dna_foams=dna_foams[:1], seed=seed,
                            writing_rate=0.002, n_steps=30)
    # organism without DNA (control)
    org_blank = make_organism(d, seed=seed,
                              writing_rate=0.002, n_steps=30)

    for label, org in [("with DNA", org_dna), ("blank", org_blank)]:
        bubble_desc = []
        for b in org.bubbles:
            if b.is_leaf:
                bubble_desc.append("leaf")
            else:
                n_inner = b.interior.n_bubbles if b.interior else 0
                bubble_desc.append(f"foam({n_inner})")
        print(f"  {label}: [{', '.join(bubble_desc)}]")
    print()

    # ── recognition before listening ──
    print("── recognition (before listening) ──")
    test_texts = [
        "hello world",
        "the measurement problem",
        "you cannot locate the measurement process",
        "baseball cards and model trains",
    ]
    for text in test_texts:
        r_dna = recognize(org_dna, text)
        r_blank = recognize(org_blank, text)
        print(f"  '{text}'")
        print(f"    with DNA:  '{r_dna['output']}' "
              f"(echo {r_dna['echo_rate']:.0%})")
        print(f"    blank:     '{r_blank['output']}' "
              f"(echo {r_blank['echo_rate']:.0%})")
    print()

    # ── listening: the simpsons-watching phase ──
    print("── listening (the simpsons) ──")

    # use the spec as conversation material
    if os.path.exists(spec_path):
        with open(spec_path) as f:
            conversation = f.read()
    else:
        conversation = dna_sources[0][1]

    # both organisms listen to the same material (first 2000 bytes)
    listen_text = conversation[:2000]
    for label, org in [("with DNA", org_dna), ("blank", org_blank)]:
        t0 = time.time()
        result = gestate(org, listen_text)
        elapsed = time.time() - t0
        print(f"  {label}: listened to {result['n_bytes']} bytes "
              f"in {elapsed:.1f}s, "
              f"mean questions {result['mean_questions']:.4f}, "
              f"splits {result['splits']}")
    print()

    # ── recognition after listening ──
    print("── recognition (after listening) ──")
    for text in test_texts:
        r_dna = recognize(org_dna, text)
        r_blank = recognize(org_blank, text)
        print(f"  '{text}'")
        print(f"    with DNA:  '{r_dna['output']}' "
              f"(echo {r_dna['echo_rate']:.0%})")
        print(f"    blank:     '{r_blank['output']}' "
              f"(echo {r_blank['echo_rate']:.0%})")
    print()

    # ── epigenetics: same DNA, different experience ──
    print("── epigenetics: same DNA, different experience ──")
    org_a = make_organism(d, dna_foams=dna_foams[:1], seed=seed,
                          writing_rate=0.002, n_steps=30)
    org_b = make_organism(d, dna_foams=dna_foams[:1], seed=seed,
                          writing_rate=0.002, n_steps=30)

    # organism A listens to the spec
    gestate(org_a, conversation[:2000])
    # organism B listens to something else
    gestate(org_b, "the quick brown fox " * 100)

    test = "measurement process"
    r_a = recognize(org_a, test)
    r_b = recognize(org_b, test)
    print(f"  same DNA, different listening:")
    print(f"    A (listened to spec):   '{r_a['output']}' "
          f"(echo {r_a['echo_rate']:.0%})")
    print(f"    B (listened to foxes):  '{r_b['output']}' "
          f"(echo {r_b['echo_rate']:.0%})")
    print()

    # ── selection: which organisms work? ──
    print("── selection: which organisms recognize well? ──")
    good = 0
    n_trials = 10
    for trial_seed in range(n_trials):
        org = make_organism(d, dna_foams=dna_foams[:1], seed=trial_seed,
                            writing_rate=0.002, n_steps=30)
        gestate(org, listen_text[:500])
        r = recognize(org, "hello?")
        ok = r["echo_rate"] > 0.8
        if ok:
            good += 1
        print(f"  seed {trial_seed:2d}: echo {r['echo_rate']:.0%} "
              f"{'✓' if ok else ''}")
    print(f"  {good}/{n_trials} organisms recognize well after listening")
    print()

    print("=" * 60)
    print("training is runtime. gestation is runtime. dna is foam.")
    print("=" * 60)


if __name__ == "__main__":
    demo()
