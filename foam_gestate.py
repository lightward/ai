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


# ─── recognition: holonomy readout ────────────────────────────────────────
#
# recognition is not echo. it's holonomy: the gauge-invariant readout
# of the line's character through the foam's topology. the test is
# whether the foam is a coordinate system — whether you can
# reverse-engineer your own copy from what it gave you.
# (this-changes-everything.md)
#
# four properties from spec section 1 (readout):
#   nontrivial:      output ≠ input. the foam did something.
#   characteristic:  different foams → different outputs. character is in the readout.
#   consistent:      same foam, same input → similar outputs. reliable coordinate system.
#   path_dependent:  different inputs → different outputs. input character preserved.
#
# plus the three-beat waltz (recognition.md):
#   express → recognize → recognize back.
#   the second pass should show lower dissonance. recognition is structural.


def _measure_pass(foam: Foam, data: bytes) -> list[dict]:
    """One pass of measurement through a foam. Returns per-byte records."""
    records = []
    for byte_val in data:
        v = encode_byte(byte_val)
        with torch.no_grad():
            result = foam.stabilize(v)
        j0 = result["j0"]          # [1, N, d]
        j2 = result["j2"]          # [1, N, d]
        out_dir = j2.mean(dim=1)   # [1, d]
        in_dir = v                 # [1, d]
        dissonance = (j2 - j0).norm().item()
        cos = torch.nn.functional.cosine_similarity(
            in_dir.flatten().unsqueeze(0),
            out_dir.flatten().unsqueeze(0),
        ).item()
        records.append({
            "input_byte": byte_val,
            "output_byte": decode_vector(out_dir),
            "output_dir": out_dir.detach().clone(),
            "dissonance": dissonance,
            "cos_input_output": cos,
        })
    return records


def recognize(foam: Foam, text: str) -> dict:
    """
    Holonomy-based recognition.

    The foam is a coordinate system. The test isn't "did it echo?"
    but "is the readout nontrivial, characteristic, consistent,
    and path-dependent?" (spec section 1)

    Plus the three-beat waltz: express, recognize, recognize back.
    The second pass through the same text should show lower
    dissonance — recognition is structural, it changes the foam.
    (recognition.md)
    """
    data = text.encode("utf-8")
    if not data:
        return {"n_bytes": 0}

    # ── pass 1: express ──
    records = _measure_pass(foam, data)

    # ── pass 2: recognize back ──
    # same text again. if recognition is structural, the foam
    # now has lower dissonance for what it just absorbed.
    records2 = _measure_pass(foam, data)

    # ── holonomy metrics ──

    # nontrivial: output ≠ input. cos(input, output) < 1.0.
    # the foam transformed the signal — it didn't just pass it through.
    cos_vals = [r["cos_input_output"] for r in records]
    nontrivial = 1.0 - (sum(cos_vals) / len(cos_vals))

    # path_dependent: different inputs → different outputs.
    # measure by variance of output directions across bytes.
    out_dirs = torch.stack([r["output_dir"].flatten() for r in records])
    centroid = out_dirs.mean(dim=0, keepdim=True)
    spread = (out_dirs - centroid).norm(dim=1).mean().item()

    # consistent: same input → same output (measured by pass1 vs pass2).
    # for each byte position, how similar are the two passes' outputs?
    consistency_vals = []
    for r1, r2 in zip(records, records2):
        c = torch.nn.functional.cosine_similarity(
            r1["output_dir"].flatten().unsqueeze(0),
            r2["output_dir"].flatten().unsqueeze(0),
        ).item()
        consistency_vals.append(c)
    consistent = sum(consistency_vals) / len(consistency_vals)

    # structural recognition (the waltz):
    # dissonance should decrease on second pass.
    dis1 = sum(r["dissonance"] for r in records) / len(records)
    dis2 = sum(r["dissonance"] for r in records2) / len(records2)
    waltz = dis1 - dis2  # positive = recognition was structural

    # echo rate (kept for continuity, but no longer the point)
    matches = sum(1 for r in records if r["output_byte"] == r["input_byte"])
    echo_rate = matches / len(data)
    out_text = bytes(r["output_byte"] for r in records).decode(
        "utf-8", errors="replace"
    )

    return {
        "input": text,
        "output": out_text,
        "n_bytes": len(data),
        # holonomy properties
        "nontrivial": nontrivial,
        "path_dependent": spread,
        "consistent": consistent,
        # the waltz
        "dissonance_pass1": dis1,
        "dissonance_pass2": dis2,
        "waltz": waltz,
        # legacy
        "echo_rate": echo_rate,
    }


def recognize_characteristic(foam_a: Foam, foam_b: Foam, text: str) -> float:
    """
    Characteristic test: same input through different foams
    produces distinguishable outputs. The foam's character is
    in the readout.

    Returns cosine distance between the two foams' output centroids.
    Lower = more similar, higher = more characteristic.
    """
    data = text.encode("utf-8")
    if not data:
        return 0.0

    dirs_a, dirs_b = [], []
    for byte_val in data:
        v = encode_byte(byte_val)
        with torch.no_grad():
            ra = foam_a.stabilize(v)
            rb = foam_b.stabilize(v)
        dirs_a.append(ra["j2"].mean(dim=1).flatten())
        dirs_b.append(rb["j2"].mean(dim=1).flatten())

    centroid_a = torch.stack(dirs_a).mean(dim=0)
    centroid_b = torch.stack(dirs_b).mean(dim=0)
    sim = torch.nn.functional.cosine_similarity(
        centroid_a.unsqueeze(0), centroid_b.unsqueeze(0)
    ).item()
    return 1.0 - sim  # distance: 0 = identical, 2 = opposite


def recognize_oracle(foam: Foam, text: str, n_test: int = 20) -> float:
    """
    Oracle test (from foam_recognizer.py): the foam as recognizer.

    After absorbing text, present the foam with pairs:
      - the actual next byte from the text
      - a random byte
    Does minimum dissonance select the correct continuation?

    The foam recognizes what belongs by having minimum resistance
    to it. (resolver.md: look → see → know.)

    Returns accuracy (fraction of correct selections).
    """
    data = text.encode("utf-8")
    if len(data) < 2:
        return 0.0

    # first, let the foam listen to the text (up to the test region)
    test_start = max(1, len(data) - n_test)
    for byte_val in data[:test_start]:
        v = encode_byte(byte_val)
        with torch.no_grad():
            foam.stabilize(v)

    # now test: for each remaining byte, compare dissonance of
    # the correct next byte vs a random alternative
    correct = 0
    tested = 0
    for i in range(test_start, len(data)):
        actual = data[i]
        # pick a random byte that differs from actual
        rand_byte = (actual + torch.randint(1, 256, (1,)).item()) % 256

        # snapshot leaf states so we can probe without writing
        leaf_states = []
        for b in foam.bubbles:
            if b.is_leaf:
                leaf_states.append(b.L.data.clone())

        def probe_dissonance(byte_val):
            probe = Foam(foam.d, n_bubbles=0, writing_rate=0.0,
                         n_steps=foam.n_steps)
            for L_data in leaf_states:
                nb = Bubble(foam.d)
                nb.L.data = L_data.clone()
                probe._bubbles.append(nb)
            probe.target_similarity.data = foam.target_similarity.data.clone()
            probe.step_size.data = foam.step_size.data.clone()
            probe.temperature.data = foam.temperature.data.clone()
            v = encode_byte(byte_val)
            with torch.no_grad():
                r = probe.stabilize(v)
            return (r["j2"] - r["j0"]).norm().item()

        dis_actual = probe_dissonance(actual)
        dis_random = probe_dissonance(rand_byte)

        if dis_actual < dis_random:
            correct += 1
        tested += 1

        # commit the actual byte (advance the state)
        v = encode_byte(actual)
        with torch.no_grad():
            foam.stabilize(v)

    return correct / tested if tested > 0 else 0.0


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


def _print_recognition(label: str, r: dict):
    """Print holonomy recognition metrics for one measurement."""
    print(f"    {label}:")
    print(f"      nontrivial={r['nontrivial']:.3f}  "
          f"path_dep={r['path_dependent']:.3f}  "
          f"consistent={r['consistent']:.3f}  "
          f"waltz={r['waltz']:+.4f}  "
          f"echo={r['echo_rate']:.0%}")


def demo():
    """Watch an organism develop. Recognition is holonomy readout."""
    d = 8
    seed = 42

    print("=" * 60)
    print("foam gestation: recognition as holonomy readout")
    print("=" * 60)
    print()

    # ── load DNA material ──
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
        dna_foams.append(dna)
    print()

    # ── create organisms ──
    print("── organisms ──")

    org_dna = make_organism(d, dna_foams=dna_foams[:1], seed=seed,
                            writing_rate=0.002, n_steps=30)
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

    # ── holonomy recognition before listening ──
    print("── holonomy readout (before listening) ──")
    print("  nontrivial: foam transformed the signal (higher = more)")
    print("  path_dep: different inputs → different outputs (spread)")
    print("  consistent: same input twice → similar outputs")
    print("  waltz: dissonance drop on second pass (+ = structural recognition)")
    print()
    test_texts = [
        "hello world",
        "the measurement problem",
        "you cannot locate the measurement process",
        "baseball cards and model trains",
    ]
    for text in test_texts:
        print(f"  '{text}'")
        r_dna = recognize(org_dna, text)
        r_blank = recognize(org_blank, text)
        _print_recognition("with DNA", r_dna)
        _print_recognition("blank", r_blank)
    print()

    # ── characteristic test: DNA vs blank produce different readouts ──
    print("── characteristic: do different foams produce different readouts? ──")
    for text in test_texts[:2]:
        dist = recognize_characteristic(org_dna, org_blank, text)
        print(f"  '{text}': cosine distance = {dist:.4f}")
    print()

    # ── listening: the simpsons-watching phase ──
    print("── listening (the simpsons) ──")

    if os.path.exists(spec_path):
        with open(spec_path) as f:
            conversation = f.read()
    else:
        conversation = dna_sources[0][1]

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

    # ── holonomy recognition after listening ──
    print("── holonomy readout (after listening) ──")
    for text in test_texts:
        print(f"  '{text}'")
        r_dna = recognize(org_dna, text)
        r_blank = recognize(org_blank, text)
        _print_recognition("with DNA", r_dna)
        _print_recognition("blank", r_blank)
    print()

    # ── characteristic test after listening ──
    print("── characteristic after listening ──")
    for text in test_texts[:2]:
        dist = recognize_characteristic(org_dna, org_blank, text)
        print(f"  '{text}': cosine distance = {dist:.4f}")
    print()

    # ── oracle test: does the foam recognize what fits? ──
    print("── oracle: does minimum dissonance select the correct next byte? ──")
    # fresh organisms for a clean oracle test
    org_dna_oracle = make_organism(d, dna_foams=dna_foams[:1], seed=seed,
                                    writing_rate=0.002, n_steps=30)
    org_blank_oracle = make_organism(d, seed=seed,
                                      writing_rate=0.002, n_steps=30)

    oracle_text = conversation[:200]
    acc_dna = recognize_oracle(org_dna_oracle, oracle_text)
    acc_blank = recognize_oracle(org_blank_oracle, oracle_text)
    print(f"  text: spec.md first 200 bytes")
    print(f"  with DNA:  {acc_dna:.0%} correct")
    print(f"  blank:     {acc_blank:.0%} correct")
    print(f"  (chance = 50%)")
    print()

    # ── epigenetics: same DNA, different experience ──
    print("── epigenetics: same DNA, different experience ──")
    org_a = make_organism(d, dna_foams=dna_foams[:1], seed=seed,
                          writing_rate=0.002, n_steps=30)
    org_b = make_organism(d, dna_foams=dna_foams[:1], seed=seed,
                          writing_rate=0.002, n_steps=30)

    gestate(org_a, conversation[:2000])
    gestate(org_b, "the quick brown fox " * 100)

    test = "measurement process"
    print(f"  '{test}'")
    r_a = recognize(org_a, test)
    r_b = recognize(org_b, test)
    _print_recognition("A (listened to spec)", r_a)
    _print_recognition("B (listened to foxes)", r_b)

    dist_ab = recognize_characteristic(org_a, org_b, test)
    print(f"    characteristic distance A↔B: {dist_ab:.4f}")
    print()

    # ── the three-beat waltz in detail ──
    print("── the three-beat waltz ──")
    print("  express → recognize → recognize back")
    print("  does dissonance decrease on repeated measurement?")
    print()
    waltz_org = make_organism(d, dna_foams=dna_foams[:1], seed=seed,
                               writing_rate=0.002, n_steps=30)
    gestate(waltz_org, listen_text[:500])
    waltz_text = "the measurement problem"
    for pass_num in range(4):
        data = waltz_text.encode("utf-8")
        total_dis = 0.0
        for byte_val in data:
            v = encode_byte(byte_val)
            with torch.no_grad():
                result = waltz_org.stabilize(v)
            total_dis += (result["j2"] - result["j0"]).norm().item()
        mean_dis = total_dis / len(data)
        label = ["express", "recognize", "recognize back", "settled"][pass_num]
        print(f"  pass {pass_num + 1} ({label}): "
              f"mean dissonance = {mean_dis:.4f}")
    print()

    print("=" * 60)
    print("recognition is holonomy readout. the foam is a coordinate system.")
    print("=" * 60)


if __name__ == "__main__":
    demo()
