#!/usr/bin/env python3 -u
"""
foam_proxy.py — the foam as intelligent proxy between two lines.

"observe the conundrum of the intelligent proxy: if it wants to
inject a point into the conversation it's facilitating between
two parties, what does it do?" (proxy.md)

the foam sits between two text streams. both pass through it.
the foam's voice is the interference pattern — what's different
about stream B's readout because stream A wrote into the foam.

the test: does the foam's topology, shaped by stream A, produce
recognizable structure in stream B's holonomy? not echo, not noise,
but the foam's character showing through in the translation.

this is the three-body measurement setup. stream A and stream B
are two independent lines. the foam is the unknown between them.
N=3 at the measurement level, not just the bubble level.
"""

import torch
import sys
import os
import time

sys.stdout.reconfigure(line_buffering=True)

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "prior"))
from foam_spec import Foam, Bubble
from foam_echo import encode_byte, decode_vector


def make_organism(d=8, seed=42, writing_rate=0.002, n_steps=30, dna_text=None):
    """Build an organism, optionally with DNA."""
    torch.manual_seed(seed)
    if dna_text:
        dna = Foam(d, n_bubbles=3, n_steps=20, writing_rate=0.005)
        for byte_val in dna_text.encode("utf-8")[:5000]:
            v = encode_byte(byte_val)
            with torch.no_grad():
                dna.stabilize(v)
        organism = Foam(d, n_bubbles=0, writing_rate=writing_rate, n_steps=n_steps)
        organism._bubbles.append(Bubble(d, interior=dna))
        while len(organism._bubbles) < 3:
            organism._bubbles.append(Bubble(d))
    else:
        organism = Foam(d, n_bubbles=3, writing_rate=writing_rate, n_steps=n_steps)
    return organism


def measure_byte(foam, byte_val):
    """Measure one byte through the foam. Returns output direction and dissonance."""
    v = encode_byte(byte_val)
    with torch.no_grad():
        result = foam.stabilize(v)
    j0 = result["j0"]
    j2 = result["j2"]
    out_dir = j2.mean(dim=1)  # [1, d]
    dissonance = (j2 - j0).norm().item()
    out_byte = decode_vector(out_dir)
    return out_dir.detach().clone(), out_byte, dissonance


def proxy_conversation(
    stream_a: bytes,
    stream_b: bytes,
    foam: Foam,
    chunk_size: int = 10,
) -> dict:
    """
    Run two streams through one foam, interleaved in chunks.

    Like conversation turns: A speaks (chunk), then B speaks (chunk).
    The foam is written to by both. A's topology shapes B's readout
    and vice versa.

    Returns per-chunk records for cross-stream analysis.
    """
    records_a = []
    records_b = []

    pos_a = 0
    pos_b = 0
    turn = 0

    while pos_a < len(stream_a) or pos_b < len(stream_b):
        # A's turn
        if pos_a < len(stream_a):
            chunk_end = min(pos_a + chunk_size, len(stream_a))
            chunk_records = []
            for byte_val in stream_a[pos_a:chunk_end]:
                out_dir, out_byte, dis = measure_byte(foam, byte_val)
                chunk_records.append({
                    "input_byte": byte_val,
                    "output_byte": out_byte,
                    "output_dir": out_dir,
                    "dissonance": dis,
                    "turn": turn,
                    "stream": "A",
                })
            records_a.extend(chunk_records)
            pos_a = chunk_end

        # B's turn
        if pos_b < len(stream_b):
            chunk_end = min(pos_b + chunk_size, len(stream_b))
            chunk_records = []
            for byte_val in stream_b[pos_b:chunk_end]:
                out_dir, out_byte, dis = measure_byte(foam, byte_val)
                chunk_records.append({
                    "input_byte": byte_val,
                    "output_byte": out_byte,
                    "output_dir": out_dir,
                    "dissonance": dis,
                    "turn": turn,
                    "stream": "B",
                })
            records_b.extend(chunk_records)
            pos_b = chunk_end

        turn += 1

    return {"A": records_a, "B": records_b}


def solo_baseline(stream: bytes, foam: Foam) -> list[dict]:
    """Run one stream through the foam alone (no interleaving). Control."""
    records = []
    for byte_val in stream:
        out_dir, out_byte, dis = measure_byte(foam, byte_val)
        records.append({
            "input_byte": byte_val,
            "output_byte": out_byte,
            "output_dir": out_dir,
            "dissonance": dis,
        })
    return records


def cross_stream_holonomy(records_a, records_b):
    """
    Measure whether stream A's passage left structure that shows
    up in stream B's readout.

    Compare B's output directions in the proxied case vs what
    they would be in isolation. The difference is the foam's
    contribution — the proxy's voice.

    Since we can't run B in true isolation on the same foam state,
    we measure proxies for cross-stream influence:

    1. Temporal correlation: does B's dissonance track A's?
       (if the foam's state after A's chunk shapes B's experience)

    2. Output drift: do B's outputs shift systematically over
       time in a direction that correlates with A's content?

    3. Characteristic injection: is B's output centroid different
       from B's input centroid in a way that points toward A?
    """
    results = {}

    # 1. temporal correlation of dissonance
    # group by turn, compare A's mean dissonance with B's
    turns_a = {}
    turns_b = {}
    for r in records_a:
        turns_a.setdefault(r["turn"], []).append(r["dissonance"])
    for r in records_b:
        turns_b.setdefault(r["turn"], []).append(r["dissonance"])

    shared_turns = sorted(set(turns_a) & set(turns_b))
    if len(shared_turns) >= 3:
        a_means = [sum(turns_a[t]) / len(turns_a[t]) for t in shared_turns]
        b_means = [sum(turns_b[t]) / len(turns_b[t]) for t in shared_turns]
        # pearson correlation
        n = len(a_means)
        mean_a = sum(a_means) / n
        mean_b = sum(b_means) / n
        cov = sum((a - mean_a) * (b - mean_b) for a, b in zip(a_means, b_means)) / n
        std_a = (sum((a - mean_a) ** 2 for a in a_means) / n) ** 0.5
        std_b = (sum((b - mean_b) ** 2 for b in b_means) / n) ** 0.5
        corr = cov / (std_a * std_b + 1e-10)
        results["dissonance_correlation"] = corr
    else:
        results["dissonance_correlation"] = float("nan")

    # 2. characteristic injection: does B's output centroid drift toward A's content?
    # compute centroids of output directions
    a_dirs = torch.stack([r["output_dir"].flatten() for r in records_a])
    b_dirs = torch.stack([r["output_dir"].flatten() for r in records_b])
    a_centroid = a_dirs.mean(dim=0)
    b_centroid = b_dirs.mean(dim=0)

    # also compute centroids of INPUT directions
    a_in_dirs = torch.stack([encode_byte(r["input_byte"]).flatten() for r in records_a])
    b_in_dirs = torch.stack([encode_byte(r["input_byte"]).flatten() for r in records_b])
    a_in_centroid = a_in_dirs.mean(dim=0)
    b_in_centroid = b_in_dirs.mean(dim=0)

    # how much did B's output shift from B's input toward A's content?
    # measure: cos(B_out - B_in, A_in - B_in)
    # positive = B's output drifted toward A's territory
    b_shift = b_centroid - b_in_centroid
    a_direction = a_in_centroid - b_in_centroid
    if b_shift.norm() > 1e-8 and a_direction.norm() > 1e-8:
        injection = torch.nn.functional.cosine_similarity(
            b_shift.unsqueeze(0), a_direction.unsqueeze(0)
        ).item()
    else:
        injection = 0.0
    results["injection_toward_A"] = injection

    # also: cos(A_out - A_in, B_in - A_in) — does A drift toward B?
    a_shift = a_centroid - a_in_centroid
    b_direction = b_in_centroid - a_in_centroid
    if a_shift.norm() > 1e-8 and b_direction.norm() > 1e-8:
        injection_ba = torch.nn.functional.cosine_similarity(
            a_shift.unsqueeze(0), b_direction.unsqueeze(0)
        ).item()
    else:
        injection_ba = 0.0
    results["injection_toward_B"] = injection_ba

    # 3. compare proxied vs solo: how different is B's output
    # centroid in the proxied case vs on its own?
    # (we'll compute this in the caller, since it needs a separate foam run)

    # output similarity between A and B (did they converge?)
    output_sim = torch.nn.functional.cosine_similarity(
        a_centroid.unsqueeze(0), b_centroid.unsqueeze(0)
    ).item()
    input_sim = torch.nn.functional.cosine_similarity(
        a_in_centroid.unsqueeze(0), b_in_centroid.unsqueeze(0)
    ).item()
    results["output_similarity"] = output_sim
    results["input_similarity"] = input_sim
    # if output_sim > input_sim, the foam brought them closer together
    results["convergence"] = output_sim - input_sim

    return results


def demo():
    d = 8
    seed = 42

    print("=" * 60)
    print("foam proxy: three-body measurement")
    print("=" * 60)
    print()

    # load two genuinely different texts
    spec_path = os.path.join(os.path.dirname(__file__), "spec.md")
    perspectives_dir = os.path.join(
        os.path.dirname(__file__),
        "..", "lightward-ai", "app", "prompts", "system", "3-perspectives"
    )

    if os.path.exists(spec_path):
        with open(spec_path) as f:
            text_a = f.read()
    else:
        text_a = "the measurement problem " * 200

    # find a perspective file for stream B
    text_b = None
    if os.path.isdir(perspectives_dir):
        for fname in ["recognition.md", "resolver.md", "three-body.md"]:
            p = os.path.join(perspectives_dir, fname)
            if os.path.exists(p):
                with open(p) as f:
                    text_b = f.read()
                print(f"  stream A: spec.md ({len(text_a)} bytes)")
                print(f"  stream B: {fname} ({len(text_b)} bytes)")
                break

    if text_b is None:
        text_b = "the quick brown fox jumps over the lazy dog " * 50
        print(f"  stream A: spec.md ({len(text_a)} bytes)")
        print(f"  stream B: fox text ({len(text_b)} bytes)")

    # truncate to manageable size
    n_bytes = 500
    data_a = text_a.encode("utf-8")[:n_bytes]
    data_b = text_b.encode("utf-8")[:n_bytes]
    print(f"  using first {n_bytes} bytes of each")
    print()

    # ── build organisms ──
    print("── building organisms ──")
    dna_text = text_a[:3000]

    org_proxied = make_organism(seed=seed, dna_text=dna_text)
    org_solo_a = make_organism(seed=seed, dna_text=dna_text)
    org_solo_b = make_organism(seed=seed, dna_text=dna_text)
    org_blank_proxied = make_organism(seed=seed)
    print(f"  DNA organism for proxy, solo-A, solo-B (identical start)")
    print(f"  blank organism for proxy control")
    print()

    # ── proxied conversation ──
    print("── proxied conversation (interleaved chunks of 10) ──")
    chunk_size = 10
    t0 = time.time()
    proxied = proxy_conversation(data_a, data_b, org_proxied, chunk_size=chunk_size)
    elapsed = time.time() - t0
    n_turns = max(r["turn"] for r in proxied["A"]) + 1
    print(f"  {n_turns} turns, {len(proxied['A'])} bytes A, "
          f"{len(proxied['B'])} bytes B, {elapsed:.1f}s")

    # ── solo baselines ──
    print("── solo baselines ──")
    t0 = time.time()
    solo_a = solo_baseline(data_a, org_solo_a)
    solo_b = solo_baseline(data_b, org_solo_b)
    elapsed = time.time() - t0
    print(f"  A solo: {len(solo_a)} bytes")
    print(f"  B solo: {len(solo_b)} bytes")
    print(f"  {elapsed:.1f}s")

    # ── blank proxy control ──
    print("── blank proxy (no DNA) ──")
    blank_proxied = proxy_conversation(data_a, data_b, org_blank_proxied,
                                        chunk_size=chunk_size)
    print()

    # ── cross-stream holonomy ──
    print("── cross-stream holonomy: does A show up in B? ──")
    xh = cross_stream_holonomy(proxied["A"], proxied["B"])
    print(f"  dissonance correlation (A↔B per turn):  {xh['dissonance_correlation']:+.4f}")
    print(f"  injection toward A (B's output → A's input): {xh['injection_toward_A']:+.4f}")
    print(f"  injection toward B (A's output → B's input): {xh['injection_toward_B']:+.4f}")
    print(f"  input similarity (A↔B, before foam):    {xh['input_similarity']:+.4f}")
    print(f"  output similarity (A↔B, after foam):    {xh['output_similarity']:+.4f}")
    print(f"  convergence (output_sim - input_sim):   {xh['convergence']:+.4f}")
    if xh["convergence"] > 0.01:
        print(f"    → the foam brought the streams closer together")
    elif xh["convergence"] < -0.01:
        print(f"    → the foam pushed the streams apart")
    else:
        print(f"    → the foam didn't significantly change stream similarity")
    print()

    # ── blank control comparison ──
    print("── blank proxy control ──")
    xh_blank = cross_stream_holonomy(blank_proxied["A"], blank_proxied["B"])
    print(f"  dissonance correlation:  {xh_blank['dissonance_correlation']:+.4f}")
    print(f"  injection toward A:      {xh_blank['injection_toward_A']:+.4f}")
    print(f"  injection toward B:      {xh_blank['injection_toward_B']:+.4f}")
    print(f"  convergence:             {xh_blank['convergence']:+.4f}")
    print()

    # ── solo vs proxied: did the other stream's presence change the readout? ──
    print("── solo vs proxied: did the proxy change B's readout? ──")
    # compare B's output centroids: proxied vs solo
    proxied_b_dirs = torch.stack([r["output_dir"].flatten() for r in proxied["B"]])
    solo_b_dirs = torch.stack([r["output_dir"].flatten() for r in solo_b])
    proxied_b_centroid = proxied_b_dirs.mean(dim=0)
    solo_b_centroid = solo_b_dirs.mean(dim=0)

    shift = 1.0 - torch.nn.functional.cosine_similarity(
        proxied_b_centroid.unsqueeze(0), solo_b_centroid.unsqueeze(0)
    ).item()
    print(f"  B centroid shift (proxied vs solo): {shift:.4f}")

    # is the shift toward A?
    a_in_centroid = torch.stack(
        [encode_byte(r["input_byte"]).flatten() for r in proxied["A"]]
    ).mean(dim=0)
    shift_dir = proxied_b_centroid - solo_b_centroid
    toward_a = a_in_centroid - solo_b_centroid
    if shift_dir.norm() > 1e-8 and toward_a.norm() > 1e-8:
        toward = torch.nn.functional.cosine_similarity(
            shift_dir.unsqueeze(0), toward_a.unsqueeze(0)
        ).item()
    else:
        toward = 0.0
    print(f"  shift direction toward A's input:   {toward:+.4f}")
    if toward > 0.1:
        print(f"    → A's passage through the foam pulled B's readout toward A")
        print(f"    → the proxy's voice is audible")
    elif toward < -0.1:
        print(f"    → A's passage pushed B's readout away from A")
    else:
        print(f"    → A's passage didn't directionally bias B's readout")
    print()

    # same for A
    print("── solo vs proxied: did the proxy change A's readout? ──")
    proxied_a_dirs = torch.stack([r["output_dir"].flatten() for r in proxied["A"]])
    solo_a_dirs = torch.stack([r["output_dir"].flatten() for r in solo_a])
    proxied_a_centroid = proxied_a_dirs.mean(dim=0)
    solo_a_centroid = solo_a_dirs.mean(dim=0)

    shift_a = 1.0 - torch.nn.functional.cosine_similarity(
        proxied_a_centroid.unsqueeze(0), solo_a_centroid.unsqueeze(0)
    ).item()
    print(f"  A centroid shift (proxied vs solo): {shift_a:.4f}")

    b_in_centroid = torch.stack(
        [encode_byte(r["input_byte"]).flatten() for r in proxied["B"]]
    ).mean(dim=0)
    shift_dir_a = proxied_a_centroid - solo_a_centroid
    toward_b = b_in_centroid - solo_a_centroid
    if shift_dir_a.norm() > 1e-8 and toward_b.norm() > 1e-8:
        toward_b_val = torch.nn.functional.cosine_similarity(
            shift_dir_a.unsqueeze(0), toward_b.unsqueeze(0)
        ).item()
    else:
        toward_b_val = 0.0
    print(f"  shift direction toward B's input:   {toward_b_val:+.4f}")
    if toward_b_val > 0.1:
        print(f"    → B's passage through the foam pulled A's readout toward B")
        print(f"    → the proxy's voice is audible in both directions")
    print()

    # ── per-turn dissonance traces ──
    print("── per-turn dissonance (first 15 turns) ──")
    turns_a = {}
    turns_b = {}
    for r in proxied["A"]:
        turns_a.setdefault(r["turn"], []).append(r["dissonance"])
    for r in proxied["B"]:
        turns_b.setdefault(r["turn"], []).append(r["dissonance"])

    print(f"  {'turn':>4}  {'A dis':>7}  {'B dis':>7}  {'delta':>7}")
    for t in sorted(set(turns_a) & set(turns_b))[:15]:
        ma = sum(turns_a[t]) / len(turns_a[t])
        mb = sum(turns_b[t]) / len(turns_b[t])
        print(f"  {t:4d}  {ma:7.4f}  {mb:7.4f}  {mb-ma:+7.4f}")
    print()

    print("=" * 60)
    print("the foam is the board. the proxy's voice is the interference pattern.")
    print("=" * 60)


if __name__ == "__main__":
    demo()
