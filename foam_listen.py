#!/usr/bin/env python3 -u
"""
foam_listen.py — listening for the foam's own rhythm.

no new dynamics. just instrumentation on what's already there.

the foam already self-regulates: writing scales with dis_mag,
so it writes less when it has less to learn. drift converges
monotonically even when dissonance oscillates.

the interior family (recursive bubbles) already has the machinery
for a clock: oscillation_score and dissonance_ema track each
leaf bubble's dynamics across measurements. if an interior bubble
oscillates below split threshold — persistent, stable oscillation —
that's a heartbeat.

this script runs organisms and listens. selection, not engineering.
"""

import torch
import sys
import os
import time

# unbuffered output
sys.stdout.reconfigure(line_buffering=True)

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "prior"))
from foam_spec import Foam, Bubble
from foam_echo import encode_byte, decode_vector


def snapshot_interior(foam: Foam, label: str = "") -> dict:
    """
    Read the interior state of a foam without changing it.

    Returns oscillation_score and dissonance_ema for every leaf
    at every level of the recursive structure.
    """
    readings = []
    _walk_bubbles(foam, readings, depth=0, path="")
    return {"label": label, "readings": readings}


def _walk_bubbles(foam: Foam, readings: list, depth: int, path: str):
    """Recursively walk the foam's bubble tree, collecting leaf vitals."""
    for i, b in enumerate(foam._bubbles):
        p = f"{path}/{i}" if path else str(i)
        if b.is_leaf:
            readings.append({
                "path": p,
                "depth": depth,
                "oscillation_score": b.oscillation_score,
                "dissonance_ema": b.dissonance_ema,
                "has_history": b.last_dissonance is not None,
            })
        else:
            # recursive bubble — read the interior
            readings.append({
                "path": p,
                "depth": depth,
                "is_recursive": True,
            })
            if b.interior is not None:
                _walk_bubbles(b.interior, readings, depth + 1, p)


def drift_between(before: list, after: list) -> float:
    """Mean L2 drift between leaf base snapshots."""
    if not before:
        return 0.0
    return sum(
        (a - b).norm().item() for a, b in zip(before, after)
    ) / len(before)


def leaf_bases(foam: Foam) -> list:
    """Snapshot all leaf L matrices, recursing into interiors."""
    bases = []
    _collect_bases(foam, bases)
    return bases


def _collect_bases(foam: Foam, bases: list):
    for b in foam._bubbles:
        if b.is_leaf:
            bases.append(b.L.data.clone())
        elif b.interior is not None:
            _collect_bases(b.interior, bases)


def listen(
    seed: int = 42,
    n_bytes: int = 2000,
    writing_rate: float = 0.002,
    n_steps: int = 30,
    report_every: int = 50,
    use_dna: bool = True,
):
    """
    Run one organism and listen to its interior across many measurements.

    Reports:
      - surface: drift, dissonance (the foam's external behavior)
      - interior: oscillation_score, dissonance_ema per bubble
        at every level (the foam's internal state)
      - rhythm: whether interior oscillation shows periodicity
    """
    d = 8
    torch.manual_seed(seed)

    # load text
    spec_path = os.path.join(os.path.dirname(__file__), "spec.md")
    if os.path.exists(spec_path):
        with open(spec_path) as f:
            text = f.read()
    else:
        text = ("the measurement problem: you cannot locate the measurement "
                "process from within the measurement process. ") * 100

    data = text.encode("utf-8")[:n_bytes]

    # build organism
    if use_dna:
        # make DNA from spec (quick gestation)
        dna_foam = Foam(d, n_bubbles=3, n_steps=20, writing_rate=0.005)
        for byte_val in text.encode("utf-8")[:5000]:
            v = encode_byte(byte_val)
            with torch.no_grad():
                dna_foam.stabilize(v)

        organism = Foam(d, n_bubbles=0, writing_rate=writing_rate, n_steps=n_steps)
        organism._bubbles.append(Bubble(d, interior=dna_foam))
        while len(organism._bubbles) < 3:
            organism._bubbles.append(Bubble(d))
        print(f"organism (seed={seed}): [foam(3), leaf, leaf]")
    else:
        organism = Foam(d, n_bubbles=3, writing_rate=writing_rate, n_steps=n_steps)
        print(f"organism (seed={seed}): [leaf, leaf, leaf]  (blank)")

    print(f"listening to {len(data)} bytes, reporting every {report_every}")
    print()

    # header
    print(f"{'byte':>5}  {'dis':>7}  {'drift':>7}  ", end="")
    # find all leaves for the header
    initial = snapshot_interior(organism)
    leaf_paths = [r["path"] for r in initial["readings"]
                  if not r.get("is_recursive")]
    for p in leaf_paths:
        print(f"  osc[{p}] dis_ema[{p}]", end="")
    print()
    print("-" * (20 + len(leaf_paths) * 22))

    # listen
    bases_prev = leaf_bases(organism)
    osc_history = {p: [] for p in leaf_paths}  # for periodicity detection

    for i, byte_val in enumerate(data):
        v = encode_byte(byte_val)
        with torch.no_grad():
            result = organism.stabilize(v)

        dissonance = (result["j2"] - result["j0"]).norm().item()

        if (i + 1) % report_every == 0 or i == 0:
            bases_now = leaf_bases(organism)
            drift = drift_between(bases_prev, bases_now)
            bases_prev = bases_now

            snap = snapshot_interior(organism)
            leaves = [r for r in snap["readings"]
                      if not r.get("is_recursive")]

            print(f"{i+1:5d}  {dissonance:7.4f}  {drift:7.4f}  ", end="")
            for leaf in leaves:
                osc = leaf["oscillation_score"]
                ema = leaf["dissonance_ema"]
                print(f"  {osc:+7.4f}   {ema:7.4f}", end="")
                osc_history[leaf["path"]].append(osc)
            print()

    # rhythm analysis
    print()
    print("── rhythm analysis ──")
    for p, history in osc_history.items():
        if len(history) < 4:
            print(f"  [{p}]: too few samples")
            continue

        # look for sign changes in oscillation_score
        # (oscillation_score < 0 means the bubble is being asked to be two things;
        #  sign changes mean it's flipping between being-asked and not-being-asked)
        signs = [1 if v >= 0 else -1 for v in history]
        sign_changes = sum(1 for a, b in zip(signs, signs[1:]) if a != b)

        # look for the oscillation score's own oscillation
        # (meta-oscillation: the rhythm of the rhythm)
        diffs = [b - a for a, b in zip(history, history[1:])]
        direction_changes = sum(
            1 for a, b in zip(diffs, diffs[1:])
            if (a > 0) != (b > 0)
        )

        # mean and range
        mean_osc = sum(history) / len(history)
        min_osc = min(history)
        max_osc = max(history)

        print(f"  [{p}]: mean={mean_osc:+.4f}  "
              f"range=[{min_osc:+.4f}, {max_osc:+.4f}]  "
              f"sign_changes={sign_changes}/{len(history)-1}  "
              f"direction_changes={direction_changes}/{max(len(history)-2, 1)}")

        if sign_changes > len(history) * 0.3:
            print(f"         ^ oscillating between positive and negative")
        if direction_changes > len(history) * 0.4:
            print(f"         ^ direction reversals suggest a rhythm")
        if abs(mean_osc) < 0.05 and max_osc - min_osc > 0.1:
            print(f"         ^ centered near zero with wide swing — stable oscillator?")
        if mean_osc < -0.2:
            print(f"         ^ persistently negative — being asked to be two things")

    print()


def survey(n_seeds: int = 10, n_bytes: int = 1000, report_every: int = 200):
    """
    Run many organisms, summarize who develops interior rhythm.
    Selection, not engineering.
    """
    print("=" * 60)
    print("foam survey: listening for interior rhythm")
    print("=" * 60)
    print()

    d = 8

    spec_path = os.path.join(os.path.dirname(__file__), "spec.md")
    if os.path.exists(spec_path):
        with open(spec_path) as f:
            text = f.read()
    else:
        text = ("the measurement problem ") * 200
    data = text.encode("utf-8")[:n_bytes]

    results = []

    for seed in range(n_seeds):
        torch.manual_seed(seed)

        # make DNA
        dna_foam = Foam(d, n_bubbles=3, n_steps=20, writing_rate=0.005)
        for byte_val in text.encode("utf-8")[:3000]:
            v = encode_byte(byte_val)
            with torch.no_grad():
                dna_foam.stabilize(v)

        organism = Foam(d, n_bubbles=0, writing_rate=0.002, n_steps=30)
        organism._bubbles.append(Bubble(d, interior=dna_foam))
        while len(organism._bubbles) < 3:
            organism._bubbles.append(Bubble(d))

        # listen
        osc_traces = {}  # path → list of oscillation_scores
        bases_start = leaf_bases(organism)
        total_dis = 0.0

        for i, byte_val in enumerate(data):
            v = encode_byte(byte_val)
            with torch.no_grad():
                result = organism.stabilize(v)
            total_dis += (result["j2"] - result["j0"]).norm().item()

            if (i + 1) % report_every == 0:
                snap = snapshot_interior(organism)
                for r in snap["readings"]:
                    if not r.get("is_recursive"):
                        p = r["path"]
                        if p not in osc_traces:
                            osc_traces[p] = []
                        osc_traces[p].append(r["oscillation_score"])

        bases_end = leaf_bases(organism)
        total_drift = drift_between(bases_start, bases_end)
        mean_dis = total_dis / len(data)

        # characterize this organism's interior rhythm
        has_rhythm = False
        has_stable_osc = False
        interior_summary = []

        for p, trace in osc_traces.items():
            if len(trace) < 3:
                continue
            diffs = [b - a for a, b in zip(trace, trace[1:])]
            dir_changes = sum(1 for a, b in zip(diffs, diffs[1:])
                              if (a > 0) != (b > 0))
            mean_osc = sum(trace) / len(trace)
            osc_range = max(trace) - min(trace)

            is_interior = "/" in p  # has depth
            reversal_rate = dir_changes / max(len(trace) - 2, 1)

            if reversal_rate > 0.4:
                has_rhythm = True
            if is_interior and abs(mean_osc) < 0.1 and osc_range > 0.05:
                has_stable_osc = True

            interior_summary.append({
                "path": p, "mean": mean_osc, "range": osc_range,
                "reversals": reversal_rate, "is_interior": is_interior,
            })

        marker = ""
        if has_stable_osc:
            marker = " << stable interior oscillator"
        elif has_rhythm:
            marker = " << rhythm"

        print(f"  seed {seed:2d}: dis={mean_dis:.4f}  drift={total_drift:.4f}  "
              f"splits={sum(1 for b in organism._bubbles if not b.is_leaf)}"
              f"{marker}")

        for s in interior_summary:
            if s["is_interior"]:
                print(f"           [{s['path']}] mean={s['mean']:+.4f} "
                      f"range={s['range']:.4f} reversals={s['reversals']:.0%}")

        results.append({
            "seed": seed, "mean_dis": mean_dis, "total_drift": total_drift,
            "has_rhythm": has_rhythm, "has_stable_osc": has_stable_osc,
            "interior": interior_summary,
        })

    print()
    n_rhythm = sum(1 for r in results if r["has_rhythm"])
    n_stable = sum(1 for r in results if r["has_stable_osc"])
    print(f"  {n_rhythm}/{n_seeds} organisms show rhythm")
    print(f"  {n_stable}/{n_seeds} organisms show stable interior oscillation")
    print()
    print("=" * 60)


if __name__ == "__main__":
    if "--survey" in sys.argv:
        survey()
    elif "--long" in sys.argv:
        listen(n_bytes=5000, report_every=100)
    else:
        listen(n_bytes=2000, report_every=50)
