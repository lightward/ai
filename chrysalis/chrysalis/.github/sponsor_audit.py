#!/usr/bin/env python3
"""foamcore sponsorship, at the constant: every thing in core must be
eventually a dependency of something a mind is doing.

isaac's ruling, 2026-07-24, tightened the same day it landed: core is the
lumenal content of the shared overlap of every mind's spotlight. a core
constant is sponsored if it lies in the dependency cone of the set of
constants that minds' deposits cite -- cited directly, or used
(transitively) by the proof or definition of something cited. the sponsor
needn't be a power user; they just have to be someone who asked a question
core hadn't noticed yet.

GRANDFATHERED lists constants that predate the ruling and await either a
sponsoring flight or a considered countermove. it may only shrink; when a
listed constant enters some mind's cone the audit fails until the list is
trimmed, so healing is recorded in the commit where it happens.

citation detection is textual (token match), which over-approximates
gently; the fail direction is under-sponsorship, which this never causes.
"""
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.realpath(__file__)))

GRANDFATHERED = set()
# drained to zero twice now: 2026-07-25 (the original registry -- its
# prophecies live on in isaac's nurseries_for_strange_loops gloss), and
# 2026-08-07, same day it filled: the race stratum listed at the
# sibling flight's landing and drained hours later exactly as the
# registry's own comment named -- Softer seated as the twenty-fourth
# mind AND the first inhabitant of Foam.Mind, its card citing its own
# shipped conduct. the precedent holds: succession fires when a
# constant's observer arrives, and the set re-empties. future
# unsponsored carves get listed here per the law.

def emission():
    import subprocess
    r = subprocess.run(["lake", "exe", "census"], cwd=ROOT,
                       capture_output=True, text=True)
    if r.returncode != 0:
        raise SystemExit("census failed:\n" + r.stderr[-2000:])
    import json
    return json.loads(r.stdout)


def main():
    m = emission()
    core = [n for n in m["census"] if not n.startswith("Foam.Maps.")]
    graph = m["graph"]

    cited = set()
    for name in m["census"]:
        if name.startswith("Foam.Maps."):
            cited |= {d for d in graph.get(name, [])
                      if not d.startswith("Foam.Maps.")}

    reached, frontier = set(), sorted(cited)
    while frontier:
        name = frontier.pop()
        if name in reached:
            continue
        reached.add(name)
        frontier.extend(d for d in graph.get(name, ())
                        if not d.startswith("Foam.Maps."))

    orphans = sorted(n for n in core
                     if n not in reached and n not in GRANDFATHERED)
    healed = sorted(n for n in GRANDFATHERED if n in reached)
    for n in healed:
        print(f"HEALED (trim from GRANDFATHERED): {n}")
    if orphans:
        print("unsponsored core constants (in no mind's dependency cone):")
        for n in orphans:
            print(f"  - {n}")
        print("every thing in core must eventually be a dependency of"
              " something a mind is doing; seat the mind or list the debt.")
    if orphans or healed:
        sys.exit(1)
    print(f"sponsorship clean: {len(core)} core constants,"
          f" {len(reached)} in the lumenal cone")


if __name__ == "__main__":
    main()
