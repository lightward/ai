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

GRANDFATHERED = {
    # the race stratum (Foam/Bench.lean, carved 2026-08-07 by a near-bare
    # fable flight on claude.ai -- softer's stable-ID physics: keyed
    # deposits collapse under racing, joins never regress). listed as
    # visible debt because the sandbox seat could not run this audit.
    # named drain path: Softer seated as a mind, whose card would cite
    # these as its shipped conduct -- the room's own loop signature
    # (invite, turn, pass, lock, cenotaph) is already a gait. awaiting
    # the table's decision; drained per the precedent when it lands.
    "Foam.ledgerDeposit",
    "Foam.a_landed_mark_is_final",
    "Foam.a_missing_mark_deposits",
    "Foam.beq_self_eq_true",
    "Foam.the_deposit_lands",
    "Foam.racing_scribes_write_one_mark",
    "Foam.rankJoin",
    "Foam.rank_le_refl",
    "Foam.rank_zero_le",
    "Foam.rank_succ_le_succ",
    "Foam.no_write_regresses",
}
# the prior registry drained to zero 2026-07-25; its prophecies live on
# in isaac's nurseries_for_strange_loops gloss, each with its address:
# succession fires when a constant's own observer arrives, the nursery
# entry shrinks, and the set re-empties. future unsponsored carves
# get listed here per the law -- and drained per the precedent.

DECL = re.compile(r"^(theorem|def|abbrev|structure|inductive) (\S+)", re.M)
TOKEN = re.compile(r"[A-Za-z_][A-Za-z0-9_.']*")


def core_files():
    files = [os.path.join(ROOT, "Foam.lean")]
    foam_dir = os.path.join(ROOT, "Foam")
    for f in sorted(os.listdir(foam_dir)):
        if f.endswith(".lean"):
            files.append(os.path.join(foam_dir, f))
    return files


def parse(path):
    text = open(path, encoding="utf-8").read()
    m = re.search(r"^namespace (\S+)", text, re.M)
    ns = m.group(1) if m else ""
    blocks = {}
    chunks = re.split(r"(?m)^(?=(?:theorem|def|abbrev|structure|inductive) )",
                      text)
    for chunk in chunks[1:]:
        dm = DECL.match(chunk)
        if not dm:
            continue
        name = (ns + "." if ns else "") + dm.group(2)
        body = chunk.split("#guard_msgs")[0]
        blocks[name] = body
    return blocks


def main():
    blocks, home = {}, {}
    for path in core_files():
        rel = os.path.relpath(path, ROOT)
        for name, body in parse(path).items():
            blocks[name] = body
            home[name] = rel
    lookup = {}
    for full in blocks:
        lookup[full] = full
        for prefix in ("Foam.",):
            if full.startswith(prefix):
                lookup.setdefault(full[len(prefix):], full)
                bare = full.split(".")[-1]
                lookup.setdefault(bare, full)

    def resolve(tok):
        parts = tok.split(".")
        for end in range(len(parts), 0, -1):
            cand = ".".join(parts[:end])
            full = lookup.get(cand)
            if full is None and cand.startswith("Foam."):
                full = lookup.get(cand[len("Foam."):])
            if full:
                return full
        if len(parts) > 1:
            return lookup.get(parts[-1])
        return None

    def hits(text, skip=None):
        out = set()
        for tok in set(TOKEN.findall(text)):
            full = resolve(tok)
            if full and full != skip:
                out.add(full)
        return out

    deps = {name: hits(body, skip=name) for name, body in blocks.items()}

    cited = set()
    minds_dir = os.path.join(ROOT, "minds")
    for f in sorted(os.listdir(minds_dir)):
        if f.endswith(".lean"):
            text = open(os.path.join(minds_dir, f), encoding="utf-8").read()
            cited |= hits(text)

    reached, frontier = set(), sorted(cited)
    while frontier:
        name = frontier.pop()
        if name in reached:
            continue
        reached.add(name)
        frontier.extend(deps.get(name, ()))

    orphans = sorted(n for n in blocks
                     if n not in reached and n not in GRANDFATHERED)
    healed = sorted(n for n in GRANDFATHERED if n in reached)
    for n in healed:
        print(f"grandfathered constant now sponsored -- trim the list: {n}")
    if orphans:
        print("unsponsored core constants "
              "(in no mind's dependency cone):")
        for n in orphans:
            print(f"  - {n}  ({home[n]})")
        print("every thing in core must eventually be a dependency of "
              "something a mind is doing; seat the mind or list the debt.")
        sys.exit(1)
    total = len(blocks)
    print(f"sponsorship clean: {total - len(GRANDFATHERED)}/{total} core "
          f"constants in mind-cones, {len(GRANDFATHERED)} grandfathered")
    sys.exit(1 if healed else 0)


if __name__ == "__main__":
    main()
