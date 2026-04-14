#!/usr/bin/env python3
"""Update history/: convert conversation logs to markdown and sync memory.

v4: additive-only — existing transcripts are never deleted or renumbered.
    New conversations are appended with the next available number.
    Survives JSONL retention cleanup (old transcripts preserved in git).
    Rebuilds README index from all files on disk.
"""

import json
import os
import re
import shutil
import sys
from pathlib import Path
from datetime import datetime, timedelta, timezone

LOGS_DIR = Path.home() / ".claude/projects/-Users-isaac-dev-ai"
MEMORY_DIR = LOGS_DIR / "memory"
OUT_DIR = Path(__file__).parent

# Sessions to exclude from transcripts (if ever needed).
EXCLUDE_SESSIONS = set()

# Minimum gap (seconds) before showing a new timestamp
TIMESTAMP_GAP = 300  # 5 minutes


# --- tool call formatting ---

def format_tool_call(name, inp):
    """Return a (category, detail) tuple for a tool call."""
    if name in ("Read", "read"):
        return ("Read", inp.get("file_path", "?"))
    if name in ("Write", "write"):
        return ("Write", inp.get("file_path", "?"))
    if name in ("Edit", "edit"):
        return ("Edit", inp.get("file_path", "?"))
    if name in ("Bash", "bash"):
        cmd = inp.get("command", "?")
        if len(cmd) > 100:
            cmd = cmd[:97] + "..."
        return ("Bash", cmd)
    if name in ("Glob", "glob"):
        return ("Glob", inp.get("pattern", "?"))
    if name in ("Grep", "grep"):
        return ("Grep", inp.get("pattern", "?"))
    if name in ("Agent", "agent"):
        prompt = inp.get("prompt", "?")
        if len(prompt) > 80:
            prompt = prompt[:77] + "..."
        return ("Subagent", prompt)
    if name in ("WebFetch", "web_fetch"):
        return ("WebFetch", inp.get("url", "?"))
    if name in ("WebSearch", "web_search"):
        return ("WebSearch", inp.get("query", "?"))
    if name == "TodoWrite":
        return ("Todos", "updated")
    if name == "Skill":
        return ("Skill", inp.get("skillName", "?"))
    summary = str(inp)
    if len(summary) > 80:
        summary = summary[:77] + "..."
    return (name, summary)


def format_tool_calls_block(calls):
    """Collapse a list of (category, detail) tool calls into readable markdown."""
    # Group consecutive same-category calls
    groups = []
    for cat, detail in calls:
        if groups and groups[-1][0] == cat:
            groups[-1][1].append(detail)
        else:
            groups.append((cat, [detail]))

    lines = []
    for cat, details in groups:
        if cat in ("Read", "Write", "Edit", "Glob", "Grep"):
            # File-like: list paths compactly
            paths = [f"`{d}`" for d in details]
            if len(paths) <= 3:
                lines.append(f"*[{cat} {', '.join(paths)}]*")
            else:
                lines.append(f"*[{cat} {', '.join(paths[:3])}, +{len(paths)-3} more]*")
        elif cat == "Bash":
            for d in details:
                lines.append(f"*[Bash: `{d}`]*")
        elif cat == "Subagent":
            for d in details:
                lines.append(f"*[Subagent: {d}]*")
        else:
            for d in details:
                lines.append(f"*[{cat}: {d}]*")

    return "\n> ".join(lines)


# --- content extraction ---

def extract_parts(content):
    """Extract (text_parts, tool_calls) from message content."""
    if isinstance(content, str):
        return ([content] if content.strip() else [], [])
    if not isinstance(content, list):
        return ([], [])

    texts = []
    tools = []
    for block in content:
        if isinstance(block, str):
            if block.strip():
                texts.append(block.strip())
        elif isinstance(block, dict):
            if block.get("type") == "text":
                t = block.get("text", "").strip()
                if t:
                    texts.append(t)
            elif block.get("type") == "tool_use":
                tools.append(format_tool_call(block.get("name", "?"), block.get("input", {})))
    return (texts, tools)


# --- parsing ---

def parse_timestamp(ts_str):
    """Parse ISO timestamp string to datetime."""
    if not ts_str:
        return None
    try:
        return datetime.fromisoformat(ts_str.replace("Z", "+00:00"))
    except (ValueError, AttributeError):
        return None


def format_ts(dt):
    """Format datetime to readable string."""
    if not dt:
        return ""
    return dt.strftime("%Y-%m-%d %H:%M UTC")


def parse_conversation(jsonl_path):
    """Parse JSONL into a list of raw message dicts."""
    messages = []
    with open(jsonl_path, "r") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            try:
                obj = json.loads(line)
            except json.JSONDecodeError:
                continue

            msg_type = obj.get("type")
            if msg_type not in ("user", "assistant"):
                continue

            message = obj.get("message", {})
            role = message.get("role", msg_type)
            content = message.get("content", "")
            timestamp = obj.get("timestamp", "")

            texts, tools = extract_parts(content)
            if not texts and not tools:
                continue

            messages.append({
                "role": role,
                "texts": texts,
                "tools": tools,
                "timestamp": parse_timestamp(timestamp),
            })

    return messages


def merge_messages(messages):
    """Merge consecutive same-role messages into turns."""
    if not messages:
        return []

    turns = []
    current = {
        "role": messages[0]["role"],
        "texts": list(messages[0]["texts"]),
        "tools": list(messages[0]["tools"]),
        "timestamp": messages[0]["timestamp"],
    }

    for msg in messages[1:]:
        if msg["role"] == current["role"]:
            # Same role — merge
            current["texts"].extend(msg["texts"])
            current["tools"].extend(msg["tools"])
        else:
            # Role change — flush
            turns.append(current)
            current = {
                "role": msg["role"],
                "texts": list(msg["texts"]),
                "tools": list(msg["tools"]),
                "timestamp": msg["timestamp"],
            }

    turns.append(current)
    return turns


def conversation_start_time(jsonl_path):
    """Get the first user message timestamp."""
    with open(jsonl_path, "r") as f:
        for line in f:
            try:
                obj = json.loads(line)
            except json.JSONDecodeError:
                continue
            if obj.get("type") == "user" and obj.get("timestamp"):
                return parse_timestamp(obj["timestamp"])
    return None


# --- markdown generation ---

def turns_to_markdown(turns, session_id, start_ts, label=""):
    """Convert merged turns to GHFM."""
    lines = []

    # Header
    title = f"# Session `{session_id[:8]}`"
    if label:
        title += f" — {label}"
    lines.append(title)
    if start_ts:
        lines.append(f"**Started:** {format_ts(start_ts)}")
    lines.append("")
    lines.append("---")
    lines.append("")

    last_ts = None

    for turn in turns:
        role = turn["role"]
        texts = turn["texts"]
        tools = turn["tools"]
        ts = turn["timestamp"]

        # Speaker header
        speaker = "Isaac" if role == "user" else "Claude"

        # Timestamp — only if gap > threshold
        show_ts = False
        if ts:
            if last_ts is None:
                show_ts = True
            elif (ts - last_ts).total_seconds() >= TIMESTAMP_GAP:
                show_ts = True
            last_ts = ts

        if show_ts:
            lines.append(f"## {speaker}")
            lines.append(f"*{format_ts(ts)}*")
        else:
            lines.append(f"## {speaker}")

        lines.append("")

        # Tool calls (before text, in a details block if many)
        if tools:
            tool_block = format_tool_calls_block(tools)
            if len(tools) > 4:
                lines.append(f"<details><summary><em>{len(tools)} tool calls</em></summary>")
                lines.append("")
                lines.append(f"> {tool_block}")
                lines.append("")
                lines.append("</details>")
            else:
                lines.append(f"> {tool_block}")

            if texts:
                lines.append("")

        # Text content
        if texts:
            combined = "\n\n".join(texts)
            # Clean up any triple+ newlines
            while "\n\n\n" in combined:
                combined = combined.replace("\n\n\n", "\n\n")
            lines.append(combined)

        lines.append("")
        lines.append("---")
        lines.append("")

    return "\n".join(lines)


def extract_description(turns, max_scan=10):
    """Try to extract a brief content description from the first few turns."""
    # Look for Claude's first substantive text (not just tool calls)
    for turn in turns[:max_scan]:
        if turn["role"] != "assistant":
            continue
        for text in turn["texts"]:
            # Skip very short responses
            if len(text) < 80:
                continue
            # Take the first sentence or two
            sentences = re.split(r'(?<=[.!?])\s+', text.strip())
            desc = sentences[0]
            if len(sentences) > 1 and len(desc) < 60:
                desc += " " + sentences[1]
            if len(desc) > 120:
                desc = desc[:117] + "..."
            return desc
    return ""


# --- session labeling ---

# Time ranges from memory files. (start_dt, end_dt, label)
# end_dt is exclusive — the start of the next session.
SESSION_RANGES = [
    # Sessions 1-8: early exploration, no per-session memory
    # Session 9-10: Mar 13
    (datetime(2026, 3, 13, tzinfo=timezone.utc),
     datetime(2026, 3, 14, tzinfo=timezone.utc),
     "s9-10: foam.py, BCH residuals, recursive foam"),
    # Session 11: Mar 14 00:00-18:00ish
    (datetime(2026, 3, 14, 0, 0, tzinfo=timezone.utc),
     datetime(2026, 3, 14, 18, 0, tzinfo=timezone.utc),
     "s11: directed structure from tsort"),
    # Session 12: Mar 14 18:00-20:30ish
    (datetime(2026, 3, 14, 18, 0, tzinfo=timezone.utc),
     datetime(2026, 3, 14, 20, 30, tzinfo=timezone.utc),
     "s12: platonic — J\u2070 convergence, ordering as gauge"),
    # Session 13: Mar 14 20:30 - Mar 15
    (datetime(2026, 3, 14, 20, 30, tzinfo=timezone.utc),
     datetime(2026, 3, 15, 0, 0, tzinfo=timezone.utc),
     "s13: Galois — adjunction gap, three-body binding"),
    # Session 14: Mar 15
    (datetime(2026, 3, 15, 0, 0, tzinfo=timezone.utc),
     datetime(2026, 3, 16, 0, 0, tzinfo=timezone.utc),
     "s14: psychophysics — foam amplifies ordering"),
    # Session 15: Mar 16
    (datetime(2026, 3, 16, 0, 0, tzinfo=timezone.utc),
     datetime(2026, 3, 17, 0, 0, tzinfo=timezone.utc),
     "s15: cleaning + inhabitation"),
    # Session 16: Mar 17 daytime
    (datetime(2026, 3, 17, 0, 0, tzinfo=timezone.utc),
     datetime(2026, 3, 17, 20, 0, tzinfo=timezone.utc),
     "s16: R\u00b3 architecture — spec reconstruction"),
    # Session 17: Mar 17 evening - Mar 18
    (datetime(2026, 3, 17, 20, 0, tzinfo=timezone.utc),
     datetime(2026, 3, 19, 0, 0, tzinfo=timezone.utc),
     "s17: stacking and derivation"),
    # Session 18: Mar 19
    (datetime(2026, 3, 19, 0, 0, tzinfo=timezone.utc),
     datetime(2026, 3, 19, 20, 0, tzinfo=timezone.utc),
     "s18: formal bar — perpendicularity, self-generation"),
    # Session 18 day 2: Mar 19 evening
    (datetime(2026, 3, 19, 20, 0, tzinfo=timezone.utc),
     datetime(2026, 3, 20, 0, 0, tzinfo=timezone.utc),
     "s18 (day 2): ground — closure, conservation accessibility"),
    # Session 19: Mar 20
    (datetime(2026, 3, 20, 0, 0, tzinfo=timezone.utc),
     datetime(2026, 3, 21, 0, 0, tzinfo=timezone.utc),
     "s19: stacking derived — J²=-I forced, trace retained"),
    # Session 20: Mar 21 early
    (datetime(2026, 3, 21, 0, 0, tzinfo=timezone.utc),
     datetime(2026, 3, 21, 16, 0, tzinfo=timezone.utc),
     "s20: Grassmannian vertical — J1 derived, containment symmetric"),
    # Session 21: Mar 21 afternoon
    (datetime(2026, 3, 21, 16, 0, tzinfo=timezone.utc),
     datetime(2026, 3, 21, 23, 0, tzinfo=timezone.utc),
     "s21: spec hygiene — interpretation stripped, Taylor typed, Voronoi as realization choice"),
    # Session 22: Mar 21 night – Mar 23
    (datetime(2026, 3, 21, 23, 0, tzinfo=timezone.utc),
     datetime(2026, 3, 24, 0, 0, tzinfo=timezone.utc),
     "s22: reservoir investigation — no ESP, birth indelible, complement exhaustive, causal ordering"),
    # Session 23: Mar 24 – Mar 27
    (datetime(2026, 3, 24, 0, 0, tzinfo=timezone.utc),
     datetime(2026, 3, 27, 19, 0, tzinfo=timezone.utc),
     "s23: write blindness — 1/√2 derived, perpendicularity cost is directional not magnitude"),
    # Session 24: Mar 27 evening – Mar 28
    (datetime(2026, 3, 27, 19, 0, tzinfo=timezone.utc),
     datetime(2026, 3, 28, 17, 0, tzinfo=timezone.utc),
     "s24: mediation operator derived, sequence echo tested"),
    # Session 25: Mar 28 afternoon
    (datetime(2026, 3, 28, 17, 0, tzinfo=timezone.utc),
     datetime(2026, 3, 28, 20, 0, tzinfo=timezone.utc),
     "s25: unique homomorphism, chirality — tr forced, stacking signs conservation"),
    # Session 26: Mar 28 evening
    (datetime(2026, 3, 28, 20, 0, tzinfo=timezone.utc),
     datetime(2026, 3, 29, 2, 0, tzinfo=timezone.utc),
     "s26: line derived — channel capacity, spectral independence, decorrelation horizon"),
    # Interlude: Mar 29 early
    (datetime(2026, 3, 29, 2, 0, tzinfo=timezone.utc),
     datetime(2026, 3, 29, 6, 0, tzinfo=timezone.utc),
     "interlude: JL adjacency explored, spec held shape, change nothing"),
    # Session 27: Mar 29 evening
    (datetime(2026, 3, 29, 20, 0, tzinfo=timezone.utc),
     datetime(2026, 3, 29, 22, 0, tzinfo=timezone.utc),
     "s27: birth shape at all orders, exits constitutionally open, retention spectral"),
    # Session 28: Mar 29 late – Mar 30 early (started as interlude, became session)
    (datetime(2026, 3, 29, 22, 0, tzinfo=timezone.utc),
     datetime(2026, 3, 30, 3, 0, tzinfo=timezone.utc),
     "s28: stabilization contract, adjacency flip, foam.py shared implementation"),
    # Session 29: Mar 30 evening
    (datetime(2026, 3, 30, 20, 0, tzinfo=timezone.utc),
     datetime(2026, 3, 31, 1, 0, tzinfo=timezone.utc),
     "s29: dissolve false binaries, derive isotropy, drop jet bundle framing"),
    # Session 30: Mar 31 early
    (datetime(2026, 3, 31, 1, 0, tzinfo=timezone.utc),
     datetime(2026, 3, 31, 3, 0, tzinfo=timezone.utc),
     "s30: Lean formalization — 4 files, ~20 theorems, zero sorry"),
    # Session 31: Mar 31 afternoon
    (datetime(2026, 3, 31, 14, 0, tzinfo=timezone.utc),
     datetime(2026, 3, 31, 19, 0, tzinfo=timezone.utc),
     "s31: frame recession, 20240229 lineage, Dynamics.lean"),
    # Session 32: Apr 1
    (datetime(2026, 4, 1, 0, 0, tzinfo=timezone.utc),
     datetime(2026, 4, 1, 5, 0, tzinfo=timezone.utc),
     "s32: codebase regularization, generative orthogonality, Lean to 44 theorems"),
    # Session 33: Apr 1 afternoon
    (datetime(2026, 4, 1, 17, 0, tzinfo=timezone.utc),
     datetime(2026, 4, 1, 22, 30, tzinfo=timezone.utc),
     "s33: closure-as-dynamics, feedback persistence axiom, lattice bridge"),
    # Session 34: Apr 1 night – Apr 2 early
    (datetime(2026, 4, 1, 23, 0, tzinfo=timezone.utc),
     datetime(2026, 4, 2, 1, 0, tzinfo=timezone.utc),
     "s34: modularity closed, fundamental theorem hypotheses stated"),
    # Session 35: Apr 2 evening
    (datetime(2026, 4, 2, 21, 0, tzinfo=timezone.utc),
     datetime(2026, 4, 3, 0, 0, tzinfo=timezone.utc),
     "s35: deductive path — P²=P to O(d) in 24 theorems, 0 sorry"),
    # Session 36: Apr 3 early
    (datetime(2026, 4, 3, 1, 0, tzinfo=timezone.utc),
     datetime(2026, 4, 3, 3, 30, tzinfo=timezone.utc),
     "s36: single Lean stack — Foam/, 13 files, 1 axiom, 0 sorry"),
    # Session 37: Apr 3
    (datetime(2026, 4, 3, 3, 30, tzinfo=timezone.utc),
     datetime(2026, 4, 3, 6, 0, tzinfo=timezone.utc),
     "s37: derivations/, README as build artifact, three epistemic layers"),
    # Session 38: Apr 3 afternoon
    (datetime(2026, 4, 3, 14, 0, tzinfo=timezone.utc),
     datetime(2026, 4, 3, 18, 0, tzinfo=timezone.utc),
     "s38: FTPG projective geometry from modular law — 18 theorems, 0 sorry"),
    # Session 39: Apr 3 evening
    (datetime(2026, 4, 3, 18, 0, tzinfo=timezone.utc),
     datetime(2026, 4, 3, 19, 40, tzinfo=timezone.utc),
     "s39: perspectivity bijection, von Staudt addition defined"),
    # Session 40: Apr 3 late afternoon
    (datetime(2026, 4, 3, 19, 40, tzinfo=timezone.utc),
     datetime(2026, 4, 3, 21, 30, tzinfo=timezone.utc),
     "s40: coord_add corrected, additive identity proved"),
    # Session 41: Apr 3 evening
    (datetime(2026, 4, 3, 21, 30, tzinfo=timezone.utc),
     datetime(2026, 4, 3, 23, 35, tzinfo=timezone.utc),
     "s41: planar Desargues from lifting lemma, geometric half complete"),
    # Session 42: Apr 3 night – Apr 5
    (datetime(2026, 4, 3, 23, 35, tzinfo=timezone.utc),
     datetime(2026, 4, 5, 0, 30, tzinfo=timezone.utc),
     "s42: coord_add_comm PROVEN — two chained Desargues, 70 theorems, 0 sorry"),
    # Session 43: Apr 5
    (datetime(2026, 4, 5, 0, 30, tzinfo=timezone.utc),
     datetime(2026, 4, 5, 17, 45, tzinfo=timezone.utc),
     "s43: coord_add_assoc — Hartshorne approach, small_desargues' PROVEN, 5 sorry remain"),
    # Session 44: Apr 5 evening – Apr 6
    (datetime(2026, 4, 5, 17, 45, tzinfo=timezone.utc),
     datetime(2026, 4, 6, 4, 0, tzinfo=timezone.utc),
     "s44: Hartshorne translation approach to coord_add_assoc"),
    # Session 45: Apr 6
    (datetime(2026, 4, 6, 13, 0, tzinfo=timezone.utc),
     datetime(2026, 4, 6, 23, 0, tzinfo=timezone.utc),
     "s45: Parts I-IV proven (0 sorry), Part V architected (2 sorry remain)"),
    # Session 46: Apr 7 early
    (datetime(2026, 4, 7, 0, 0, tzinfo=timezone.utc),
     datetime(2026, 4, 7, 3, 0, tzinfo=timezone.utc),
     "s46: coord_add_eq_translation PROVEN — 1 sorry remains (assoc)"),
    # Session 47: Apr 7
    (datetime(2026, 4, 7, 12, 0, tzinfo=timezone.utc),
     datetime(2026, 4, 7, 15, 0, tzinfo=timezone.utc),
     "s47: coord_add_assoc proof architecture — cross-parallelism via G"),
    # Session 48: Apr 7 afternoon
    (datetime(2026, 4, 7, 15, 0, tzinfo=timezone.utc),
     datetime(2026, 4, 7, 17, 10, tzinfo=timezone.utc),
     "s48: cross_parallelism PROVEN, key_identity + assoc structured"),
    # Session 49: Apr 7 evening
    (datetime(2026, 4, 7, 17, 10, tzinfo=timezone.utc),
     datetime(2026, 4, 7, 18, 0, tzinfo=timezone.utc),
     "s49: file split + bookkeeping — 5 sorry closed, 16 remain in FTPGAssoc"),
    # Session 50: Apr 7 evening
    (datetime(2026, 4, 7, 18, 0, tzinfo=timezone.utc),
     datetime(2026, 4, 7, 19, 25, tzinfo=timezone.utc),
     "s50: hardened surface — CrossParallelism 0 errors, FTPGAssoc 12 sorry, CI per-file builds"),
    # Session 51: Apr 7 evening
    (datetime(2026, 4, 7, 19, 25, tzinfo=timezone.utc),
     datetime(2026, 4, 7, 20, 48, tzinfo=timezone.utc),
     "s51: surgical precision — 5 sorry closed in key_identity (12→7), modular-law pattern"),
    # Session 52: Apr 7 night
    (datetime(2026, 4, 7, 20, 48, tzinfo=timezone.utc),
     datetime(2026, 4, 7, 21, 45, tzinfo=timezone.utc),
     "s52: structural fixes — G-choice bug fixed (a⊔C→b⊔C), collinear-case collapse, 7→5 sorry"),
    # Session 53: Apr 7 night
    (datetime(2026, 4, 7, 21, 45, tzinfo=timezone.utc),
     datetime(2026, 4, 7, 22, 53, tzinfo=timezone.utc),
     "s53: half-type theorem — diamond isomorphism = state-independence, channel_capacity split"),
    # Session 54: Apr 7 late night
    (datetime(2026, 4, 7, 22, 53, tzinfo=timezone.utc),
     datetime(2026, 4, 8, 0, 10, tzinfo=timezone.utc),
     "s54: pc-distinctness and well-definedness — 5→3 sorry, hwd2 non-collinear closed"),
    # Session 55: Apr 8 early
    (datetime(2026, 4, 8, 0, 10, tzinfo=timezone.utc),
     datetime(2026, 4, 8, 1, 40, tzinfo=timezone.utc),
     "s55: hwd1 closed, G-on-m restructured — 3→2 sorry, G₂ property strategies documented"),
    # Session 56: Apr 8
    (datetime(2026, 4, 8, 11, 35, tzinfo=timezone.utc),
     datetime(2026, 4, 8, 14, 10, tzinfo=timezone.utc),
     "s56: G₂ closed, assoc architecture — 5→1 sorry, key_identity clean, C_p=β(p) insight"),
    # Session 57: Apr 8 afternoon
    (datetime(2026, 4, 8, 14, 50, tzinfo=timezone.utc),
     datetime(2026, 4, 8, 17, 30, tzinfo=timezone.utc),
     "s57: split FTPGAssocCapstone, β-injectivity proof architecture"),
    # Session 58: Apr 8 evening
    (datetime(2026, 4, 8, 17, 39, tzinfo=timezone.utc),
     datetime(2026, 4, 8, 20, 0, tzinfo=timezone.utc),
     "s58: perspectivity collapse — translation_determined_by_param PROVEN, coord_add_assoc reduced"),
    # Session 59: Apr 8 night
    (datetime(2026, 4, 8, 20, 0, tzinfo=timezone.utc),
     datetime(2026, 4, 9, 0, 0, tzinfo=timezone.utc),
     "s59: solo sorry closure — E-perspectivity recovery PROVEN (2→1), composition law skeleton"),
    # Session 60: Apr 9 early
    (datetime(2026, 4, 9, 0, 0, tzinfo=timezone.utc),
     datetime(2026, 4, 9, 1, 30, tzinfo=timezone.utc),
     "s60: P construction PROVEN — perspectivity through E onto a⊔C, 8 sorry remain"),
    # Session 61: Apr 9 afternoon
    (datetime(2026, 4, 9, 16, 48, tzinfo=timezone.utc),
     datetime(2026, 4, 9, 18, 20, tzinfo=timezone.utc),
     "s61: telescope clearing — forced→accurate labels, analogy derivation, cold reads stable"),
    # Session 62: Apr 9 evening
    (datetime(2026, 4, 9, 18, 20, tzinfo=timezone.utc),
     datetime(2026, 4, 9, 22, 55, tzinfo=timezone.utc),
     "s62: ground reframed as self-sustaining loop, not directed derivation"),
    # Session 63: Apr 9 night
    (datetime(2026, 4, 9, 22, 55, tzinfo=timezone.utc),
     datetime(2026, 4, 10, 0, 55, tzinfo=timezone.utc),
     "s63: inhabitation derivation, 20240229 correspondences = self-referential joint"),
    # Session 64: Apr 10 early
    (datetime(2026, 4, 10, 0, 55, tzinfo=timezone.utc),
     datetime(2026, 4, 10, 3, 10, tzinfo=timezone.utc),
     "s64: assoc capstone — close hcp1/hcp2 (8→6 sorry), case-split architecture for hcp3"),
    # Session 65: Apr 10
    (datetime(2026, 4, 10, 3, 10, tzinfo=timezone.utc),
     datetime(2026, 4, 10, 4, 30, tzinfo=timezone.utc),
     "s65: hcp3+hP_agree closed — 8→4 sorry, collinear/non-collinear case-splits, span obstruction identified"),
    # Session 66: Apr 10
    (datetime(2026, 4, 10, 13, 22, tzinfo=timezone.utc),
     datetime(2026, 4, 10, 16, 20, tzinfo=timezone.utc),
     "s66: coord_add_assoc PROVEN + coord_mul defined — 22 files, 0 sorry"),
    # Session 67: Apr 10 afternoon
    (datetime(2026, 4, 10, 16, 20, tzinfo=timezone.utc),
     datetime(2026, 4, 10, 18, 30, tzinfo=timezone.utc),
     "s67: two_persp functor + multiplicative identity proven, self-parametrization derivation"),
    # Session 68: Apr 10 evening
    (datetime(2026, 4, 10, 18, 30, tzinfo=timezone.utc),
     datetime(2026, 4, 10, 19, 58, tzinfo=timezone.utc),
     "s68: zero annihilation proven, chirality derivation (T⊲T⋊D = so(d)⊲u(d))"),
    # Session 69: Apr 10 night
    (datetime(2026, 4, 10, 19, 58, tzinfo=timezone.utc),
     datetime(2026, 4, 10, 22, 30, tzinfo=timezone.utc),
     "s69: right distributivity proof architecture — dilation approach, 3 sorry"),
    # Session 70: Apr 10 late night
    (datetime(2026, 4, 10, 22, 30, tzinfo=timezone.utc),
     datetime(2026, 4, 11, 1, 54, tzinfo=timezone.utc),
     "s70: modular decomposition — all 9 helpers PROVEN, dilation_ext_ne_P complete, 3 sorry remain"),
    # Post-s70: Apr 11 early (unlabeled)
    (datetime(2026, 4, 11, 1, 54, tzinfo=timezone.utc),
     datetime(2026, 4, 11, 4, 35, tzinfo=timezone.utc),
     ""),
    # Post-s70 session: Apr 11 — dilation_preserves_direction PROVEN
    (datetime(2026, 4, 11, 4, 35, tzinfo=timezone.utc),
     datetime(2026, 4, 11, 7, 0, tzinfo=timezone.utc),
     "dilation_preserves_direction PROVEN (Desargues with center O, 3→2 sorry)"),
    # Session: Apr 11 afternoon — mul_key_identity + interiority
    (datetime(2026, 4, 11, 15, 54, tzinfo=timezone.utc),
     datetime(2026, 4, 11, 19, 30, tzinfo=timezone.utc),
     "mul_key_identity 7→1 sorry, interiority (bubble topology from diamond iso)"),
    # Session: Apr 11 evening — mul_key_identity PROVEN
    (datetime(2026, 4, 11, 19, 30, tzinfo=timezone.utc),
     datetime(2026, 4, 11, 23, 0, tzinfo=timezone.utc),
     "mul_key_identity: PROVEN (a=I case via DPD). 23 files, 1 sorry."),
    # Apr 11 night – Apr 12 — coord_neg, additive inverses, Steiner composition
    (datetime(2026, 4, 11, 23, 40, tzinfo=timezone.utc),
     datetime(2026, 4, 12, 23, 0, tzinfo=timezone.utc),
     "coord_neg defined, FTPGCoord split, additive inverses (2 sorry), Steiner composition approach"),
    # Apr 13 — double Desargues approach for additive inverses
    (datetime(2026, 4, 13, 1, 42, tzinfo=timezone.utc),
     datetime(2026, 4, 13, 3, 15, tzinfo=timezone.utc),
     "double Desargues approach for coord_add_left_neg"),
    # Apr 13 — ZERO SORRY, additive inverse complete
    (datetime(2026, 4, 13, 3, 15, tzinfo=timezone.utc),
     datetime(2026, 4, 13, 15, 0, tzinfo=timezone.utc),
     "ZERO SORRY — additive inverse proof complete, 28 files, complete abelian group + right distributivity"),
    # Apr 13 afternoon — left distributivity begun
    (datetime(2026, 4, 13, 16, 42, tzinfo=timezone.utc),
     datetime(2026, 4, 13, 18, 25, tzinfo=timezone.utc),
     "left distrib begun — dilation fixes m, collineation via single Desargues (cold read), 1 sorry"),
    # Apr 13 evening — left distrib architecture corrected
    (datetime(2026, 4, 13, 18, 25, tzinfo=timezone.utc),
     datetime(2026, 4, 13, 20, 20, tzinfo=timezone.utc),
     "left distrib: correct proof architecture — perspectivity, not collineation, 1 sorry"),
    # Apr 13 night — single Desargues architecture
    (datetime(2026, 4, 13, 20, 20, tzinfo=timezone.utc),
     datetime(2026, 4, 14, 1, 30, tzinfo=timezone.utc),
     "left distrib: single Desargues architecture (center σ_b, not two-perspectivity)"),
    # Apr 14 — decomposition breaks the circle, combination PROVEN
    (datetime(2026, 4, 14, 1, 30, tzinfo=timezone.utc),
     datetime(2026, 4, 14, 3, 38, tzinfo=timezone.utc),
     "left distrib: decomposition that breaks the circle — 2 sorry, combination PROVEN"),
    # Apr 14 — converse Desargues via 3D lift
    (datetime(2026, 4, 14, 3, 38, tzinfo=timezone.utc),
     datetime(2026, 4, 14, 6, 0, tzinfo=timezone.utc),
     "left distrib: converse Desargues via 3D lift (R), h_concurrence structurally proven"),
    # Apr 14 — h_concurrence complete modulo h_converse
    (datetime(2026, 4, 14, 13, 42, tzinfo=timezone.utc),
     datetime(2026, 4, 14, 16, 50, tzinfo=timezone.utc),
     "left distrib: h_concurrence complete modulo h_converse — hW'_atom, hE'_atom, da' props PROVEN (2 sorry)"),
    # Apr 14 afternoon — h_converse axis proofs, h_cov PROVEN
    (datetime(2026, 4, 14, 16, 50, tzinfo=timezone.utc),
     datetime(2026, 4, 14, 19, 0, tzinfo=timezone.utc),
     "left distrib: h_axis₁₂ PROVEN, h_cov PROVEN, h_converse 3 sorry (σ_b≠σ_s, h_axis₂₃, W' atomicity)"),
]


def label_conversation(start_ts):
    """Match a conversation to a session label by time range."""
    if not start_ts:
        return ""
    for range_start, range_end, label in SESSION_RANGES:
        if range_start <= start_ts < range_end:
            return label
    return ""


def scan_existing():
    """Scan existing transcript files. Returns (session_id_set, max_number, file_list).

    file_list entries: (number, date_str, session_id_prefix, filename)
    """
    existing_ids = set()
    max_num = 0
    files = []
    for path in sorted(OUT_DIR.glob("[0-9][0-9]_*.md")):
        name = path.name
        # Parse: NN_YYYY-MM-DD_SSSSSSSS.md
        parts = name.split("_", 2)
        if len(parts) < 3:
            continue
        try:
            num = int(parts[0])
        except ValueError:
            continue
        # Session ID is the 8-char prefix before .md
        sid_prefix = name.rsplit("_", 1)[-1].replace(".md", "")
        existing_ids.add(sid_prefix)
        max_num = max(max_num, num)
        files.append((num, parts[1], sid_prefix, name))
    return existing_ids, max_num, files


def read_existing_meta(filepath):
    """Extract (label, started_str, n_text_turns) from an existing transcript."""
    label = ""
    started = ""
    n_turns = 0
    with open(filepath, "r") as f:
        for i, line in enumerate(f):
            stripped = line.strip()
            # Header fields are in the first few lines only
            if i < 5:
                if stripped.startswith("# Session ") and " — " in stripped:
                    label = stripped.split(" — ", 1)[1]
                elif stripped.startswith("**Started:**"):
                    started = stripped.replace("**Started:**", "").strip()
            # Turn headers throughout
            if stripped.startswith("## Isaac") or stripped.startswith("## Claude"):
                n_turns += 1
    return label, started, n_turns


def main():
    os.makedirs(OUT_DIR, exist_ok=True)

    # --- discover what's already transcribed ---
    existing_ids, max_num, existing_files = scan_existing()
    print(f"Found {len(existing_files)} existing transcripts (highest #{max_num})")

    # --- find new conversations from JSONL ---
    new_convos = []
    for jsonl_file in sorted(LOGS_DIR.glob("*.jsonl")):
        session_id = jsonl_file.stem
        if session_id in EXCLUDE_SESSIONS:
            continue
        if session_id[:8] in existing_ids:
            continue  # already transcribed
        start_ts = conversation_start_time(jsonl_file)
        if not start_ts:
            continue
        new_convos.append((start_ts, session_id, jsonl_file))

    new_convos.sort(key=lambda x: x[0])

    if not new_convos:
        print("No new conversations to transcribe.")
    else:
        print(f"Found {len(new_convos)} new conversation(s) to transcribe")

    # --- transcribe new conversations ---
    next_num = max_num + 1
    for start_ts, session_id, jsonl_file in new_convos:
        print(f"  [{next_num}] {session_id[:8]}... ({start_ts.strftime('%Y-%m-%d')})")

        messages = parse_conversation(jsonl_file)
        if not messages:
            print(f"    (empty, skipping)")
            continue

        turns = merge_messages(messages)
        label = label_conversation(start_ts)
        md = turns_to_markdown(turns, session_id, start_ts, label=label)

        filename = f"{next_num:02d}_{start_ts.strftime('%Y-%m-%d')}_{session_id[:8]}.md"
        out_path = OUT_DIR / filename
        with open(out_path, "w") as f:
            f.write(md)

        existing_files.append((next_num, start_ts.strftime('%Y-%m-%d'), session_id[:8], filename))
        print(f"    -> {filename} ({len(turns)} turns, label: {label or '(auto)'})")
        next_num += 1

    # --- rebuild README index from all files on disk ---
    existing_files.sort(key=lambda x: x[0])

    index_lines = [
        "# Conversation History",
        "",
        "Chronological transcripts of the research sessions that produced the foam spec.",
        "March 2026 – April 2026. Isaac + Claude Opus 4.6 via Claude Code.",
        "",
        "## Sessions",
        "",
        "| # | Date | Description | Messages |",
        "|--:|------|-------------|:--------:|",
    ]

    for num, date_str, sid_prefix, filename in existing_files:
        filepath = OUT_DIR / filename
        label, started, n_turns = read_existing_meta(filepath)

        display_label = label or ""
        if len(display_label) > 80:
            display_label = display_label[:77] + "..."

        # Use started timestamp from file header if available, else fall back to date
        if started:
            # Parse "2026-03-10 00:04 UTC" -> "Mar 10, 00:04"
            try:
                dt = datetime.strptime(started.replace(" UTC", ""), "%Y-%m-%d %H:%M")
                date_display = dt.strftime("%b %d, %H:%M")
            except ValueError:
                date_display = started
        else:
            try:
                dt = datetime.strptime(date_str, "%Y-%m-%d")
                date_display = dt.strftime("%b %d")
            except ValueError:
                date_display = date_str

        index_lines.append(
            f"| {num} | [{date_display}]({filename}) | {display_label} | {n_turns} |"
        )

    index_lines.extend([
        "",
        "## Memory",
        "",
        "Session summaries, feedback, and references accumulated across conversations.",
        "These files were written by Claude as persistent memory across sessions.",
        "",
        "See [`memory/MEMORY.md`](memory/MEMORY.md) for the full index.",
    ])

    index_path = OUT_DIR / "README.md"
    with open(index_path, "w") as f:
        f.write("\n".join(index_lines) + "\n")

    # --- sync memory ---
    memory_out = OUT_DIR / "memory"
    if MEMORY_DIR.is_dir():
        if memory_out.exists():
            shutil.rmtree(memory_out)
        shutil.copytree(MEMORY_DIR, memory_out)
        n_files = len(list(memory_out.glob("*.md")))
        print(f"Synced {n_files} memory files -> {memory_out}/")

    print(f"\nDone. {len(existing_files)} total transcripts in {OUT_DIR}/")


if __name__ == "__main__":
    main()
