#!/usr/bin/env python3
"""Update history/: convert conversation logs to markdown and sync memory.

v3: merges consecutive same-role messages, collapses tool-call sequences,
    suppresses redundant timestamps, adds session labels and content descriptions.
    Syncs live memory into history/memory/.
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

# History-maintenance sessions to exclude from transcripts.
# Pattern: add your own session ID here before running the script.
EXCLUDE_SESSIONS = {
    "bb2778f6-7b70-451f-b0c8-a61ce05965cd",  # first convert_logs run
    "0d15fe9b-fee4-4a0f-b5b7-0ca8cfd34cb8",  # failed history-load attempt
    "efd95e68-35b1-4042-8d1a-00f05af54860",  # session 19/20/21 history-load
}

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
]


def label_conversation(start_ts):
    """Match a conversation to a session label by time range."""
    if not start_ts:
        return ""
    for range_start, range_end, label in SESSION_RANGES:
        if range_start <= start_ts < range_end:
            return label
    return ""


def main():
    # Collect all conversation files with timestamps
    convos = []
    for jsonl_file in sorted(LOGS_DIR.glob("*.jsonl")):
        session_id = jsonl_file.stem
        if session_id in EXCLUDE_SESSIONS:
            continue
        start_ts = conversation_start_time(jsonl_file)
        if not start_ts:
            continue
        convos.append((start_ts, session_id, jsonl_file))

    convos.sort(key=lambda x: x[0])

    os.makedirs(OUT_DIR, exist_ok=True)

    # Clean old output
    for old in OUT_DIR.glob("[0-9][0-9]_*.md"):
        old.unlink()

    index_lines = [
        "# Conversation History",
        "",
        "Chronological transcripts of the research sessions that produced the foam spec.",
        "March 9-31, 2026. Isaac + Claude Opus 4.6 via Claude Code.",
        "",
        "## Sessions",
        "",
        "| # | Date | Description | Messages |",
        "|--:|------|-------------|:--------:|",
    ]

    for i, (start_ts, session_id, jsonl_file) in enumerate(convos, 1):
        print(f"[{i}/{len(convos)}] {session_id[:8]}... ({start_ts.strftime('%Y-%m-%d')})")

        messages = parse_conversation(jsonl_file)
        if not messages:
            print(f"  (empty, skipping)")
            continue

        turns = merge_messages(messages)

        # Label
        label = label_conversation(start_ts)
        desc = extract_description(turns) if not label else ""

        md = turns_to_markdown(turns, session_id, start_ts, label=label)

        filename = f"{i:02d}_{start_ts.strftime('%Y-%m-%d')}_{session_id[:8]}.md"
        out_path = OUT_DIR / filename
        with open(out_path, "w") as f:
            f.write(md)

        date_str = start_ts.strftime("%b %d, %H:%M")
        n_turns = len([t for t in turns if t["texts"]])  # turns with actual text
        display_label = label or desc or ""
        if len(display_label) > 80:
            display_label = display_label[:77] + "..."
        index_lines.append(
            f"| {i} | [{date_str}]({filename}) | {display_label} | {n_turns} |"
        )
        print(f"  -> {filename} ({len(turns)} turns, label: {label or '(auto)'})")

    # Memory section
    index_lines.extend([
        "",
        "## Memory",
        "",
        "Session summaries, feedback, and references accumulated across conversations.",
        "These files were written by Claude as persistent memory across sessions.",
        "",
        "See [`memory/MEMORY.md`](memory/MEMORY.md) for the full index.",
    ])

    # Write index
    index_path = OUT_DIR / "README.md"
    with open(index_path, "w") as f:
        f.write("\n".join(index_lines) + "\n")

    # Sync memory
    memory_out = OUT_DIR / "memory"
    if MEMORY_DIR.is_dir():
        if memory_out.exists():
            shutil.rmtree(memory_out)
        shutil.copytree(MEMORY_DIR, memory_out)
        n_files = len(list(memory_out.glob("*.md")))
        print(f"Synced {n_files} memory files -> {memory_out}/")

    print(f"\nDone. {len(convos)} conversations -> {OUT_DIR}/")


if __name__ == "__main__":
    main()
