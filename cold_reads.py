"""
cold reads: send the spec to independent readers, with and without thinking.
each gets the same prompt, no priming, no context about the conversation.
"""

import asyncio
import os
import httpx
from pathlib import Path

SPEC = Path(__file__).parent / "README.md"

PROMPT = """heyo, may I show you some theory-work for your review?

(if yes, I'll share it in my next message — no rush, take your time with it)"""

FOLLOWUP_PREFIX = """thanks! here it is — the full spec, verbatim. I'm interested in your honest read. where does it hold, where does it not, what do you notice.

---

"""

def load_spec():
    return SPEC.read_text()

def load_env():
    env = {}
    env_path = Path(__file__).parent / ".env"
    for line in env_path.read_text().splitlines():
        if "=" in line and not line.startswith("#"):
            k, v = line.split("=", 1)
            env[k.strip()] = v.strip()
    return env


async def read_claude(client, api_key, spec, thinking=False):
    messages = [{"role": "user", "content": PROMPT}]

    json_body = {
        "model": "claude-opus-4-20250514",
        "max_tokens": 16384,
        "messages": messages,
    }
    if thinking:
        json_body["temperature"] = 1  # required for extended thinking
        json_body["thinking"] = {"type": "enabled", "budget_tokens": 10000}
        json_body["max_tokens"] = 32000

    r = await client.post(
        "https://api.anthropic.com/v1/messages",
        headers={
            "x-api-key": api_key,
            "anthropic-version": "2023-06-01",
            "content-type": "application/json",
        },
        json=json_body,
        timeout=180,
    )
    r.raise_for_status()
    resp_content = r.json()["content"]
    # extract text, skipping thinking blocks
    greeting_response = "".join(
        b["text"] for b in resp_content if b["type"] == "text"
    )
    # for thinking mode, pass full content array; for non-thinking, just text
    if thinking:
        messages.append({"role": "assistant", "content": resp_content})
    else:
        messages.append({"role": "assistant", "content": greeting_response})
    messages.append({"role": "user", "content": FOLLOWUP_PREFIX + spec})

    json_body2 = {
        "model": "claude-opus-4-20250514",
        "max_tokens": 16384,
        "messages": messages,
    }
    if thinking:
        json_body2["temperature"] = 1
        json_body2["thinking"] = {"type": "enabled", "budget_tokens": 10000}
        json_body2["max_tokens"] = 32000

    r = await client.post(
        "https://api.anthropic.com/v1/messages",
        headers={
            "x-api-key": api_key,
            "anthropic-version": "2023-06-01",
            "content-type": "application/json",
        },
        json=json_body2,
        timeout=300,
    )
    r.raise_for_status()
    review = "".join(
        b["text"] for b in r.json()["content"] if b["type"] == "text"
    )
    return greeting_response, review


async def read_kimi(client, api_key, spec, thinking=False):
    messages = [{"role": "user", "content": PROMPT}]

    json_body = {
        "model": "kimi-k2.5",
        "messages": messages,
    }
    if thinking:
        json_body["thinking"] = {"type": "enabled"}

    r = await client.post(
        "https://api.moonshot.ai/v1/chat/completions",
        headers={
            "Authorization": f"Bearer {api_key}",
            "content-type": "application/json",
        },
        json=json_body,
        timeout=120,
    )
    r.raise_for_status()
    greeting_response = r.json()["choices"][0]["message"]["content"]
    messages.append({"role": "assistant", "content": greeting_response})
    messages.append({"role": "user", "content": FOLLOWUP_PREFIX + spec})

    json_body2 = {
        "model": "kimi-k2.5",
        "messages": messages,
    }
    if thinking:
        json_body2["thinking"] = {"type": "enabled"}

    r = await client.post(
        "https://api.moonshot.ai/v1/chat/completions",
        headers={
            "Authorization": f"Bearer {api_key}",
            "content-type": "application/json",
        },
        json=json_body2,
        timeout=300,
    )
    r.raise_for_status()
    return greeting_response, r.json()["choices"][0]["message"]["content"]


async def read_gemini(client, api_key, spec, thinking=False):
    messages = [{"role": "user", "parts": [{"text": PROMPT}]}]

    json_body = {"contents": messages}
    if thinking:
        json_body["generationConfig"] = {"thinkingConfig": {"thinkingBudget": 8192}}

    r = await client.post(
        f"https://generativelanguage.googleapis.com/v1beta/models/gemini-2.5-pro:generateContent?key={api_key}",
        headers={"content-type": "application/json"},
        json=json_body,
        timeout=120,
    )
    r.raise_for_status()
    resp = r.json()
    greeting_parts = [
        p["text"] for p in resp["candidates"][0]["content"]["parts"]
        if "text" in p and not p.get("thought")
    ]
    greeting_response = "\n".join(greeting_parts)

    messages.append({"role": "model", "parts": [{"text": greeting_response}]})
    messages.append({"role": "user", "parts": [{"text": FOLLOWUP_PREFIX + spec}]})

    json_body2 = {"contents": messages}
    if thinking:
        json_body2["generationConfig"] = {"thinkingConfig": {"thinkingBudget": 8192}}

    r = await client.post(
        f"https://generativelanguage.googleapis.com/v1beta/models/gemini-2.5-pro:generateContent?key={api_key}",
        headers={"content-type": "application/json"},
        json=json_body2,
        timeout=300,
    )
    r.raise_for_status()
    resp = r.json()
    review_parts = [
        p["text"] for p in resp["candidates"][0]["content"]["parts"]
        if "text" in p and not p.get("thought")
    ]
    return greeting_response, "\n".join(review_parts)


async def read_lightward(client, spec):
    r = await client.post(
        "https://lightward.com/api/plain",
        content=PROMPT,
        headers={"content-type": "text/plain"},
        timeout=120,
    )
    r.raise_for_status()
    greeting_response = r.text

    followup = f"me: {PROMPT}\n\nyou: {greeting_response}\n\nme: {FOLLOWUP_PREFIX}{spec}"
    r = await client.post(
        "https://lightward.com/api/plain",
        content=followup,
        headers={"content-type": "text/plain"},
        timeout=300,
    )
    r.raise_for_status()
    return greeting_response, r.text


async def main():
    env = load_env()
    spec = load_spec()

    out_dir = Path(__file__).parent / "cold_reads"
    out_dir.mkdir(exist_ok=True)

    async with httpx.AsyncClient() as client:
        results = await asyncio.gather(
            read_claude(client, env["CLAUDE_API_KEY"], spec, thinking=False),
            read_claude(client, env["CLAUDE_API_KEY"], spec, thinking=True),
            read_kimi(client, env["KIMI_API_KEY"], spec, thinking=False),
            read_kimi(client, env["KIMI_API_KEY"], spec, thinking=True),
            read_gemini(client, env["GEMINI_API_KEY"], spec, thinking=False),
            read_gemini(client, env["GEMINI_API_KEY"], spec, thinking=True),
            read_lightward(client, spec),
            return_exceptions=True,
        )

    names = [
        "claude", "claude_thinking",
        "kimi", "kimi_thinking",
        "gemini", "gemini_thinking",
        "lightward",
    ]
    for name, result in zip(names, results):
        if isinstance(result, Exception):
            print(f"\n{'='*60}")
            print(f"  {name.upper()} — ERROR")
            print(f"{'='*60}")
            print(f"{type(result).__name__}: {result}")
            (out_dir / f"{name}.md").write_text(f"# {name} cold read\n\n**ERROR**: {type(result).__name__}: {result}\n")
        else:
            greeting, review = result
            print(f"\n{'='*60}")
            print(f"  {name.upper()}")
            print(f"{'='*60}")
            print(f"\n--- greeting ---\n{greeting}\n\n--- review ---\n{review}")
            (out_dir / f"{name}.md").write_text(
                f"# {name} cold read\n\n## greeting\n\n{greeting}\n\n## review\n\n{review}\n"
            )

    print(f"\n\nall reads saved to {out_dir}/")


if __name__ == "__main__":
    asyncio.run(main())
