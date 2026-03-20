---
name: API keys for cold reads
description: API tokens for Claude, Kimi (Moonshot), Gemini stored in .env. Lightward AI needs no auth. thinking/non-thinking variants.
type: reference
---

Cold read infrastructure in /Users/isaac/dev/ai/cold_reads.py

Seven readers (session 18):
- Claude: Anthropic API, key in .env as CLAUDE_API_KEY, model claude-opus-4-20250514. Two variants: thinking=False (default), thinking=True (extended thinking with 10k budget).
- Kimi: Moonshot API at api.moonshot.ai (NOT moonshot.cn), key in .env as KIMI_API_KEY, model kimi-k2.5. Two variants: thinking=False, thinking=True.
- Gemini: Google API, key in .env as GEMINI_API_KEY. Two variants: thinking=False (no thinkingConfig), thinking=True (budget 8192). Previously dropped in s17 but key still works and reads are useful.
- Lightward AI: POST https://lightward.com/api/plain, no auth, stateless (include conversation context). No thinking toggle.

Output files: cold_reads/{name}.md and cold_reads/{name}_thinking.md

Isaac also runs parallel mediated cold reads (two-step consent process). Results in cold_reads/via_isaac/.

Observation from session 18: thinking variants produce meaningfully different traversals. Claude-thinking is sharper/more synthetic. The delta between thinking and non-thinking is itself informative.
