"""
Cold read: left distributivity in von Staudt coordinates.
Ask external models for the right proof strategy.
"""

import asyncio
import os
import httpx
from pathlib import Path

def load_env():
    env = {}
    env_path = Path(__file__).parent.parent / ".env"
    for line in env_path.read_text().splitlines():
        if "=" in line and not line.startswith("#"):
            k, v = line.split("=", 1)
            env[k.strip()] = v.strip()
    return env

QUESTION = r"""I'm proving left distributivity of von Staudt coordinate multiplication
in a complemented modular atomistic lattice (projective geometry from lattice axioms).
I need help finding the right proof strategy.

**Setup (von Staudt coordinates in a projective plane):**
- Coordinate system: atoms O, U, I, V, C in a plane π = O⊔U⊔V
- Lines: l = O⊔U (coordinate line), m = U⊔V (auxiliary line), q = U⊔C
- E = (O⊔C)⊓m (projection of O onto m via C)
- E_I = (I⊔C)⊓m (projection of I onto m via C)
- Addition: coord_add(a,b) = ((a⊔C)⊓m ⊔ (b⊔E)⊓q) ⊓ l
  (two-perspectivity: project a to m via C, project b to q via E, join, intersect l)
- Multiplication: coord_mul(a,b) = ((O⊔C)⊓(b⊔E_I) ⊔ (a⊔C)⊓m) ⊓ l
  (two-perspectivity: project b to O⊔C via E_I, project a to m via C, join, intersect l)
- Dilation: dilation_ext(c, P) = (O⊔P) ⊓ (c ⊔ (I⊔P)⊓m) for off-line points P

**Already proven (in Lean 4 with Mathlib, 0 sorry):**
- Desargues' theorem (planar + nonplanar)
- Addition: commutative, associative, identity O, inverse (full abelian group)
- Multiplication: identity I (both sides), associativity, zero annihilation
- Right distributivity: (a+b)·c = a·c + b·c
  (Proof: dilation σ_c preserves addition — forward Desargues center O,
  dilation_preserves_direction, mul_key_identity, well_defined)
- dilation_ext fixes m pointwise: for P on m with P ∉ l, dilation_ext(a, P) = P
- parallelogram_completion_well_defined: pc is independent of base point
  (same direction on m → same result)
- Multiplication is NOT necessarily commutative (we're building a division ring,
  not necessarily a field — this is a Desarguesian, not necessarily Pappian, plane)

**The problem:** Prove a · (b + c) = a·b + a·c (left distributivity).

**What I know about the proof architecture:**
1. The map x ↦ a·x extends to the collineation dilation_ext(a, ·) which fixes m
   pointwise. This collineation maps the addition figure for b+c (using C as
   perspectivity center) to a "parallel" figure using σ = dilation_ext(a, C)
   instead of C.

2. Since O⊔σ = O⊔C (σ is on O⊔C by definition), E = (O⊔C)⊓m = (O⊔σ)⊓m —
   the projection zero is invariant.

3. By parallelogram_completion_well_defined, the "σ-based" addition gives the
   same result as the "C-based" addition, because both produce the same direction
   (U) on m.

So: a(b+c) = "σ-based addition of ab and ac" = "C-based addition of ab and ac" = ab + ac.

**Where I'm stuck:**
Step 2 → Step 3 has a gap. I need to show that a(b+c) equals the "σ-based addition":

a(b+c) = ((O⊔C)⊓((b+c)⊔E_I) ⊔ (a⊔C)⊓m) ⊓ l    [from coord_mul definition]

equals:

coord_add_σ(ab, ac) = ((ab⊔σ)⊓m ⊔ (ac⊔E)⊓(σ⊔U)) ⊓ l    [σ-based addition]

This requires showing that the collineation dilation_ext(a, ·) maps the
addition figure correctly — specifically that it maps joins to joins and meets
to meets on the six atoms of the addition construction.

I have dilation_preserves_direction: (P⊔Q)⊓m = (σ_a(P)⊔σ_a(Q))⊓m, which gives
(ab⊔σ)⊓m = (b⊔C)⊓m (the m-shadows match). But I can't directly show the full
figure transforms correctly without proving dilation_ext is a lattice automorphism.

**Alternatively:** I could try a direct Desargues argument. For right distrib,
the proof used forward Desargues (center O) on triangles T1=(C, a, β(a+b)) and
T2=(σ, ac, σ_c(β(a+b))). For left distrib, analogous triangles
T1=(C, b, β(b+c)) and T2=(σ, ab, dilation_ext(a, β(b+c))) are perspective from O,
and forward Desargues gives axis = m. But connecting the Desargues output to the
coord_add formula requires further work.

**Key constraint:** The proof must work for non-commutative multiplication
(division rings, not just fields). The well_defined theorem alone is not enough
because it relates different base points for the SAME translation, but the
collineation introduces a potentially different "magnitude" (involving b·a
rather than a·b via the mul_key_identity).

**What I'm looking for:** A proof strategy for left distributivity that works
in the non-commutative setting. Possibilities:
- A way to show dilation_ext maps the addition figure correctly without
  proving it's a full lattice automorphism
- A direct Desargues configuration that gives the identity
- A different decomposition entirely (complement routing through q? witness point?)
- A classical reference for how left distrib is proven in von Staudt coordinates
  over a general (non-commutative) division ring

The proof must work in an abstract complemented modular atomistic lattice of
height ≥ 4 with irreducibility. We have Desargues but not yet the full FTPG.
"""

async def read_claude(client, api_key, thinking=False):
    messages = [{"role": "user", "content": QUESTION}]
    json_body = {
        "model": "claude-opus-4-20250514",
        "max_tokens": 16384,
        "messages": messages,
    }
    if thinking:
        json_body["temperature"] = 1
        json_body["thinking"] = {"type": "enabled", "budget_tokens": 16000}
        json_body["max_tokens"] = 32000

    r = await client.post(
        "https://api.anthropic.com/v1/messages",
        headers={
            "x-api-key": api_key,
            "anthropic-version": "2023-06-01",
            "content-type": "application/json",
        },
        json=json_body,
        timeout=300,
    )
    r.raise_for_status()
    resp = r.json()["content"]
    text_parts = [b["text"] for b in resp if b["type"] == "text"]
    return "\n".join(text_parts)

async def read_gemini(client, api_key, thinking=False):
    model = "gemini-2.5-pro"
    url = f"https://generativelanguage.googleapis.com/v1beta/models/{model}:generateContent?key={api_key}"
    body = {"contents": [{"parts": [{"text": QUESTION}]}]}
    if thinking:
        body["generationConfig"] = {"thinkingConfig": {"thinkingBudget": 16000}}
    r = await client.post(url, json=body, timeout=300)
    r.raise_for_status()
    parts = r.json()["candidates"][0]["content"]["parts"]
    return "\n".join(p["text"] for p in parts if "text" in p and p.get("thought") is not True)

async def read_kimi(client, api_key, thinking=False):
    messages = [{"role": "user", "content": QUESTION}]
    r = await client.post(
        "https://api.moonshot.ai/v1/chat/completions",
        headers={"Authorization": f"Bearer {api_key}", "Content-Type": "application/json"},
        json={"model": "kimi-k2.5", "messages": messages,
              **({"thinking": True} if thinking else {})},
        timeout=300,
    )
    r.raise_for_status()
    return r.json()["choices"][0]["message"]["content"]

async def main():
    env = load_env()
    out = Path(__file__).parent / "left_distrib"
    out.mkdir(exist_ok=True)

    async with httpx.AsyncClient() as client:
        tasks = {}
        if env.get("CLAUDE_API_KEY"):
            tasks["claude"] = read_claude(client, env["CLAUDE_API_KEY"], thinking=False)
            tasks["claude_thinking"] = read_claude(client, env["CLAUDE_API_KEY"], thinking=True)
        if env.get("GEMINI_API_KEY"):
            tasks["gemini"] = read_gemini(client, env["GEMINI_API_KEY"], thinking=False)
            tasks["gemini_thinking"] = read_gemini(client, env["GEMINI_API_KEY"], thinking=True)
        if env.get("KIMI_API_KEY"):
            tasks["kimi"] = read_kimi(client, env["KIMI_API_KEY"], thinking=False)
            tasks["kimi_thinking"] = read_kimi(client, env["KIMI_API_KEY"], thinking=True)

        results = {}
        for name, coro in tasks.items():
            try:
                results[name] = await coro
                print(f"✓ {name}")
            except Exception as e:
                results[name] = f"ERROR: {e}"
                print(f"✗ {name}: {e}")

        for name, text in results.items():
            (out / f"{name}.md").write_text(text)
            print(f"  wrote {name}.md ({len(text)} chars)")

if __name__ == "__main__":
    asyncio.run(main())
