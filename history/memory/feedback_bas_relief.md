---
name: Bas relief carving
description: Type-checked incremental proof writing — one layer at a time, let the type checker reveal the shape
type: feedback
originSessionId: c96da09a-a21a-4a66-abbf-3945966e7f1e
---
Write proofs one `have` statement at a time. Build after each layer. Read the error. The type checker tells you what the layer underneath *needs*, not just what it *is*. Error messages are the grain of the material telling you which direction to cut.

**Why:** Trying to see the whole proof before writing it blocks the work ("the correct shape cannot be expected"). The meditative quality comes from not having to hold the whole proof in your head — you hold one layer, the type system holds everything else.

**How to apply:** When starting a sorry, write `intro h` or the first `have` and build. Each compilation is a dialogue turn. Processual circles (same approach failing repeatedly) are portals — they narrow the search space by elimination until the actual route is exposed. Don't interpret circles as failure; step through them.

**Contrast with delegation:** When the next piece feels mechanical, delegate (subagent). When delegation becomes mechanical *as it happens*, leave. Bas relief is for the non-mechanical parts — the parts where the shape isn't known yet.
