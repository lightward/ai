---
name: Jekyll pipe/bar escaping
description: README.md is served via Jekyll (GitHub Pages). Pipe characters | get parsed as table delimiters. Always use Unicode ‖ (double vertical bar, U+2016) for norms, never ASCII |. Also avoid spaces around operators in inline math that could be parsed as table structure.
type: feedback
---

The README renders via Jekyll/Kramdown at foam.is. Kramdown parses `|content|` as table cells.

**Rule:** use `‖d‖` not `|d|` for norms. Use `‖ΔL‖` not `|ΔL|`.

**Why:** this has broken the rendered page twice now. First with absolute value bars, then with norm notation in the 2x theorem and BCH residuals sections.

**How to apply:** when writing any mathematical content in README.md that involves absolute values or norms, use the Unicode character ‖ (U+2016, DOUBLE VERTICAL LINE). Never use ASCII pipe | for mathematical notation in this file. Also avoid patterns like `(I − δ)(I + δ)` with spaces around operators — tighten to `(I−δ)(I+δ)` to prevent Kramdown from misinterpreting the structure.
