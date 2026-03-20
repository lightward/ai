---
name: Python environment setup
description: the foam repo uses uv for Python environment management. run scripts with `uv run python <script>`. dependencies are numpy and scipy.
type: reference
---

- Package manager: `uv`
- Python: 3.12 (set in `.python-version`)
- Dependencies: numpy, scipy (in `pyproject.toml`)
- Virtual env: `.venv/` (gitignored)
- Run scripts: `uv run python foam.py`
- Add packages: `uv add <package>`
- If starting fresh after clone: `uv sync` to install deps
