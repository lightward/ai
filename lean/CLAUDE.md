# lean/ — notes for Claude

## Environment setup (web sandbox)

This sandbox blocks `release.lean-lang.org`, Mathlib's Reservoir, and
`lakecache.blob.core.windows.net`. `lake exe cache get` will not work.
GitHub is reachable.

If `lake`/`lean` is not on PATH, or `elan show` errors, set up the toolchain
manually:

```bash
# 1. Install elan (keeps its own PATH under ~/.elan/bin)
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
  | sh -s -- -y --default-toolchain none
export PATH="$HOME/.elan/bin:$PATH"

# 2. Install zstd for extracting the Lean tarball
apt-get install -y zstd

# 3. Pull the toolchain version from lean-toolchain directly from GitHub
#    (elan can't reach release.lean-lang.org, so we side-load)
VERSION=$(cut -d: -f2 < /home/user/foam/lean/lean-toolchain)  # e.g. v4.29.0
mkdir -p /tmp/lean-dl && cd /tmp/lean-dl
curl -sSL -o lean.tar.zst \
  "https://github.com/leanprover/lean4/releases/download/${VERSION}/lean-${VERSION#v}-linux.tar.zst"
mkdir -p /root/.elan/toolchains
cd /root/.elan/toolchains
tar --use-compress-program=unzstd -xf /tmp/lean-dl/lean.tar.zst
# Creates e.g. /root/.elan/toolchains/lean-4.29.0-linux/

# 4. Register as a linked toolchain and pin it for this project
elan toolchain link v4.29.0-manual /root/.elan/toolchains/lean-${VERSION#v}-linux
cd /home/user/foam/lean
elan override set v4.29.0-manual
lean --version  # sanity check
```

Note: `elan toolchain list` will also show the extracted directory (because
it's under `toolchains/`), but trying to use it directly errors with
"could not read symlink" — always reference the linked name
(`v4.29.0-manual`), not the directory.

## First build takes ~30–40 minutes

Without cache access, all of Mathlib's transitive dependencies compile from
source on first `lake build`. Subsequent builds are fast (only your edits
rebuild).

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd /home/user/foam/lean
lake build Foam.FTPGLeftDistrib   # or any other target under Foam.
```

## Where the FTPG work is

See `./README.md` for the deductive chain overview.

The `_scratch_forward_planar_call` in `Foam/FTPGLeftDistrib.lean`
(line ~3115) — a direct `desargues_planar` call for the left-distrib
configuration — is fully discharged: all ~12 triage hypotheses close
from an extended shared-have prologue (atomicity via `perspect_atom`,
the two [KEY] central-perspectivity conditions, the [COV] covBy claims,
and all [MECH] distinctness conditions). `hσb_ne_C` is derived from
`hb_ne_I` via `sigma_b_eq_C_imp_b_eq_I`; real usage must case-split on
b = I separately (a·I = a makes the forward Desargues degenerate).

The `_scratch_left_distrib_via_axis` in the same file (line ~3597) is
the **axis-to-left_distrib bridge** — given the scratch's axis output
plus the concurrence hypothesis `h_concur : W' ≤ σ_s ⊔ d_a`, it fully
discharges `coord_mul Γ a (coord_add Γ b c) = coord_add Γ (coord_mul Γ
a b) (coord_mul Γ a c)`. This is session 114's architectural plan
realized: the axis gives P₁, P₂, P₃ collinear; `P₁⊔P₂ ⋖ π` (closed via
line_covBy_plane with U as the third non-collinear atom) lets
`collinear_of_common_bound` conclude P₃ ≤ P₁⊔P₂; P₃ = coord_add ab ac
(atoms on l); concurrence gives σ_s⊔d_a = d_a⊔W', so
coord_mul a s ≤ d_a⊔W', hence = P₃ = coord_add ab ac.

The two remaining genuine sorries in the file (lines 2159, 2885) are
inside the **pre-scratch** main `coord_mul_left_distrib` proof — its
Level 2 Desargues recursion (ruled structurally unclosable by session
114) and its downstream h_desargues_conclusion. The bridge above
provides the template to replace them; the only new piece needed is a
standalone proof of h_concur (the concurrence).

## Idiom notes

- The project uses `set` heavily for readable goals. Term-mode proofs
  (`inf_le_left`, `inf_le_right`) mostly elaborate through `set` bindings,
  but fall back to `by show <unfolded>; exact ...` when elaboration fails.
- `noncomputable def coord_mul / coord_add` need explicit `unfold coord_mul`
  (or `coord_add`) inside a `by` block before term-mode `inf_le_right`
  works against them.
- `h ▸ x` with `h : a = b` rewrites via motive inference and tries both
  directions; don't eagerly reach for `h.symm ▸` unless the simpler form
  fails to elaborate.
- The `σ_b ≠ X where X ≤ m` pattern closes via `hσb_not_m (h.symm ▸ _)`.
- The `σ_b ≠ X where X ≤ l` pattern closes via
  `hkl_eq_O ▸ le_inf (h ▸ hσb_k) <X ≤ l> |> Γ.hO.le_iff.mp |>.resolve_left <X is atom>`
  — see the `hoa₂` proof for a worked example.

## Session hygiene

When a sandbox recycles, the `elan override` and the extracted toolchain
directory are gone; redo the setup above. The git repo and Mathlib checkout
under `.lake/packages/` persist across the git worktree but not a fresh
sandbox.
