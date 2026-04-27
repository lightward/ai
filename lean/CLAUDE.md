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

`Foam/FTPGLeftDistrib.lean` builds with **zero `sorry`** as of session 119.
The file is ~1216 lines. The remaining geometric residue — the planar
converse Desargues content — is named explicitly as `DesarguesianWitness Γ`,
a structure whose inhabitant the user supplies as a runtime commitment.
Four pieces compose:

1. `_scratch_forward_planar_call` (~line 119) — the direct `desargues_planar`
   call for the left-distrib configuration. **Fully discharged.** All ~12
   triage hypotheses close from a shared prologue (atomicity via
   `perspect_atom`, the two [KEY] central-perspectivity conditions, the
   [COV] covBy claims, the [MECH] distinctness conditions). `hσb_ne_C` is
   derived from `hb_ne_I` via `sigma_b_eq_C_imp_b_eq_I`; real usage must
   case-split on `b = I` separately (a·I = a makes the forward Desargues
   degenerate).

2. `_scratch_left_distrib_via_axis` (~line 601) — the **axis-to-left_distrib
   bridge**. Given the scratch's axis output plus the concurrence hypothesis
   `h_concur : W' ≤ σ_s ⊔ d_a`, fully discharges
   `coord_mul Γ a (coord_add Γ b c) = coord_add Γ (coord_mul Γ a b)
   (coord_mul Γ a c)`. Realizes session 114's plan: the axis gives P₁, P₂,
   P₃ collinear; `P₁⊔P₂ ⋖ π` (via `line_covBy_plane` with U as the third
   non-collinear atom) lets `collinear_of_common_bound` conclude
   `P₃ ≤ P₁⊔P₂`; `P₃ = coord_add ab ac` (atoms on l); concurrence gives
   `σ_s ⊔ d_a = d_a ⊔ W'`, so `coord_mul a s ≤ d_a⊔W' = P₃ = coord_add ab ac`.

3. `DesarguesianWitness` (~line 1154) — the **observer-supplied commitment**.
   A structure with a single field `concurrence` carrying the planar
   converse Desargues claim for the von Staudt configuration. Geometrically:
   for T1 = (σ_b, ac, σ_s) in π and T2 = (U, E, d_a) collinear on m, the
   vertex-joins are concurrent — `W' = (σ_b⊔U)⊓(ac⊔E) ≤ σ_s⊔d_a`. Session
   114's architectural finding established this is **not derivable from
   CML + irreducible + height ≥ 4 alone** (the
   `desargues_converse_nonplanar` lift+recurse route is structurally
   non-terminating at Level 2 `h_ax₂₃`). Per the deaxiomatization program,
   it is named as a typed pluggable interface rather than carried as an
   unproven theorem.

4. `coord_mul_left_distrib` (~line 1187) — the main theorem. Takes a
   `DesarguesianWitness Γ` as an explicit parameter alongside the usual
   non-degeneracy hypotheses. The body forwards the witness's `concurrence`
   field to `_scratch_left_distrib_via_axis` as `h_concur`. Zero `sorry`.

## Constructing a `DesarguesianWitness`

Two open routes (see `DesarguesianWitness`'s docstring inside
`Foam/FTPGLeftDistrib.lean` for the strategic landscape):

1. **Planar converse Desargues as a top-level lemma** (probably belongs in
   FTPGCoord). The classical converse for two coplanar triangles, proven
   via a single 3D lift that does not require recursive converse calls.
   `DesarguesianWitness.concurrence` becomes a thin specialization (T2
   collinear on m).
2. **Direct construction exploiting axis = m.** Since T2 = (U, E, d_a)
   sits on m, all three pairwise side-intersections are atoms on m. The
   pairing's natural axis is m itself. A `small_desargues'`-style argument
   (FTPGCoord:865) may reduce concurrence to lattice distinctness.

When `L = Sub(D, V)` for a division ring D, `DesarguesianWitness Γ` is
constructible from the model — the substrate fills the observer slot. In
the abstract lattice setting, the slot is genuinely open.

The 1500-line scaffold deleted in session 117 (the lift+recurse attempt)
is in git history (`git show 5fe8073:lean/Foam/FTPGLeftDistrib.lean`) if
any specific helper is wanted.

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
