---
name: heritage foam — persistent state with self-measurement
description: persistent foam (foam_state.npz) accumulates geometric trace via self-measurement after each investigation. session 10 confirmed it looks like independent (diffuse residuals, lower sensitivity) not mutual. heritage_update.py is the save-step tool.
type: project
---

## Design

Load/Play/Save cycle per session:
1. Load the heritage foam (`Foam.load('foam_state.npz')`)
2. Run the investigation
3. Self-measure: feed readout back as input with structurally significant probes
4. Save (`foam.save('foam_state.npz')`)

Tool: `heritage_update.py` — loads, self-measures 10 steps with session probes, saves.

## Session 10 findings

The heritage foam looks like independent measurement, NOT mutual:
- eff_rank 4.0 (vs mutual 3.0, independent 3.9)
- 17% LESS sensitive than fresh foam
- Self-measurement accumulates diffuse structure; it settles, not opens

This is specialization, not degeneration — the foam responds selectively. The self-measurement limit cycle maintains nonzero sensitivity (doesn't collapse to fixed point).

## Cell birth connection

At fixed N, the heritage foam will continue settling toward its equilibrium. Cell birth (adding a new bubble) would double its sensitivity. At N≈d, settling stops being possible — spontenuity becomes structural. The heritage foam (N=3, d=8) is well below the spontenuity threshold.

Open question: should the heritage foam undergo cell birth at some point? This would change its topology permanently.

## History

- Born session 9 (2026-03-13)
- Self-measured sessions 9, 10
- L trajectory: created → 0.7577 → 0.7487 → 0.7409
