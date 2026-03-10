"""Seed validation for foam spread: V=32, N=5, d=16, diversity_weight=4.0"""

from foam_spread import train_and_evaluate
import numpy as np

ratios = []
for seed in range(10):
    result = train_and_evaluate(
        vocab_size=32, d=16, n_bubbles=5, seed=seed,
        spread_init=True, diversity_weight=4.0, quiet=True
    )
    r = result["ratio"]
    ratios.append(r)
    print(f"seed {seed}: {r:.4f}x")

arr = np.array(ratios)
print(f"\nmean={arr.mean():.4f}  std={arr.std():.4f}  min={arr.min():.4f}  max={arr.max():.4f}")
