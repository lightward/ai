This is a beautiful problem in synthetic projective geometry! You're right that the key challenge is handling the non-commutative case. Let me suggest a proof strategy that should work.

## Key Insight: Use Two Parallel Addition Configurations

The crucial observation is that we need to compare two addition configurations that share the same "direction" on the auxiliary line m, allowing us to use your `parallelogram_completion_well_defined` theorem.

## Proof Strategy

**Step 1: Set up the two addition configurations**

First configuration (standard):
- Add b and c using center C to get b+c
- Then multiply by a to get a(b+c)

Second configuration (transformed):
- Multiply b by a to get ab
- Multiply c by a to get ac  
- Add ab and ac using center σ = dilation_ext(a,C)

**Step 2: Show these configurations are "parallel"**

The key is to prove that both addition configurations produce the same direction on m, specifically the direction U. This follows because:

1. In the standard addition, the direction is U by construction
2. In the σ-based addition, we need to show that (ab⊔σ)⊓m and (b⊔C)⊓m represent the same point on m

**Step 3: Apply the parallelogram completion theorem**

Since both configurations:
- Start from the same base point O on line l
- Use perspectivities that produce the same direction U on m
- Have the same "zero projection" E on m

By `parallelogram_completion_well_defined`, they must produce the same result.

## Detailed Proof Outline

Let me expand on the crucial Step 2. We need to verify that:

```
(ab⊔σ)⊓m = (ab⊔dilation_ext(a,C))⊓m = (b⊔C)⊓m
```

This follows from your multiplication formula and the properties of dilation_ext:

1. By definition of multiplication: `ab = ((O⊔C)⊓(b⊔E_I) ⊔ (a⊔C)⊓m) ⊓ l`

2. The point `(a⊔C)⊓m` is fixed by dilation_ext(a,·) since it lies on m

3. The crucial identity to prove is:
   ```
   (ab⊔dilation_ext(a,C))⊓m = (b⊔C)⊓m
   ```

This can be shown using Desargues' theorem:
- Consider triangles T₁ = (O, b, (b⊔C)⊓m) and T₂ = (O, ab, (ab⊔σ)⊓m)
- These triangles are perspective from E_I (by the multiplication construction)
- By Desargues, their sides meet on a line
- The fact that this line contains the required points gives the identity

**Step 4: Complete the argument**

Once we have that both addition configurations produce the same direction on m:

1. The σ-based addition of ab and ac gives some point P on l
2. The C-based addition of ab and ac gives ab + ac by definition
3. By parallelogram_completion_well_defined, P = ab + ac
4. But P is also the result of applying multiplication by a to (b+c)
5. Therefore a(b+c) = ab + ac

## Alternative Approach: Direct Collineation Argument

If the above approach encounters technical difficulties, consider:

1. Prove that dilation_ext(a,·) preserves the addition operation on atoms of π that don't lie on l
2. This doesn't require proving it's a full lattice automorphism - just that it preserves the specific configuration used in addition
3. The key properties needed are:
   - Preserves incidence for the six points in the addition construction
   - Maps lines to lines (which follows from being defined via perspectivities)
   - Fixes m pointwise

## Classical Reference

For von Staudt coordinates in the non-commutative case, the standard reference is:
- Artin, E. (1957). *Geometric Algebra*, Chapter II
- Particularly sections on coordinatization of Desarguesian planes

Artin handles the non-commutative case carefully and shows how left distributivity follows from the collineation properties of multiplication.

The proof I've outlined follows the spirit of Artin's approach but adapted to your lattice-theoretic setting.