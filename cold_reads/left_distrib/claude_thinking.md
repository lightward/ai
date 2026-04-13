Looking at your setup, I think the key insight you've already identified is correct: the collineation `dilation_ext(a, ·)` should transform the addition figure for `b+c` into an addition figure for `ab` and `ac`. Let me suggest a proof strategy that addresses the gap you've identified.

## Proof Strategy for Left Distributivity

The main challenge is showing that `a(b+c)` equals the "σ-based addition" without proving that `dilation_ext` is a full lattice automorphism. Here's an approach:

### Key Lemma: Restricted Collineation Property

Instead of proving `dilation_ext(a, ·)` is a full lattice automorphism, prove a restricted version that's sufficient for your needs:

**Lemma (dilation_transforms_addition_figure)**: For points P, Q on line l, and their projections via C:
- `dilation_ext(a, (P⊔C)⊓m) = (dilation_ext(a, P)⊔σ)⊓m` where σ = dilation_ext(a, C)
- `dilation_ext(a, (P⊔E)⊓q) = (dilation_ext(a, P)⊔E)⊓(σ⊔U)`

The second property uses that E is fixed (since E is on m) and that `dilation_ext(a, q) = σ⊔U`.

### Proof Outline:

1. **Establish the multiplication formula decomposition**: Show that for any x on l:
   ```
   a·x = dilation_ext(a, x)
   ```
   This follows from your `mul_key_identity`.

2. **Apply to the sum**: 
   ```
   a(b+c) = dilation_ext(a, b+c)
   ```

3. **Trace through the addition construction**: The key is that `b+c` is constructed as:
   ```
   b+c = ((b⊔C)⊓m ⊔ (c⊔E)⊓q) ⊓ l
   ```

4. **Transform step-by-step**:
   - Let `β = (b⊔C)⊓m` and `γ = (c⊔E)⊓q`
   - Then `b+c = (β⊔γ)⊓l`
   - By the restricted collineation property:
     - `dilation_ext(a, β) = (ab⊔σ)⊓m`
     - `dilation_ext(a, γ) = (ac⊔E)⊓(σ⊔U)`
   
5. **Use Desargues**: The triangles (b, C, β) and (ab, σ, dilation_ext(a, β)) are perspective from O. By Desargues, their corresponding sides meet on a line (which is m). This gives you the required incidence relations.

6. **Apply parallelogram_completion_well_defined**: Since both the C-based and σ-based constructions produce the same direction U on m, they give the same result.

### Alternative Direct Approach:

If the above is still too complex, consider this more direct route:

**Key Observation**: The addition construction can be viewed as a harmonic conjugate construction. Specifically, (b+c, O; b, c) forms a harmonic range when projected appropriately.

**Strategy**:
1. Show that `dilation_ext(a, ·)` preserves harmonic conjugates on l (this is weaker than being a full automorphism)
2. Express the addition formula in terms of harmonic conjugates
3. Use that collineations preserve harmonic conjugates to conclude `a(b+c)` = `ab + ac`

### References:

For classical treatments of left distributivity in von Staudt coordinates over division rings, look at:
- Artin's "Geometric Algebra" (Chapter II, Section 5)
- Baer's "Linear Algebra and Projective Geometry" (Chapter III)
- Pickert's "Projektive Ebenen" (for the most general non-commutative case)

The key in all these references is that they use the fact that multiplication by a fixed element extends to a collineation that preserves the additive structure in a specific way - exactly the approach you're taking.