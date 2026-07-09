# Overlay scoping for `exists_mpEquiv_cutNormDiff_lt_add`

**Status (2026-07-09).** R2 has discharged three of the four corrected Rokhlin cores:

- `MeasurePreserving.exists_controlled_cell_alignment`
- `MeasurePreserving.exists_common_coupling_maps`
- `cutNormDiff_pullback_le`

The only live graphon-theory core left is:

```lean
theorem exists_mpEquiv_cutNormDiff_lt_add [StandardBorelSpace α] [NoAtoms μ]
    (U W : Graphon α μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (σ : α ≃ᵐ α) (hσ : MeasurePreserving σ μ μ),
      cutNormDiff (pullback U σ hσ) W < cutDistance U W + ε
```

All remaining project sorries outside this core are frozen known-false/off-route stubs.

## 1. Why this core is different

`cutDistance` is an infimum over pairs of measure-preserving maps:

```lean
cutNormDiff (pullback U φ hφ) (pullback W ψ hψ)
```

The remaining core asks for a single measure-preserving **bijection** `σ` and a bare `W`:

```lean
cutNormDiff (pullback U σ hσ) W
```

This is not a formal consequence of `exists_common_coupling_maps` or
`cutNormDiff_pullback_le`. Non-injective MP maps, e.g. the doubling map, cannot be cancelled
or inverted pointwise. The missing theorem is the classical overlay fact: on an atomless
space, couplings of two graphons can be approximated in cut norm by graphs of
measure-preserving bijections.

## 2. Exact consumer

The sole live consumer is `exists_cutNormDiff_cauchy_realignment` in
`Graphon/Compactness.lean`.

At step `k`, the proof needs:

```lean
∃ σ : α ≃ᵐ α, MeasurePreserving σ μ μ ∧
  cutNormDiff (pullback (V (k + 1)) σ hσ) (V k)
    < cutDistance (V (k + 1)) (V k) + 1 / 3 ^ k
```

Then it builds coherent frames by recursion:

```lean
f 0 = refl
f (k + 1) = (f k).trans σ_k
```

This recursive frame is exactly why a coupling-only telescope does not replace the core:
the same middle graphon must be a bare reference at one step and a pulled-back graphon at
the next. Coupling maps can align two frames locally, but they do not produce a fixed
invertible frame sequence.

## 3. Minimal overlay theorem

A consumer-shaped theorem sufficient for the core is:

```lean
theorem cutDistance_maps_to_equiv_overlay
    [StandardBorelSpace α] [NoAtoms μ]
    (U W : Graphon α μ)
    (φ ψ : α → α) (hφ : MeasurePreserving φ μ μ) (hψ : MeasurePreserving ψ μ μ)
    {η : ℝ} (hη : 0 < η) :
    ∃ (σ : α ≃ᵐ α) (hσ : MeasurePreserving σ μ μ),
      cutNormDiff (pullback U σ hσ) W
        ≤ cutNormDiff (pullback U φ hφ) (pullback W ψ hψ) + η
```

Then `exists_mpEquiv_cutNormDiff_lt_add` follows by choosing near-optimal maps
`φ, ψ` from `cutDistance_lt_add_of_pos` at error `ε / 2`, applying the overlay theorem at
error `ε / 2`, and combining inequalities.

This theorem is preferable to attacking `exists_mpEquiv_cutNormDiff_lt_add` directly
because it isolates the analytic content from the `sInf` bookkeeping.

## 4. Expected proof route

The proof should be built as a separate campaign, not folded into the completeness proof.

1. **Step approximation.** Approximate `U` and `W` in cut norm by step graphons on a common
   finite equipartition. This reduces the overlay estimate to finitely many cell-pair
   coefficients.

2. **Coupling matrix.** Push `μ` through `(φ, ψ)` and record the finite coupling matrix
   between source cells and target cells. The row and column sums are the common cell
   measures because `φ` and `ψ` are measure-preserving.

3. **Finite overlay.** Approximate the finite coupling matrix by a rational coupling, split
   cells into equal subcells, and realize the rational coupling by a permutation of subcells.
   This is the finite Birkhoff/integer-matching step.

4. **Realize as an MP bijection.** Use the already-proved
   `MeasurePreserving.exists_controlled_cell_alignment` to turn the finite subcell
   permutation into a measure-preserving `α ≃ᵐ α`.

5. **Cut-norm error.** Bound the error between the original coupling pullback and the
   permutation graph by the step approximation error plus the rational-coupling error.

## 5. Work plan

Recommended first Lean target:

```lean
theorem finiteCoupling_approximated_by_cellPermutation
```

for finite probability vectors, producing a common refinement and a permutation of equal
mass atoms approximating a bistochastic matrix. Keep it graphon-free.

Second target:

```lean
theorem stepGraphon_overlay_by_mpEquiv
```

for step graphons on equal-measure finite partitions, consuming the finite theorem and
`exists_controlled_cell_alignment`.

Only after those land should the full `cutDistance_maps_to_equiv_overlay` be assembled.

## 6. Decision

Do not try to eliminate `exists_mpEquiv_cutNormDiff_lt_add` by further coupling-telescope
rewrites. The current proof architecture already uses coupling maps where they suffice;
the remaining core is exactly the overlay/bijection-density theorem.
