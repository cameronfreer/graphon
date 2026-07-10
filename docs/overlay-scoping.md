# Overlay scoping for `exists_mpEquiv_cutNormDiff_lt_add`

> **OUTCOME (2026-07-09, campaign R3 COMPLETE).** The plan below was executed the same day
> in `Graphon/Overlay.lean` (commits 1d0aa32 O1, 08cb8e4 O2, 85768ea O3): the theorem is
> **proved and axiom-clean**, and with it `complete`, `compact`, `cutDistance_triangle`,
> `first_sampling_lemma`, and `cutDistance_zero_of_homDensity_eq` all verify with standard
> axioms only. The Rokhlin gap is closed; the project has no live sorries.

**Status (2026-07-09, at scoping time).** R2 has discharged three of the four corrected Rokhlin cores:

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

(With the exact-carving route of §4 the intermediate theorem is even stronger: at the
step-graphon level the overlay is realized with `η = 0` — see O2 in §5 — and the `η` in the
general statement comes purely from step approximation of `U` and `W`.)

## 4. Proof route — exact carving, no Birkhoff (scoping upgrade, 2026-07-09)

The proof should be built as a separate campaign, not folded into the completeness proof.

**Key simplification found during scoping**: for *step* graphons, the value of any coupling
`(φ, ψ)` is achieved **exactly** by an MP bijection — no rational approximation of the
coupling matrix, no Birkhoff/permutation matching. The atomless carving primitives realize
arbitrary real masses directly, so the only ε in the whole proof comes from step
approximation (regularity).

Let `U' = stepify P U` (cells `S_i`, values `u_{ii'}`), `W' = stepify Q W` (cells `T_k`,
values `w_{kk'}`) — independent partitions, no common refinement needed — and `(φ, ψ)` an MP
pair. Define the **coupling matrix**

```
λ_{ik} := μ (φ⁻¹(S_i) ∩ ψ⁻¹(T_k)),   ∑_k λ_{ik} = μ(S_i),   ∑_i λ_{ik} = μ(T_k)
```

(marginals because `φ, ψ` are MP). Then:

1. **Carve** (atomless; `exists_measurable_subset_of_measure`): split each `T_k` into
   disjoint measurable `T_{ik} ⊆ T_k` with `μ(T_{ik}) = λ_{ik}`, and each `S_i` into
   `S_{ik} ⊆ S_i` with `μ(S_{ik}) = λ_{ik}`. Two refined partitions, both indexed by
   `(i, k)`, with equal masses cell-by-cell.

2. **Align twice** via the proved `exists_controlled_cell_alignment` (whose a.e. conclusion
   handles null cells `λ_{ik} = 0` vacuously — exactly why its pointwise form was refuted
   and weakened in R2.1):
   - `σ : α ≃ᵐ α` MP with `σ(T_{ik}) ⊆ S_{ik}` a.e. — **the answer bijection**;
   - `τ : α ≃ᵐ α` MP with `τ(T_{ik}) ⊆ φ⁻¹(S_i) ∩ ψ⁻¹(T_k)` a.e. — a **proof-only
     transfer** (same masses `λ_{ik}` on both sides, so R2.1 applies again).

3. **Transfer.** For a.e. `x ∈ T_{ik}`, `y ∈ T_{i'k'}`:
   `(pullback U' φ)(τx, τy) = u_{ii'} = (pullback U' σ)(x, y)` and
   `(pullback W' ψ)(τx, τy) = w_{kk'} = W'(x, y)`. Hence a.e.
   `pullback (pullback U' φ) τ = pullback U' σ` and `pullback (pullback W' ψ) τ = W'`, so

   ```
   cutNormDiff (pullback U' σ) W'
     = cutNormDiff (pullback (pullback U' φ) τ) (pullback (pullback W' ψ) τ)  -- a.e. congr
     = cutNormDiff (pullback U' φ) (pullback W' ψ)                            -- τ bijection
   ```

   the second equality by `cutNormDiff_pullback_measurableEquiv`. This is precisely the
   mechanism already executed once in the totally-bounded net proof
   (`Compactness.lean:~2050–2135`: assemble refined `MeasurablePartition`s with a waste
   cell, apply R2.1, prove a.e. step equality of pullbacks) — reusable as a template.

**ε-budget for the core.** Given `ε > 0`:

1. `regularity` (`Regularity.lean:4550`) at `ε/8` twice: `‖U − U'‖_□ ≤ ε/8`,
   `‖W − W'‖_□ ≤ ε/8`.
2. `cutDistance U' W' ≤ cutDistance U W + ε/4` via the now-proved `cutDistance_triangle`
   plus `cutDistance_le_cutNormDiff`.
3. `cutDistance_lt_add_of_pos` at `ε/8`: MP pair `(φ, ψ)` with
   `cutNormDiff (pullback U' φ) (pullback W' ψ) < cutDistance U' W' + ε/8`.
4. Overlay above: bijection `σ` with `cutNormDiff (pullback U' σ) W'` equal to that value.
5. `cutNormDiff_triangle` twice (σ is a bijection, so
   `cutNormDiff (pullback U σ) (pullback U' σ) = ‖U − U'‖_□`):

   ```
   cutNormDiff (U^σ) W ≤ ε/8 + (cutDistance U W + ε/4 + ε/8) + ε/8
                       = cutDistance U W + 5ε/8 < cutDistance U W + ε.
   ```

   Slack `3ε/8`.

## 5. Work plan (campaign R3; reviewed & corrected 2026-07-09; est. 500–800 lines)

**Architectural corrections from review (all verified against the codebase):**
- **New file `Graphon/Overlay.lean` importing `Graphon.Regularity`** — O1–O3 cannot live in
  CutDistance.lean: `Regularity → Approximation → CutDistance` in the import graph, so
  `regularity`/`stepify`/`exists_measurable_subset_of_measure` are unavailable there.
  Compactness (which imports both) switches to `import Graphon.Overlay`.
- **Relocate the public theorem**: once O2 compiles, delete the sorried
  `exists_mpEquiv_cutNormDiff_lt_add` from CutDistance.lean and redeclare it (identical name,
  statement, docstring) in Overlay.lean. This also fixes declaration order:
  `cutDistance_lt_add_of_pos` (:1806) and `cutDistance_triangle` (:1836) sit *after* the
  current sorry (:1773) in CutDistance.lean.
- **Filter zero coupling cells**: `exists_controlled_cell_alignment` requires
  `Function.Injective` cell families; multiple `λ_{ik} = 0` pieces may all be `∅`. Align only
  `good := {(i,k) | λ_{ik} ≠ 0}` and discard the finite null union a.e. — exactly the
  positive-cell filtering pattern at `Compactness.lean:1980`.
- **No `cutNormDiff_congr_ae` helper**: prove actual graphon *equalities* via
  `Graphon.ext`/`SymmKernel.ext`/`AEEqFun.ext` + `pullback_ae`/`stepify_ae`, then `rw` and
  apply `cutNormDiff_pullback_measurableEquiv`.

**Units:**
- **O1 — finite carving + waste partitions**: for `r : Fin n → ℝ≥0∞` with `∑ i, r i ≤ μ C`,
  produce measurable pairwise-disjoint `A i ⊆ C` with `μ (A i) = r i` (iterate
  `exists_measurable_subset_of_measure`, `Regularity.lean:4669`). Plus a helper assembling a
  `MeasurablePartition` from finitely many disjoint cells + a waste cell.
- **O2 — exact step overlay** (the bulk): the §4 double-alignment lemma, shaped
  `∃ σ hσ, cutNormDiff (pullback (stepify P U) σ hσ) (stepify Q W) =
    cutNormDiff (pullback (stepify P U) φ hφ) (pullback (stepify Q W) ψ hψ)`.
  Enumerate cells, define `λ_{ik}`, prove marginals, carve both refinements (O1), filter
  `λ_{ik} ≠ 0`, apply controlled alignment twice (σ = answer, τ = proof-only transfer).
  `stepify` values are `rectAverage`s but O2 only needs constancy on cells.
- **O3 — assembly + relocation**: `regularity` at `ε/8` for both graphons; near-optimal MP
  maps `(φ, ψ)` **for the original `U, W`** at `ε/8` (`cutDistance_lt_add_of_pos`); use the
  same maps in O2; bound both step-approximation errors under `φ, ψ` via the proved
  contraction `cutNormDiff_pullback_le` + `cutNormDiff_triangle` (no `cutDistance U' W'`
  detour needed): total `cutDistance U W + 5ε/8 < cutDistance U W + ε`. Removes the last
  live Rokhlin sorry; unlocks `complete`/`compact` and the InverseCounting chain.

Commit discipline as in R2: O1/O2 land only sorry-free (the old sorry stays put until O3),
O3's commit removes the crux sorry; `lake build` + sorry scan + `#print axioms` on the
overlay theorem and its completeness/compactness consumers before each commit. Note: `.olean`
files may be stale at campaign start — rebuild before trusting LSP elaboration/axiom checks.

**Ingredient inventory (all verified to exist by name):**

| Ingredient | Location | Status |
|---|---|---|
| `regularity` (Frieze–Kannan weak) + `stepify` | `Regularity.lean:4550` | proved |
| `cutDistance_lt_add_of_pos` (ε-optimal MP pair) | `CutDistance.lean` | proved |
| `exists_measurable_subset_of_measure` (carve prescribed mass) | `Regularity.lean:4669` | proved |
| `exists_equal_chunks_inside` | `Regularity.lean:4851` | proved |
| `exists_controlled_cell_alignment` (R2.1) | `CutDistance.lean` | proved this campaign |
| `cutNormDiff_pullback_measurableEquiv` | `CutDistance.lean` | proved |
| `cutNormDiff_triangle`, `cutDistance_le_cutNormDiff` | `CutDistance.lean` | proved |
| `cutDistance_triangle` | `CutDistance.lean` | fully proved as of R2.4 |
| Refined-partition + waste-cell + R2.1 template | `Compactness.lean:~2050–2135` | proved (net proof) |

## 6. Decision

Do not try to eliminate `exists_mpEquiv_cutNormDiff_lt_add` by further coupling-telescope
rewrites. The current proof architecture already uses coupling maps where they suffice;
the remaining core is exactly the overlay/bijection-density theorem.
