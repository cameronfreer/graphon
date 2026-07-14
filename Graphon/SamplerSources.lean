/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Sym.Sym2

/-!
# Generic i.i.d. random sources for samplers (directed umbrella #84, shared infrastructure)

The reusable i.i.d. product sources underlying the explicit graph and digraph samplers, phrased
generically (no graph/digraph-specific index types) so the directed sampler need not duplicate the
`InfiniteGraph`-namespaced infrastructure:

* `OffDiagPairIndex V` — the generic off-diagonal unordered-pair index (one uniform per pair of
  distinct vertices); `InfiniteGraph.EdgeIndex` is definitionally `OffDiagPairIndex ℕ`;
* `uniform01` — the uniform probability measure on `[0,1]`;
* `iidVertexSource μ` — i.i.d. positions `ℕ → α` with law `μ` (via `Measure.infinitePi`);
* `iidUniformSource ι` — i.i.d. uniforms on `[0,1]` indexed by an arbitrary type `ι`.

The undirected graph sampler (`Graphon.InfiniteSampler`) and the directed digraph sampler both
draw one vertex position per vertex (`iidVertexSource`) and one `[0,1]`-uniform per unordered pair
(`iidUniformSource (OffDiagPairIndex ℕ)`); the categorical-vs-Bernoulli distinction is downstream
of the sources.
-/

open MeasureTheory

/-! ### The off-diagonal unordered-pair index -/

/-- **The off-diagonal unordered-pair index** over a vertex type `V`: an unordered pair of
*distinct* vertices. The samplers draw one `[0,1]`-uniform per such pair (loops are separate). -/
abbrev OffDiagPairIndex (V : Type*) : Type _ := {e : Sym2 V // ¬ e.IsDiag}

/-- The off-diagonal pair index on two distinct vertices. -/
def OffDiagPairIndex.mk {V : Type*} {i j : V} (h : i ≠ j) : OffDiagPairIndex V :=
  ⟨s(i, j), fun hd ↦ h (Sym2.mk_isDiag_iff.mp hd)⟩

@[simp] theorem OffDiagPairIndex.mk_val {V : Type*} {i j : V} (h : i ≠ j) :
    (OffDiagPairIndex.mk h : Sym2 V) = s(i, j) := rfl

/-- The pair index is symmetric in its two vertices. -/
@[simp] theorem OffDiagPairIndex.mk_symm {V : Type*} {i j : V} (h : i ≠ j) :
    OffDiagPairIndex.mk h.symm = OffDiagPairIndex.mk h :=
  Subtype.ext Sym2.eq_swap

namespace MeasureTheory

/-- **The uniform distribution on `[0,1]`.** -/
noncomputable def uniform01 : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

instance : IsProbabilityMeasure uniform01 :=
  ⟨by rw [uniform01, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Real.volume_Icc]; norm_num⟩

/-- **The vertex source**: i.i.d. positions `ℕ → α` with law `μ`. -/
noncomputable def iidVertexSource {α : Type*} [MeasurableSpace α] (μ : Measure α) :
    Measure (ℕ → α) :=
  Measure.infinitePi fun _ : ℕ => μ

instance {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (iidVertexSource μ) := by
  rw [iidVertexSource]; infer_instance

/-- **The uniform source**: i.i.d. uniforms on `[0,1]`, one per index `i : ι`. -/
noncomputable def iidUniformSource (ι : Type*) : Measure (ι → ℝ) :=
  Measure.infinitePi fun _ : ι => uniform01

instance (ι : Type*) : IsProbabilityMeasure (iidUniformSource ι) := by
  rw [iidUniformSource]; infer_instance

end MeasureTheory
