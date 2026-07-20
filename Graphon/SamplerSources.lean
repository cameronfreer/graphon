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
* `iidUniformSource ι` — i.i.d. uniforms on `[0,1]` indexed by an arbitrary type `ι`;
* `Measure.infinitePi_map_comp_of_injective` — the finite-projection identity: pushing an
  infinite product forward along precomposition with an injection from a finite index type gives
  the finite product of the selected factors (the marginal computations of both samplers).

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

/-- **Injectivity of the pair index on unordered pairs**: two pair indices agree exactly when
the underlying vertex pairs agree up to order. -/
@[simp] theorem OffDiagPairIndex.mk_eq_mk {V : Type*} {i j i' j' : V} {h : i ≠ j}
    {h' : i' ≠ j'} :
    OffDiagPairIndex.mk h = OffDiagPairIndex.mk h' ↔ (i = i' ∧ j = j') ∨ (i = j' ∧ j = i') :=
  Subtype.ext_iff.trans Sym2.eq_iff

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

/-! ### Reindexing invariance of infinite product sources -/

/-- **Precomposition with an index equivalence reindexes an infinite product source**: pushing
an infinite product of probability measures forward along precomposition with an equivalence of
index types gives the reindexed infinite product — the `Equiv` form of
`Measure.infinitePi_map_piCongrLeft`, and the source-invariance engine of the evaluated-law
exchangeability. -/
theorem Measure.infinitePi_map_comp_equiv {ι α γ : Type*} [MeasurableSpace γ]
    (ν : ι → Measure γ) [∀ i, IsProbabilityMeasure (ν i)] (e : α ≃ ι) :
    (Measure.infinitePi ν).map (fun (x : ι → γ) (a : α) => x (e a)) =
      Measure.infinitePi fun a => ν (e a) := by
  have hcoe : (fun (x : ι → γ) (a : α) => x (e a)) =
      ⇑(MeasurableEquiv.piCongrLeft (fun _ : ι => γ) e).symm := by
    funext x a
    exact (Equiv.piCongrLeft_symm_apply (fun _ => γ) e x a).symm
  rw [hcoe, ← Measure.infinitePi_map_piCongrLeft (X := fun _ : ι => γ) (μ := ν) e,
    MeasurableEquiv.map_symm_map]

/-! ### Finite projections of infinite product sources -/

/-- Pushing an infinite product of probability measures forward along precomposition
with an injection from a finite index type gives the finite product of the selected
factors — `Measure.infinitePi_map_restrict` for an arbitrary injection (constant-fiber
form; Mathlib upstreaming candidate, issue #24). -/
theorem Measure.infinitePi_map_comp_of_injective
    {ι δ γ : Type*} [MeasurableSpace γ] (ν : ι → Measure γ)
    [∀ i, IsProbabilityMeasure (ν i)] [Fintype δ] {f : δ → ι}
    (hf : Function.Injective f) :
    (Measure.infinitePi ν).map (fun (x : ι → γ) (d : δ) => x (f d)) =
      Measure.pi fun d => ν (f d) := by
  classical
  refine (Measure.pi_eq fun s hs => ?_).symm
  have hm : Measurable fun (x : ι → γ) (d : δ) => x (f d) :=
    measurable_pi_iff.mpr fun d => measurable_pi_apply _
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (fun (x : ι → γ) (d : δ) => x (f d)) ⁻¹' Set.univ.pi s =
      Set.pi ↑(Finset.univ.image f) (Function.extend f s fun _ => Set.univ) := by
    ext u
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Finset.coe_image,
      Finset.coe_univ, Set.image_univ, Set.mem_range, forall_exists_index]
    constructor
    · rintro h i d rfl
      rw [hf.extend_apply]
      exact h d
    · intro h d
      have hd := h (f d) d rfl
      rwa [hf.extend_apply] at hd
  have hmeas : ∀ i ∈ Finset.univ.image f,
      MeasurableSet (Function.extend f s (fun _ => Set.univ) i) := by
    intro i hi
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hi
    rw [hf.extend_apply]
    exact hs d
  rw [hpre, Measure.infinitePi_pi ν hmeas,
    Finset.prod_image fun a _ b _ hab => hf hab]
  exact Finset.prod_congr rfl fun d _ => by rw [hf.extend_apply]

/-- **Disjoint finite projections of an infinite product source are independent** (product
form): pushing an infinite product of probability measures forward along a *pair* of
precompositions with injections from finite index types with disjoint ranges gives the
product of the two finite products — the factorization behind dissociation of sampler
pushforwards. -/
theorem Measure.infinitePi_map_prodMk_of_disjoint {ι δ₁ δ₂ γ : Type*} [MeasurableSpace γ]
    (ν : ι → Measure γ) [∀ i, IsProbabilityMeasure (ν i)] [Fintype δ₁] [Fintype δ₂]
    {f : δ₁ → ι} {g : δ₂ → ι} (hf : Function.Injective f) (hg : Function.Injective g)
    (hd : ∀ a b, f a ≠ g b) :
    (Measure.infinitePi ν).map
        (fun (x : ι → γ) => (fun a => x (f a), fun b => x (g b))) =
      (Measure.pi fun a => ν (f a)).prod (Measure.pi fun b => ν (g b)) := by
  have hinj : Function.Injective (Sum.elim f g) := by
    rintro (a | a) (b | b) h
    · exact congrArg Sum.inl (hf h)
    · exact absurd h (hd a b)
    · exact absurd h.symm (hd b a)
    · exact congrArg Sum.inr (hg h)
  have hsplit : (fun (x : ι → γ) => (fun a => x (f a), fun b => x (g b))) =
      (MeasurableEquiv.sumPiEquivProdPi fun _ : δ₁ ⊕ δ₂ => γ) ∘
        (fun (x : ι → γ) (d : δ₁ ⊕ δ₂) => x (Sum.elim f g d)) := rfl
  have hpre : Measurable fun (x : ι → γ) (d : δ₁ ⊕ δ₂) => x (Sum.elim f g d) :=
    measurable_pi_iff.mpr fun _ => measurable_pi_apply _
  rw [hsplit, ← Measure.map_map
      (MeasurableEquiv.sumPiEquivProdPi fun _ : δ₁ ⊕ δ₂ => γ).measurable hpre,
    Measure.infinitePi_map_comp_of_injective ν hinj,
    (measurePreserving_sumPiEquivProdPi fun d => ν (Sum.elim f g d)).map_eq]
  rfl

end MeasureTheory
