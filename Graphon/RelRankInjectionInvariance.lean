/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelRankRepresentation

/-!
# Joint invariance under sortwise self-injections (R4 converse, #107)

The isolated proof risk of the pooled-latent extension gate: `RankRepresentation.invariant` is
stated for **finitely supported permutations**, but the cheap `poolVertexEquiv` construction of a
pooled object needs the joint law to be invariant under **arbitrary sortwise self-injections**.
This file closes that gap by finite-cylinder extensionality, once and for all, so that full mixed
pooled invariance later costs no additional mathematics.

## Contents

* `rankLatentIndexInj` / `rankLatentReindex` — the latent action of a sortwise self-injection.
  Only injectivity is used (a support keeps its cardinality), so this extends
  `rankLatentIndexEquiv` / `rankLatentRelabel` from permutations to injections; on a permutation
  the two agree (`rankLatentReindex_toEmbedding`).
* `exists_finSuppPerm_agree_on_finset` — a sortwise self-injection agrees with some **finitely
  supported permutation** on any finite set of tagged vertices.
* `ext_of_prod_cylinders` — joint extensionality: two finite measures on
  `RelStructure × RankLatentSpace` agreeing on all rectangles of coordinate cylinders are equal.
* `RankRepresentation.map_prodMap_restrict_self` — **the theorem**: the joint law is invariant
  under the diagonal action of any sortwise self-injection.

## No finiteness hypothesis on sorts

Testing measure equality on *coordinate* cylinders — finitely many `RelCoord`s and finitely many
`RankLatentIndex`es — is what keeps `[Fintype S.Srt]` out of this file. Their combined vertex
support is a single finite `Finset (Σ s, Vinfinite S s)`, so only finitely many sorts are active,
and a self-injection is matched there by a finitely supported permutation: extend it separately on
each active sort, take the identity elsewhere, and take the maximum of the finitely many support
bounds. The coarser `cylinders S` family would not do — a cylinder there is an arbitrary
measurable event after `restrictFin m`, whose finite level can still involve every sort, forcing a
uniform all-sort bound that no self-injection need admit.

-/

open MeasureTheory Set

namespace RelSignature

variable {S : RelSignature}

/-! ### The latent action of a sortwise self-injection -/

open scoped Classical in
/-- The index action of a sortwise self-injection: push a support forward. Injectivity alone
preserves cardinality, so this lands in the same rank. -/
noncomputable def rankLatentIndexInj (ι : ∀ s, Vinfinite S s ↪ Vinfinite S s) (n : ℕ) :
    RankLatentIndex S n → RankLatentIndex S n := fun A =>
  ⟨A.1.image (Sigma.map id fun s => ⇑(ι s)), by
    rw [Finset.card_image_of_injective _
      (Function.injective_id.sigma_map fun s => (ι s).injective)]
    exact A.2⟩

open scoped Classical in
@[simp] theorem rankLatentIndexInj_coe (ι : ∀ s, Vinfinite S s ↪ Vinfinite S s) (n : ℕ)
    (A : RankLatentIndex S n) :
    (rankLatentIndexInj ι n A).1 = A.1.image (Sigma.map id fun s => ⇑(ι s)) := rfl

/-- The latent action of a sortwise self-injection: reindex the cube by pushing supports
forward. For a permutation this is `rankLatentRelabel`. -/
noncomputable def rankLatentReindex (ι : ∀ s, Vinfinite S s ↪ Vinfinite S s) (n : ℕ) :
    RankLatentSpace S n → RankLatentSpace S n := fun ω A => ω (rankLatentIndexInj ι n A)

theorem measurable_rankLatentReindex (ι : ∀ s, Vinfinite S s ↪ Vinfinite S s) (n : ℕ) :
    Measurable (rankLatentReindex (S := S) ι n) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

/-! ### Agreement of an injection with a permutation on a finite support -/

/-- If a sortwise self-injection and a permutation agree on every vertex of a support, they send
that support to the same index. -/
theorem rankLatentIndexInj_eq_of_agree {ι : ∀ s, Vinfinite S s ↪ Vinfinite S s}
    {σ : FinSuppPerm S} {n : ℕ} {A : RankLatentIndex S n}
    (h : ∀ v ∈ A.1, ι v.1 v.2 = σ.1 v.1 v.2) :
    rankLatentIndexInj ι n A = rankLatentIndexEquiv σ n A := by
  classical
  refine Subtype.ext ?_
  rw [rankLatentIndexInj_coe, rankLatentIndexEquiv_apply_coe]
  refine Finset.image_congr fun v hv => ?_
  obtain ⟨s, x⟩ := v
  exact Sigma.ext rfl (heq_of_eq (h ⟨s, x⟩ hv))

@[simp] theorem rankLatentReindex_toEmbedding (σ : FinSuppPerm S) (n : ℕ) :
    rankLatentReindex (S := S) (fun s => (σ.1 s).toEmbedding) n = rankLatentRelabel σ n := by
  funext ω A
  show ω (rankLatentIndexInj (fun s => (σ.1 s).toEmbedding) n A) = _
  rw [rankLatentIndexInj_eq_of_agree (σ := σ) fun v _ => rfl]
  rfl

/-- **Finite-support agreement**: a sortwise self-injection agrees with some finitely supported
permutation on any finite set of tagged vertices. Only the finitely many sorts occurring in that
set are active; every other sort takes the identity, so the support bounds to be maximized are
finite in number — no hypothesis on the sort type is needed. -/
theorem exists_finSuppPerm_agree_on_finset (ι : ∀ s, Vinfinite S s ↪ Vinfinite S s)
    (V : Finset (Σ s : S.Srt, Vinfinite S s)) :
    ∃ σ : FinSuppPerm S, ∀ v ∈ V, σ.1 v.1 v.2 = ι v.1 v.2 := by
  classical
  have hext : ∀ s, ∃ (π : Equiv.Perm ℕ) (N : ℕ), (∀ x, N ≤ x → π x = x) ∧
      ∀ a : Fin ((V.sup fun v => v.2) + 1), π (a : ℕ) = ι s (a : ℕ) := by
    intro s
    exact exists_finSupp_perm_extend
      ⟨fun a : Fin ((V.sup fun v => v.2) + 1) => ι s (a : ℕ), fun a b hab =>
        Fin.val_injective ((ι s).injective hab)⟩
  choose π N hsupp hagree using hext
  refine ⟨⟨fun s => if s ∈ V.image Sigma.fst then π s else 1,
    ⟨(V.image Sigma.fst).sup N, fun s x hx => ?_⟩⟩, fun v hv => ?_⟩
  · by_cases hs : s ∈ V.image Sigma.fst
    · simpa only [if_pos hs] using hsupp s x (le_trans (Finset.le_sup hs) hx)
    · simp only [if_neg hs]
      rfl
  · have hs : v.1 ∈ V.image Sigma.fst := Finset.mem_image.mpr ⟨v, hv, rfl⟩
    have hlt : v.2 < (V.sup fun w => w.2) + 1 :=
      Nat.lt_succ_of_le (Finset.le_sup (f := fun w : Σ s : S.Srt, Vinfinite S s => w.2) hv)
    simpa only [if_pos hs] using hagree v.1 ⟨v.2, hlt⟩

/-! ### Joint cylinder extensionality -/

variable (S) in
/-- The coordinate cylinders of the structure cube: finitely many `RelCoord`s constrained. -/
abbrev structureCylinders : Set (Set (RelStructure S (Vinfinite S))) :=
  measurableCylinders fun _ : RelCoord S (Vinfinite S) => Bool

variable (S) in
/-- The coordinate cylinders of the latent cube: finitely many latent indices constrained. -/
abbrev latentCylinders (n : ℕ) : Set (Set (RankLatentSpace S n)) :=
  measurableCylinders fun _ : RankLatentIndex S n => ℝ

theorem isCountablySpanning_structureCylinders :
    IsCountablySpanning (structureCylinders S) :=
  ⟨fun _ => Set.univ, fun _ => univ_mem_measurableCylinders _, Set.iUnion_const _⟩

theorem isCountablySpanning_latentCylinders (n : ℕ) :
    IsCountablySpanning (latentCylinders S n) :=
  ⟨fun _ => Set.univ, fun _ => univ_mem_measurableCylinders _, Set.iUnion_const _⟩

/-- **Joint extensionality**: two finite measures on the structure–latent product agreeing on
every rectangle of coordinate cylinders are equal. -/
theorem ext_of_prod_cylinders {n : ℕ}
    {μ ν : Measure (RelStructure S (Vinfinite S) × RankLatentSpace S n)} [IsFiniteMeasure μ]
    (h : ∀ A ∈ structureCylinders S, ∀ B ∈ latentCylinders S n, μ (A ×ˢ B) = ν (A ×ˢ B))
    (huniv : μ Set.univ = ν Set.univ) : μ = ν := by
  refine MeasureTheory.ext_of_generate_finite
    (Set.image2 (· ×ˢ ·) (structureCylinders S) (latentCylinders S n)) ?_
    (isPiSystem_measurableCylinders.prod isPiSystem_measurableCylinders) ?_ huniv
  · exact (generateFrom_eq_prod (C := structureCylinders S)
      (generateFrom_measurableCylinders (α := fun _ : RelCoord S (Vinfinite S) => Bool))
      (generateFrom_measurableCylinders (α := fun _ : RankLatentIndex S n => ℝ))
      isCountablySpanning_structureCylinders (isCountablySpanning_latentCylinders n)).symm
  · rintro _ ⟨A, hA, B, hB, rfl⟩
    exact h A hA B hB

/-! ### The theorem -/

namespace InfiniteRelExchangeableLaw

variable [Countable S.Srt] [Countable S.Rel] {M : InfiniteRelExchangeableLaw S} {n : ℕ}

/-- **Joint invariance under an arbitrary sortwise self-injection.** `RankRepresentation.invariant`
gives this only for finitely supported permutations; finite-cylinder extensionality upgrades it to
every self-injection, because on any single joint coordinate cylinder the injection agrees with
some finitely supported permutation. No hypothesis on the sort type: the cylinder's combined
vertex support is finite, hence touches finitely many sorts. This is the theorem the cheap pooled
construction rests on. -/
theorem RankRepresentation.map_prodMap_restrict_self
    (C : M.RankRepresentation n) (ι : ∀ s, Vinfinite S s ↪ Vinfinite S s) :
    C.P.map (Prod.map (RelStructure.restrict ι) (rankLatentReindex ι n)) = C.P := by
  classical
  haveI := C.isProbabilityMeasure_P
  have hjoint : Measurable
      (Prod.map (RelStructure.restrict ι) (rankLatentReindex (S := S) ι n)) :=
    (measurable_restrict ι).prodMap (measurable_rankLatentReindex ι n)
  haveI : IsProbabilityMeasure
      (C.P.map (Prod.map (RelStructure.restrict ι) (rankLatentReindex (S := S) ι n))) :=
    Measure.isProbabilityMeasure_map hjoint.aemeasurable
  refine ext_of_prod_cylinders ?_ (by simp)
  rintro A hA B hB
  have hAmeas : MeasurableSet A := MeasurableSet.of_mem_measurableCylinders hA
  have hBmeas : MeasurableSet B := MeasurableSet.of_mem_measurableCylinders hB
  rw [mem_measurableCylinders] at hA hB
  obtain ⟨Fs, T, hT, rfl⟩ := hA
  obtain ⟨Fl, T', hT', rfl⟩ := hB
  -- the combined vertex support of the two cylinders: finite, so finitely many sorts are active
  obtain ⟨σ, hσ⟩ := exists_finSuppPerm_agree_on_finset ι
    (Fs.biUnion RelCoord.support ∪ Fl.biUnion fun A => A.1)
  have hmemL : ∀ v ∈ Fs.biUnion RelCoord.support, ι v.1 v.2 = σ.1 v.1 v.2 := fun v hv =>
    (hσ v (Finset.mem_union_left _ hv)).symm
  have hmemR : ∀ v ∈ Fl.biUnion fun A => A.1, ι v.1 v.2 = σ.1 v.1 v.2 := fun v hv =>
    (hσ v (Finset.mem_union_right _ hv)).symm
  have hstruct : RelStructure.restrict ι ⁻¹' cylinder Fs T
      = RelStructure.relabel σ.1 ⁻¹' cylinder Fs T := by
    ext X
    simp only [Set.mem_preimage, mem_cylinder]
    refine Iff.of_eq (congrArg (fun y => y ∈ T) ?_)
    funext c
    show X (RelCoord.map (fun s => ⇑(ι s)) c) = X (RelCoord.map (fun s => ⇑(σ.1 s)) c)
    refine congrArg X (Sigma.ext rfl (heq_of_eq (funext fun i => ?_)))
    exact hmemL ((c : RelCoord S (Vinfinite S)).taggedValue i)
      (Finset.mem_biUnion.mpr ⟨c, c.2, (RelCoord.mem_support_iff _ _).mpr ⟨i, rfl⟩⟩)
  have hlat : rankLatentReindex ι n ⁻¹' cylinder Fl T'
      = rankLatentRelabel σ n ⁻¹' cylinder Fl T' := by
    ext ω
    simp only [Set.mem_preimage, mem_cylinder]
    refine Iff.of_eq (congrArg (fun y => y ∈ T') ?_)
    funext i
    show ω (rankLatentIndexInj ι n i) = ω (rankLatentIndexEquiv σ n i)
    exact congrArg ω (rankLatentIndexInj_eq_of_agree fun v hv =>
      hmemR v (Finset.mem_biUnion.mpr ⟨i, i.2, hv⟩))
  rw [Measure.map_apply hjoint (hAmeas.prod hBmeas), Set.preimage_prod_map_prod, hstruct, hlat,
    ← Set.preimage_prod_map_prod,
    ← Measure.map_apply ((measurable_relabel σ.1).prodMap (rankLatentRelabel σ n).measurable)
      (hAmeas.prod hBmeas),
    C.invariant σ]

end InfiniteRelExchangeableLaw

end RelSignature
