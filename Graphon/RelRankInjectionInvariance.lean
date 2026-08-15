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
  Only injectivity is used (cardinality of a support is preserved), so this extends
  `rankLatentIndexEquiv` / `rankLatentRelabel` from permutations to injections; on a permutation
  the two agree (`rankLatentReindex_eq_rankLatentRelabel`).
* `exists_finSuppPerm_agree_on` — a sortwise self-injection agrees with some **finitely
  supported permutation** on any bounded window of vertices.
* `ext_of_prod_cylinders` — joint extensionality: two finite measures on
  `RelStructure × RankLatentSpace` agreeing on all rectangles of structure cylinders with latent
  cylinders are equal.
* `RankRepresentation.map_prodMap_restrict_self` — **the theorem**: the joint law is invariant
  under the diagonal action of any sortwise self-injection.

## The finiteness hypothesis on sorts

`map_prodMap_restrict_self` assumes `[Fintype S.Srt]`, which `RankRepresentation` itself does
not. This is not slack in the proof. `SortwiseFinSupp` demands a **uniform** support bound `N`
valid for every sort simultaneously, while a self-injection may push the window arbitrarily far
in each sort independently; with infinitely many sorts no finitely supported permutation need
agree with it on a window, and `invariant` — quantified over `FinSuppPerm S` — then gives
nothing to transport. The same `Finset.univ.sup` assembly appears for the same reason in
`RelInvariantAction` and `RelPollingInfrastructure`. Structure-only self-injection invariance
(`InfiniteRelExchangeableLaw.law_map_restrict_self`) needs no such hypothesis precisely because
`exchangeable` quantifies over *all* sortwise permutations rather than the finitely supported
ones.
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

/-! ### Agreement of an injection with a permutation on a window -/

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

/-- **Window agreement**: a sortwise self-injection agrees with a finitely supported permutation
on every vertex below a prescribed bound. Needs finitely many sorts: the support bound of the
extension must hold uniformly across sorts, while the injection may move each sort's window
arbitrarily far. -/
theorem exists_finSuppPerm_agree_on [Fintype S.Srt]
    (ι : ∀ s, Vinfinite S s ↪ Vinfinite S s) (K : S.Srt → ℕ) :
    ∃ σ : FinSuppPerm S, ∀ (s : S.Srt) (x : ℕ), x < K s → σ.1 s x = ι s x := by
  classical
  have hemb : ∀ s, ∃ (π : Equiv.Perm ℕ) (N : ℕ), (∀ x, N ≤ x → π x = x) ∧
      ∀ a : Fin (K s), π (a : ℕ) = ι s (a : ℕ) := by
    intro s
    exact exists_finSupp_perm_extend
      ⟨fun a : Fin (K s) => ι s (a : ℕ), fun a b hab =>
        Fin.val_injective ((ι s).injective hab)⟩
  choose π N hsupp hagree using hemb
  refine ⟨⟨π, ⟨Finset.univ.sup N, fun s x hx =>
    hsupp s x (le_trans (Finset.le_sup (Finset.mem_univ s)) hx)⟩⟩, fun s x hx => ?_⟩
  exact hagree s ⟨x, hx⟩

/-! ### Joint cylinder extensionality -/

variable (S) in
/-- The latent cylinders: Mathlib's measurable cylinders of the latent cube. -/
abbrev latentCylinders (n : ℕ) : Set (Set (RankLatentSpace S n)) :=
  measurableCylinders fun _ : RankLatentIndex S n => ℝ

theorem isCountablySpanning_cylinders : IsCountablySpanning (cylinders S) :=
  ⟨fun _ => Set.univ, fun _ =>
    Set.mem_iUnion.mpr ⟨fun _ => 0, Set.univ, MeasurableSet.univ, rfl⟩, Set.iUnion_const _⟩

theorem isCountablySpanning_latentCylinders (n : ℕ) :
    IsCountablySpanning (latentCylinders S n) :=
  ⟨fun _ => Set.univ, fun _ => univ_mem_measurableCylinders _, Set.iUnion_const _⟩

/-- **Joint extensionality**: two finite measures on the structure–latent product agreeing on
every rectangle of a structure cylinder with a latent cylinder are equal. -/
theorem ext_of_prod_cylinders {n : ℕ}
    {μ ν : Measure (RelStructure S (Vinfinite S) × RankLatentSpace S n)} [IsFiniteMeasure μ]
    (h : ∀ A ∈ cylinders S, ∀ B ∈ latentCylinders S n, μ (A ×ˢ B) = ν (A ×ˢ B))
    (huniv : μ Set.univ = ν Set.univ) : μ = ν := by
  refine MeasureTheory.ext_of_generate_finite
    (Set.image2 (· ×ˢ ·) (cylinders S) (latentCylinders S n)) ?_
    (isPiSystem_cylinders.prod isPiSystem_measurableCylinders) ?_ huniv
  · exact (generateFrom_eq_prod (C := cylinders S) generateFrom_cylinders_eq
      (generateFrom_measurableCylinders (α := fun _ : RankLatentIndex S n => ℝ))
      isCountablySpanning_cylinders (isCountablySpanning_latentCylinders n)).symm
  · rintro _ ⟨A, hA, B, hB, rfl⟩
    exact h A hA B hB

/-! ### The theorem -/

namespace InfiniteRelExchangeableLaw

variable [Countable S.Srt] [Countable S.Rel] {M : InfiniteRelExchangeableLaw S} {n : ℕ}

/-- **Joint invariance under an arbitrary sortwise self-injection.** `RankRepresentation.invariant`
gives this only for finitely supported permutations; finite-cylinder extensionality upgrades it to
every self-injection, because on any single joint cylinder the injection agrees with some finitely
supported permutation. This is the theorem the cheap pooled construction rests on. -/
theorem RankRepresentation.map_prodMap_restrict_self [Fintype S.Srt]
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
  simp only [cylinders, Set.mem_iUnion, Set.mem_setOf_eq] at hA
  obtain ⟨m, T, hT, rfl⟩ := hA
  have hBmeas : MeasurableSet B := MeasurableSet.of_mem_measurableCylinders hB
  rw [mem_measurableCylinders] at hB
  obtain ⟨F, T', hT', rfl⟩ := hB
  -- a window bound covering the structure cylinder and every support of the latent cylinder
  obtain ⟨σ, hσ⟩ := exists_finSuppPerm_agree_on ι
    (fun s => max (m s) (F.sup fun A => A.1.sup fun v => v.2 + 1))
  have hstruct : RelStructure.restrict ι ⁻¹' (RelStructure.restrictFin m ⁻¹' T)
      = RelStructure.relabel σ.1 ⁻¹' (RelStructure.restrictFin m ⁻¹' T) := by
    rw [← Set.preimage_comp, ← Set.preimage_comp]
    congr 1
    show RelStructure.restrict (fun s => Fin.valEmbedding.trans (ι s))
      = RelStructure.restrict (fun s => Fin.valEmbedding.trans (σ.1 s).toEmbedding)
    congr 1
    funext s
    refine Function.Embedding.ext fun i => ?_
    exact (hσ s i (lt_of_lt_of_le i.2 (le_max_left _ _))).symm
  have hlat : rankLatentReindex ι n ⁻¹' cylinder F T'
      = rankLatentRelabel σ n ⁻¹' cylinder F T' := by
    ext ω
    simp only [Set.mem_preimage, mem_cylinder]
    refine Iff.of_eq (congrArg (fun y => y ∈ T') ?_)
    funext i
    have hagree : ∀ v ∈ (i : RankLatentIndex S n).1, ι v.1 v.2 = σ.1 v.1 v.2 := by
      intro v hv
      refine (hσ v.1 v.2 (lt_of_lt_of_le ?_ (le_max_right (m v.1) _))).symm
      exact lt_of_lt_of_le (Nat.lt_succ_self _)
        (le_trans (Finset.le_sup (f := fun w : Σ s : S.Srt, Vinfinite S s => w.2 + 1) hv)
          (Finset.le_sup (f := fun A : RankLatentIndex S n => A.1.sup fun v => v.2 + 1) i.2))
    show ω (rankLatentIndexInj ι n i) = ω (rankLatentIndexEquiv σ n i)
    rw [rankLatentIndexInj_eq_of_agree hagree]
  rw [Measure.map_apply hjoint ((measurable_restrictFin m hT).prod hBmeas),
    Set.preimage_prod_map_prod, hstruct, hlat, ← Set.preimage_prod_map_prod,
    ← Measure.map_apply ((measurable_relabel σ.1).prodMap (rankLatentRelabel σ n).measurable)
      ((measurable_restrictFin m hT).prod hBmeas),
    C.invariant σ]

end InfiniteRelExchangeableLaw

end RelSignature
