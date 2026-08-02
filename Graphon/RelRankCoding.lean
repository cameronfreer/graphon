/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelRankLatents
import Graphon.RelRankSuccessor
import Graphon.RelRankOneTransfer

/-!
# The inductive interface for the rank transition (R4 converse piece 3, #107)

The two objects the rank recursion is organized around, and the base case.

A `RankCoding n` is a *representation of the lower-rank factor by latents*: a measurable map from
the rank-`n` latent space to the rank-`n` factor space representing its law: it carries the
latent source to the factor law and commutes with relabeling almost everywhere. A `ShellProperty n` is the conclusion
the recursion needs at rank `n`: mutual conditional independence of the exact-anchor layers over
the supports of rank `n`, **together with** per-support locality.

## Why the shell theorem is not proved unconditionally

The recursion is `shell_of_rankCoding : RankCoding n → ShellProperty n` followed by
`nextRankCoding : RankCoding n → ShellProperty n → Nonempty (RankCoding (n+1))`, with the
unconditional statement obtained only after both are assembled. This is deliberate. A direct
attack on mutual independence from the two-set theorem, lower-rank intersections and the polling
engine does not work: pairwise conditional independence does not assemble into mutual
independence over the joined lower-rank algebra, and above rank one distinct supports of equal
rank can meet, so a peel would enlarge the conditioning algebra part-way through.

What the induction hypothesis buys is a *represented* lower-rank factor: on the augmented coupling
derived from a `RankCoding n`, a relabeling acts on the latents as well as on the structure. That
joint action is the leverage a direct proof lacks — with no represented factor there is nothing on
the latent side for a relabeling to move.

## Two halves, neither implying the other

`ShellProperty` bundles both because neither follows from the other. Mutual independence given the
*whole* lower-rank factor permits each individual conditional law to depend on all of it; it says
nothing about that dependence being only through `boundaryMap A`. Conversely locality is a
per-support statement and says nothing about joint behaviour across supports.

## Contents

* `RankCoding` — the inductive datum, with `RankCoding.rankOne` constructing it at `n = 1`;
* `ShellProperty` — the conclusion at rank `n`.
-/

open MeasureTheory ProbabilityTheory

namespace RelSignature

namespace CoherentBasis

universe u

variable {S : RelSignature.{u}} {M : InfiniteRelExchangeableLaw S} (B : CoherentBasis M)

/-! ### The inductive datum -/

/-- **A representation of the rank-`n` factor by latents.** "Representation" is about laws, not
about images: `map_f` identifies the pushforward of the latent source with the factor law, and no
pointwise surjectivity onto the factor space is asserted or used.

The equivariance clause is an
almost-everywhere statement, and must be: `lowerFactorSpaceEquiv σ n` fixes the *image* of
`lowerFactorMap n`, not the whole factor space, so the strict version is false already at
`n = 1`. -/
structure RankCoding [Countable S.Srt] [Countable S.Rel] (n : ℕ) where
  /-- The coding map from latents to the rank-`n` factor space. Only the pushforward law is
  constrained, by `map_f`; **no surjectivity is claimed or needed**. -/
  f : RankLatentSpace S n → B.LowerFactorSpace n
  /-- The coding map is measurable. -/
  measurable_f : Measurable f
  /-- It carries the latent source to the law of the factor. -/
  map_f : (rankLatentSource S n).map f =
    (M.law : Measure (RelStructure S (Vinfinite S))).map (B.lowerFactorMap n)
  /-- It intertwines the latent and factor relabeling actions, almost everywhere. -/
  equivariant : ∀ σ : FinSuppPerm S,
    ⇑(B.lowerFactorSpaceEquiv σ n) ∘ f =ᵐ[rankLatentSource S n] f ∘ ⇑(rankLatentRelabel σ n)

/-! ### The conclusion at rank `n` -/

/-- **The shell property at rank `n`**: the two halves the recursion consumes.

Both are stated against `lowerRankAlgebra n` and `boundaryMap A` — the objects the fixing-algebra
machinery is phrased in — rather than against the represented factor. Transfer to
`comap (lowerFactorMap n)` is a separate step, available from the eventwise generation of the
lower-rank algebra together with the conditioning bridge. -/
structure ShellProperty [Countable S.Srt] [Countable S.Rel] (n : ℕ) : Prop where
  /-- The exact-anchor layers over the supports of rank `n` are **mutually** conditionally
  independent given everything of lower rank. -/
  mutual_condIndep :
    iCondIndepFun (RelStructure.lowerRankAlgebra (S := S) n)
      (RelStructure.lowerRankAlgebra_le n)
      (fun A : RankSupport S n => B.exactMap A.1)
      (M.law : Measure (RelStructure S (Vinfinite S)))
  /-- **Locality**: at each support of rank `n`, the exact layer depends on the lower-rank factor
  only through the boundary at that support. Not a consequence of mutual independence, which
  permits dependence on the whole factor. -/
  locality : ∀ A : Finset (Σ s : S.Srt, Vinfinite S s), A.card = n →
    CondIndepFun (MeasurableSpace.comap (B.boundaryMap A) inferInstance)
      (B.measurable_boundaryMap A).comap_le (B.exactMap A) (B.lowerFactorMap n)
      (M.law : Measure (RelStructure S (Vinfinite S)))

/-! ### The base case -/

variable [Countable S.Srt] [Countable S.Rel]

open scoped Classical in
/-- **The rank-one coding.** The coding map is the randomization adapter of #140 applied to the
law of the rank-one factor, transported along `rankLatentOneEquiv`.

The equivariance clause is *not* vacuous here. `lowerFactorSpaceEquiv σ 1` permutes the
empty-anchor basis indices, which name the same invariant event but are distinct coordinates of
the Bool-cube; what is true is that it fixes the image of `lowerFactorMap 1`, so the clause holds
almost everywhere and not identically. Rank one is therefore the first test that the field is
correctly stated a.e. -/
noncomputable def RankCoding.rankOne : B.RankCoding 1 := by
  classical
  haveI : IsProbabilityMeasure (M.law : Measure (RelStructure S (Vinfinite S))) := M.law.2
  haveI : IsProbabilityMeasure
      ((M.law : Measure (RelStructure S (Vinfinite S))).map (B.lowerFactorMap 1)) :=
    Measure.isProbabilityMeasure_map (B.measurable_lowerFactorMap' 1).aemeasurable
  have hex := ((M.law : Measure (RelStructure S (Vinfinite S))).map
    (B.lowerFactorMap 1)).exists_measurable_map_eq_uniform01
  choose g hg hgmap using hex
  refine ⟨g ∘ rankLatentOneEquiv, hg.comp rankLatentOneEquiv.measurable, ?_, ?_⟩
  · rw [← Measure.map_map hg rankLatentOneEquiv.measurable,
      rankLatentSource_map_rankLatentOneEquiv, hgmap]
  · intro σ
    -- the factor equivalence fixes every realized point of the factor space
    have hfix : ∀ X : RelStructure S (Vinfinite S),
        B.lowerFactorSpaceEquiv σ 1 (B.lowerFactorMap 1 X) = B.lowerFactorMap 1 X := by
      intro X
      have hnat : B.lowerFactorSpaceEquiv σ 1 (B.lowerFactorMap 1 X)
          = B.lowerFactorMap 1 (RelStructure.relabel σ.1 X) :=
        congrFun (B.lowerFactorSpaceEquiv_comp_lowerFactorMap σ 1) X
      have hone : B.lowerFactorMap 1 (RelStructure.relabel σ.1 X) = B.lowerFactorMap 1 X :=
        congrFun (B.lowerFactorMap_one_relabel σ) X
      rw [hnat, hone]
    have hsetc : MeasurableSet
        {y : B.LowerFactorSpace 1 | ¬ B.lowerFactorSpaceEquiv σ 1 y = y} :=
      (measurableSet_eq_fun (B.lowerFactorSpaceEquiv σ 1).measurable measurable_id).compl
    -- hence it fixes the factor law almost everywhere
    have hlaw : ∀ᵐ y ∂((M.law : Measure (RelStructure S (Vinfinite S))).map
        (B.lowerFactorMap 1)), B.lowerFactorSpaceEquiv σ 1 y = y := by
      rw [ae_iff, Measure.map_apply (B.measurable_lowerFactorMap' 1) hsetc]
      convert measure_empty (μ := (M.law : Measure (RelStructure S (Vinfinite S))))
      ext X
      simp [hfix X]
    -- pull it back along the coding map, where the latent relabeling is the identity
    rw [← hgmap, ← rankLatentSource_map_rankLatentOneEquiv,
      Measure.map_map hg rankLatentOneEquiv.measurable, ae_iff,
      Measure.map_apply (hg.comp rankLatentOneEquiv.measurable) hsetc] at hlaw
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null (fun ω hω => ?_) hlaw
    simp only [Set.mem_setOf_eq, Function.comp_apply, Set.mem_preimage,
      rankLatentRelabel_one_eq σ ω] at hω ⊢
    exact hω

end CoherentBasis

end RelSignature
