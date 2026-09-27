/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelMarkedRowKernel
import Graphon.RelWeakUnion

/-!
# Rank one: joint-law locality of the marked rows

Fix a pooled rank extension `Q` of a rank-one representation and a finite original set `A`. The
full induced original structure on `A`, the marked rows of the vertices of `A`, and the purely
spare structure are all read off the marked observation at `A` by coordinate restriction.
-/

universe u

open MeasureTheory ProbabilityTheory

namespace RelSignature

variable {S : RelSignature.{u}}

/-! ### Exact coordinate factorizations through the marked observation -/

theorem markedSet_mono {A B : Finset (Σ s : S.Srt, Vinfinite S s)} (h : A ⊆ B) :
    markedSet (S := S) A ⊆ markedSet B := by
  rintro v (⟨a, ha, hA⟩ | ⟨b, hb⟩)
  · exact Or.inl ⟨a, ha, h hA⟩
  · exact Or.inr ⟨b, hb⟩

/-- The marked observation at a smaller set, read off the marked observation at a larger one. -/
def markedRestrict {A B : Finset (Σ s : S.Srt, Vinfinite S s)} (h : A ⊆ B) :
    MarkedSpace (S := S) B → MarkedSpace (S := S) A :=
  fun m c => m ⟨c.1, fun v hv => markedSet_mono h (c.2 v hv)⟩

theorem measurable_markedRestrict {A B : Finset (Σ s : S.Srt, Vinfinite S s)} (h : A ⊆ B) :
    Measurable (markedRestrict (S := S) h) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

theorem markedRestrict_markedObs {A B : Finset (Σ s : S.Srt, Vinfinite S s)} (h : A ⊆ B)
    (Y : RelStructure S (PoolVertex S)) : markedRestrict h (markedObs B Y) = markedObs A Y :=
  rfl

/-- An induced coordinate on `A`, read on the original copy, is a marked coordinate at `A`. -/
def InducedIndex.toMarked {A : Finset (Σ s : S.Srt, Vinfinite S s)} (c : InducedIndex (S := S) A) :
    MarkedCoord (S := S) A :=
  ⟨RelCoord.map (fun s => (originalVertex S s : Vinfinite S s → PoolVertex S s)) c.1, by
    intro v hv
    obtain ⟨i, rfl⟩ := (RelCoord.mem_support_iff _ _).mp hv
    exact Or.inl ⟨c.1.2 i, rfl, c.2 ((RelCoord.mem_support_iff _ _).mpr ⟨i, rfl⟩)⟩⟩

/-- The full induced original structure on `A`, read off the marked observation at `A`. -/
def markedToInduced (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    MarkedSpace (S := S) A → InducedSpace (S := S) A :=
  fun m c => m c.toMarked

theorem measurable_markedToInduced (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    Measurable (markedToInduced (S := S) A) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

/-- **The induced original structure factors through the marked observation**, pointwise. -/
theorem inducedMap_restrictOriginal (A : Finset (Σ s : S.Srt, Vinfinite S s))
    (Y : RelStructure S (PoolVertex S)) :
    inducedMap A (restrictOriginal S Y) = markedToInduced A (markedObs A Y) :=
  rfl

/-- A coordinate of the spare copy, read on the pool, is a marked coordinate at every `A`. -/
def RelCoord.toMarkedSpare (A : Finset (Σ s : S.Srt, Vinfinite S s))
    (c : RelCoord S (Vinfinite S)) : MarkedCoord (S := S) A :=
  ⟨RelCoord.map (fun s => (poolVertex S s : Vinfinite S s → PoolVertex S s)) c, by
    intro v hv
    obtain ⟨i, rfl⟩ := (RelCoord.mem_support_iff _ _).mp hv
    exact Or.inr ⟨c.2 i, rfl⟩⟩

/-- The purely spare structure, read off the marked observation at `A`. -/
def markedToSpare (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    MarkedSpace (S := S) A → RelStructure S (Vinfinite S) :=
  fun m c => m (c.toMarkedSpare A)

theorem measurable_markedToSpare (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    Measurable (markedToSpare (S := S) A) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

/-- **The purely spare structure factors through the marked observation**, pointwise. -/
theorem restrictPool_eq_markedToSpare (A : Finset (Σ s : S.Srt, Vinfinite S s))
    (Y : RelStructure S (PoolVertex S)) : restrictPool S Y = markedToSpare A (markedObs A Y) :=
  rfl

/-- The marked rows of the vertices of `A`, read off the marked observation at `A`. -/
def markedToRows (A : Finset (RowIndex S)) :
    MarkedSpace (S := S) A → ∀ v : A, MarkedSpace (S := S) {v.1} :=
  fun m v => markedRestrict (Finset.singleton_subset_iff.mpr v.2) m

theorem measurable_markedToRows (A : Finset (RowIndex S)) :
    Measurable (markedToRows (S := S) A) :=
  measurable_pi_lambda _ fun _ => measurable_markedRestrict _

/-- **The rows inside `A` factor through the marked observation**, pointwise. -/
theorem restrict_rowsObs (A : Finset (RowIndex S)) (p : PooledOne S) :
    A.restrict (rowsObs p) = markedToRows A (markedObs A p.1) :=
  rfl

/-- **The environment factors through the marked observation and the latent array**,
pointwise. -/
theorem envObs_eq_markedToSpare (A : Finset (RowIndex S)) (p : PooledOne S) :
    envObs p = (markedToSpare A (markedObs A p.1), p.2) :=
  rfl

end RelSignature
