/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelBasisSyntax
import Graphon.RelErgodicExtreme

/-!
# The saturated atom family (R4 converse piece 3, #107)

The atoms of the coherent basis: one **seed** family of events per finite tagged vertex set,
saturated by the finitely supported relabelings.

## The construction

An atom is a pair `(seed, τ)` where `seed` is a seed event anchored at some finite `A` and `τ`
is a finitely supported sortwise permutation. Its anchor is `A.image τ` and its event is
`relabel τ ⁻¹' seed`. The relabeling action is **left multiplication in the second coordinate**,

`atomAct σ (seed, τ) = (seed, σ * τ)`,

which is what makes the two action laws *group* laws rather than anything about events:
`act_one` is `one_mul` and `act_mul` is `mul_assoc` in `FinSuppPerm S`, the finitely supported
subgroup. The anchor law is then
`Finset.image_image`, and the event law is `RelStructure.relabel_preimage_relabel_preimage` —
the orientation matches because `relabel` is contravariant.

Saturation is built into the index rather than imposed afterwards: every relabel of every seed
is already an atom, so the family is closed under the action *by construction*, with no orbit
representatives and no choices to make equivariant.

## Contents

* `RelSignature.SeedData` — a countable family of `fixingAlgebra A`-events for each finite `A`,
  the input to the construction (its existence, from separability, is the next step);
* `RelSignature.SaturatedAtom` and its `atomAnchor` / `atomEvent` / `atomAct`, with the four
  atom-level laws `BasisExpr` needs, plus `Countable`.
-/

open MeasureTheory MeasurableSpace

namespace RelSignature

variable {S : RelSignature}

/-! ### Countability of the relabeling subgroup -/

/-- The finitely supported sortwise permutations form a countable group under finitely many
sorts — the subgroup itself lives beside `SortwiseFinSupp` in `Graphon.RelInvariantAction`;
countability is recorded here, where `Fintype S.Srt` is in play. -/
instance [Fintype S.Srt] : Countable (FinSuppPerm S) :=
  (countable_setOf_sortwiseFinSupp (S := S)).to_subtype

/-! ### Seed data -/

/-- **Seed data**: a countable family of events for each finite tagged vertex set, each
measurable for the corresponding fixing algebra.

This is the input to the saturated construction, kept abstract so that the algebra below is
independent of *how* the seeds are produced. The seeds that matter come from separability of the
law — `MeasureTheory.isSeparable_trim` applied to `fixingAlgebra A` — and carry measure density
as well; that is supplied separately, since none of the structural laws need it. -/
structure SeedData (S : RelSignature) where
  /-- The seed events available over `A`. -/
  seed : Finset (Σ s : S.Srt, Vinfinite S s) → Set (Set (RelStructure S (Vinfinite S)))
  /-- Countably many seeds over each `A`. -/
  countable_seed : ∀ A, (seed A).Countable
  /-- Each seed over `A` is a `fixingAlgebra A`-event. -/
  seed_mem : ∀ A, ∀ E ∈ seed A, MeasurableSet[RelStructure.fixingAlgebra A] E

namespace SeedData

variable (D : SeedData S)

/-- The seeds, bundled with the vertex set they are anchored at. -/
def Index : Type := Σ A : Finset (Σ s : S.Srt, Vinfinite S s), {E : Set (RelStructure S (Vinfinite S)) // E ∈ D.seed A}

instance [Fintype S.Srt] : Countable D.Index := by
  haveI : ∀ A, Countable {E : Set (RelStructure S (Vinfinite S)) // E ∈ D.seed A} :=
    fun A => (D.countable_seed A).to_subtype
  unfold Index
  infer_instance

end SeedData

/-! ### Seed data from separability -/

section OfSeparable

variable [Countable S.Rel] (M : InfiniteRelExchangeableLaw S)

/-- The countable measure-dense family for `fixingAlgebra A` supplied by separability of the
law. `[Countable S.Rel]` alone gives `IsSeparable M.law`; `isSeparable_trim` transports that to
each fixing algebra, and this is its chosen witness. -/
noncomputable def seedOf (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    Set (Set (RelStructure S (Vinfinite S))) :=
  (MeasureTheory.isSeparable_trim (μ := (M.law : Measure (RelStructure S (Vinfinite S))))
    (RelStructure.fixingAlgebra_le A)).1.choose

theorem countable_seedOf (A : Finset (Σ s : S.Srt, Vinfinite S s)) : (seedOf M A).Countable :=
  (MeasureTheory.isSeparable_trim (μ := (M.law : Measure (RelStructure S (Vinfinite S))))
    (RelStructure.fixingAlgebra_le A)).1.choose_spec.1

/-- **The density carried alongside the seeds.** Kept out of `SeedData`, which stays structural:
the atom-level laws never look at the law, and only the final `CoherentBasis.density` field
does. -/
theorem measureDense_seedOf (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    @Measure.MeasureDense (RelStructure S (Vinfinite S)) (RelStructure.fixingAlgebra A)
      ((M.law : Measure (RelStructure S (Vinfinite S))).trim (RelStructure.fixingAlgebra_le A))
      (seedOf M A) :=
  (MeasureTheory.isSeparable_trim (μ := (M.law : Measure (RelStructure S (Vinfinite S))))
    (RelStructure.fixingAlgebra_le A)).1.choose_spec.2

/-- **The seed data of a law**: the separability-supplied families, packaged structurally. -/
noncomputable def seedDataOf : SeedData S where
  seed := seedOf M
  countable_seed := countable_seedOf M
  seed_mem := fun A => @Measure.MeasureDense.measurable (RelStructure S (Vinfinite S))
    (RelStructure.fixingAlgebra A) _ _ (measureDense_seedOf M A)

@[simp] theorem seedDataOf_seed (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    (seedDataOf M).seed A = seedOf M A := rfl

end OfSeparable

/-! ### The saturated atoms -/

/-- **A saturated atom**: a seed together with a finitely supported relabeling of it. Saturation
is part of the index, so the atom family is closed under the relabeling action by construction
— no orbit representatives, and nothing to make equivariant after the fact. -/
def SaturatedAtom (D : SeedData S) : Type := D.Index × FinSuppPerm S

namespace SaturatedAtom

variable {D : SeedData S}

instance [Fintype S.Srt] : Countable (SaturatedAtom D) := instCountableProd

/-- The anchor of an atom: the seed's vertex set, moved by the relabeling. -/
noncomputable def anchor (a : SaturatedAtom D) : Finset (Σ s : S.Srt, Vinfinite S s) := by
  classical
  exact a.1.1.image (Sigma.map id fun s => ⇑(a.2.1 s))

/-- The event of an atom: the seed event, pulled back along the relabeling. -/
def event (a : SaturatedAtom D) : Set (RelStructure S (Vinfinite S)) :=
  RelStructure.relabel a.2.1 ⁻¹' a.1.2.1

/-- **The action: left multiplication in the relabeling coordinate.** -/
def act (σ : FinSuppPerm S) (a : SaturatedAtom D) : SaturatedAtom D := (a.1, σ * a.2)

/-- `act_one` is literally `one_mul` in the relabeling subgroup. -/
theorem act_one (a : SaturatedAtom D) : act 1 a = a := by
  show (a.1, (1 : FinSuppPerm S) * a.2) = a
  rw [one_mul]
  rfl

/-- `act_mul` is literally `mul_assoc` — the point of putting the relabeling in the index, and
of typing the action by the subgroup rather than by raw permutation families. -/
theorem act_mul (σ τ : FinSuppPerm S) (a : SaturatedAtom D) :
    act (σ * τ) a = act σ (act τ a) := by
  show (a.1, σ * τ * a.2) = (a.1, σ * (τ * a.2))
  rw [mul_assoc]

open scoped Classical in
/-- The anchor transports by the image map: `Finset.image_image`, since multiplication of
permutation families is pointwise composition. -/
theorem anchor_act (σ : FinSuppPerm S) (a : SaturatedAtom D) :
    anchor (act σ a) = (anchor a).image (Sigma.map id fun s => ⇑(σ.1 s)) := by
  show (act σ a).1.1.image _ = (a.1.1.image _).image _
  rw [Finset.image_image]
  refine Finset.image_congr fun v _ => ?_
  obtain ⟨s, x⟩ := v
  rfl

/-- The event transports by preimage, exactly — `relabel_preimage_relabel_preimage`, whose
orientation is exactly the left-multiplication convention. -/
theorem event_act (σ : FinSuppPerm S) (a : SaturatedAtom D) :
    event (act σ a) = RelStructure.relabel σ.1 ⁻¹' event a := by
  show RelStructure.relabel (fun s => σ.1 s * a.2.1 s) ⁻¹' _ = _
  rw [event, RelStructure.relabel_preimage_relabel_preimage]
  rfl

/-- Every atom event lies in the fixing algebra of its own anchor: the seed lies in
`fixingAlgebra A`, and `fixingAlgebra_comap_relabel` moves that to the image vertex set. -/
theorem event_mem (a : SaturatedAtom D) :
    MeasurableSet[RelStructure.fixingAlgebra (anchor a)] (event a) := by
  classical
  have hmem : MeasurableSet[RelStructure.fixingAlgebra a.1.1] a.1.2.1 :=
    D.seed_mem a.1.1 a.1.2.1 a.1.2.2
  have htrans := RelStructure.fixingAlgebra_comap_relabel a.2.2 a.1.1
  show MeasurableSet[RelStructure.fixingAlgebra
    (a.1.1.image (Sigma.map id fun s => ⇑(a.2.1 s)))] (RelStructure.relabel a.2.1 ⁻¹' a.1.2.1)
  rw [← htrans]
  exact ⟨a.1.2.1, hmem, rfl⟩

end SaturatedAtom

end RelSignature
