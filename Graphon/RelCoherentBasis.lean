/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelFixingCondIndep
import Graphon.SeparableFactor

/-!
# The coherent-basis interface for the fixing σ-algebras (R4 converse piece 3, #107)

The **interface** for a simultaneous, coherent family of factors for `fixingAlgebra A`, as `A`
ranges over the finite sets of tagged vertices. This file *defines* the interface and derives
its formal consequences; it does **not** construct an instance — that is the next PR.

## Why not one factor per `A`

`Graphon.SeparableFactor` already produces a factor map for a *single* sub-σ-algebra, via
`MeasurableSpace.mapNatBool`. That map cannot be used family-wide: its generating sequence is
chosen by the `CountablyGenerated` instance, so factors for different `A` have no relation to
one another — no literal inclusion when `C ⊆ A`, and no equivariance under relabeling. Choosing
per-`A` maps and repairing the relations afterwards leads straight back into coherence choices,
because independently chosen transports need not respect a given inclusion.

## The design

A single **global countable index type** `ι`, each index carrying an explicit finite **anchor**
and an **event**:

* `anchor : ι → Finset (Σ s, Vinfinite S s)` and `event : ι → Set (RelStructure S (Vinfinite S))`,
  with `event i` measurable for `fixingAlgebra (anchor i)`;
* the indices available over `A` are `BasisIndex A := {i // anchor i ⊆ A}`, so `C ⊆ A` induces a
  **literal** embedding `BasisIndex C ↪ BasisIndex A`;
* the factor space is `BasisIndex A → Bool` — a **varying** index, not `ℕ → Bool`. It is still
  standard Borel because the index is countable, and unlike a Cantor coding it keeps the
  inclusions literal, so the factor projection is ordinary coordinate restriction and its
  cocycle law is definitional;
* the finitely supported relabelings act on `ι` — an action proper, with identity and
  multiplicativity laws, not merely a map — transporting anchors by the image map and events by
  *exact* preimage equality, with no null sets. The action is typed by the subgroup
  `FinSuppPerm S` rather than by raw permutation families with a side condition: a countable
  index cannot carry an exact action of the uncountable full permutation group, so the subgroup
  is precisely the symmetry the interface can honestly guarantee. Its group inverses are what
  let a later layer upgrade a relabeling to an equivalence `BasisIndex A ≃ BasisIndex (A.image σ)`;
* the family is closed under finite Boolean operations, so it is a countable set ring. This is
  demanded up front rather than derived later: the conditional-law and Dynkin arguments
  downstream are far easier over a ring than over an arbitrary dense family;
* **measure density**: for each `A`, the events indexed by `BasisIndex A` approximate every
  `fixingAlgebra A`-event modulo the law. Combined with
  `Measure.MeasureDense.exists_generateFrom_ae_eq` this is what turns approximation into a.e.
  representatives.

## Contents

* `RelSignature.CoherentBasis` — the interface;
* `CoherentBasis.BasisIndex` / `basisIndexEmbedding` / `factorMap` / `factorProjection` — the
  derived objects, with the coordinate-restriction cocycle `factorProjection_comp` and the
  compatibility `factorProjection_factorMap`;
* `CoherentBasis.measurable_factorMap` and `CoherentBasis.comap_factorMap_le` — the factor map
  is `fixingAlgebra A`-measurable, so its pullback lands inside `fixingAlgebra A`;
* `CoherentBasis.exists_comap_factorMap_ae_eq` — the payoff: every `fixingAlgebra A`-event has
  an a.e. representative in the pullback of the factor map.
-/

open MeasureTheory MeasurableSpace

namespace RelSignature

universe u

variable {S : RelSignature.{u}}

/-! ### The interface -/

open scoped Classical in
/-- **A coherent basis** for the fixing σ-algebras of `M`: one global countable family of
anchored events, from which a factor for every finite tagged vertex set `A` is read off by
restricting to the indices anchored inside `A`.

The point of the single global index is that all the coherence is *structural*: the inclusion
for `C ⊆ A` is a literal subtype inclusion, the relabeling action is an action on indices with
exact anchor and event transport, and the factor projections are coordinate restrictions. Only
`density` refers to the law. -/
structure CoherentBasis (M : InfiniteRelExchangeableLaw S) where
  /-- The global index type. It lives in the signature's universe: the anchors are
  `Finset`s of tagged vertices and the events are sets of structures, both of which do. -/
  ι : Type u
  /-- The index type is countable, so each factor space is standard Borel. -/
  countable_ι : Countable ι
  /-- The finite tagged vertex set an index is anchored at. -/
  anchor : ι → Finset (Σ s : S.Srt, Vinfinite S s)
  /-- The event an index names. -/
  event : ι → Set (RelStructure S (Vinfinite S))
  /-- Each event is measurable for the fixing algebra of its own anchor — hence for
  `fixingAlgebra A` whenever the anchor sits inside `A`. -/
  event_mem : ∀ i, MeasurableSet[RelStructure.fixingAlgebra (anchor i)] (event i)
  /-- An index naming the empty event, anchored at `∅` — hence available over every `A`. -/
  bot : ι
  anchor_bot : anchor bot = ∅
  event_bot : event bot = ∅
  /-- Complementation on indices, fixing the anchor. -/
  compl : ι → ι
  anchor_compl : ∀ i, anchor (compl i) = anchor i
  event_compl : ∀ i, event (compl i) = (event i)ᶜ
  /-- Intersection on indices; the anchor is the union, which is exactly what keeps
  `BasisIndex A` closed under the operation. -/
  inter : ι → ι → ι
  anchor_inter : ∀ i j, anchor (inter i j) = anchor i ∪ anchor j
  event_inter : ∀ i j, event (inter i j) = event i ∩ event j
  /-- A finitely supported sortwise relabeling acts on indices.

  The field is typed by the *subgroup* `FinSuppPerm S`, not by a raw permutation family with a
  `SortwiseFinSupp` side condition. That is deliberate: a countable index cannot carry an exact
  action of the uncountable full permutation group, so a raw-permutation field would claim more
  than any construction can supply. The finitely supported subgroup is exactly the symmetry the
  interface guarantees, and typing it that way also makes inverses available for free. -/
  act : FinSuppPerm S → ι → ι
  /-- The identity relabeling acts trivially. -/
  act_one : ∀ i, act 1 i = i
  /-- The action is multiplicative. The orientation matches `event_act` and the contravariance
  of `relabel`: `relabel (σ * τ) ⁻¹' E = relabel σ ⁻¹' (relabel τ ⁻¹' E)`, by
  `RelStructure.relabel_preimage_relabel_preimage`.

  With `act_one` this makes `act` an action rather than a bare map, which is what lets a later
  layer turn a relabeling into an *equivalence* `BasisIndex A ≃ BasisIndex (A.image σ)`: the
  group inverse supplies the two-sided inverse via `act σ⁻¹ ∘ act σ = act 1 = id`. -/
  act_mul : ∀ σ τ i, act (σ * τ) i = act σ (act τ i)
  /-- The action transports anchors by the image map, exactly. -/
  anchor_act : ∀ (σ : FinSuppPerm S) i,
    anchor (act σ i) = (anchor i).image (Sigma.map id fun s => ⇑(σ.1 s))
  /-- The action transports events by preimage, exactly — no null sets. -/
  event_act : ∀ (σ : FinSuppPerm S) i,
    event (act σ i) = RelStructure.relabel σ.1 ⁻¹' event i
  /-- **Measure density**: over each `A`, the events anchored inside `A` approximate every
  `fixingAlgebra A`-event. This is the only field that mentions the law. -/
  density : ∀ A : Finset (Σ s : S.Srt, Vinfinite S s),
    @Measure.MeasureDense (RelStructure S (Vinfinite S)) (RelStructure.fixingAlgebra A)
      ((M.law : Measure (RelStructure S (Vinfinite S))).trim (RelStructure.fixingAlgebra_le A))
      {E | ∃ i, anchor i ⊆ A ∧ event i = E}

namespace CoherentBasis

variable {M : InfiniteRelExchangeableLaw S} (B : CoherentBasis M)

instance : Countable B.ι := B.countable_ι

/-! ### The derived factors -/

/-- **The indices available over `A`**: those anchored inside `A`. Countable, so
`BasisIndex A → Bool` is standard Borel. -/
def BasisIndex (A : Finset (Σ s : S.Srt, Vinfinite S s)) := {i : B.ι // B.anchor i ⊆ A}

instance (A : Finset (Σ s : S.Srt, Vinfinite S s)) : Countable (B.BasisIndex A) :=
  Subtype.countable

/-- **The inclusion of sub-indices**, for `C ⊆ A`: a literal subtype inclusion, which is the
whole reason for anchoring indices at finite sets rather than coding each factor separately. -/
def basisIndexEmbedding {C A : Finset (Σ s : S.Srt, Vinfinite S s)} (hCA : C ⊆ A) :
    B.BasisIndex C → B.BasisIndex A := fun i => ⟨i.1, i.2.trans hCA⟩

open scoped Classical in
/-- **The factor map at `A`**: evaluate every event anchored inside `A`. -/
noncomputable def factorMap (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    RelStructure S (Vinfinite S) → (B.BasisIndex A → Bool) :=
  fun X i => decide (X ∈ B.event i.1)

/-- **The factor projection** from `A` down to `C ⊆ A`: precomposition with the index inclusion,
i.e. ordinary coordinate restriction. -/
def factorProjection {C A : Finset (Σ s : S.Srt, Vinfinite S s)} (hCA : C ⊆ A) :
    (B.BasisIndex A → Bool) → (B.BasisIndex C → Bool) :=
  fun f => f ∘ B.basisIndexEmbedding hCA

/-- **The projections are compatible with the factor maps** — by definition, since both sides
evaluate the same events. -/
theorem factorProjection_factorMap {C A : Finset (Σ s : S.Srt, Vinfinite S s)} (hCA : C ⊆ A) :
    B.factorProjection hCA ∘ B.factorMap A = B.factorMap C := rfl

/-- **The cocycle law**, definitional: restricting through an intermediate set is the same as
restricting directly. -/
theorem factorProjection_comp {D C A : Finset (Σ s : S.Srt, Vinfinite S s)} (hDC : D ⊆ C)
    (hCA : C ⊆ A) :
    B.factorProjection hDC ∘ B.factorProjection hCA = B.factorProjection (hDC.trans hCA) := rfl

/-! ### Measurability and generation -/

/-- The factor map at `A` is measurable for `fixingAlgebra A`: each coordinate is the indicator
of an event whose anchor lies inside `A`, and `fixingAlgebra` is monotone. -/
theorem measurable_factorMap (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    Measurable[RelStructure.fixingAlgebra A] (B.factorMap A) := by
  classical
  letI : MeasurableSpace (RelStructure S (Vinfinite S)) := RelStructure.fixingAlgebra A
  refine measurable_pi_iff.mpr fun i => measurable_to_bool ?_
  have hmem : MeasurableSet[RelStructure.fixingAlgebra A] (B.event i.1) :=
    RelStructure.fixingAlgebra_mono i.2 _ (B.event_mem i.1)
  convert hmem using 1
  ext X
  simp [factorMap]

/-- Consequently the pullback of the factor σ-algebra sits inside `fixingAlgebra A`. -/
theorem comap_factorMap_le (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    MeasurableSpace.comap (B.factorMap A) inferInstance ≤ RelStructure.fixingAlgebra A :=
  (B.measurable_factorMap A).comap_le

/-- **The payoff**: every `fixingAlgebra A`-event has an a.e. representative in the pullback of
the factor map at `A`. Stated eventwise, like everything else in this layer — never as an
equality of σ-algebras "modulo null sets".

Together with `comap_factorMap_le` this says the factor captures `fixingAlgebra A` exactly
modulo the law, while `factorProjection_factorMap` and `factorProjection_comp` say the family
of factors is coherent on the nose. -/
theorem exists_comap_factorMap_ae_eq (A : Finset (Σ s : S.Srt, Vinfinite S s))
    {E : Set (RelStructure S (Vinfinite S))}
    (hE : MeasurableSet[RelStructure.fixingAlgebra A] E) :
    ∃ E', MeasurableSet[MeasurableSpace.comap (B.factorMap A) inferInstance] E' ∧
      E' =ᵐ[(M.law : Measure (RelStructure S (Vinfinite S)))] E := by
  classical
  haveI : IsProbabilityMeasure (M.law : Measure (RelStructure S (Vinfinite S))) := M.law.2
  obtain ⟨E', hE'gen, hE'ae⟩ :=
    (B.density A).exists_generateFrom_ae_eq (RelStructure.fixingAlgebra_le A) hE
  refine ⟨E', ?_, hE'ae⟩
  refine (generateFrom_le ?_) E' hE'gen
  rintro - ⟨i, hiA, rfl⟩
  refine ⟨{f | f ⟨i, hiA⟩ = true}, ?_, ?_⟩
  · have hcoord : Measurable fun f : B.BasisIndex A → Bool => f ⟨i, hiA⟩ :=
      measurable_pi_apply _
    exact hcoord (measurableSet_singleton true)
  · ext X
    simp [factorMap]

end CoherentBasis

end RelSignature
