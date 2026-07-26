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
its formal consequences, including the relabeling equivalence `basisIndexEquiv`; it does
**not** construct an instance — that is
`RelSignature.InfiniteRelExchangeableLaw.nonempty_coherentBasis`, in
`Graphon.RelBasisSaturation`.

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
  `FinSuppPerm S` rather than by raw permutation families with a side condition: closure under
  finitely supported relabelings is all this layer provides and all it needs, whereas closure of
  the chosen event family under the full permutation group is neither constructed nor countable
  in general. So the subgroup is precisely the symmetry the interface can honestly guarantee,
  and its group inverses are what let `basisIndexEquiv`, below, upgrade a relabeling to an
  equivalence `BasisIndex A ≃ BasisIndex (A.image σ)`;
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
  an a.e. representative in the pullback of the factor map;
* `CoherentBasis.FactorSpace` — the factor space at `A`, standard Borel because the index is
  countable, with the measurability of the factor maps and projections, and
  `factorSpaceEquiv`, a relabeling as a *measurable* equivalence of factor spaces;
* `CoherentBasis.basisIndexEquiv` — a relabeling as an *equivalence*
  `BasisIndex A ≃ BasisIndex (A.image σ)`, with `factorMap_basisIndexEquiv` /
  `factorMap_comp_relabel` (naturality against `relabel`, orientation forced by `event_act`
  being a preimage equality) and the two definitional compatibilities with
  `basisIndexEmbedding` and `factorProjection`.
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
  `SortwiseFinSupp` side condition. That is deliberate: closure under finitely supported
  relabelings is what the construction supplies and what the downstream arguments use, while
  closure of the chosen event family under the full permutation group is neither constructed
  here nor countable in general. Typing the field by the subgroup states exactly the symmetry
  guaranteed, and makes inverses available for free. -/
  act : FinSuppPerm S → ι → ι
  /-- The identity relabeling acts trivially. -/
  act_one : ∀ i, act 1 i = i
  /-- The action is multiplicative. The orientation matches `event_act` and the contravariance
  of `relabel`: `relabel (σ * τ) ⁻¹' E = relabel σ ⁻¹' (relabel τ ⁻¹' E)`, by
  `RelStructure.relabel_preimage_relabel_preimage`.

  With `act_one` this makes `act` an action rather than a bare map, which is what lets
  `basisIndexEquiv` turn a relabeling into an *equivalence*
  `BasisIndex A ≃ BasisIndex (A.image σ)`: the group inverse supplies the two-sided inverse via
  `act σ⁻¹ ∘ act σ = act 1 = id`. -/
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

/-! ### The factor spaces -/

/-- **The factor space at `A`**: the Boolean cube over the indices anchored inside `A`.

Standard Borel, because the index is countable — this is what the conditional-kernel step will
need, and it is the reason for indexing by `BasisIndex A` rather than coding every factor into
`ℕ → Bool`: the varying index keeps the inclusions literal without giving up the measurable
structure. -/
abbrev FactorSpace (A : Finset (Σ s : S.Srt, Vinfinite S s)) := B.BasisIndex A → Bool

instance (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    StandardBorelSpace (B.FactorSpace A) := inferInstance

/-- **The inclusion of sub-indices**, for `C ⊆ A`: a literal subtype inclusion, which is the
whole reason for anchoring indices at finite sets rather than coding each factor separately. -/
def basisIndexEmbedding {C A : Finset (Σ s : S.Srt, Vinfinite S s)} (hCA : C ⊆ A) :
    B.BasisIndex C → B.BasisIndex A := fun i => ⟨i.1, i.2.trans hCA⟩

open scoped Classical in
/-- **The factor map at `A`**: evaluate every event anchored inside `A`. -/
noncomputable def factorMap (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    RelStructure S (Vinfinite S) → B.FactorSpace A :=
  fun X i => decide (X ∈ B.event i.1)

/-- **The factor projection** from `A` down to `C ⊆ A`: precomposition with the index inclusion,
i.e. ordinary coordinate restriction. -/
def factorProjection {C A : Finset (Σ s : S.Srt, Vinfinite S s)} (hCA : C ⊆ A) :
    B.FactorSpace A → B.FactorSpace C :=
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

/-- A coordinate of the factor map reads membership in the corresponding event. -/
@[simp] theorem factorMap_eq_true {A : Finset (Σ s : S.Srt, Vinfinite S s)}
    (X : RelStructure S (Vinfinite S)) (i : B.BasisIndex A) :
    B.factorMap A X i = true ↔ X ∈ B.event i.1 := by
  simp [factorMap]

/-- The factor projections are measurable — they are coordinate restrictions. -/
theorem measurable_factorProjection {C A : Finset (Σ s : S.Srt, Vinfinite S s)} (hCA : C ⊆ A) :
    Measurable (B.factorProjection hCA) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

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

/-- The factor map is measurable for the ambient σ-algebra too, by `fixingAlgebra_le`. -/
theorem measurable_factorMap' (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    Measurable (B.factorMap A) :=
  (B.measurable_factorMap A).mono (RelStructure.fixingAlgebra_le A) le_rfl

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

/-! ### Relabeling equivariance -/

open scoped Classical in
/-- Relabeling by `σ` and then by `σ⁻¹` returns a vertex set to itself. -/
theorem image_image_inv (σ : FinSuppPerm S) (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    (A.image (Sigma.map id fun s => ⇑(σ.1 s))).image
      (Sigma.map id fun s => ⇑((σ⁻¹ : FinSuppPerm S).1 s)) = A := by
  rw [Finset.image_image]
  refine (Finset.image_congr fun v _ => ?_).trans A.image_id
  obtain ⟨s, x⟩ := v
  show (⟨s, (σ.1 s)⁻¹ (σ.1 s x)⟩ : Σ s : S.Srt, Vinfinite S s) = ⟨s, x⟩
  rw [show (σ.1 s)⁻¹ (σ.1 s x) = x from (σ.1 s).symm_apply_apply x]

open scoped Classical in
/-- **A relabeling is an equivalence of index sets**: `BasisIndex A ≃ BasisIndex (A.image σ)`.

The two-sided inverse is the group inverse of `σ`, available because the action is typed by the
subgroup: `act σ⁻¹ ∘ act σ = act 1 = id` by `act_mul` and `act_one`. -/
noncomputable def basisIndexEquiv (σ : FinSuppPerm S)
    (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    B.BasisIndex A ≃ B.BasisIndex (A.image (Sigma.map id fun s => ⇑(σ.1 s))) where
  toFun i := ⟨B.act σ i.1, by
    rw [B.anchor_act]
    exact Finset.image_subset_image i.2⟩
  invFun j := ⟨B.act σ⁻¹ j.1, by
    -- rewrite in the hypothesis: `A` sits in a dependent position in the goal
    have h := Finset.image_subset_image
      (f := (Sigma.map id fun s => ⇑((σ⁻¹ : FinSuppPerm S).1 s) :
        (Σ s : S.Srt, Vinfinite S s) → Σ s : S.Srt, Vinfinite S s)) j.2
    rw [image_image_inv σ A] at h
    rw [B.anchor_act]
    exact h⟩
  left_inv i := by
    refine Subtype.ext ?_
    show B.act σ⁻¹ (B.act σ i.1) = i.1
    rw [← B.act_mul, inv_mul_cancel, B.act_one]
  right_inv j := by
    refine Subtype.ext ?_
    show B.act σ (B.act σ⁻¹ j.1) = j.1
    rw [← B.act_mul, mul_inv_cancel, B.act_one]

open scoped Classical in
@[simp] theorem basisIndexEquiv_apply_coe (σ : FinSuppPerm S)
    (A : Finset (Σ s : S.Srt, Vinfinite S s)) (i : B.BasisIndex A) :
    (B.basisIndexEquiv σ A i).1 = B.act σ i.1 := rfl

open scoped Classical in
@[simp] theorem basisIndexEquiv_symm_apply_coe (σ : FinSuppPerm S)
    (A : Finset (Σ s : S.Srt, Vinfinite S s))
    (j : B.BasisIndex (A.image (Sigma.map id fun s => ⇑(σ.1 s)))) :
    ((B.basisIndexEquiv σ A).symm j).1 = B.act σ⁻¹ j.1 := rfl

open scoped Classical in
/-- **Identity**, at the level of underlying indices. The equivalence at `σ = 1` does not have
type `BasisIndex A ≃ BasisIndex A` on the nose — its codomain is `BasisIndex (A.image id)` —
so the law is stated where no transport is needed. -/
@[simp] theorem basisIndexEquiv_one_coe (A : Finset (Σ s : S.Srt, Vinfinite S s))
    (i : B.BasisIndex A) : (B.basisIndexEquiv 1 A i).1 = i.1 :=
  B.act_one i.1

open scoped Classical in
/-- **Composition**, likewise at the level of underlying indices: the codomains
`BasisIndex (A.image (σ * τ))` and `BasisIndex ((A.image τ).image σ)` agree only after
`Finset.image_image`. -/
@[simp] theorem basisIndexEquiv_mul_coe (σ τ : FinSuppPerm S)
    (A : Finset (Σ s : S.Srt, Vinfinite S s)) (i : B.BasisIndex A) :
    (B.basisIndexEquiv (σ * τ) A i).1 =
      B.act σ (B.basisIndexEquiv τ A i).1 :=
  B.act_mul σ τ i.1

open scoped Classical in
/-- **Naturality of the factor map**, with the orientation explicit: evaluating the factor at
the *image* vertex set, on the index transported by `σ`, is evaluating the factor at `A` on the
relabeled structure.

The direction is forced by `event_act` being a *preimage* equality: `X ∈ event (act σ i)` iff
`relabel σ X ∈ event i`. -/
theorem factorMap_basisIndexEquiv (σ : FinSuppPerm S)
    (A : Finset (Σ s : S.Srt, Vinfinite S s)) (X : RelStructure S (Vinfinite S))
    (i : B.BasisIndex A) :
    B.factorMap (A.image (Sigma.map id fun s => ⇑(σ.1 s))) X (B.basisIndexEquiv σ A i) =
      B.factorMap A (RelStructure.relabel σ.1 X) i := by
  show decide (X ∈ B.event (B.act σ i.1)) = decide (RelStructure.relabel σ.1 X ∈ B.event i.1)
  rw [B.event_act]
  rfl

open scoped Classical in
/-- **A relabeling as a measurable equivalence of factor spaces.** The forward map is
precomposition with `basisIndexEquiv σ A`; both directions are coordinate reindexings, hence
measurable.

This is the form the conditional kernels consume: transporting a kernel across a relabeling
needs the measurable equivalence, not just the underlying bijection of indices. -/
noncomputable def factorSpaceEquiv (σ : FinSuppPerm S)
    (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    B.FactorSpace (A.image (Sigma.map id fun s => ⇑(σ.1 s))) ≃ᵐ B.FactorSpace A where
  toEquiv := Equiv.arrowCongr (B.basisIndexEquiv σ A).symm (Equiv.refl Bool)
  measurable_toFun := measurable_pi_lambda _ fun _ => measurable_pi_apply _
  measurable_invFun := measurable_pi_lambda _ fun _ => measurable_pi_apply _

open scoped Classical in
@[simp] theorem factorSpaceEquiv_apply (σ : FinSuppPerm S)
    (A : Finset (Σ s : S.Srt, Vinfinite S s))
    (f : B.FactorSpace (A.image (Sigma.map id fun s => ⇑(σ.1 s)))) :
    B.factorSpaceEquiv σ A f = f ∘ B.basisIndexEquiv σ A := rfl

open scoped Classical in
/-- The naturality equation as a **commuting square**, through the named measurable
equivalence: the factor at the image vertex set, transported back along `σ`, is the factor at
`A` precomposed with the relabeling. -/
theorem factorMap_comp_relabel (σ : FinSuppPerm S)
    (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    B.factorSpaceEquiv σ A ∘ B.factorMap (A.image (Sigma.map id fun s => ⇑(σ.1 s))) =
      B.factorMap A ∘ RelStructure.relabel σ.1 :=
  funext fun X => funext fun i => B.factorMap_basisIndexEquiv σ A X i

open scoped Classical in
/-- **The index equivalence commutes with the sub-index inclusions** — and definitionally, since
both routes act by `σ` and only the containment proof differs. -/
theorem basisIndexEmbedding_basisIndexEquiv {C A : Finset (Σ s : S.Srt, Vinfinite S s)}
    (hCA : C ⊆ A) (σ : FinSuppPerm S) :
    B.basisIndexEmbedding (Finset.image_subset_image hCA) ∘ B.basisIndexEquiv σ C =
      B.basisIndexEquiv σ A ∘ B.basisIndexEmbedding hCA := rfl

open scoped Classical in
/-- Dually, the factor **projection** commutes with precomposition by the index equivalence —
again definitionally, so the relabeling action descends along the tower of factors with no
coherence condition to check. -/
theorem factorProjection_basisIndexEquiv {C A : Finset (Σ s : S.Srt, Vinfinite S s)}
    (hCA : C ⊆ A) (σ : FinSuppPerm S)
    (f : B.FactorSpace (A.image (Sigma.map id fun s => ⇑(σ.1 s)))) :
    B.factorProjection hCA (f ∘ B.basisIndexEquiv σ A) =
      (B.factorProjection (Finset.image_subset_image hCA) f) ∘ B.basisIndexEquiv σ C := rfl

end CoherentBasis

end RelSignature
