/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelPooledFixingSeam
import Graphon.RelBasisSaturation

/-!
# The finite-active coherent extension of a coherent basis (R4 converse, #107, #197)

A countable standard-Borel realization of the finite-active fixing algebras, built **relative** to
a raw coherent basis `B` rather than chosen independently of it.

## The contract

`FiniteActiveExtension B` is a global finite-active coherent basis on `Vinfinite` — anchors range
over every finite support, events lie in `finiteActiveFixingAlgebra` of their anchor, and the
action is by the countable finite-active subgroup — together with a **distinguished coordinate**
`raw j` for every raw index `j : B.ι`, anchored at the doubled support of `B.anchor j` and naming
the strictified doubled representative of `B.event j` (the countable invariant hull of
`Graphon.RelPooledFixingSeam`). The distinguished coordinates are what the finite-active factor
spaces project to:

* `toRaw A` is literal coordinate restriction, exactly coherent with the factor projections
  (`toRaw_faProjection`, definitional);
* the only law-dependent statement is the almost-everywhere evaluation comparison
  `toRaw A ∘ faFactorMap (doubleSupport A) =ᵐ B.factorMap A ∘ restrict (doubleEmb S)`
  (`toRaw_faFactorMap_ae_eq`);
* the distinguished coordinates act compatibly **at the level of anchors and events**
  (`anchor_raw_act`, `event_raw_act`): for a finite-active `σ` of the original carrier, the
  distinguished coordinate of `B.act σ j` names exactly the pullback of that of `j` along the
  doubled lift of `σ`. This is exact, by the hull's equivariance, because the representatives are
  canonical rather than chosen. It is not an equality of *indices*: a tagged atom remembers which
  raw index it came from, and the raw basis's own action on indices is opaque here.

Extra finite-active coordinates — the separability seeds of each `finiteActiveFixingAlgebra A` —
are deliberately discarded by `toRaw`; they need not be raw fixing events.

## The construction

Tagged seeds, saturated by orbit compression under the finite-active subgroup: an atom is a tag
(a raw index, or a finite-active seed at some support) together with a sortwise-injective
reassignment of the tag's anchor. Its event is the pullback of the tag's event along a
**finite-active** finitely supported relabeling agreeing with the reassignment on the anchor
(`extendPermFA`), and all such agree (`relabel_preimage_eq_of_agree_fa`), since two of them differ
by a finite-active permutation fixing the anchor. The Boolean syntax `BasisExpr` closes the atoms
under complement and intersection with the action kept strict.
-/

open MeasureTheory

namespace RelSignature

universe u

variable {S : RelSignature.{u}}

open InfiniteRelExchangeableLaw

/-! ### Finite-active extension of a reassignment -/

/-- A finite-active finitely supported relabeling agreeing with a reassignment on its anchor. -/
noncomputable def extendPermFA {A : Finset (Σ s : S.Srt, Vinfinite S s)}
    {f : {v // v ∈ A} → ℕ} (hf : SortwiseInjOn A f) : FiniteActiveFinSuppPerm S := by
  classical
  exact ⟨(Classical.choose (exists_finSuppPerm_agree_on_finset'
      (SaturatedAtom.globalInj hf) A)).1,
    (Classical.choose (exists_finSuppPerm_agree_on_finset' (SaturatedAtom.globalInj hf) A)).2,
    ⟨A.image Sigma.fst, (Classical.choose_spec (exists_finSuppPerm_agree_on_finset'
      (SaturatedAtom.globalInj hf) A)).2⟩⟩

theorem extendPermFA_apply {A : Finset (Σ s : S.Srt, Vinfinite S s)}
    {f : {v // v ∈ A} → ℕ} (hf : SortwiseInjOn A f) (v : Σ s : S.Srt, Vinfinite S s)
    (hv : v ∈ A) : (extendPermFA hf).1 v.1 v.2 = f ⟨v, hv⟩ := by
  classical
  have h := (Classical.choose_spec (exists_finSuppPerm_agree_on_finset'
    (SaturatedAtom.globalInj hf) A)).1 v hv
  show (Classical.choose (exists_finSuppPerm_agree_on_finset'
    (SaturatedAtom.globalInj hf) A)).1 v.1 v.2 = f ⟨v, hv⟩
  rw [h]
  exact SaturatedAtom.globalInj_apply_of_mem hf v hv

/-- **Orbit compression, finite-active form**: two finite-active finitely supported relabelings
agreeing on `A` pull a `finiteActiveFixingAlgebra A`-event back to the same event. -/
theorem relabel_preimage_eq_of_agree_fa {A : Finset (Σ s : S.Srt, Vinfinite S s)}
    {E : Set (RelStructure S (Vinfinite S))}
    (hE : MeasurableSet[RelStructure.finiteActiveFixingAlgebra A] E)
    (τ τ' : FiniteActiveFinSuppPerm S) (h : ∀ v ∈ A, τ.1 v.1 v.2 = τ'.1 v.1 v.2) :
    RelStructure.relabel τ.1 ⁻¹' E = RelStructure.relabel τ'.1 ⁻¹' E := by
  have hπ : SortwiseFixing (S := S) A (τ⁻¹ * τ').1 := ⟨(τ⁻¹ * τ').2.1, fun v hv => by
    show (τ.1 v.1)⁻¹ (τ'.1 v.1 v.2) = v.2
    rw [← h v hv]
    exact (τ.1 v.1).symm_apply_apply v.2⟩
  have hfix := hE.2 _ hπ (τ⁻¹ * τ').2.2
  conv_rhs => rw [show τ' = τ * (τ⁻¹ * τ') from by group]
  show _ = RelStructure.relabel (fun s => τ.1 s * (τ⁻¹ * τ').1 s) ⁻¹' E
  rw [← RelStructure.relabel_preimage_relabel_preimage, hfix]

/-! ### Tagged seeds -/

section Atoms

variable [Countable S.Rel] {M : InfiniteRelExchangeableLaw S}

/-- The countable measure-dense family for `finiteActiveFixingAlgebra A` supplied by separability
of the law. -/
noncomputable def faSeedOf (M : InfiniteRelExchangeableLaw S)
    (A : Finset (Σ s : S.Srt, Vinfinite S s)) : Set (Set (RelStructure S (Vinfinite S))) :=
  (MeasureTheory.isSeparable_trim (μ := (M.law : Measure (RelStructure S (Vinfinite S))))
    (RelStructure.finiteActiveFixingAlgebra_le A)).1.choose

theorem countable_faSeedOf (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    (faSeedOf M A).Countable :=
  (MeasureTheory.isSeparable_trim (μ := (M.law : Measure (RelStructure S (Vinfinite S))))
    (RelStructure.finiteActiveFixingAlgebra_le A)).1.choose_spec.1

theorem measureDense_faSeedOf (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    @Measure.MeasureDense (RelStructure S (Vinfinite S)) (RelStructure.finiteActiveFixingAlgebra A)
      ((M.law : Measure (RelStructure S (Vinfinite S))).trim
        (RelStructure.finiteActiveFixingAlgebra_le A))
      (faSeedOf M A) :=
  (MeasureTheory.isSeparable_trim (μ := (M.law : Measure (RelStructure S (Vinfinite S))))
    (RelStructure.finiteActiveFixingAlgebra_le A)).1.choose_spec.2

theorem faSeedOf_mem {A : Finset (Σ s : S.Srt, Vinfinite S s)}
    {E : Set (RelStructure S (Vinfinite S))} (hE : E ∈ faSeedOf M A) :
    MeasurableSet[RelStructure.finiteActiveFixingAlgebra A] E :=
  @Measure.MeasureDense.measurable (RelStructure S (Vinfinite S))
    (RelStructure.finiteActiveFixingAlgebra A) _ _ (measureDense_faSeedOf A) E hE

/-- **The tags**: a raw index of `B`, or a finite-active seed at some support. -/
def FaTag (B : CoherentBasis M) : Type u :=
  B.ι ⊕ Σ A : Finset (Σ s : S.Srt, Vinfinite S s),
    {E : Set (RelStructure S (Vinfinite S)) // E ∈ faSeedOf M A}

instance [Countable S.Srt] (B : CoherentBasis M) : Countable (FaTag B) := by
  haveI : ∀ A, Countable {E : Set (RelStructure S (Vinfinite S)) // E ∈ faSeedOf M A} :=
    fun A => (countable_faSeedOf A).to_subtype
  unfold FaTag
  infer_instance

namespace FaTag

variable {B : CoherentBasis M}

/-- The anchor of a tag: the doubled support of a raw index, or the seed's support. -/
noncomputable def anchor : FaTag B → Finset (Σ s : S.Srt, Vinfinite S s)
  | .inl j => doubleSupport (B.anchor j)
  | .inr ⟨A, _⟩ => A

/-- The event of a tag: the strictified doubled representative of a raw event, or the seed. -/
noncomputable def event : FaTag B → Set (RelStructure S (Vinfinite S))
  | .inl j => finiteActiveHull (doubleSupport (B.anchor j))
      (RelStructure.restrict (doubleEmb S) ⁻¹' B.event j)
  | .inr ⟨_, E⟩ => E.1

theorem event_mem [Countable S.Srt] : ∀ t : FaTag B,
    MeasurableSet[RelStructure.finiteActiveFixingAlgebra (anchor t)] (event t)
  | .inl j => measurableSet_finiteActiveHull _ (measurable_restrict _ (B.event_mem j).1)
  | .inr ⟨_, E⟩ => faSeedOf_mem E.2

/-- The distinguished event of a raw index is a.e. the raw event read on the doubled sub-copy. -/
theorem event_inl_ae_eq [Countable S.Srt] (j : B.ι) :
    event (B := B) (.inl j) =ᵐ[(M.law : Measure (RelStructure S (Vinfinite S)))]
      RelStructure.restrict (doubleEmb S) ⁻¹' B.event j :=
  finiteActiveHull_ae_eq _ fun σ =>
    M.relabel_preimage_ae_eq_of_fixingAlgebra_doubled (B.event_mem j) σ.2.1 σ.2.2

end FaTag

/-! ### The saturated atoms -/

/-- **A finite-active atom**: a tag together with a sortwise-injective reassignment of its
anchor's vertices. -/
def FaAtom (B : CoherentBasis M) :=
  Σ t : FaTag B, {f : {v // v ∈ FaTag.anchor t} → ℕ // SortwiseInjOn (FaTag.anchor t) f}

namespace FaAtom

variable {B : CoherentBasis M}

instance [Countable S.Srt] : Countable (FaAtom B) := by
  unfold FaAtom
  infer_instance

open scoped Classical in
/-- The anchor of an atom: the tag's anchor, reassigned. -/
noncomputable def anchor (a : FaAtom B) : Finset (Σ s : S.Srt, Vinfinite S s) :=
  (FaTag.anchor a.1).attach.image fun v => ⟨v.1.1, a.2.1 v⟩

/-- The event of an atom: the tag's event, pulled back along a finite-active extension of the
reassignment. -/
noncomputable def event (a : FaAtom B) : Set (RelStructure S (Vinfinite S)) :=
  RelStructure.relabel (extendPermFA a.2.2).1 ⁻¹' FaTag.event a.1

/-- **The action: post-composition on the reassignment**, by the finite-active subgroup. -/
def act (σ : FiniteActiveFinSuppPerm S) (a : FaAtom B) : FaAtom B :=
  ⟨a.1, ⟨fun v => σ.1 v.1.1 (a.2.1 v), fun v w hs hfw =>
    a.2.2 v w hs (by
      have h1 : σ.1 v.1.1 (a.2.1 v) = σ.1 w.1.1 (a.2.1 w) := hfw
      rw [← hs] at h1
      exact (σ.1 v.1.1).injective h1)⟩⟩

theorem act_one (a : FaAtom B) : act 1 a = a := rfl

theorem act_mul (σ τ : FiniteActiveFinSuppPerm S) (a : FaAtom B) :
    act (σ * τ) a = act σ (act τ a) := rfl

open scoped Classical in
theorem anchor_act (σ : FiniteActiveFinSuppPerm S) (a : FaAtom B) :
    anchor (act σ a) = (anchor a).image (Sigma.map id fun s => ⇑(σ.1 s)) := by
  show (FaTag.anchor a.1).attach.image _ = ((FaTag.anchor a.1).attach.image _).image _
  rw [Finset.image_image]
  rfl

open scoped Classical in
theorem anchor_eq_image (a : FaAtom B) :
    anchor a = (FaTag.anchor a.1).image (Sigma.map id fun s => ⇑((extendPermFA a.2.2).1 s)) := by
  ext v
  rw [anchor, Finset.mem_image, Finset.mem_image]
  constructor
  · rintro ⟨w, -, rfl⟩
    refine ⟨w.1, w.2, ?_⟩
    show (⟨w.1.1, (extendPermFA a.2.2).1 w.1.1 w.1.2⟩ : Σ s : S.Srt, Vinfinite S s) =
      ⟨w.1.1, a.2.1 w⟩
    rw [extendPermFA_apply a.2.2 w.1 w.2]
  · rintro ⟨w, hw, rfl⟩
    refine ⟨⟨w, hw⟩, Finset.mem_attach _ _, ?_⟩
    show (⟨w.1, a.2.1 ⟨w, hw⟩⟩ : Σ s : S.Srt, Vinfinite S s) =
      ⟨w.1, (extendPermFA a.2.2).1 w.1 w.2⟩
    rw [extendPermFA_apply a.2.2 w hw]

theorem event_act [Countable S.Srt] (σ : FiniteActiveFinSuppPerm S) (a : FaAtom B) :
    event (act σ a) = RelStructure.relabel σ.1 ⁻¹' event a := by
  rw [event, event, RelStructure.relabel_preimage_relabel_preimage]
  refine relabel_preimage_eq_of_agree_fa (FaTag.event_mem a.1) _ (σ * extendPermFA a.2.2)
    fun v hv => ?_
  rw [extendPermFA_apply (act σ a).2.2 v hv]
  show σ.1 v.1 (a.2.1 ⟨v, hv⟩) = σ.1 v.1 ((extendPermFA a.2.2).1 v.1 v.2)
  rw [extendPermFA_apply a.2.2 v hv]

theorem event_mem [Countable S.Srt] (a : FaAtom B) :
    MeasurableSet[RelStructure.finiteActiveFixingAlgebra (anchor a)] (event a) := by
  classical
  have htrans := RelStructure.finiteActiveFixingAlgebra_comap_relabel (extendPermFA a.2.2).2.2
    (FaTag.anchor a.1)
  rw [anchor_eq_image, ← htrans]
  exact ⟨_, FaTag.event_mem a.1, rfl⟩

omit [Countable S.Rel] in
/-- The identity reassignment of a tag's anchor. -/
theorem sortwiseInjOn_id (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    SortwiseInjOn A fun v : {v // v ∈ A} => v.1.2 := fun _ _ hs hx =>
  Subtype.ext (Sigma.ext hs (heq_of_eq hx))

/-- **The distinguished atom** of a raw index: its tag with the identity reassignment. -/
noncomputable def raw (j : B.ι) : FaAtom B :=
  ⟨.inl j, ⟨fun v => v.1.2, sortwiseInjOn_id _⟩⟩

theorem anchor_raw (j : B.ι) : anchor (raw (B := B) j) = doubleSupport (B.anchor j) := by
  classical
  ext v
  rw [anchor, Finset.mem_image]
  constructor
  · rintro ⟨w, -, rfl⟩
    exact w.2
  · intro hv
    exact ⟨⟨v, hv⟩, Finset.mem_attach _ _, rfl⟩

theorem event_raw [Countable S.Srt] (j : B.ι) :
    event (raw (B := B) j) = FaTag.event (B := B) (.inl j) := by
  rw [event]
  have hfix : SortwiseFixing (S := S) (doubleSupport (B.anchor j)) (extendPermFA
      (raw (B := B) j).2.2).1 :=
    ⟨(extendPermFA _).2.1, fun v hv => by
      rw [extendPermFA_apply (raw (B := B) j).2.2 v hv]
      rfl⟩
  exact (FaTag.event_mem (B := B) (.inl j)).2 _ hfix (extendPermFA _).2.2

end FaAtom

end Atoms

/-! ### The doubled geometry under the finite-active action -/

section Doubled

theorem doubleSupport_mono {A C : Finset (Σ s : S.Srt, Vinfinite S s)} (h : A ⊆ C) :
    doubleSupport A ⊆ doubleSupport C := by
  intro v hv
  obtain ⟨w, hw, rfl⟩ := mem_doubleSupport.mp hv
  exact mem_doubleSupport.mpr ⟨w, h hw, rfl⟩

open scoped Classical in
/-- Doubling commutes with the lifted action. -/
theorem doubleSupport_image (σ : ∀ _ : S.Srt, Equiv.Perm ℕ)
    (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    doubleSupport (A.image (Sigma.map id fun s => ⇑(σ s))) =
      (doubleSupport A).image (Sigma.map id fun s => ⇑(doubledLift σ s)) := by
  ext v
  rw [mem_doubleSupport, Finset.mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
    refine ⟨⟨u.1, poolVertexEquiv S u.1 (Sum.inl u.2)⟩, mem_doubleSupport.mpr ⟨u, hu, rfl⟩, ?_⟩
    show (⟨u.1, doubledLift σ u.1 (poolVertexEquiv S u.1 (Sum.inl u.2))⟩ :
      Σ s : S.Srt, Vinfinite S s) = ⟨u.1, poolVertexEquiv S u.1 (Sum.inl (σ u.1 u.2))⟩
    congr 1
    show poolVertexEquiv S u.1 (Equiv.sumCongr (σ u.1) (Equiv.refl _)
      ((poolVertexEquiv S u.1).symm (poolVertexEquiv S u.1 (Sum.inl u.2)))) = _
    rw [Equiv.symm_apply_apply]
    rfl
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨u, hu, rfl⟩ := mem_doubleSupport.mp hw
    refine ⟨Sigma.map id (fun s => ⇑(σ s)) u, Finset.mem_image_of_mem _ hu, ?_⟩
    show (⟨u.1, poolVertexEquiv S u.1 (Sum.inl (σ u.1 u.2))⟩ : Σ s : S.Srt, Vinfinite S s) =
      ⟨u.1, doubledLift σ u.1 (poolVertexEquiv S u.1 (Sum.inl u.2))⟩
    congr 1
    show _ = poolVertexEquiv S u.1 (Equiv.sumCongr (σ u.1) (Equiv.refl _)
      ((poolVertexEquiv S u.1).symm (poolVertexEquiv S u.1 (Sum.inl u.2))))
    rw [Equiv.symm_apply_apply]
    rfl

/-- The doubled lift of a finite-active finitely supported permutation is one. -/
theorem doubledLift_mem {σ : ∀ _ : S.Srt, Equiv.Perm ℕ} (hσ : σ ∈ finiteActiveFinSuppSubgroup S) :
    doubledLift σ ∈ finiteActiveFinSuppSubgroup S := by
  obtain ⟨⟨N, hN⟩, ⟨T, hT⟩⟩ := hσ
  refine conjPooled_mem_finiteActiveFinSuppSubgroup
    ⟨⟨N, fun s x hx => ⟨?_, rfl⟩⟩, ⟨T, fun s hs => ?_⟩⟩
  · show Sum.inl (σ s x) = Sum.inl x
    rw [hN s x hx]
  · show Equiv.sumCongr (σ s) (Equiv.refl _) = 1
    rw [hT s hs]
    ext x
    cases x <;> rfl

/-- Pulling back along the doubled lift, then restricting, is restricting, then pulling back. -/
theorem relabel_doubledLift_preimage_restrict (σ : ∀ _ : S.Srt, Equiv.Perm ℕ)
    (E : Set (RelStructure S (Vinfinite S))) :
    RelStructure.relabel (doubledLift σ) ⁻¹' (RelStructure.restrict (doubleEmb S) ⁻¹' E) =
      RelStructure.restrict (doubleEmb S) ⁻¹' (RelStructure.relabel σ ⁻¹' E) := by
  ext Y
  simp only [Set.mem_preimage]
  rw [restrict_doubleEmb_relabel_doubledLift]

end Doubled

/-! ### The extension -/

variable {M : InfiniteRelExchangeableLaw S}

open scoped Classical in
/-- **A finite-active coherent extension** of a raw coherent basis `B`: a global finite-active
coherent basis on `Vinfinite`, with a distinguished coordinate for every raw index. See the module
docstring for the contract. -/
structure FiniteActiveExtension (B : CoherentBasis M) where
  /-- The global index type. -/
  ι : Type u
  countable_ι : Countable ι
  anchor : ι → Finset (Σ s : S.Srt, Vinfinite S s)
  event : ι → Set (RelStructure S (Vinfinite S))
  /-- Each event is measurable for the **finite-active** fixing algebra of its anchor. -/
  event_mem : ∀ i, MeasurableSet[RelStructure.finiteActiveFixingAlgebra (anchor i)] (event i)
  bot : ι
  anchor_bot : anchor bot = ∅
  event_bot : event bot = ∅
  compl : ι → ι
  anchor_compl : ∀ i, anchor (compl i) = anchor i
  event_compl : ∀ i, event (compl i) = (event i)ᶜ
  inter : ι → ι → ι
  anchor_inter : ∀ i j, anchor (inter i j) = anchor i ∪ anchor j
  event_inter : ∀ i j, event (inter i j) = event i ∩ event j
  /-- The action of the **countable** finite-active subgroup. -/
  act : FiniteActiveFinSuppPerm S → ι → ι
  act_one : ∀ i, act 1 i = i
  act_mul : ∀ σ τ i, act (σ * τ) i = act σ (act τ i)
  anchor_act : ∀ (σ : FiniteActiveFinSuppPerm S) i,
    anchor (act σ i) = (anchor i).image (Sigma.map id fun s => ⇑(σ.1 s))
  event_act : ∀ (σ : FiniteActiveFinSuppPerm S) i,
    event (act σ i) = RelStructure.relabel σ.1 ⁻¹' event i
  /-- Measure density over each support, for the finite-active fixing algebra. -/
  density : ∀ A : Finset (Σ s : S.Srt, Vinfinite S s),
    @Measure.MeasureDense (RelStructure S (Vinfinite S)) (RelStructure.finiteActiveFixingAlgebra A)
      ((M.law : Measure (RelStructure S (Vinfinite S))).trim
        (RelStructure.finiteActiveFixingAlgebra_le A))
      {E | ∃ i, anchor i ⊆ A ∧ event i = E}
  /-- **The distinguished coordinates**: one per raw index, injectively — so that the projection
  to the raw factor is literally a coordinate restriction. -/
  raw : B.ι → ι
  raw_injective : Function.Injective raw
  /-- Anchored at the doubled support of the raw anchor. -/
  anchor_raw : ∀ j, anchor (raw j) = doubleSupport (B.anchor j)
  /-- Naming, almost surely, the raw event read on the doubled sub-copy. -/
  event_raw_ae : ∀ j, event (raw j) =ᵐ[(M.law : Measure (RelStructure S (Vinfinite S)))]
    RelStructure.restrict (doubleEmb S) ⁻¹' B.event j
  /-- **Action compatibility at the level of events**: the distinguished event of a moved raw
  index is exactly the pullback of the distinguished event along the doubled lift. -/
  event_raw_act : ∀ (σ : FiniteActiveFinSuppPerm S) (j : B.ι),
    event (raw (B.act ⟨σ.1, σ.2.1⟩ j)) =
      RelStructure.relabel (doubledLift σ.1) ⁻¹' event (raw j)

namespace FiniteActiveExtension

variable {B : CoherentBasis M} (F : FiniteActiveExtension B)

instance : Countable F.ι := F.countable_ι

open scoped Classical in
/-- Action compatibility at the level of anchors, derived. -/
theorem anchor_raw_act (σ : FiniteActiveFinSuppPerm S) (j : B.ι) :
    F.anchor (F.raw (B.act ⟨σ.1, σ.2.1⟩ j)) =
      (F.anchor (F.raw j)).image (Sigma.map id fun s => ⇑(doubledLift σ.1 s)) := by
  rw [F.anchor_raw, F.anchor_raw, B.anchor_act, doubleSupport_image]

/-! ### The factor spaces and the projection to the raw factors -/

/-- The indices available over `A`. -/
def FaIndex (A : Finset (Σ s : S.Srt, Vinfinite S s)) := {i : F.ι // F.anchor i ⊆ A}

instance (A : Finset (Σ s : S.Srt, Vinfinite S s)) : Countable (F.FaIndex A) :=
  Subtype.countable

/-- The finite-active factor space at `A`. -/
abbrev FaFactorSpace (A : Finset (Σ s : S.Srt, Vinfinite S s)) := F.FaIndex A → Bool

instance (A : Finset (Σ s : S.Srt, Vinfinite S s)) : StandardBorelSpace (F.FaFactorSpace A) :=
  inferInstance

open scoped Classical in
/-- The finite-active factor map at `A`. -/
noncomputable def faFactorMap (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    RelStructure S (Vinfinite S) → F.FaFactorSpace A :=
  fun X i => decide (X ∈ F.event i.1)

/-- The factor projection, coordinate restriction. -/
def faProjection {C A : Finset (Σ s : S.Srt, Vinfinite S s)} (hCA : C ⊆ A) :
    F.FaFactorSpace A → F.FaFactorSpace C :=
  fun f i => f ⟨i.1, i.2.trans hCA⟩

theorem faProjection_faFactorMap {C A : Finset (Σ s : S.Srt, Vinfinite S s)} (hCA : C ⊆ A) :
    F.faProjection hCA ∘ F.faFactorMap A = F.faFactorMap C := rfl

theorem faProjection_comp {D C A : Finset (Σ s : S.Srt, Vinfinite S s)} (hDC : D ⊆ C)
    (hCA : C ⊆ A) :
    F.faProjection hDC ∘ F.faProjection hCA = F.faProjection (hDC.trans hCA) := rfl

theorem measurable_faProjection {C A : Finset (Σ s : S.Srt, Vinfinite S s)} (hCA : C ⊆ A) :
    Measurable (F.faProjection hCA) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

/-- The distinguished index of a raw index over `A`, over the doubled support. -/
def rawIndex {A : Finset (Σ s : S.Srt, Vinfinite S s)} (j : B.BasisIndex A) :
    F.FaIndex (doubleSupport A) :=
  ⟨F.raw j.1, by rw [F.anchor_raw]; exact doubleSupport_mono j.2⟩

/-- **The projection to the raw factor**: literal coordinate restriction to the distinguished
coordinates. Extra finite-active coordinates are discarded. -/
def toRaw (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    F.FaFactorSpace (doubleSupport A) → B.FactorSpace A :=
  fun x j => x (F.rawIndex j)

theorem measurable_toRaw (A : Finset (Σ s : S.Srt, Vinfinite S s)) : Measurable (F.toRaw A) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

/-- **Exact coherence** of the projection with the factor projections, definitional. -/
theorem toRaw_faProjection {C A : Finset (Σ s : S.Srt, Vinfinite S s)} (hCA : C ⊆ A) :
    F.toRaw C ∘ F.faProjection (doubleSupport_mono hCA) =
      B.factorProjection hCA ∘ F.toRaw A := rfl

/-- **The almost-everywhere evaluation comparison**: projecting the finite-active factor of the
doubled support to the raw coordinates is, modulo the law, the raw factor map read on the
doubled sub-copy. The only law-dependent statement of the interface. -/
theorem toRaw_faFactorMap_ae_eq (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    F.toRaw A ∘ F.faFactorMap (doubleSupport A)
      =ᵐ[(M.law : Measure (RelStructure S (Vinfinite S)))]
        B.factorMap A ∘ RelStructure.restrict (doubleEmb S) := by
  classical
  have h : ∀ j : B.BasisIndex A, ∀ᵐ X ∂(M.law : Measure (RelStructure S (Vinfinite S))),
      (F.toRaw A ∘ F.faFactorMap (doubleSupport A)) X j =
        (B.factorMap A ∘ RelStructure.restrict (doubleEmb S)) X j := by
    intro j
    filter_upwards [Filter.eventuallyEq_set.mp (F.event_raw_ae j.1)] with X hX
    exact Bool.decide_congr hX
  filter_upwards [ae_all_iff.mpr h] with X hX
  funext j
  exact hX j

/-! ### Measurability and generation -/

/-- The factor map at `A` is measurable for `finiteActiveFixingAlgebra A`. -/
theorem measurable_faFactorMap (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    Measurable[RelStructure.finiteActiveFixingAlgebra A] (F.faFactorMap A) := by
  classical
  letI : MeasurableSpace (RelStructure S (Vinfinite S)) :=
    RelStructure.finiteActiveFixingAlgebra A
  refine measurable_pi_iff.mpr fun i => measurable_to_bool ?_
  have hmem : MeasurableSet[RelStructure.finiteActiveFixingAlgebra A] (F.event i.1) :=
    RelStructure.finiteActiveFixingAlgebra_mono i.2 _ (F.event_mem i.1)
  convert hmem using 1
  ext X
  simp [faFactorMap]

/-- The factor map is measurable for the ambient σ-algebra. -/
theorem measurable_faFactorMap' (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    Measurable (F.faFactorMap A) :=
  (F.measurable_faFactorMap A).mono (RelStructure.finiteActiveFixingAlgebra_le A) le_rfl

theorem comap_faFactorMap_le (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    MeasurableSpace.comap (F.faFactorMap A) inferInstance ≤
      RelStructure.finiteActiveFixingAlgebra A :=
  (F.measurable_faFactorMap A).comap_le

/-- **Generation modulo the law**: every `finiteActiveFixingAlgebra A`-event has an a.e.
representative in the pullback of the factor map at `A`. Eventwise, never as an equality of
σ-algebras modulo null sets. -/
theorem exists_comap_faFactorMap_ae_eq (A : Finset (Σ s : S.Srt, Vinfinite S s))
    {E : Set (RelStructure S (Vinfinite S))}
    (hE : MeasurableSet[RelStructure.finiteActiveFixingAlgebra A] E) :
    ∃ E', MeasurableSet[MeasurableSpace.comap (F.faFactorMap A) inferInstance] E' ∧
      E' =ᵐ[(M.law : Measure (RelStructure S (Vinfinite S)))] E := by
  classical
  haveI : IsProbabilityMeasure (M.law : Measure (RelStructure S (Vinfinite S))) := M.law.2
  obtain ⟨E', hE'gen, hE'ae⟩ :=
    (F.density A).exists_generateFrom_ae_eq (RelStructure.finiteActiveFixingAlgebra_le A) hE
  refine ⟨E', ?_, hE'ae⟩
  refine (MeasurableSpace.generateFrom_le ?_) E' hE'gen
  rintro - ⟨i, hiA, rfl⟩
  refine ⟨{f | f ⟨i, hiA⟩ = true}, ?_, ?_⟩
  · have hcoord : Measurable fun f : F.FaIndex A → Bool => f ⟨i, hiA⟩ := measurable_pi_apply _
    exact hcoord (measurableSet_singleton true)
  · ext X
    simp [faFactorMap]

/-! ### Relabeling equivariance -/

open scoped Classical in
theorem image_image_inv_fa (σ : FiniteActiveFinSuppPerm S)
    (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    (A.image (Sigma.map id fun s => ⇑(σ.1 s))).image
      (Sigma.map id fun s => ⇑((σ⁻¹ : FiniteActiveFinSuppPerm S).1 s)) = A := by
  rw [Finset.image_image]
  refine (Finset.image_congr fun v _ => ?_).trans A.image_id
  obtain ⟨s, x⟩ := v
  show (⟨s, (σ.1 s)⁻¹ (σ.1 s x)⟩ : Σ s : S.Srt, Vinfinite S s) = ⟨s, x⟩
  rw [show (σ.1 s)⁻¹ (σ.1 s x) = x from (σ.1 s).symm_apply_apply x]

open scoped Classical in
/-- **A finite-active relabeling is an equivalence of index sets.** -/
noncomputable def faIndexEquiv (σ : FiniteActiveFinSuppPerm S)
    (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    F.FaIndex A ≃ F.FaIndex (A.image (Sigma.map id fun s => ⇑(σ.1 s))) where
  toFun i := ⟨F.act σ i.1, by
    rw [F.anchor_act]
    exact Finset.image_subset_image i.2⟩
  invFun j := ⟨F.act σ⁻¹ j.1, by
    have h := Finset.image_subset_image
      (f := (Sigma.map id fun s => ⇑((σ⁻¹ : FiniteActiveFinSuppPerm S).1 s) :
        (Σ s : S.Srt, Vinfinite S s) → Σ s : S.Srt, Vinfinite S s)) j.2
    rw [image_image_inv_fa σ A] at h
    rw [F.anchor_act]
    exact h⟩
  left_inv i := by
    refine Subtype.ext ?_
    show F.act σ⁻¹ (F.act σ i.1) = i.1
    rw [← F.act_mul, inv_mul_cancel, F.act_one]
  right_inv j := by
    refine Subtype.ext ?_
    show F.act σ (F.act σ⁻¹ j.1) = j.1
    rw [← F.act_mul, mul_inv_cancel, F.act_one]

open scoped Classical in
@[simp] theorem faIndexEquiv_apply_coe (σ : FiniteActiveFinSuppPerm S)
    (A : Finset (Σ s : S.Srt, Vinfinite S s)) (i : F.FaIndex A) :
    (F.faIndexEquiv σ A i).1 = F.act σ i.1 := rfl

open scoped Classical in
/-- **Exact naturality of the factor map** under the finite-active action. -/
theorem faFactorMap_faIndexEquiv (σ : FiniteActiveFinSuppPerm S)
    (A : Finset (Σ s : S.Srt, Vinfinite S s)) (X : RelStructure S (Vinfinite S))
    (i : F.FaIndex A) :
    F.faFactorMap (A.image (Sigma.map id fun s => ⇑(σ.1 s))) X (F.faIndexEquiv σ A i) =
      F.faFactorMap A (RelStructure.relabel σ.1 X) i := by
  show decide (X ∈ F.event (F.act σ i.1)) = decide (RelStructure.relabel σ.1 X ∈ F.event i.1)
  rw [F.event_act]
  rfl

open scoped Classical in
/-- A finite-active relabeling as a measurable equivalence of factor spaces. -/
noncomputable def faFactorSpaceEquiv (σ : FiniteActiveFinSuppPerm S)
    (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    F.FaFactorSpace (A.image (Sigma.map id fun s => ⇑(σ.1 s))) ≃ᵐ F.FaFactorSpace A where
  toEquiv := Equiv.arrowCongr (F.faIndexEquiv σ A).symm (Equiv.refl Bool)
  measurable_toFun := measurable_pi_lambda _ fun _ => measurable_pi_apply _
  measurable_invFun := measurable_pi_lambda _ fun _ => measurable_pi_apply _

open scoped Classical in
@[simp] theorem faFactorSpaceEquiv_apply (σ : FiniteActiveFinSuppPerm S)
    (A : Finset (Σ s : S.Srt, Vinfinite S s))
    (f : F.FaFactorSpace (A.image (Sigma.map id fun s => ⇑(σ.1 s)))) :
    F.faFactorSpaceEquiv σ A f = f ∘ F.faIndexEquiv σ A := rfl

open scoped Classical in
/-- The naturality equation as a commuting square. -/
theorem faFactorMap_comp_relabel (σ : FiniteActiveFinSuppPerm S)
    (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    F.faFactorSpaceEquiv σ A ∘ F.faFactorMap (A.image (Sigma.map id fun s => ⇑(σ.1 s))) =
      F.faFactorMap A ∘ RelStructure.relabel σ.1 :=
  funext fun X => funext fun i => F.faFactorMap_faIndexEquiv σ A X i

/-- The sub-index inclusion. -/
def faIndexEmbedding {C A : Finset (Σ s : S.Srt, Vinfinite S s)} (hCA : C ⊆ A) :
    F.FaIndex C → F.FaIndex A := fun i => ⟨i.1, i.2.trans hCA⟩

open scoped Classical in
theorem faIndexEmbedding_faIndexEquiv {C A : Finset (Σ s : S.Srt, Vinfinite S s)}
    (hCA : C ⊆ A) (σ : FiniteActiveFinSuppPerm S) :
    F.faIndexEmbedding (Finset.image_subset_image hCA) ∘ F.faIndexEquiv σ C =
      F.faIndexEquiv σ A ∘ F.faIndexEmbedding hCA := rfl

open scoped Classical in
theorem faProjection_faIndexEquiv {C A : Finset (Σ s : S.Srt, Vinfinite S s)}
    (hCA : C ⊆ A) (σ : FiniteActiveFinSuppPerm S)
    (f : F.FaFactorSpace (A.image (Sigma.map id fun s => ⇑(σ.1 s)))) :
    F.faProjection hCA (f ∘ F.faIndexEquiv σ A) =
      (F.faProjection (Finset.image_subset_image hCA) f) ∘ F.faIndexEquiv σ C := rfl

/-- The distinguished index map is injective: `toRaw` is literally a coordinate restriction. -/
theorem rawIndex_injective (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    Function.Injective (F.rawIndex (A := A)) := fun _ _ h =>
  Subtype.ext (F.raw_injective (congrArg Subtype.val h))

end FiniteActiveExtension

/-! ### The construction -/

section Construction

variable [Countable S.Srt] [Countable S.Rel] (B : CoherentBasis M)

omit [Countable S.Srt] in
open scoped Classical in
/-- A finite-active seed is an indexed event over its own support: its tag with the identity
reassignment. -/
private theorem faSeedOf_mem_indexed {A : Finset (Σ s : S.Srt, Vinfinite S s)}
    {E : Set (RelStructure S (Vinfinite S))} (hE : E ∈ faSeedOf M A) :
    ∃ i : BasisExpr (FaAtom B),
      BasisExpr.anchorOf FaAtom.anchor i ⊆ A ∧ BasisExpr.eval FaAtom.event i = E := by
  refine ⟨.atom ⟨.inr ⟨A, ⟨E, hE⟩⟩, ⟨fun v => v.1.2, FaAtom.sortwiseInjOn_id _⟩⟩, ?_, ?_⟩
  · intro v hv
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hv
    exact w.2
  · show RelStructure.relabel (extendPermFA (FaAtom.sortwiseInjOn_id A)).1 ⁻¹' E = E
    have hfix : SortwiseFixing (S := S) A (extendPermFA (FaAtom.sortwiseInjOn_id A)).1 :=
      ⟨(extendPermFA _).2.1, fun v hv => by
        rw [extendPermFA_apply (FaAtom.sortwiseInjOn_id A) v hv]⟩
    exact (faSeedOf_mem hE).2 _ hfix (extendPermFA _).2.2

open scoped Classical in
/-- **Every coherent basis has a finite-active coherent extension**, under ambient countability. -/
noncomputable def finiteActiveExtensionOf : FiniteActiveExtension B where
  ι := BasisExpr (FaAtom B)
  countable_ι := inferInstance
  anchor := BasisExpr.anchorOf FaAtom.anchor
  event := BasisExpr.eval FaAtom.event
  event_mem := BasisExpr.eval_mem_of_mono (fun h => RelStructure.finiteActiveFixingAlgebra_mono h)
    FaAtom.event_mem
  bot := .bot
  anchor_bot := rfl
  event_bot := rfl
  compl := .compl
  anchor_compl := fun _ => rfl
  event_compl := fun _ => rfl
  inter := .inter
  anchor_inter := fun _ _ => rfl
  event_inter := fun _ _ => rfl
  act := BasisExpr.act FaAtom.act
  act_one := BasisExpr.act_one (atomAct := FaAtom.act) FaAtom.act_one
  act_mul := fun σ τ => BasisExpr.act_mul (atomAct := FaAtom.act) fun a => FaAtom.act_mul σ τ a
  anchor_act := fun σ => BasisExpr.anchorOf_act (atomAnchor := FaAtom.anchor)
    (atomAct := FaAtom.act) fun a => FaAtom.anchor_act σ a
  event_act := fun σ => BasisExpr.eval_act (atomEvent := FaAtom.event) (atomAct := FaAtom.act)
    fun a => FaAtom.event_act σ a
  density := fun A => by
    refine @MeasureTheory.Measure.MeasureDense.mono (RelStructure S (Vinfinite S))
      (RelStructure.finiteActiveFixingAlgebra A)
      ((M.law : Measure (RelStructure S (Vinfinite S))).trim
        (RelStructure.finiteActiveFixingAlgebra_le A))
      (faSeedOf M A) _ (measureDense_faSeedOf A) (fun E hE => faSeedOf_mem_indexed B hE) ?_
    rintro - ⟨i, hiA, rfl⟩
    exact RelStructure.finiteActiveFixingAlgebra_mono hiA _
      (BasisExpr.eval_mem_of_mono (fun h => RelStructure.finiteActiveFixingAlgebra_mono h)
        FaAtom.event_mem i)
  raw := fun j => .atom (FaAtom.raw j)
  raw_injective := fun j j' h => by
    have h1 : FaAtom.raw (B := B) j = FaAtom.raw j' := BasisExpr.atom.inj h
    have h2 : (Sum.inl j : FaTag B) = Sum.inl j' := congrArg Sigma.fst h1
    exact Sum.inl.inj h2
  anchor_raw := fun j => FaAtom.anchor_raw j
  event_raw_ae := fun j => by
    show FaAtom.event (FaAtom.raw j) =ᵐ[_] _
    rw [FaAtom.event_raw]
    exact FaTag.event_inl_ae_eq j
  event_raw_act := fun σ j => by
    show FaAtom.event (FaAtom.raw (B.act ⟨σ.1, σ.2.1⟩ j)) =
      RelStructure.relabel (doubledLift σ.1) ⁻¹' FaAtom.event (FaAtom.raw j)
    rw [FaAtom.event_raw, FaAtom.event_raw]
    show finiteActiveHull (doubleSupport (B.anchor (B.act ⟨σ.1, σ.2.1⟩ j)))
        (RelStructure.restrict (doubleEmb S) ⁻¹' B.event (B.act ⟨σ.1, σ.2.1⟩ j)) =
      RelStructure.relabel (doubledLift σ.1) ⁻¹' finiteActiveHull (doubleSupport (B.anchor j))
        (RelStructure.restrict (doubleEmb S) ⁻¹' B.event j)
    rw [finiteActiveHull_relabel (doubledLift_mem σ.2), B.anchor_act, B.event_act,
      doubleSupport_image, relabel_doubledLift_preimage_restrict]

theorem nonempty_finiteActiveExtension : Nonempty (FiniteActiveExtension B) :=
  ⟨finiteActiveExtensionOf B⟩

end Construction


end RelSignature
