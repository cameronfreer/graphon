/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelLowerFactor
import Graphon.RelFactorLaws

/-!
# The rank successor decomposition (R4 converse piece 3, #107)

Unit 1 of the rank transition `n → n+1`: the structural splitting of the lower-rank factor space
into everything below rank `n` and the layer at rank exactly `n`. Law-free throughout — this file
defines index types, equivalences and projections, and mentions no measure.

## The layer is a Bool-cube, not a dependent product

The layer at rank `n` is naturally indexed by supports of cardinality `n`, one `ExactSpace A` per
support, so the obvious definition is the dependent product `Π A : RankSupport S n, ExactSpace A`.
That definition would be a mistake. It forces every downstream conditional law to be a kernel into
a dependent product, and **Mathlib has no countable dependent product of kernels** — there is no
`Kernel.pi`; the only `Π`-valued kernels are the Ionescu–Tulcea trajectory kernels, which are
ℕ-indexed chains whose source is the history rather than a fixed common parameter.

Since `ExactSpace A = ExactIndex A → Bool`, the dependent product is *already* a Bool-cube:

`Π A : RankSupport S n, ExactSpace A ≃ ((Σ A, ExactIndex A) → Bool)`

and the sigma index is just `{i // (anchor i).card = n}`. So the layer is defined directly as that
Bool-cube (`RankLayerIndex` / `RankLayerSpace`), with `sigmaExactIndexEquiv` recording the bridge
and `rankLayerMap_sigmaExactIndexEquiv` identifying each block with `exactMap A`. Countability and
standard Borelness are then the same instances that already serve `LowerFactorSpace`, and no
product kernel is needed anywhere downstream: a conditional law of the whole layer is an ordinary
`condDistrib` into a standard Borel space, and mutual conditional independence supplies the finite
products that finite-cylinder extensionality consumes.

## Contents

* `RankLayerIndex` / `RankLayerSpace` / `rankLayerMap` — the layer at rank exactly `n`;
* `RelSignature.RankSupport` and `sigmaExactIndexEquiv` — the bridge to the per-support view;
* `lowerIndexSuccEquiv` and `lowerFactorSpaceSuccEquiv` — the successor split
  `LowerFactorSpace (n+1) ≃ᵐ LowerFactorSpace n × RankLayerSpace n`;
* `lowerToBoundaryProjection` — for `A.card = n`, the rank-`n` factor reads the boundary at `A`,
  with `lowerToBoundaryProjection_lowerFactorMap` definitional;
* `rankSupportEquiv` / `rankLayerIndexEquiv` / `rankLayerSpaceEquiv` — the relabeling actions,
  with `lowerIndexSuccEquiv_rankLayerIndexEquiv` the square against the successor split.

The successor split is a case distinction on `card < n` versus `card = n`, so it is a `dite` and
the *index-level* square against it, `lowerIndexSuccEquiv_rankLayerIndexEquiv`, is **not**
definitional: the branch conditions on the two sides agree only after rewriting anchor cardinality
through the image map. The named coordinate and projection compatibility lemmas *are* definitional
— `rankLayerMap_sigmaExactIndexEquiv`, `lowerFactorSpaceSuccEquiv_lowerFactorMap`,
`fst_lowerFactorSpaceSuccEquiv`, `lowerToBoundaryProjection_lowerFactorMap`,
`rankLayerToExactProjection_rankLayerMap`, the three naturality squares, and the *space-level*
successor square `lowerFactorSpaceSuccEquiv_lowerFactorSpaceEquiv`, which escapes the case split
because it is built from `lowerIndexSuccEquiv.symm` and that is a `Sum.elim`.
-/

open MeasureTheory

namespace RelSignature

/-- The supports of rank exactly `n`: the index of the *family* whose layers make up the rank-`n`
step. Not the index of the layer space itself — see the module header. -/
def RankSupport (S : RelSignature) (n : ℕ) :=
  {A : Finset (Σ s : S.Srt, Vinfinite S s) // A.card = n}

instance {S : RelSignature} [Countable S.Srt] (n : ℕ) : Countable (RankSupport S n) :=
  Subtype.countable

section RankSupport

variable {S : RelSignature}

open scoped Classical in
/-- Relabeling preserves rank: the image map is injective, so it preserves anchor cardinality.
The workhorse of every rank-indexed transport in this file. -/
theorem card_image_sigmaMap {A : Finset (Σ s : S.Srt, Vinfinite S s)} {n : ℕ} (hA : A.card = n)
    (σ : FinSuppPerm S) :
    (A.image (Sigma.map id fun s => ⇑(σ.1 s) :
      (Σ s : S.Srt, Vinfinite S s) → Σ s : S.Srt, Vinfinite S s)).card = n := by
  rw [Finset.card_image_of_injective _
    (Function.injective_id.sigma_map fun s => (σ.1 s).injective)]
  exact hA

open scoped Classical in
/-- **An arbitrary sortwise permutation permutes the supports of each rank.** Finite support is
irrelevant here: only injectivity is used, and that is what preserves cardinality. Stated for
arbitrary sortwise permutations because the exchangeability of a law is an invariance under *all*
of them, not only the finitely supported ones. -/
noncomputable def rankSupportPerm (σ : ∀ s, Equiv.Perm (Vinfinite S s)) (n : ℕ) :
    RankSupport S n ≃ RankSupport S n where
  toFun A := ⟨A.1.image (Sigma.map id fun s => ⇑(σ s)), by
    rw [Finset.card_image_of_injective _
      (Function.injective_id.sigma_map fun s => (σ s).injective)]
    exact A.2⟩
  invFun A := ⟨A.1.image (Sigma.map id fun s => ⇑(σ s)⁻¹), by
    rw [Finset.card_image_of_injective _
      (Function.injective_id.sigma_map fun s => ((σ s)⁻¹).injective)]
    exact A.2⟩
  left_inv A := Subtype.ext (by
    show (A.1.image (Sigma.map id fun s => ⇑(σ s))).image (Sigma.map id fun s => ⇑(σ s)⁻¹)
      = A.1
    rw [Finset.image_image]
    refine (Finset.image_congr fun v _ => ?_).trans A.1.image_id
    obtain ⟨s, x⟩ := v
    show (⟨s, (σ s)⁻¹ ((σ s) x)⟩ : Σ s : S.Srt, Vinfinite S s) = ⟨s, x⟩
    rw [show (σ s)⁻¹ ((σ s) x) = x from (σ s).symm_apply_apply x])
  right_inv A := Subtype.ext (by
    show (A.1.image (Sigma.map id fun s => ⇑(σ s)⁻¹)).image (Sigma.map id fun s => ⇑(σ s))
      = A.1
    rw [Finset.image_image]
    refine (Finset.image_congr fun v _ => ?_).trans A.1.image_id
    obtain ⟨s, x⟩ := v
    show (⟨s, (σ s) ((σ s)⁻¹ x)⟩ : Σ s : S.Srt, Vinfinite S s) = ⟨s, x⟩
    rw [show (σ s) ((σ s)⁻¹ x) = x from (σ s).apply_symm_apply x])

open scoped Classical in
@[simp] theorem rankSupportPerm_coe (σ : ∀ s, Equiv.Perm (Vinfinite S s)) (n : ℕ)
    (A : RankSupport S n) :
    (rankSupportPerm σ n A).1 = A.1.image (Sigma.map id fun s => ⇑(σ s)) := rfl

open scoped Classical in
/-- A relabeling permutes the supports of each rank — the finitely supported case. -/
noncomputable def rankSupportEquiv (σ : FinSuppPerm S) (n : ℕ) :
    RankSupport S n ≃ RankSupport S n :=
  rankSupportPerm σ.1 n


open scoped Classical in
@[simp] theorem rankSupportEquiv_one (n : ℕ) :
    rankSupportEquiv (S := S) (1 : FinSuppPerm S) n = Equiv.refl _ :=
  Equiv.ext fun A => Subtype.ext (by
    show A.1.image (Sigma.map id fun s => ⇑((1 : FinSuppPerm S).1 s)) = A.1
    refine (Finset.image_congr fun v _ => ?_).trans A.1.image_id
    obtain ⟨s, x⟩ := v
    rfl)

open scoped Classical in
@[simp] theorem rankSupportEquiv_mul (σ τ : FinSuppPerm S) (n : ℕ) :
    rankSupportEquiv (S := S) (σ * τ) n =
      (rankSupportEquiv τ n).trans (rankSupportEquiv σ n) :=
  Equiv.ext fun A => Subtype.ext (by
    show A.1.image (Sigma.map id fun s => ⇑((σ * τ).1 s))
      = (A.1.image (Sigma.map id fun s => ⇑(τ.1 s))).image
        (Sigma.map id fun s => ⇑(σ.1 s) :
          (Σ s : S.Srt, Vinfinite S s) → Σ s : S.Srt, Vinfinite S s)
    rw [Finset.image_image]
    refine Finset.image_congr fun v _ => ?_
    obtain ⟨s, x⟩ := v
    rfl)

end RankSupport

namespace CoherentBasis

universe u

variable {S : RelSignature.{u}} {M : InfiniteRelExchangeableLaw S} (B : CoherentBasis M)

/-! ### The rank layer -/

/-- Indices anchored at a support of cardinality exactly `n`. -/
def RankLayerIndex (n : ℕ) := {i : B.ι // (B.anchor i).card = n}

instance (n : ℕ) : Countable (B.RankLayerIndex n) :=
  haveI := B.countable_ι
  Subtype.countable

/-- **The rank-`n` layer of the factor space**, as a Bool-cube on a countable index. -/
abbrev RankLayerSpace (n : ℕ) := B.RankLayerIndex n → Bool

instance (n : ℕ) : StandardBorelSpace (B.RankLayerSpace n) := inferInstance

open scoped Classical in
/-- **The rank-`n` layer map**: evaluate every basis event anchored at rank exactly `n`. -/
noncomputable def rankLayerMap (n : ℕ) :
    RelStructure S (Vinfinite S) → B.RankLayerSpace n :=
  fun X i => decide (X ∈ B.event i.1)

open scoped Classical in
theorem measurable_rankLayerMap (n : ℕ) : Measurable (B.rankLayerMap n) := by
  classical
  refine measurable_pi_iff.mpr fun i => measurable_to_bool ?_
  have hmem : MeasurableSet (B.event i.1) :=
    RelStructure.fixingAlgebra_le (B.anchor i.1) _ (B.event_mem i.1)
  convert hmem using 1
  ext X
  simp [rankLayerMap]

/-! ### The bridge to the per-support view -/

/-- **The layer is the disjoint union of the exact layers over the supports of rank `n`.** This
is the bridge between the Bool-cube definition of `RankLayerSpace` and the per-support view in
which the rank-`n` step is a family indexed by `RankSupport S n`. -/
def sigmaExactIndexEquiv (n : ℕ) :
    (Σ A : RankSupport S n, B.ExactIndex A.1) ≃ B.RankLayerIndex n where
  toFun p := ⟨p.2.1, by rw [p.2.2]; exact p.1.2⟩
  invFun i := ⟨⟨B.anchor i.1, i.2⟩, ⟨i.1, rfl⟩⟩
  left_inv := by
    rintro ⟨⟨A, hA⟩, ⟨i, hi⟩⟩
    cases hi
    rfl
  right_inv i := rfl

/-- **Each block of the layer map is the exact-anchor map at its support.** Definitional: both
sides evaluate the same basis event at the same point. -/
theorem rankLayerMap_sigmaExactIndexEquiv (n : ℕ) (X : RelStructure S (Vinfinite S))
    (A : RankSupport S n) (i : B.ExactIndex A.1) :
    B.rankLayerMap n X (B.sigmaExactIndexEquiv n ⟨A, i⟩) = B.exactMap A.1 X i := rfl

/-! ### The successor split -/

/-- Rank below `n+1` means rank below `n` or rank exactly `n`. -/
def lowerIndexSuccEquiv (n : ℕ) :
    B.LowerIndex (n + 1) ≃ B.LowerIndex n ⊕ B.RankLayerIndex n where
  toFun i :=
    if h : (B.anchor i.1).card < n then Sum.inl ⟨i.1, h⟩
    else Sum.inr ⟨i.1, by have := i.2; omega⟩
  invFun := Sum.elim (fun i => ⟨i.1, by have := i.2; omega⟩)
    (fun i => ⟨i.1, by have := i.2; omega⟩)
  left_inv i := by
    by_cases h : (B.anchor i.1).card < n
    · simp only [dif_pos h, Sum.elim_inl]
      rfl
    · simp only [dif_neg h, Sum.elim_inr]
      rfl
  right_inv p := by
    rcases p with i | i
    · simp only [Sum.elim_inl, dif_pos i.2]
      rfl
    · simp only [Sum.elim_inr, dif_neg (by have := i.2; omega : ¬ (B.anchor i.1).card < n)]
      rfl

/-- **The successor split of the lower-rank factor space**: everything below rank `n`, together
with the layer at rank exactly `n`. -/
noncomputable def lowerFactorSpaceSuccEquiv (n : ℕ) :
    B.LowerFactorSpace (n + 1) ≃ᵐ B.LowerFactorSpace n × B.RankLayerSpace n where
  toFun f := (fun i => f ((B.lowerIndexSuccEquiv n).symm (Sum.inl i)),
    fun i => f ((B.lowerIndexSuccEquiv n).symm (Sum.inr i)))
  invFun p i := Sum.elim p.1 p.2 (B.lowerIndexSuccEquiv n i)
  left_inv f := by
    funext i
    show Sum.elim (fun j => f ((B.lowerIndexSuccEquiv n).symm (Sum.inl j)))
      (fun j => f ((B.lowerIndexSuccEquiv n).symm (Sum.inr j))) (B.lowerIndexSuccEquiv n i) = f i
    rcases h : B.lowerIndexSuccEquiv n i with j | j
    · rw [Sum.elim_inl, ← h, Equiv.symm_apply_apply]
    · rw [Sum.elim_inr, ← h, Equiv.symm_apply_apply]
  right_inv p := by
    refine Prod.ext ?_ ?_
    · funext i
      show Sum.elim p.1 p.2
        (B.lowerIndexSuccEquiv n ((B.lowerIndexSuccEquiv n).symm (Sum.inl i))) = p.1 i
      rw [Equiv.apply_symm_apply, Sum.elim_inl]
    · funext i
      show Sum.elim p.1 p.2
        (B.lowerIndexSuccEquiv n ((B.lowerIndexSuccEquiv n).symm (Sum.inr i))) = p.2 i
      rw [Equiv.apply_symm_apply, Sum.elim_inr]
  measurable_toFun := by
    refine Measurable.prod ?_ ?_ <;>
      exact measurable_pi_lambda _ fun _ => measurable_pi_apply _
  measurable_invFun := by
    refine measurable_pi_lambda _ fun i => ?_
    show Measurable fun p : B.LowerFactorSpace n × B.RankLayerSpace n =>
      Sum.elim p.1 p.2 (B.lowerIndexSuccEquiv n i)
    rcases h : B.lowerIndexSuccEquiv n i with j | j
    · exact measurable_fst.eval
    · exact measurable_snd.eval

/-- The successor split refines the rank nesting: its first component is the rank-`n` projection. -/
theorem fst_lowerFactorSpaceSuccEquiv (n : ℕ) (f : B.LowerFactorSpace (n + 1)) :
    (B.lowerFactorSpaceSuccEquiv n f).1 = B.lowerFactorProjection (Nat.le_succ n) f := rfl

/-- The successor split applied to the factor map reads the two layers. -/
theorem lowerFactorSpaceSuccEquiv_lowerFactorMap (n : ℕ) (X : RelStructure S (Vinfinite S)) :
    B.lowerFactorSpaceSuccEquiv n (B.lowerFactorMap (n + 1) X) =
      (B.lowerFactorMap n X, B.rankLayerMap n X) := rfl

/-! ### The boundary projection at a support of rank `n` -/

/-- A boundary index at a support of rank `n` has rank `< n`. -/
def boundaryToLowerIndex {A : Finset (Σ s : S.Srt, Vinfinite S s)} {n : ℕ} (hA : A.card = n) :
    B.BoundaryIndex A → B.LowerIndex n :=
  fun i => ⟨i.1, hA ▸ Finset.card_lt_card i.2⟩

/-- **The rank-`n` factor reads the boundary at every support of rank `n`.** -/
def lowerToBoundaryProjection {A : Finset (Σ s : S.Srt, Vinfinite S s)} {n : ℕ} (hA : A.card = n) :
    B.LowerFactorSpace n → B.BoundarySpace A :=
  fun f => f ∘ B.boundaryToLowerIndex hA

theorem measurable_lowerToBoundaryProjection {A : Finset (Σ s : S.Srt, Vinfinite S s)} {n : ℕ}
    (hA : A.card = n) : Measurable (B.lowerToBoundaryProjection hA) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

/-- Definitional, as intended: the boundary map at `A` factors through the rank-`n` factor. -/
theorem lowerToBoundaryProjection_lowerFactorMap {A : Finset (Σ s : S.Srt, Vinfinite S s)} {n : ℕ}
    (hA : A.card = n) :
    B.lowerToBoundaryProjection hA ∘ B.lowerFactorMap n = B.boundaryMap A := rfl

/-! ### The exact projection at a support of rank `n` -/

/-- An exact index at a support of rank `n` lies in the rank-`n` layer. -/
def rankLayerToExactIndex {A : Finset (Σ s : S.Srt, Vinfinite S s)} {n : ℕ} (hA : A.card = n) :
    B.ExactIndex A → B.RankLayerIndex n :=
  fun i => ⟨i.1, by rw [i.2]; exact hA⟩

/-- **The layer projects onto the exact layer at each support of rank `n`.** The per-support view
of the Bool-cube: this is the map along which the layer's conditional law restricts to
`stepKernel A`'s target. -/
def rankLayerToExactProjection {A : Finset (Σ s : S.Srt, Vinfinite S s)} {n : ℕ}
    (hA : A.card = n) : B.RankLayerSpace n → B.ExactSpace A :=
  fun f => f ∘ B.rankLayerToExactIndex hA

theorem measurable_rankLayerToExactProjection {A : Finset (Σ s : S.Srt, Vinfinite S s)} {n : ℕ}
    (hA : A.card = n) : Measurable (B.rankLayerToExactProjection hA) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

/-- Definitional: the exact-anchor map at `A` factors through the rank-`n` layer. -/
theorem rankLayerToExactProjection_rankLayerMap {A : Finset (Σ s : S.Srt, Vinfinite S s)} {n : ℕ}
    (hA : A.card = n) :
    B.rankLayerToExactProjection hA ∘ B.rankLayerMap n = B.exactMap A := rfl

/-! ### Relabeling actions -/

open scoped Classical in
/-- A relabeling permutes the rank-`n` layer index: the action transports anchors by an injective
image map, so it preserves cardinality exactly. -/
noncomputable def rankLayerIndexEquiv (σ : FinSuppPerm S) (n : ℕ) :
    B.RankLayerIndex n ≃ B.RankLayerIndex n where
  toFun i := ⟨B.act σ i.1, by
    rw [B.anchor_act, Finset.card_image_of_injective _
      (Function.injective_id.sigma_map fun s => (σ.1 s).injective)]
    exact i.2⟩
  invFun j := ⟨B.act σ⁻¹ j.1, by
    rw [B.anchor_act, Finset.card_image_of_injective _
      (Function.injective_id.sigma_map fun s => ((σ⁻¹ : FinSuppPerm S).1 s).injective)]
    exact j.2⟩
  left_inv i := Subtype.ext (by
    show B.act σ⁻¹ (B.act σ i.1) = i.1
    rw [← B.act_mul, inv_mul_cancel, B.act_one])
  right_inv j := Subtype.ext (by
    show B.act σ (B.act σ⁻¹ j.1) = j.1
    rw [← B.act_mul, mul_inv_cancel, B.act_one])

open scoped Classical in
@[simp] theorem rankLayerIndexEquiv_apply_coe (σ : FinSuppPerm S) (n : ℕ)
    (i : B.RankLayerIndex n) : (B.rankLayerIndexEquiv σ n i).1 = B.act σ i.1 := rfl

open scoped Classical in
/-- **Identity**, as an equality of equivalences: these are automorphisms of one fixed type. -/
@[simp] theorem rankLayerIndexEquiv_one (n : ℕ) :
    B.rankLayerIndexEquiv (1 : FinSuppPerm S) n = Equiv.refl _ :=
  Equiv.ext fun i => Subtype.ext (B.act_one i.1)

open scoped Classical in
/-- **Composition**, likewise. -/
@[simp] theorem rankLayerIndexEquiv_mul (σ τ : FinSuppPerm S) (n : ℕ) :
    B.rankLayerIndexEquiv (σ * τ) n =
      (B.rankLayerIndexEquiv τ n).trans (B.rankLayerIndexEquiv σ n) :=
  Equiv.ext fun i => Subtype.ext (B.act_mul σ τ i.1)

open scoped Classical in
/-- **Naturality of the layer map**, with the same orientation as `lowerFactorMap_lowerIndexEquiv`
— forced by `event_act` being a preimage equality. -/
theorem rankLayerMap_rankLayerIndexEquiv (σ : FinSuppPerm S) (n : ℕ)
    (X : RelStructure S (Vinfinite S)) (i : B.RankLayerIndex n) :
    B.rankLayerMap n X (B.rankLayerIndexEquiv σ n i) =
      B.rankLayerMap n (RelStructure.relabel σ.1 X) i := by
  show decide (X ∈ B.event (B.act σ i.1)) = decide (RelStructure.relabel σ.1 X ∈ B.event i.1)
  rw [B.event_act]
  rfl

open scoped Classical in
/-- A relabeling as a measurable automorphism of the layer space, by coordinate reindexing. -/
noncomputable def rankLayerSpaceEquiv (σ : FinSuppPerm S) (n : ℕ) :
    B.RankLayerSpace n ≃ᵐ B.RankLayerSpace n where
  toEquiv := Equiv.arrowCongr (B.rankLayerIndexEquiv σ n).symm (Equiv.refl Bool)
  measurable_toFun := measurable_pi_lambda _ fun _ => measurable_pi_apply _
  measurable_invFun := measurable_pi_lambda _ fun _ => measurable_pi_apply _

open scoped Classical in
theorem rankLayerSpaceEquiv_comp_rankLayerMap (σ : FinSuppPerm S) (n : ℕ) :
    B.rankLayerSpaceEquiv σ n ∘ B.rankLayerMap n =
      B.rankLayerMap n ∘ RelStructure.relabel σ.1 :=
  funext fun X => funext fun i => B.rankLayerMap_rankLayerIndexEquiv σ n X i

open scoped Classical in
/-- **The successor split is equivariant.** Not definitional: the split branches on
`card < n`, and the two sides' branch conditions agree only after transporting anchor cardinality
through the image map — which is exactly `rankLayerIndexEquiv`'s defining computation. -/
theorem lowerIndexSuccEquiv_rankLayerIndexEquiv (σ : FinSuppPerm S) (n : ℕ) :
    (B.lowerIndexSuccEquiv n) ∘ (B.lowerIndexEquiv σ (n + 1)) =
      (Sum.map (B.lowerIndexEquiv σ n) (B.rankLayerIndexEquiv σ n)) ∘
        (B.lowerIndexSuccEquiv n) := by
  classical
  funext i
  have hcard : (B.anchor (B.act σ i.1)).card = (B.anchor i.1).card := by
    rw [B.anchor_act, Finset.card_image_of_injective _
      (Function.injective_id.sigma_map fun s => (σ.1 s).injective)]
  by_cases h : (B.anchor i.1).card < n
  · show (if _ : (B.anchor (B.act σ i.1)).card < n then _ else _) = _
    rw [dif_pos (hcard ▸ h)]
    show Sum.inl _ = Sum.map _ _ (if _ : (B.anchor i.1).card < n then _ else _)
    rw [dif_pos h]
    rfl
  · show (if _ : (B.anchor (B.act σ i.1)).card < n then _ else _) = _
    rw [dif_neg (hcard ▸ h)]
    show Sum.inr _ = Sum.map _ _ (if _ : (B.anchor i.1).card < n then _ else _)
    rw [dif_neg h]
    rfl

open scoped Classical in
@[simp] theorem rankLayerSpaceEquiv_apply (σ : FinSuppPerm S) (n : ℕ)
    (g : B.RankLayerSpace n) (i : B.RankLayerIndex n) :
    B.rankLayerSpaceEquiv σ n g i = g (B.rankLayerIndexEquiv σ n i) := rfl

open scoped Classical in
/-- **Identity**, as an equality of measurable equivalences. -/
@[simp] theorem rankLayerSpaceEquiv_one (n : ℕ) :
    B.rankLayerSpaceEquiv (1 : FinSuppPerm S) n = MeasurableEquiv.refl _ :=
  MeasurableEquiv.ext <| funext fun g => funext fun i => by simp

open scoped Classical in
/-- **Composition**, contravariantly, matching `lowerFactorSpaceEquiv_mul`. -/
@[simp] theorem rankLayerSpaceEquiv_mul (σ τ : FinSuppPerm S) (n : ℕ) :
    B.rankLayerSpaceEquiv (σ * τ) n =
      (B.rankLayerSpaceEquiv σ n).trans (B.rankLayerSpaceEquiv τ n) :=
  MeasurableEquiv.ext <| funext fun g => funext fun i => by simp

/-! ### Naturality -/

open scoped Classical in
/-- **The support/exact bridge is natural**: acting on a support and its exact index agrees with
acting on the corresponding layer index. Definitional — both routes are `act σ` on the index and
differ only in which anchor proof is carried. -/
theorem rankLayerIndexEquiv_sigmaExactIndexEquiv (σ : FinSuppPerm S) (n : ℕ)
    (A : RankSupport S n) (i : B.ExactIndex A.1) :
    B.rankLayerIndexEquiv σ n (B.sigmaExactIndexEquiv n ⟨A, i⟩) =
      B.sigmaExactIndexEquiv n ⟨rankSupportEquiv σ n A, B.exactIndexEquiv σ A.1 i⟩ := rfl

open scoped Classical in
/-- **The exact projection is natural.** Reading the exact layer at `A` after relabeling is
relabeling after reading it at the image support. Definitional. -/
theorem exactSpaceEquiv_rankLayerToExactProjection (σ : FinSuppPerm S)
    {A : Finset (Σ s : S.Srt, Vinfinite S s)} {n : ℕ} (hA : A.card = n) :
    ⇑(B.exactSpaceEquiv σ A) ∘ B.rankLayerToExactProjection (card_image_sigmaMap hA σ) =
      B.rankLayerToExactProjection hA ∘ ⇑(B.rankLayerSpaceEquiv σ n) := rfl

open scoped Classical in
/-- **The boundary projection is natural**, likewise definitional. -/
theorem boundarySpaceEquiv_lowerToBoundaryProjection (σ : FinSuppPerm S)
    {A : Finset (Σ s : S.Srt, Vinfinite S s)} {n : ℕ} (hA : A.card = n) :
    ⇑(B.boundarySpaceEquiv σ A) ∘ B.lowerToBoundaryProjection (card_image_sigmaMap hA σ) =
      B.lowerToBoundaryProjection hA ∘ ⇑(B.lowerFactorSpaceEquiv σ n) := rfl

open scoped Classical in
/-- **The successor split is equivariant at the level of spaces** — and here, unlike the
index-level square `lowerIndexSuccEquiv_rankLayerIndexEquiv`, the statement is definitional. The
space-level map is built from `lowerIndexSuccEquiv.symm`, which is a `Sum.elim` and so computes on
the constructors; the forward `dite` that forces the case split never appears. -/
theorem lowerFactorSpaceSuccEquiv_lowerFactorSpaceEquiv (σ : FinSuppPerm S) (n : ℕ) :
    ⇑(B.lowerFactorSpaceSuccEquiv n) ∘ ⇑(B.lowerFactorSpaceEquiv σ (n + 1)) =
      Prod.map ⇑(B.lowerFactorSpaceEquiv σ n) ⇑(B.rankLayerSpaceEquiv σ n) ∘
        ⇑(B.lowerFactorSpaceSuccEquiv n) := rfl

end CoherentBasis

end RelSignature
