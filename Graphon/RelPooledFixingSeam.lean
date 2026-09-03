/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelPooledAcceptance
import Graphon.RelFixingAlgebra
import Graphon.RelPollingInfrastructure

/-!
# The pooled fixing seam (R4 converse, #107, #197)

A fixing event of the original carrier, read on the pooled carrier through the original half,
has a representative that is **exactly** invariant under the finite-active pooled stabilizer of
its support, modulo the pooled structure marginal — and hence modulo the joint pooled law.

## The carrier issue

`finiteActiveFixingAlgebra` lives on `Vinfinite = ℕ`; the seam lives on `PoolVertex = ℕ ⊕ ℕ`.
Nothing here applies one as the other. The pooled carrier is identified with the original one by
`poolVertexEquiv` (`inl n ↦ 2n`, `inr n ↦ 2n + 1`), transported to structures by
`RelStructure.congrCarrier`; the pooled finite-active fixing algebra is the pullback of the
original one along that identification (`pooledFiniteActiveFixingAlgebra`), and
`conjPooled_mem_finiteActiveFinSuppSubgroup` records that a pooled permutation with finite
support on both halves and finitely many active sorts — boundary crossings included — conjugates
into `FiniteActiveFinSuppPerm`.

Under that identification the pooled structure marginal of a pooled rank extension **is** the
exchangeable law itself (`map_poolVertexEquiv`), so the analysis runs on `M.law` over
`Vinfinite`, against the *doubled* copy of the original carrier.

## The two named results

* `relabel_preimage_ae_eq_of_fixingAlgebra_doubled` — **a.e. invariance**: for
  `E ∈ fixingAlgebra A`, the event "the doubled sub-copy lies in `E`" is invariant modulo `M.law`
  under every finite-active finitely supported permutation fixing the doubled `A`. The proof is
  window-moving: approximate `E` by a coordinate cylinder on finitely many tagged vertices, move
  those vertices outside `A` deep into the sub-copy by a half-preserving permutation fixing `A`
  (which fixes the event exactly), where the given permutation acts trivially; measure
  preservation under the exchangeable law closes the estimate.
* `exists_finiteActiveFixingAlgebra_ae_eq_doubled` — **strictification**: the countable invariant
  hull of that event over the finite-active stabilizer of the doubled `A` is measurable, exactly
  invariant, and a.e. equal to it. Countability of `FiniteActiveFinSuppPerm` under
  `[Countable S.Srt]` is what makes the hull measurable; the raw finitely supported group is
  uncountable over infinitely many sorts and the argument is unavailable for it.

Both are then stated on the pooled structure marginal
(`PooledRankExtension.exists_pooledFiniteActiveFixingAlgebra_ae_eq`) and lifted to the joint
pooled law (`PooledRankExtension.exists_pooledFiniteActiveFixingAlgebra_ae_eq_fst`).

The hull construction and the bundled stabilizer are private: no second consumer justifies
extracting them yet.
-/

open MeasureTheory
open scoped symmDiff

namespace RelSignature

universe u

variable {S : RelSignature.{u}}

/-! ### The carrier identification -/

/-- The pooled carrier identified with the original one, on structures. -/
noncomputable abbrev poolStructureEquiv (S : RelSignature.{u}) :
    RelStructure S (PoolVertex S) ≃ᵐ RelStructure S (Vinfinite S) :=
  RelStructure.congrCarrier fun s => poolVertexEquiv S s

/-- The doubling embedding: the original half, read inside the identified carrier. -/
def doubleEmb (S : RelSignature.{u}) (s : S.Srt) : Vinfinite S s ↪ Vinfinite S s :=
  ⟨fun x => poolVertexEquiv S s (Sum.inl x),
    fun _ _ h => Sum.inl_injective ((poolVertexEquiv S s).injective h)⟩

/-- A tagged vertex set of the original carrier, doubled. -/
noncomputable def doubleSupport (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    Finset (Σ s : S.Srt, Vinfinite S s) :=
  supportImage (doubleEmb S) A

/-- Vertices of the doubled support are the doubled vertices of the support. -/
theorem mem_doubleSupport {A : Finset (Σ s : S.Srt, Vinfinite S s)}
    {v : Σ s : S.Srt, Vinfinite S s} :
    v ∈ doubleSupport A ↔ ∃ w ∈ A, (⟨w.1, poolVertexEquiv S w.1 (Sum.inl w.2)⟩ :
      Σ s : S.Srt, Vinfinite S s) = v := by
  rw [doubleSupport, mem_supportImage_iff]
  rfl

/-- Reading the original half of the identified carrier is restriction along the doubling. -/
theorem restrictOriginal_comp_symm :
    restrictOriginal S ∘ (poolStructureEquiv S).symm =
      RelStructure.restrict (doubleEmb S) := rfl

@[simp] theorem poolVertexEquiv_inl (s : S.Srt) (z : ℕ) :
    poolVertexEquiv S s (Sum.inl z) = 2 * z := by simp [poolVertexEquiv]

@[simp] theorem poolVertexEquiv_inr (s : S.Srt) (z : ℕ) :
    poolVertexEquiv S s (Sum.inr z) = 2 * z + 1 := by simp [poolVertexEquiv]

/-- A pooled permutation with a common support bound on both halves and finitely many active
sorts. Boundary crossings are allowed. -/
def PooledFiniteActive (ρ : ∀ s, Equiv.Perm (PoolVertex S s)) : Prop :=
  (∃ N : ℕ, ∀ s x, N ≤ x → ρ s (Sum.inl x) = Sum.inl x ∧ ρ s (Sum.inr x) = Sum.inr x) ∧
    ∃ T : Finset S.Srt, ∀ s, s ∉ T → ρ s = 1

/-- The conjugate of a pooled permutation by the carrier identification. -/
def conjPooled (ρ : ∀ s, Equiv.Perm (PoolVertex S s)) : ∀ _ : S.Srt, Equiv.Perm ℕ :=
  fun s => (poolVertexEquiv S s).symm.trans ((ρ s).trans (poolVertexEquiv S s))

/-- **Boundary-crossing pooled permutations conjugate into the finite-active subgroup.** -/
theorem conjPooled_mem_finiteActiveFinSuppSubgroup {ρ : ∀ s, Equiv.Perm (PoolVertex S s)}
    (hρ : PooledFiniteActive ρ) : conjPooled ρ ∈ finiteActiveFinSuppSubgroup S := by
  obtain ⟨⟨N, hN⟩, ⟨T, hT⟩⟩ := hρ
  refine ⟨⟨2 * N + 1, fun s x hx => ?_⟩, ⟨T, fun s hs => ?_⟩⟩
  · show poolVertexEquiv S s (ρ s ((poolVertexEquiv S s).symm x)) = x
    have hsplit : ∀ y : PoolVertex S s, (∃ z, N ≤ z ∧ y = Sum.inl z) ∨
        (∃ z, N ≤ z ∧ y = Sum.inr z) → ρ s y = y := by
      rintro y (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
      · exact (hN s z hz).1
      · exact (hN s z hz).2
    have hfix : ρ s ((poolVertexEquiv S s).symm x) = (poolVertexEquiv S s).symm x := by
      apply hsplit
      obtain ⟨y, hy⟩ : ∃ y, (poolVertexEquiv S s).symm x = y := ⟨_, rfl⟩
      have hxy : poolVertexEquiv S s y = x := by rw [← hy]; exact Equiv.apply_symm_apply _ _
      rcases y with z | z
      · refine Or.inl ⟨z, ?_, hy⟩
        rw [poolVertexEquiv_inl] at hxy
        have h2 : (2 : ℕ) * z = x := hxy
        have h3 : (2 : ℕ) * N + 1 ≤ x := hx
        omega
      · refine Or.inr ⟨z, ?_, hy⟩
        rw [poolVertexEquiv_inr] at hxy
        have h2 : (2 : ℕ) * z + 1 = x := hxy
        have h3 : (2 : ℕ) * N + 1 ≤ x := hx
        omega
    rw [hfix]
    exact Equiv.apply_symm_apply _ _
  · show (poolVertexEquiv S s).symm.trans ((ρ s).trans (poolVertexEquiv S s)) = 1
    rw [hT s hs]
    ext x
    simp

/-- **The pooled finite-active fixing σ-algebra** at a pooled tagged vertex set: the pullback
of the original finite-active fixing algebra along the carrier identification. -/
@[implicit_reducible]
noncomputable def pooledFiniteActiveFixingAlgebra (X : Finset (Σ s : S.Srt, PoolVertex S s)) :
    MeasurableSpace (RelStructure S (PoolVertex S)) :=
  MeasurableSpace.comap (poolStructureEquiv S)
    (RelStructure.finiteActiveFixingAlgebra
      (supportImage (fun s => (poolVertexEquiv S s).toEmbedding) X))

/-! ### The doubled sub-copy under an exchangeable law -/

namespace InfiniteRelExchangeableLaw

variable (M : InfiniteRelExchangeableLaw S)

/-- The half-preserving lift of an original permutation, conjugated to the identified carrier:
it acts on the doubled sub-copy as `τ` and fixes the odd vertices. -/
noncomputable def doubledLift (τ : ∀ _ : S.Srt, Equiv.Perm ℕ) : ∀ _ : S.Srt, Equiv.Perm ℕ :=
  conjPooled fun s => Equiv.sumCongr (τ s) (Equiv.refl _)

omit M in
/-- Restriction along the doubling intertwines the lift with `τ`. -/
theorem restrict_doubleEmb_relabel_doubledLift (τ : ∀ _ : S.Srt, Equiv.Perm ℕ)
    (Y : RelStructure S (Vinfinite S)) :
    RelStructure.restrict (doubleEmb S) (RelStructure.relabel (doubledLift τ) Y) =
      RelStructure.relabel τ (RelStructure.restrict (doubleEmb S) Y) := by
  show RelStructure.comap _ (RelStructure.comap _ Y) = RelStructure.comap _ (RelStructure.comap _ Y)
  rw [← RelStructure.comap_comp, ← RelStructure.comap_comp]
  congr 1
  funext s x
  show poolVertexEquiv S s (Equiv.sumCongr (τ s) (Equiv.refl _)
      ((poolVertexEquiv S s).symm (poolVertexEquiv S s (Sum.inl x)))) =
    poolVertexEquiv S s (Sum.inl (τ s x))
  rw [Equiv.symm_apply_apply]
  rfl

/-- **A.e. invariance of a fixing event read on the doubled sub-copy** under every finite-active
finitely supported permutation fixing the doubled support. The permutation may move the
sub-copy's vertices anywhere, boundary crossings included: it is the half-preserving lift of a
permutation fixing `A` that moves the finitely many relevant vertices out of its way. -/
theorem relabel_preimage_ae_eq_of_fixingAlgebra_doubled [Countable S.Rel]
    {A : Finset (Σ s : S.Srt, Vinfinite S s)} {E : Set (RelStructure S (Vinfinite S))}
    (hE : MeasurableSet[RelStructure.fixingAlgebra A] E)
    {σ : ∀ _ : S.Srt, Equiv.Perm ℕ} (hσ : σ ∈ finiteActiveFinSuppSubgroup S)
    (hfix : ∀ v ∈ doubleSupport A, σ v.1 v.2 = v.2) :
    RelStructure.relabel σ ⁻¹' (RelStructure.restrict (doubleEmb S) ⁻¹' E)
      =ᵐ[(M.law : Measure (RelStructure S (Vinfinite S)))]
        RelStructure.restrict (doubleEmb S) ⁻¹' E := by
  classical
  set μ : Measure (RelStructure S (Vinfinite S)) :=
    (M.law : Measure (RelStructure S (Vinfinite S))) with hμ
  haveI : IsProbabilityMeasure μ := M.law.2
  set F : Set (RelStructure S (Vinfinite S)) := RelStructure.restrict (doubleEmb S) ⁻¹' E with hF
  have hFmeas : MeasurableSet F := measurable_restrict _ hE.1
  have hMPσ : MeasurePreserving (RelStructure.relabel σ) μ μ := M.measurePreserving_relabel σ
  have hMPd : MeasurePreserving (RelStructure.restrict (doubleEmb S)) μ μ :=
    ⟨measurable_restrict _, M.law_map_restrict_self _⟩
  obtain ⟨⟨Nσ, hNσ⟩, -⟩ := hσ
  have key : ∀ ε : ENNReal, 0 < ε → μ ((RelStructure.relabel σ ⁻¹' F) ∆ F) < ε := by
    intro ε hε
    -- approximate `E` by a coordinate cylinder
    have hring : IsSetRing (measurableCylinders fun _ : RelCoord S (Vinfinite S) => Bool) :=
      ⟨empty_mem_measurableCylinders _, fun _ _ hs ht => union_mem_measurableCylinders hs ht,
        fun _ _ hs ht => sdiff_mem_measurableCylinders hs ht⟩
    obtain ⟨D₀, hD₀mem, hD₀lt⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing
      (μ := μ) hring ⟨{Set.univ}, Set.countable_singleton _,
        Set.singleton_subset_iff.mpr (univ_mem_measurableCylinders _), by simp⟩
      generateFrom_measurableCylinders.symm hE.1 (ENNReal.half_pos hε.ne')
    obtain ⟨K, T, hT, rfl⟩ := (mem_measurableCylinders _).mp hD₀mem
    have hD₀meas : MeasurableSet (cylinder K T) :=
      MeasurableSet.cylinder (α := fun _ : RelCoord S (Vinfinite S) => Bool) K hT
    -- the relevant vertices, and a bound above the permutation's support
    set W : Finset (Σ s : S.Srt, Vinfinite S s) := K.biUnion RelCoord.support ∪ A with hW
    set Nb : ℕ := max Nσ ((W.sup fun v => v.2) + 1) with hNb
    have hinj : ∀ s : S.Srt, Function.Injective
        (fun v : ℕ => if (⟨s, v⟩ : Σ s : S.Srt, Vinfinite S s) ∈ A then v else v + Nb) := by
      intro s a b hab
      have hlt : ∀ v ∈ A, v.2 < Nb := fun v hv => lt_of_lt_of_le
        (Nat.lt_succ_of_le (Finset.le_sup (f := fun w : Σ s : S.Srt, Vinfinite S s => w.2)
          (Finset.mem_union_right _ hv))) (le_max_right _ _)
      simp only at hab
      by_cases ha : (⟨s, a⟩ : Σ s : S.Srt, Vinfinite S s) ∈ A <;>
        by_cases hb : (⟨s, b⟩ : Σ s : S.Srt, Vinfinite S s) ∈ A
      · rw [if_pos ha, if_pos hb] at hab; exact hab
      · rw [if_pos ha, if_neg hb] at hab
        have h1 : (a : ℕ) < Nb := hlt ⟨s, a⟩ ha
        omega
      · rw [if_neg ha, if_pos hb] at hab
        have h1 : (b : ℕ) < Nb := hlt ⟨s, b⟩ hb
        omega
      · rw [if_neg ha, if_neg hb] at hab; omega
    obtain ⟨τ, hτ⟩ := exists_finSuppPerm_agree_on_finset
      (fun s => ⟨_, hinj s⟩ : ∀ s, Vinfinite S s ↪ Vinfinite S s) W
    have hτ' : ∀ (s : S.Srt) (x : ℕ), (⟨s, x⟩ : Σ s : S.Srt, Vinfinite S s) ∈ W →
        τ.1 s x = if (⟨s, x⟩ : Σ s : S.Srt, Vinfinite S s) ∈ A then x else x + Nb :=
      fun s x h => hτ ⟨s, x⟩ h
    have hτA : ∀ v ∈ A, τ.1 v.1 v.2 = v.2 := fun v hv => by
      rw [hτ' v.1 v.2 (Finset.mem_union_right _ (by simpa using hv)), if_pos (by simpa using hv)]
    -- the lift fixes `F` exactly
    have hgF : RelStructure.relabel (doubledLift τ.1) ⁻¹' F = F := by
      ext Y
      simp only [Set.mem_preimage, hF]
      rw [restrict_doubleEmb_relabel_doubledLift]
      have := hE.2 τ.1 ⟨τ.2, hτA⟩
      constructor
      · intro h; rw [← this]; exact h
      · intro h; rw [← this] at h; exact h
    have hMPg : MeasurePreserving (RelStructure.relabel (doubledLift τ.1)) μ μ :=
      M.measurePreserving_relabel (doubledLift τ.1)
    set D : Set (RelStructure S (Vinfinite S)) :=
      RelStructure.restrict (doubleEmb S) ⁻¹' cylinder K T with hD
    have hDmeas : MeasurableSet D := measurable_restrict _ hD₀meas
    -- the given permutation fixes the moved cylinder exactly
    have hσgD : RelStructure.relabel σ ⁻¹' (RelStructure.relabel (doubledLift τ.1) ⁻¹' D) =
        RelStructure.relabel (doubledLift τ.1) ⁻¹' D := by
      ext Y
      simp only [Set.mem_preimage, hD]
      rw [restrict_doubleEmb_relabel_doubledLift, restrict_doubleEmb_relabel_doubledLift,
        mem_cylinder, mem_cylinder]
      have hagree : K.restrict (RelStructure.relabel τ.1
          (RelStructure.restrict (doubleEmb S) (RelStructure.relabel σ Y))) =
          K.restrict (RelStructure.relabel τ.1 (RelStructure.restrict (doubleEmb S) Y)) := by
        funext c
        show Y (RelCoord.map (fun s => ⇑(σ s)) (RelCoord.map (fun s => ⇑(doubleEmb S s))
            (RelCoord.map (fun s => ⇑(τ.1 s)) c.1))) =
          Y (RelCoord.map (fun s => ⇑(doubleEmb S s)) (RelCoord.map (fun s => ⇑(τ.1 s)) c.1))
        congr 1
        refine Sigma.ext rfl (heq_of_eq (funext fun i => ?_))
        -- the vertex at position `i` of the moved, doubled coordinate is fixed by `σ`
        have hmem : (⟨S.argSort c.1.1 i, c.1.2 i⟩ : Σ s : S.Srt, Vinfinite S s) ∈ W :=
          Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨c.1, c.2,
            (RelCoord.mem_support_iff _ _).mpr ⟨i, rfl⟩⟩)
        show σ _ (poolVertexEquiv S _ (Sum.inl (τ.1 _ (c.1.2 i)))) =
          poolVertexEquiv S _ (Sum.inl (τ.1 _ (c.1.2 i)))
        rw [hτ' _ _ hmem]
        by_cases hA : (⟨S.argSort c.1.1 i, c.1.2 i⟩ : Σ s : S.Srt, Vinfinite S s) ∈ A
        · rw [if_pos hA]
          exact hfix _ (mem_doubleSupport.mpr ⟨_, hA, rfl⟩)
        · rw [if_neg hA, poolVertexEquiv_inl]
          exact hNσ _ _ (by
            have h1 : Nσ ≤ Nb := le_max_left _ _
            show Nσ ≤ 2 * (c.1.2 i + Nb)
            omega)
      rw [hagree]
    -- the estimate
    have hFD : μ (F ∆ (RelStructure.relabel (doubledLift τ.1) ⁻¹' D)) = μ (F ∆ D) := by
      rw [show F ∆ (RelStructure.relabel (doubledLift τ.1) ⁻¹' D) =
          RelStructure.relabel (doubledLift τ.1) ⁻¹' (F ∆ D) from by
        rw [Set.preimage_symmDiff, hgF]]
      exact hMPg.measure_preimage (hFmeas.symmDiff hDmeas).nullMeasurableSet
    have h1 : μ ((RelStructure.relabel σ ⁻¹' F) ∆
        (RelStructure.relabel σ ⁻¹' (RelStructure.relabel (doubledLift τ.1) ⁻¹' D))) =
        μ (F ∆ D) := by
      rw [← Set.preimage_symmDiff, hMPσ.measure_preimage
        (hFmeas.symmDiff ((measurable_relabel _) hDmeas)).nullMeasurableSet, hFD]
    have h2 : μ ((RelStructure.relabel σ ⁻¹' (RelStructure.relabel (doubledLift τ.1) ⁻¹' D)) ∆ F)
        = μ (D ∆ F) := by
      rw [hσgD, symmDiff_comm, hFD, symmDiff_comm]
    have h3 : μ (F ∆ D) = μ (E ∆ cylinder K T) := by
      rw [hF, hD, ← Set.preimage_symmDiff]
      exact hMPd.measure_preimage (hE.1.symmDiff hD₀meas).nullMeasurableSet
    calc μ ((RelStructure.relabel σ ⁻¹' F) ∆ F)
        ≤ μ ((RelStructure.relabel σ ⁻¹' F) ∆
            (RelStructure.relabel σ ⁻¹' (RelStructure.relabel (doubledLift τ.1) ⁻¹' D))) +
          μ ((RelStructure.relabel σ ⁻¹' (RelStructure.relabel (doubledLift τ.1) ⁻¹' D)) ∆ F) :=
          measure_symmDiff_le _ _ _
      _ = μ (cylinder K T ∆ E) + μ (cylinder K T ∆ E) := by
          rw [h1, h2, h3, symmDiff_comm D F, h3, symmDiff_comm]
      _ < ε := by
          rw [← ENNReal.add_halves ε]; exact ENNReal.add_lt_add hD₀lt hD₀lt
  rw [← measure_symmDiff_eq_zero_iff]
  by_contra hne
  exact absurd (key _ (pos_iff_ne_zero.mpr hne)) (lt_irrefl _)

/-! ### The countable invariant hull -/

/-- The finite-active stabilizer of a tagged vertex set, bundled. Private: it indexes the hull
and nothing else. -/
private def finiteActiveStabilizer (X : Finset (Σ s : S.Srt, Vinfinite S s)) :
    Subgroup (∀ _ : S.Srt, Equiv.Perm ℕ) where
  carrier := {σ | σ ∈ finiteActiveFinSuppSubgroup S ∧ ∀ v ∈ X, σ v.1 v.2 = v.2}
  mul_mem' := fun {σ τ} hσ hτ => ⟨(finiteActiveFinSuppSubgroup S).mul_mem hσ.1 hτ.1,
    fun v hv => by
      show σ v.1 (τ v.1 v.2) = v.2
      rw [hτ.2 v hv, hσ.2 v hv]⟩
  one_mem' := ⟨(finiteActiveFinSuppSubgroup S).one_mem, fun _ _ => rfl⟩
  inv_mem' := fun {σ} hσ => ⟨(finiteActiveFinSuppSubgroup S).inv_mem hσ.1, fun v hv => by
    show (σ v.1)⁻¹ v.2 = v.2
    conv_lhs => rw [← hσ.2 v hv]
    exact (σ v.1).symm_apply_apply v.2⟩

private instance [Countable S.Srt] (X : Finset (Σ s : S.Srt, Vinfinite S s)) :
    Countable (finiteActiveStabilizer (S := S) X) :=
  Function.Injective.countable (f := fun σ : finiteActiveStabilizer (S := S) X =>
    (⟨σ.1, σ.2.1⟩ : FiniteActiveFinSuppPerm S)) fun _ _ h =>
      Subtype.ext (by simpa using congrArg Subtype.val h)

/-- The countable invariant hull of an event over the finite-active stabilizer. -/
private def finiteActiveHull (X : Finset (Σ s : S.Srt, Vinfinite S s))
    (F : Set (RelStructure S (Vinfinite S))) : Set (RelStructure S (Vinfinite S)) :=
  ⋂ σ : finiteActiveStabilizer (S := S) X, RelStructure.relabel σ.1 ⁻¹' F

/-- **Strictification**: the countable invariant hull of a fixing event read on the doubled
sub-copy is measurable for the finite-active fixing algebra of the doubled support and a.e.
equal to the event. -/
theorem exists_finiteActiveFixingAlgebra_ae_eq_doubled [Countable S.Srt] [Countable S.Rel]
    {A : Finset (Σ s : S.Srt, Vinfinite S s)} {E : Set (RelStructure S (Vinfinite S))}
    (hE : MeasurableSet[RelStructure.fixingAlgebra A] E) :
    ∃ Ê, MeasurableSet[RelStructure.finiteActiveFixingAlgebra (doubleSupport A)] Ê ∧
      Ê =ᵐ[(M.law : Measure (RelStructure S (Vinfinite S)))]
        RelStructure.restrict (doubleEmb S) ⁻¹' E := by
  classical
  set F : Set (RelStructure S (Vinfinite S)) := RelStructure.restrict (doubleEmb S) ⁻¹' E with hF
  have hFmeas : MeasurableSet F := measurable_restrict _ hE.1
  refine ⟨finiteActiveHull (doubleSupport A) F, ⟨?_, ?_⟩, ?_⟩
  · exact MeasurableSet.iInter fun σ => measurable_relabel _ hFmeas
  · -- exact invariance: reindex the intersection by multiplication
    intro τ hτ hτ'
    have hτmem : τ ∈ finiteActiveStabilizer (S := S) (doubleSupport A) :=
      ⟨⟨hτ.1, hτ'⟩, hτ.2⟩
    have hcomp : ∀ (a b : ∀ _ : S.Srt, Equiv.Perm ℕ) (Y : RelStructure S (Vinfinite S)),
        RelStructure.relabel a (RelStructure.relabel b Y) =
          RelStructure.relabel (fun s => b s * a s) Y :=
      fun a b Y => congrFun (RelStructure.relabel_comp_relabel a b) Y
    ext Y
    simp only [finiteActiveHull, Set.mem_preimage, Set.mem_iInter]
    constructor
    · intro h σ
      have := h ⟨τ⁻¹ * σ.1, (finiteActiveStabilizer (S := S) (doubleSupport A)).mul_mem
        ((finiteActiveStabilizer (S := S) (doubleSupport A)).inv_mem hτmem) σ.2⟩
      rw [hcomp] at this
      convert this using 2
      funext s
      show σ.1 s = τ s * ((τ s)⁻¹ * σ.1 s)
      group
    · intro h σ
      have := h ⟨τ * σ.1, (finiteActiveStabilizer (S := S) (doubleSupport A)).mul_mem hτmem σ.2⟩
      rw [hcomp]
      exact this
  · -- a.e. equality: the hull sits inside the event, and misses it by a countable union of
    -- null sets
    have hinv : ∀ σ : finiteActiveStabilizer (S := S) (doubleSupport A),
        RelStructure.relabel σ.1 ⁻¹' F =ᵐ[(M.law : Measure (RelStructure S (Vinfinite S)))] F :=
      fun σ => M.relabel_preimage_ae_eq_of_fixingAlgebra_doubled hE σ.2.1 σ.2.2
    refine ae_eq_set.mpr ⟨?_, ?_⟩
    · rw [Set.sdiff_eq_empty.mpr fun Y hY => ?_, measure_empty]
      have := Set.mem_iInter.mp hY ⟨1, (finiteActiveStabilizer (S := S) (doubleSupport A)).one_mem⟩
      exact this
    · refine measure_mono_null (fun Y hY => ?_)
        (measure_iUnion_null fun σ : finiteActiveStabilizer (S := S) (doubleSupport A) =>
          (ae_eq_set.mp (hinv σ)).2)
      obtain ⟨hYF, hYnot⟩ := hY
      rw [Set.mem_iUnion]
      simp only [finiteActiveHull, Set.mem_iInter, not_forall] at hYnot
      obtain ⟨σ, hσ⟩ := hYnot
      exact ⟨σ, hYF, hσ⟩

end InfiniteRelExchangeableLaw

/-! ### The seam on the pooled carrier -/

/-- The doubled support of `A` is the pooled original image of `A`, read through the carrier
identification. -/
theorem doubleSupport_eq (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    doubleSupport A = supportImage (fun s => (poolVertexEquiv S s).toEmbedding)
      (supportImage (originalVertex S) A) := by
  classical
  refine Finset.ext fun v => ?_
  rw [mem_doubleSupport, mem_supportImage_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨⟨w.1, originalVertex S w.1 w.2⟩, (mem_supportImage_iff _ _ _).mpr ⟨w, hw, rfl⟩, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨w, hw, rfl⟩ := (mem_supportImage_iff _ _ _).mp hu
    exact ⟨w, hw, rfl⟩


namespace InfiniteRelExchangeableLaw

variable {M : InfiniteRelExchangeableLaw S} {n : ℕ} [Countable S.Srt] [Countable S.Rel]
  {C : M.RankRepresentation n}

/-- The pooled structure marginal, identified with the original carrier, is the law itself. -/
theorem PooledRankExtension.map_fst_poolStructureEquiv (Q : PooledRankExtension C) :
    ((Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)).map
        Prod.fst).map (poolStructureEquiv S) =
      (M.law : Measure (RelStructure S (Vinfinite S))) := by
  haveI := C.isProbabilityMeasure_P
  rw [Measure.map_map (poolStructureEquiv S).measurable measurable_fst, ← C.map_fst,
    ← Q.map_poolVertexEquiv, Measure.map_map measurable_fst
    ((measurable_restrict _).prodMap (measurable_latentRestrictOver _ n))]
  rfl

/-- **The pooled seam, on the pooled structure marginal**: a fixing event of the original
carrier, read through the original half, has a representative measurable for the pooled
finite-active fixing algebra of its original image, modulo the pooled structure marginal. -/
theorem PooledRankExtension.exists_pooledFiniteActiveFixingAlgebra_ae_eq
    (Q : PooledRankExtension C) {A : Finset (Σ s : S.Srt, Vinfinite S s)}
    {E : Set (RelStructure S (Vinfinite S))} (hE : MeasurableSet[RelStructure.fixingAlgebra A] E) :
    ∃ Ê, MeasurableSet[pooledFiniteActiveFixingAlgebra (supportImage (originalVertex S) A)] Ê ∧
      Ê =ᵐ[(Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)).map
        Prod.fst] restrictOriginal S ⁻¹' E := by
  haveI := C.isProbabilityMeasure_P
  obtain ⟨Ê₀, hÊ₀, hae⟩ := M.exists_finiteActiveFixingAlgebra_ae_eq_doubled hE
  rw [doubleSupport_eq] at hÊ₀
  refine ⟨poolStructureEquiv S ⁻¹' Ê₀, ⟨Ê₀, hÊ₀, rfl⟩, ?_⟩
  have hqmp : Measure.QuasiMeasurePreserving (poolStructureEquiv S)
      ((Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)).map
        Prod.fst) (M.law : Measure (RelStructure S (Vinfinite S))) :=
    ⟨(poolStructureEquiv S).measurable, Q.map_fst_poolStructureEquiv ▸
      Measure.AbsolutelyContinuous.rfl⟩
  have h := hqmp.preimage_ae_eq hae
  rwa [show poolStructureEquiv S ⁻¹' (RelStructure.restrict (doubleEmb S) ⁻¹' E) =
      restrictOriginal S ⁻¹' E from by
    rw [← Set.preimage_comp, ← restrictOriginal_comp_symm]
    ext X
    simp only [Set.mem_preimage, Function.comp_apply, MeasurableEquiv.symm_apply_apply]] at h

/-- **The pooled seam, on the joint pooled law**: the same representative, pulled back through
the structure coordinate. -/
theorem PooledRankExtension.exists_pooledFiniteActiveFixingAlgebra_ae_eq_fst
    (Q : PooledRankExtension C) {A : Finset (Σ s : S.Srt, Vinfinite S s)}
    {E : Set (RelStructure S (Vinfinite S))} (hE : MeasurableSet[RelStructure.fixingAlgebra A] E) :
    ∃ Ê, MeasurableSet[pooledFiniteActiveFixingAlgebra (supportImage (originalVertex S) A)] Ê ∧
      Prod.fst ⁻¹' Ê =ᵐ[(Q.law : Measure (RelStructure S (PoolVertex S) ×
        PooledRankLatentSpace S n))] Prod.fst ⁻¹' (restrictOriginal S ⁻¹' E) := by
  obtain ⟨Ê, hÊ, hae⟩ := Q.exists_pooledFiniteActiveFixingAlgebra_ae_eq hE
  refine ⟨Ê, hÊ, ?_⟩
  have hqmp : Measure.QuasiMeasurePreserving
      (Prod.fst : RelStructure S (PoolVertex S) × PooledRankLatentSpace S n → _)
      (Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n))
      ((Q.law : Measure (RelStructure S (PoolVertex S) × PooledRankLatentSpace S n)).map
        Prod.fst) :=
    ⟨measurable_fst, Measure.AbsolutelyContinuous.rfl⟩
  exact hqmp.preimage_ae_eq hae

end InfiniteRelExchangeableLaw

end RelSignature
