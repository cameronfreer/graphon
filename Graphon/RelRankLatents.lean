/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelRankSuccessor
import Graphon.RelLatentGeometry
import Graphon.SamplerSources
import Mathlib.Probability.Independence.InfinitePi

/-!
# Rank-indexed latent sources (R4 converse piece 3, #107)

The latent-side infrastructure for the coupled rank induction.  At rank `n` the source has one
independent uniform coordinate for every finite tagged support of cardinality strictly below `n`
(so the empty support appears exactly when `0 < n`).
This is deliberately separate from `CoherentBasis.LowerFactorSpace`: the latent space is an
`ℝ`-valued cube indexed by tagged supports, whereas the factor space is a `Bool`-valued cube
indexed by basis expressions.  A rank coding is the later map relating the two.

The nesting maps and their cocycle are definitional.  Sortwise relabelings act through genuine
index equivalences and preserve the i.i.d. source.  Rank one is identified measurably and
measure-preservingly with a single uniform.  Finally, the successor source splits into the old
latents and the fresh rank-`n` layer; this split is included here so the coherent-randomization
step does not have to rediscover the latent-side decomposition.
-/

open MeasureTheory

namespace RelSignature

variable {S : RelSignature}

/-- Finite tagged supports of cardinality strictly below `n`; this includes the empty support
when `0 < n`. -/
@[reducible] def RankLatentIndex (S : RelSignature) (n : ℕ) :=
  LatentIndexOver S (Vinfinite S) n

instance [Countable S.Srt] (n : ℕ) : Countable (RankLatentIndex S n) :=
  Subtype.countable

/-- The empty support, regarded as the unique rank-one latent index. -/
def rankLatentEmpty : RankLatentIndex S 1 := ⟨∅, by simp⟩

instance : Unique (RankLatentIndex S 1) where
  default := rankLatentEmpty
  uniq A := Subtype.ext (Finset.card_eq_zero.mp (Nat.lt_one_iff.mp A.2))

/-- The rank-`n` latent space: one real-valued coordinate per support of rank below `n`. -/
abbrev RankLatentSpace (S : RelSignature) (n : ℕ) := RankLatentIndex S n → ℝ

instance [Countable S.Srt] (n : ℕ) : StandardBorelSpace (RankLatentSpace S n) := inferInstance

/-- The rank-`n` latent source: independent `uniform01` coordinates on all supports below `n`. -/
noncomputable def rankLatentSource (S : RelSignature) (n : ℕ) : Measure (RankLatentSpace S n) :=
  iidUniformSource (RankLatentIndex S n)

instance (n : ℕ) : IsProbabilityMeasure (rankLatentSource S n) := by
  rw [rankLatentSource]
  infer_instance

/-! ### Rank nesting -/

/-- Inclusion of the supports below rank `n` among those below rank `m`. -/
def rankLatentIndexEmbedding {n m : ℕ} (h : n ≤ m) :
    RankLatentIndex S n → RankLatentIndex S m :=
  fun A ↦ ⟨A.1, A.2.trans_le h⟩

/-- Restriction of a rank-`m` latent assignment to ranks below `n`. -/
def rankLatentProjection {n m : ℕ} (h : n ≤ m) :
    RankLatentSpace S m → RankLatentSpace S n :=
  fun ω ↦ ω ∘ rankLatentIndexEmbedding h

theorem measurable_rankLatentProjection [Countable S.Srt] {n m : ℕ} (h : n ≤ m) :
    Measurable (rankLatentProjection (S := S) h) :=
  measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

/-- Rank restriction reads the same coordinates on the source. -/
theorem rankLatentProjection_apply {n m : ℕ} (h : n ≤ m)
    (ω : RankLatentSpace S m) (A : RankLatentIndex S n) :
    rankLatentProjection h ω A = ω (rankLatentIndexEmbedding h A) := rfl

/-- The rank projections form a strict cocycle. -/
theorem rankLatentProjection_comp {n m k : ℕ} (hnm : n ≤ m) (hmk : m ≤ k) :
    rankLatentProjection (S := S) hnm ∘ rankLatentProjection hmk =
      rankLatentProjection (hnm.trans hmk) := rfl

/-! ### Relabeling action -/

open scoped Classical in
/-- A finitely supported sortwise relabeling permutes the supports below each rank. -/
noncomputable def rankLatentIndexEquiv (σ : FinSuppPerm S) (n : ℕ) :
    RankLatentIndex S n ≃ RankLatentIndex S n where
  toFun A := ⟨A.1.image (Sigma.map id fun s ↦ ⇑(σ.1 s)), by
    rw [Finset.card_image_of_injective _
      (Function.injective_id.sigma_map fun s ↦ (σ.1 s).injective)]
    exact A.2⟩
  invFun A := ⟨A.1.image (Sigma.map id fun s ↦ ⇑(σ.1 s)⁻¹), by
    rw [Finset.card_image_of_injective _
      (Function.injective_id.sigma_map fun s ↦ ((σ.1 s)⁻¹).injective)]
    exact A.2⟩
  left_inv A := Subtype.ext (by
    show (A.1.image (Sigma.map id fun s ↦ ⇑(σ.1 s))).image (Sigma.map id fun s ↦ ⇑(σ.1 s)⁻¹) = A.1
    rw [Finset.image_image]
    refine (Finset.image_congr fun v _ ↦ ?_).trans A.1.image_id
    obtain ⟨s, x⟩ := v
    show (⟨s, (σ.1 s)⁻¹ ((σ.1 s) x)⟩ : Σ s : S.Srt, Vinfinite S s) = ⟨s, x⟩
    rw [show (σ.1 s)⁻¹ ((σ.1 s) x) = x from (σ.1 s).symm_apply_apply x])
  right_inv A := Subtype.ext (by
    show (A.1.image (Sigma.map id fun s ↦ ⇑(σ.1 s)⁻¹)).image (Sigma.map id fun s ↦ ⇑(σ.1 s)) = A.1
    rw [Finset.image_image]
    refine (Finset.image_congr fun v _ ↦ ?_).trans A.1.image_id
    obtain ⟨s, x⟩ := v
    show (⟨s, (σ.1 s) ((σ.1 s)⁻¹ x)⟩ : Σ s : S.Srt, Vinfinite S s) = ⟨s, x⟩
    rw [show (σ.1 s) ((σ.1 s)⁻¹ x) = x from (σ.1 s).apply_symm_apply x])

open scoped Classical in
@[simp] theorem rankLatentIndexEquiv_apply_coe (σ : FinSuppPerm S) (n : ℕ)
    (A : RankLatentIndex S n) :
    (rankLatentIndexEquiv σ n A).1 =
      A.1.image (Sigma.map id fun s ↦ ⇑(σ.1 s)) := rfl

open scoped Classical in
@[simp] theorem rankLatentIndexEquiv_one (n : ℕ) :
    rankLatentIndexEquiv (S := S) (1 : FinSuppPerm S) n = Equiv.refl _ :=
  Equiv.ext fun A ↦ Subtype.ext (by
    show A.1.image (Sigma.map id fun s ↦ ⇑((1 : FinSuppPerm S).1 s)) = A.1
    refine (Finset.image_congr fun v _ ↦ ?_).trans A.1.image_id
    obtain ⟨s, x⟩ := v
    rfl)

open scoped Classical in
@[simp] theorem rankLatentIndexEquiv_mul (σ τ : FinSuppPerm S) (n : ℕ) :
    rankLatentIndexEquiv (S := S) (σ * τ) n =
      (rankLatentIndexEquiv τ n).trans (rankLatentIndexEquiv σ n) :=
  Equiv.ext fun A ↦ Subtype.ext (by
    show A.1.image (Sigma.map id fun s ↦ ⇑((σ * τ).1 s)) =
      (A.1.image (Sigma.map id fun s ↦ ⇑(τ.1 s))).image
        (Sigma.map id fun s ↦ ⇑(σ.1 s) :
          (Σ s : S.Srt, Vinfinite S s) → Σ s : S.Srt, Vinfinite S s)
    rw [Finset.image_image]
    refine Finset.image_congr fun v _ ↦ ?_
    obtain ⟨s, x⟩ := v
    rfl)

open scoped Classical in
/-- Relabeling of a latent assignment, by coordinate reindexing. -/
noncomputable def rankLatentRelabel (σ : FinSuppPerm S) (n : ℕ) :
    RankLatentSpace S n ≃ᵐ RankLatentSpace S n where
  toEquiv := Equiv.arrowCongr (rankLatentIndexEquiv σ n).symm (Equiv.refl ℝ)
  measurable_toFun := measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _
  measurable_invFun := measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

open scoped Classical in
@[simp] theorem rankLatentRelabel_apply (σ : FinSuppPerm S) (n : ℕ)
    (ω : RankLatentSpace S n) (A : RankLatentIndex S n) :
    rankLatentRelabel σ n ω A = ω (rankLatentIndexEquiv σ n A) := rfl

open scoped Classical in
@[simp] theorem rankLatentRelabel_one (n : ℕ) :
    rankLatentRelabel (S := S) (1 : FinSuppPerm S) n = MeasurableEquiv.refl _ :=
  MeasurableEquiv.ext <| funext fun ω ↦ funext fun A ↦ by simp

open scoped Classical in
/-- **At rank one every latent relabeling is the identity.** `RankLatentIndex S 1` is the single
support `∅`, so any permutation of it is trivial — which is why the rank-one equivariance clause
says only that the *factor* equivalence fixes the coding map almost everywhere. -/
@[simp] theorem rankLatentRelabel_one_eq (σ : FinSuppPerm S) (ω : RankLatentSpace S 1) :
    rankLatentRelabel σ 1 ω = ω := by
  funext A
  rw [rankLatentRelabel_apply]
  congr 1
  exact Subsingleton.elim _ _

open scoped Classical in
@[simp] theorem rankLatentRelabel_mul (σ τ : FinSuppPerm S) (n : ℕ) :
    rankLatentRelabel (S := S) (σ * τ) n =
      (rankLatentRelabel σ n).trans (rankLatentRelabel τ n) :=
  MeasurableEquiv.ext <| funext fun ω ↦ funext fun A ↦ by simp

/-- Rank projection commutes definitionally with relabeling. -/
theorem rankLatentProjection_rankLatentRelabel (σ : FinSuppPerm S) {n m : ℕ} (h : n ≤ m) :
    rankLatentProjection h ∘ rankLatentRelabel σ m =
      rankLatentRelabel σ n ∘ rankLatentProjection h := rfl

open scoped Classical in
/-- The i.i.d. latent source is invariant under sortwise relabeling. -/
theorem rankLatentSource_map_rankLatentRelabel (σ : FinSuppPerm S) (n : ℕ) :
    (rankLatentSource S n).map (rankLatentRelabel σ n) = rankLatentSource S n := by
  rw [rankLatentSource, iidUniformSource]
  exact Measure.infinitePi_map_comp_equiv _ (rankLatentIndexEquiv σ n)

/-! ### Rank one -/

/-- Evaluation at the unique empty-support coordinate. -/
noncomputable def rankLatentOneEquiv : RankLatentSpace S 1 ≃ᵐ ℝ :=
  MeasurableEquiv.piUnique fun _ : RankLatentIndex S 1 ↦ ℝ

@[simp] theorem rankLatentOneEquiv_apply (ω : RankLatentSpace S 1) :
    rankLatentOneEquiv ω = ω rankLatentEmpty := rfl

/-- The rank-one latent source is exactly one `uniform01` random variable. -/
theorem rankLatentSource_map_rankLatentOneEquiv :
    (rankLatentSource S 1).map rankLatentOneEquiv = uniform01 := by
  rw [rankLatentSource, iidUniformSource]
  exact Measure.infinitePi_map_eval (fun _ : RankLatentIndex S 1 ↦ uniform01) rankLatentEmpty

/-! ### Successor split -/

/-- Rank below `n+1` means rank below `n` or rank exactly `n`. -/
def rankLatentIndexSuccEquiv (n : ℕ) :
    RankLatentIndex S (n + 1) ≃ RankLatentIndex S n ⊕ RankSupport S n where
  toFun A :=
    if h : A.1.card < n then Sum.inl ⟨A.1, h⟩
    else Sum.inr ⟨A.1, by have := A.2; omega⟩
  invFun := Sum.elim (fun A ↦ ⟨A.1, by have := A.2; omega⟩)
    (fun A ↦ ⟨A.1, by have := A.2; omega⟩)
  left_inv A := by
    by_cases h : A.1.card < n
    · simp only [dif_pos h, Sum.elim_inl]
      rfl
    · simp only [dif_neg h, Sum.elim_inr]
      rfl
  right_inv p := by
    rcases p with A | A
    · simp only [Sum.elim_inl, dif_pos A.2]
      rfl
    · simp only [Sum.elim_inr, dif_neg (by have := A.2; omega : ¬ A.1.card < n)]
      rfl

/-- The successor split of the latent space into old and fresh coordinates. -/
noncomputable def rankLatentSpaceSuccEquiv (n : ℕ) :
    RankLatentSpace S (n + 1) ≃ᵐ RankLatentSpace S n × (RankSupport S n → ℝ) where
  toFun ω := (fun A ↦ ω ((rankLatentIndexSuccEquiv n).symm (Sum.inl A)),
    fun A ↦ ω ((rankLatentIndexSuccEquiv n).symm (Sum.inr A)))
  invFun p A := Sum.elim p.1 p.2 (rankLatentIndexSuccEquiv n A)
  left_inv ω := by
    funext A
    show Sum.elim (fun i ↦ ω ((rankLatentIndexSuccEquiv n).symm (Sum.inl i)))
      (fun i ↦ ω ((rankLatentIndexSuccEquiv n).symm (Sum.inr i)))
        (rankLatentIndexSuccEquiv n A) = ω A
    rcases h : rankLatentIndexSuccEquiv n A with A | A
    · rw [Sum.elim_inl, ← h, Equiv.symm_apply_apply]
    · rw [Sum.elim_inr, ← h, Equiv.symm_apply_apply]
  right_inv p := by
    refine Prod.ext ?_ ?_
    · funext A
      show Sum.elim p.1 p.2
        (rankLatentIndexSuccEquiv n ((rankLatentIndexSuccEquiv n).symm (Sum.inl A))) = p.1 A
      rw [Equiv.apply_symm_apply, Sum.elim_inl]
    · funext A
      show Sum.elim p.1 p.2
        (rankLatentIndexSuccEquiv n ((rankLatentIndexSuccEquiv n).symm (Sum.inr A))) = p.2 A
      rw [Equiv.apply_symm_apply, Sum.elim_inr]
  measurable_toFun := by
    refine Measurable.prod ?_ ?_ <;> exact measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _
  measurable_invFun := by
    refine measurable_pi_lambda _ fun A ↦ ?_
    show Measurable fun p : RankLatentSpace S n × (RankSupport S n → ℝ) ↦
      Sum.elim p.1 p.2 (rankLatentIndexSuccEquiv n A)
    rcases h : rankLatentIndexSuccEquiv n A with A | A
    · exact measurable_fst.eval
    · exact measurable_snd.eval

/-- The first component of the successor split is the existing rank projection. -/
theorem fst_rankLatentSpaceSuccEquiv (n : ℕ) (ω : RankLatentSpace S (n + 1)) :
    (rankLatentSpaceSuccEquiv n ω).1 = rankLatentProjection (Nat.le_succ n) ω := rfl

/-- The successor split also splits the source: the old lower-rank latents and the fresh
rank-`n` latents are independent i.i.d. uniform families. -/
theorem rankLatentSource_map_rankLatentSpaceSuccEquiv (n : ℕ) :
    (rankLatentSource S (n + 1)).map (rankLatentSpaceSuccEquiv n) =
      (rankLatentSource S n).prod (iidUniformSource (RankSupport S n)) := by
  have hpre : Measurable fun (ω : RankLatentSpace S (n + 1))
      (i : RankLatentIndex S n ⊕ RankSupport S n) ↦
        ω ((rankLatentIndexSuccEquiv n).symm i) :=
    measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _
  rw [rankLatentSource, iidUniformSource,
    show ⇑(rankLatentSpaceSuccEquiv (S := S) n) =
      ⇑(MeasurableEquiv.sumPiEquivProdPi
        fun _ : RankLatentIndex S n ⊕ RankSupport S n ↦ ℝ) ∘
        (fun (ω : RankLatentSpace S (n + 1))
          (i : RankLatentIndex S n ⊕ RankSupport S n) ↦
            ω ((rankLatentIndexSuccEquiv n).symm i)) from rfl,
    ← Measure.map_map
      (MeasurableEquiv.sumPiEquivProdPi
        fun _ : RankLatentIndex S n ⊕ RankSupport S n ↦ ℝ).measurable hpre,
    Measure.infinitePi_map_comp_equiv _ (rankLatentIndexSuccEquiv n).symm,
    Measure.infinitePi_map_sumPiEquivProdPi]
  rfl

open scoped Classical in
/-- Relabeling of the fresh rank-`n` latent layer, again by coordinate reindexing. -/
noncomputable def rankSupportLatentRelabel (σ : FinSuppPerm S) (n : ℕ) :
    (RankSupport S n → ℝ) ≃ᵐ (RankSupport S n → ℝ) where
  toEquiv := Equiv.arrowCongr (rankSupportEquiv σ n).symm (Equiv.refl ℝ)
  measurable_toFun := measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _
  measurable_invFun := measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

open scoped Classical in
@[simp] theorem rankSupportLatentRelabel_apply (σ : FinSuppPerm S) (n : ℕ)
    (ω : RankSupport S n → ℝ) (A : RankSupport S n) :
    rankSupportLatentRelabel σ n ω A = ω (rankSupportEquiv σ n A) := rfl

open scoped Classical in
@[simp] theorem rankSupportLatentRelabel_one (n : ℕ) :
    rankSupportLatentRelabel (S := S) (1 : FinSuppPerm S) n = MeasurableEquiv.refl _ :=
  MeasurableEquiv.ext <| funext fun ω ↦ funext fun A ↦ by simp

open scoped Classical in
@[simp] theorem rankSupportLatentRelabel_mul (σ τ : FinSuppPerm S) (n : ℕ) :
    rankSupportLatentRelabel (S := S) (σ * τ) n =
      (rankSupportLatentRelabel σ n).trans (rankSupportLatentRelabel τ n) :=
  MeasurableEquiv.ext <| funext fun ω ↦ funext fun A ↦ by simp

open scoped Classical in
/-- The successor index split is natural under relabeling. -/
theorem rankLatentIndexSuccEquiv_rankLatentIndexEquiv (σ : FinSuppPerm S) (n : ℕ) :
    rankLatentIndexSuccEquiv n ∘ rankLatentIndexEquiv σ (n + 1) =
      Sum.map (rankLatentIndexEquiv σ n) (rankSupportEquiv σ n) ∘
        rankLatentIndexSuccEquiv n := by
  funext A
  have hcard : (rankLatentIndexEquiv σ (n + 1) A).1.card = A.1.card := by
    rw [rankLatentIndexEquiv_apply_coe, Finset.card_image_of_injective _
      (Function.injective_id.sigma_map fun s ↦ (σ.1 s).injective)]
  by_cases h : A.1.card < n
  · show (if _ : (rankLatentIndexEquiv σ (n + 1) A).1.card < n then _ else _) = _
    rw [dif_pos (hcard ▸ h)]
    show Sum.inl _ = Sum.map _ _ (if _ : A.1.card < n then _ else _)
    rw [dif_pos h]
    rfl
  · show (if _ : (rankLatentIndexEquiv σ (n + 1) A).1.card < n then _ else _) = _
    rw [dif_neg (hcard ▸ h)]
    show Sum.inr _ = Sum.map _ _ (if _ : A.1.card < n then _ else _)
    rw [dif_neg h]
    rfl

/-- The successor latent split is equivariant.  As on the factor side, the space-level square is
definitional even though the forward index split branches on a cardinality test. -/
theorem rankLatentSpaceSuccEquiv_rankLatentRelabel (σ : FinSuppPerm S) (n : ℕ) :
    rankLatentSpaceSuccEquiv n ∘ rankLatentRelabel σ (n + 1) =
      MeasurableEquiv.prodCongr (rankLatentRelabel σ n) (rankSupportLatentRelabel σ n) ∘
        rankLatentSpaceSuccEquiv n := rfl

/-! ### Bridge to the carrier-parametric core

The rank-indexed operations were built before the carrier-parametric core and choose their own
`Decidable` instances; they agree with the generic ones extensionally but not by `rfl`. -/

theorem rankLatentIndexEquiv_eq_latentIndexPerm (σ : FinSuppPerm S) (n : ℕ)
    (A : RankLatentIndex S n) :
    rankLatentIndexEquiv σ n A = latentIndexPerm (fun s => σ.1 s) n A := by
  classical
  refine Subtype.ext (Finset.ext fun v => ?_)
  rw [rankLatentIndexEquiv_apply_coe, latentIndexPerm_apply_coe]
  simp [Finset.mem_image]

/-- **Bridge**: the rank-indexed relabeling is the carrier-parametric action at `Vinfinite S`. -/
theorem rankLatentRelabel_eq_latentRelabelOver (σ : FinSuppPerm S) (n : ℕ) :
    rankLatentRelabel σ n = latentRelabelOver (fun s => σ.1 s) n := by
  refine MeasurableEquiv.ext (funext fun ω => funext fun A => ?_)
  show ω (rankLatentIndexEquiv σ n A) = ω (latentIndexPerm _ n A)
  rw [rankLatentIndexEquiv_eq_latentIndexPerm]


end RelSignature
