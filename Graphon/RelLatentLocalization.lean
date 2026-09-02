/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelRankLatents
import Graphon.RelObservationGeometry
import Graphon.RelFixingAlgebra
import Graphon.ForMathlib.CondIndepSup
import Graphon.ForMathlib.CondExpComap
import Mathlib.Probability.ConditionalExpectation

/-!
# Localizing latent events at a support (R4 converse, #107)

Source-level machinery for the fixing-completeness API: an event of the latent cube that is
almost surely invariant under the permutations fixing `A` has a representative reading only the
latent coordinates **visible at `A`**. This is a relative Hewitt–Savage theorem for the rank-`n`
latent source, proved once here so that every representation witness can discharge its local
completeness obligation from a whole-array one.

The layer is deliberately **route-neutral**. Nothing here mentions a `RankRepresentation`, an
exchangeable law, or a coherent basis, and the module sits strictly below the representation
contract so that the contract can consume it. In particular:

* invariance is accepted **almost everywhere**, not strictly. Strictifying it through an invariant
  hull would need countability of the relabeling group, hence `[Fintype S.Srt]`, which this layer
  does not have and should not acquire;
* there is no `A.card < n` hypothesis — that restriction belongs to the representation theorem
  built on top, not to the statement about the source;
* the only ambient hypothesis is `[Countable S.Srt]`, which makes the latent cube standard Borel
  so that Mathlib's conditional independence applies.

## Contents

* `LocalLatentIndex` / `LocalLatentSpace` / `localLatents` — the coordinates visible at `A` and
  the restriction of the latent array to them (the `Vinfinite`-indexed instance of
  `localLatentsOver`);
* `latentCylinders` — the coordinate cylinders of the latent cube, the generating ring used for
  approximation in measure;
* `exists_finSuppPerm_displacing` — **finite displacement**: any finite family of latent indices
  can be pushed off itself, in its nonlocal part, by one finitely supported sortwise permutation
  fixing `A` pointwise;
* `rankLatentIndexEquiv_eq_self_of_subset` / `localLatents_comp_rankLatentRelabel` — **the
  exact action lemma**: a permutation fixing `A` fixes every local index, so the local window is
  literally unchanged by relabeling;
* `comap_localLatents_eq_cylinderEvents` — the local window generates exactly the cylinder
  events on the local indices;
* `rankLatentSource_exists_local_ae_eq_of_ae_invariant` — **the localization theorem**.

## The argument

Write `L` for the local window, `μ` for the source and `h = μ⟦D | L⟧`. Approximate `D` in measure
by a coordinate cylinder `C` on a finite index set `F`, and displace the nonlocal part of `F` off
`F` by a permutation `σ` fixing `A`. The source is `σ`-invariant, `D` is almost surely
`σ`-invariant, and `σ` acts trivially on `L`, so `C ∩ σ⁻¹C` is within twice the approximation
error of `D` while, conditionally on `L`, the two cylinders read disjoint nonlocal coordinates and
are independent: the mass of `C ∩ σ⁻¹C` is the energy `∫ g²` of `g = μ⟦C | L⟧`. The
`L¹`-contraction of conditional expectation controls `g − h` by the approximation error, so the
mass of `D` equals `∫ h²`. Together with `∫ h = μ D` and the orthogonality `∫ 1_D h = ∫ h²`, this
forces `1_D = h` almost surely, and `{h > 1/2}` is the local representative.

Only the finite union of the tagged supports of `A` and of the cylinder's index set is active in
the displacement step, so every sort outside that union takes the identity and no finiteness
hypothesis on the sort type is introduced — the same active-sort discipline as the finite-support
agreement lemma it is built from.
-/

open MeasureTheory ProbabilityTheory
open scoped symmDiff

namespace RelSignature

universe u

variable {S : RelSignature.{u}} {n : ℕ}

/-! ### Local latents -/

/-- The latent coordinates visible at `A`: supports contained in `A`. Within `RankLatentIndex n`
this automatically means *proper* subsets when `A.card = n`. -/
@[reducible] def LocalLatentIndex (A : Finset (Σ s : S.Srt, Vinfinite S s)) (n : ℕ) :=
  LocalLatentIndexOver (Vinfinite S) A n

instance [Countable S.Srt] (A : Finset (Σ s : S.Srt, Vinfinite S s)) (n : ℕ) :
    Countable (LocalLatentIndex A n) := Subtype.countable

/-- The local latent space at `A`. -/
abbrev LocalLatentSpace (A : Finset (Σ s : S.Srt, Vinfinite S s)) (n : ℕ) :=
  LocalLatentIndex A n → ℝ

/-- Restriction of the latent array to the coordinates visible at `A`. -/
def localLatents (A : Finset (Σ s : S.Srt, Vinfinite S s)) (n : ℕ) :
    RankLatentSpace S n → LocalLatentSpace A n := localLatentsOver A n

theorem measurable_localLatents [Countable S.Srt]
    (A : Finset (Σ s : S.Srt, Vinfinite S s)) (n : ℕ) :
    Measurable (localLatents A n) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

/-! ### Latent cylinders -/

variable (S) in
/-- The coordinate cylinders of the latent cube: finitely many latent indices constrained. -/
abbrev latentCylinders (n : ℕ) : Set (Set (RankLatentSpace S n)) :=
  measurableCylinders fun _ : RankLatentIndex S n => ℝ

theorem isCountablySpanning_latentCylinders (n : ℕ) :
    IsCountablySpanning (latentCylinders S n) :=
  ⟨fun _ => Set.univ, fun _ => univ_mem_measurableCylinders _, Set.iUnion_const _⟩

/-! ### Finite displacement -/

/-- **Finite displacement.** Any finite family of latent indices can be moved off itself, in its
nonlocal part, by a single finitely supported sortwise permutation fixing `A` pointwise.

Only the finite union of the tagged supports of `A` and of the family is active, so every sort
outside that union takes the identity and no finiteness hypothesis on the sort type is needed. -/
theorem exists_finSuppPerm_displacing (A : Finset (Σ s : S.Srt, Vinfinite S s))
    (F : Finset (RankLatentIndex S n)) :
    ∃ σ : FinSuppPerm S, SortwiseFixing A σ.1 ∧
      ∀ B ∈ F, ¬ (B.1 ⊆ A) → rankLatentIndexEquiv σ n B ∉ F := by
  classical
  -- the active tagged vertices, and a bound strictly above all of them
  set V : Finset (Σ s : S.Srt, Vinfinite S s) := A ∪ F.biUnion (fun B => B.1) with hV
  set Nb : ℕ := (V.sup fun v => v.2) + 1 with hNb
  have hlt : ∀ v ∈ V, v.2 < Nb := fun v hv =>
    Nat.lt_succ_of_le (Finset.le_sup (f := fun w : Σ s : S.Srt, Vinfinite S s => w.2) hv)
  have hAV : A ⊆ V := Finset.subset_union_left
  -- shift every active non-`A` vertex above the bound, fixing `A`
  have hinj : ∀ s : S.Srt, Function.Injective
      (fun v : ℕ => if (⟨s, v⟩ : Σ s : S.Srt, Vinfinite S s) ∈ A then v else v + Nb) := by
    intro s a b hab
    simp only at hab
    by_cases ha : (⟨s, a⟩ : Σ s : S.Srt, Vinfinite S s) ∈ A <;>
      by_cases hb : (⟨s, b⟩ : Σ s : S.Srt, Vinfinite S s) ∈ A
    · rw [if_pos ha, if_pos hb] at hab
      exact hab
    · rw [if_pos ha, if_neg hb] at hab
      have h1 : (a : ℕ) < Nb := hlt ⟨s, a⟩ (hAV ha)
      omega
    · rw [if_neg ha, if_pos hb] at hab
      have h1 : (b : ℕ) < Nb := hlt ⟨s, b⟩ (hAV hb)
      omega
    · rw [if_neg ha, if_neg hb] at hab
      omega
  obtain ⟨σ, hσ⟩ := exists_finSuppPerm_agree_on_finset
    (fun s => ⟨_, hinj s⟩ : ∀ s, Vinfinite S s ↪ Vinfinite S s) V
  have hσV : ∀ v ∈ V, σ.1 v.1 v.2 =
      if (⟨v.1, v.2⟩ : Σ s : S.Srt, Vinfinite S s) ∈ A then v.2 else v.2 + Nb :=
    fun v hv => hσ v hv
  refine ⟨σ, ⟨σ.2, fun v hv => ?_⟩, fun B hB hBA hmem => ?_⟩
  · rw [hσV v (hAV hv), if_pos (by simpa using hv)]
  · -- a vertex of `B` outside `A` is pushed above the bound, so the image leaves `V`
    obtain ⟨w, hwB, hwA⟩ := Finset.not_subset.mp hBA
    have hwV : w ∈ V := Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨B, hB, hwB⟩)
    have himg : (Sigma.map id (fun s => ⇑(σ.1 s)) w : Σ s : S.Srt, Vinfinite S s)
        ∈ (rankLatentIndexEquiv σ n B).1 := Finset.mem_image_of_mem _ hwB
    have hmemV : (Sigma.map id (fun s => ⇑(σ.1 s)) w : Σ s : S.Srt, Vinfinite S s) ∈ V :=
      Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨rankLatentIndexEquiv σ n B, hmem, himg⟩)
    have hval : (Sigma.map id (fun s => ⇑(σ.1 s)) w).2 = w.2 + Nb := by
      show σ.1 w.1 w.2 = w.2 + Nb
      rw [hσV w hwV, if_neg (by simpa using hwA)]
    have hbound := hlt _ hmemV
    rw [hval] at hbound
    exact absurd hbound (Nat.not_lt.mpr (Nat.le_add_left Nb w.2))

/-! ### The exact action on local indices -/

/-- A permutation fixing `A` pointwise fixes every latent index supported inside `A`. -/
theorem rankLatentIndexEquiv_eq_self_of_subset {A : Finset (Σ s : S.Srt, Vinfinite S s)}
    {σ : FinSuppPerm S} (hσ : SortwiseFixing A σ.1) {B : RankLatentIndex S n} (hB : B.1 ⊆ A) :
    rankLatentIndexEquiv σ n B = B := by
  classical
  apply Subtype.ext
  rw [rankLatentIndexEquiv_apply_coe]
  ext v
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨⟨s, x⟩, hv, rfl⟩
    have h := hσ.2 ⟨s, x⟩ (hB hv)
    show (⟨s, σ.1 s x⟩ : Σ s : S.Srt, Vinfinite S s) ∈ B.1
    rw [h]
    exact hv
  · intro hv
    obtain ⟨s, x⟩ := v
    refine ⟨⟨s, x⟩, hv, ?_⟩
    show (⟨s, σ.1 s x⟩ : Σ s : S.Srt, Vinfinite S s) = ⟨s, x⟩
    rw [hσ.2 ⟨s, x⟩ (hB hv)]

/-- Locality of an index is preserved by a permutation fixing `A`. -/
theorem rankLatentIndexEquiv_subset_iff {A : Finset (Σ s : S.Srt, Vinfinite S s)}
    {σ : FinSuppPerm S} (hσ : SortwiseFixing A σ.1) (B : RankLatentIndex S n) :
    (rankLatentIndexEquiv σ n B).1 ⊆ A ↔ B.1 ⊆ A := by
  refine ⟨fun h => ?_, fun h => by rw [rankLatentIndexEquiv_eq_self_of_subset hσ h]; exact h⟩
  have hinv : SortwiseFixing A (σ⁻¹).1 := hσ.inv
  have := rankLatentIndexEquiv_eq_self_of_subset (n := n) hinv h
  rw [← Equiv.trans_apply, ← rankLatentIndexEquiv_mul, inv_mul_cancel, rankLatentIndexEquiv_one,
    Equiv.refl_apply] at this
  exact this ▸ h

/-- **The exact action lemma**: the local window at `A` is unchanged by relabeling along a
permutation fixing `A`. -/
theorem localLatents_comp_rankLatentRelabel {A : Finset (Σ s : S.Srt, Vinfinite S s)}
    {σ : FinSuppPerm S} (hσ : SortwiseFixing A σ.1) :
    localLatents A n ∘ rankLatentRelabel σ n = localLatents A n := by
  funext ω B
  show ω (rankLatentIndexEquiv σ n B.1) = ω B.1
  rw [rankLatentIndexEquiv_eq_self_of_subset hσ B.2]

/-! ### Generic helpers

Private at their single consumer; extraction to `ForMathlib` awaits a second independent one. -/

private theorem comp_eq_self_of_measurable_comap {Ω β γ : Type*} [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSingletonClass γ] {L : Ω → β} {T : Ω → Ω}
    (hLT : L ∘ T = L) {g : Ω → γ}
    (hg : Measurable[MeasurableSpace.comap L inferInstance] g) : g ∘ T = g := by
  funext ω
  obtain ⟨V, -, hV⟩ := hg (measurableSet_singleton (g ω))
  have hω : ω ∈ g ⁻¹' {g ω} := rfl
  rw [← hV] at hω
  have hTω : T ω ∈ L ⁻¹' V := by
    show L (T ω) ∈ V
    rw [show L (T ω) = L ω from congrFun hLT ω]
    exact hω
  rw [hV] at hTω
  exact hTω

private theorem abs_measureReal_sub_le_symmDiff {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] (s t : Set α) :
    |μ.real s - μ.real t| ≤ μ.real (s ∆ t) := by
  have h1 : μ.real s ≤ μ.real t + μ.real (s ∆ t) :=
    (measureReal_mono (show s ⊆ t ∪ s ∆ t from fun x hx => by
      by_cases hxt : x ∈ t
      · exact Or.inl hxt
      · exact Or.inr (Set.mem_symmDiff.mpr (Or.inl ⟨hx, hxt⟩)))).trans
      (measureReal_union_le _ _)
  have h2 : μ.real t ≤ μ.real s + μ.real (s ∆ t) :=
    (measureReal_mono (show t ⊆ s ∪ s ∆ t from fun x hx => by
      by_cases hxs : x ∈ s
      · exact Or.inl hxs
      · exact Or.inr (Set.mem_symmDiff.mpr (Or.inr ⟨hx, hxs⟩)))).trans
      (measureReal_union_le _ _)
  rw [abs_sub_le_iff]
  constructor <;> linarith

private theorem condIndep_of_indep {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {m' m₁ m₂ : MeasurableSpace Ω}
    (hm' : m' ≤ mΩ) (hm₁ : m₁ ≤ mΩ) (hm₂ : m₂ ≤ mΩ)
    (h12 : Indep m₁ m₂ μ) (h : Indep m' (m₁ ⊔ m₂) μ) : CondIndep m' m₁ m₂ hm' μ := by
  rw [condIndep_iff _ _ _ _ hm₁ hm₂]
  intro t₁ t₂ ht₁ ht₂
  have hsup : m₁ ⊔ m₂ ≤ mΩ := sup_le hm₁ hm₂
  have hconst : ∀ t, MeasurableSet[m₁ ⊔ m₂] t →
      (μ⟦t | m'⟧) =ᵐ[μ] fun _ => μ.real t := by
    intro t ht
    have := condExp_indep_eq hsup hm' (f := t.indicator fun _ => (1 : ℝ))
      ((@stronglyMeasurable_const _ _ (m₁ ⊔ m₂) _ (1 : ℝ)).indicator ht) h.symm
    refine this.trans (Filter.Eventually.of_forall fun _ => ?_)
    exact integral_indicator_one (hsup t ht)
  have hmul : μ.real (t₁ ∩ t₂) = μ.real t₁ * μ.real t₂ := by
    rw [measureReal_def, measureReal_def, measureReal_def,
      (indep_iff_forall_indepSet μ).mp h12 t₁ t₂ ht₁ ht₂ |>.measure_inter_eq_mul,
      ENNReal.toReal_mul]
  have e1 := hconst t₁ (le_sup_left (a := m₁) (b := m₂) t₁ ht₁)
  have e2 := hconst t₂ (le_sup_right (a := m₁) (b := m₂) t₂ ht₂)
  have e12 := hconst (t₁ ∩ t₂) ((le_sup_left (a := m₁) (b := m₂) t₁ ht₁).inter
    (le_sup_right (a := m₁) (b := m₂) t₂ ht₂))
  filter_upwards [e1, e2, e12] with ω h1 h2 h12'
  simp only [Pi.mul_apply, h1, h2, h12', hmul]

private theorem condExp_indicator_bounds {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {s : Set Ω} (hs : MeasurableSet[mΩ] s) :
    0 ≤ᵐ[μ] (μ⟦s | m⟧) ∧ (μ⟦s | m⟧) ≤ᵐ[μ] fun _ => (1 : ℝ) := by
  refine ⟨condExp_nonneg (μ := μ) (m := m) (f := s.indicator fun _ => (1 : ℝ))
    (Filter.Eventually.of_forall fun ω => Set.indicator_nonneg (fun _ _ => zero_le_one) ω), ?_⟩
  refine (condExp_mono (μ := μ) (m := m) ((integrable_const (1 : ℝ)).indicator hs)
    (integrable_const (1 : ℝ)) (Filter.Eventually.of_forall fun ω =>
      Set.indicator_le_self' (fun _ _ => zero_le_one) ω)).trans ?_
  exact Filter.Eventually.of_forall fun ω => (congrFun (condExp_const (μ := μ) hm (1 : ℝ)) ω).le

/-! ### The displaced-cylinder identity -/

/-- The local window generates exactly the cylinder events on the local indices. -/
theorem comap_localLatents_eq_cylinderEvents [Countable S.Srt]
    (A : Finset (Σ s : S.Srt, Vinfinite S s)) :
    MeasurableSpace.comap (localLatents (S := S) A n) inferInstance =
      cylinderEvents (X := fun _ : RankLatentIndex S n => ℝ) {B | B.1 ⊆ A} := by
  apply le_antisymm
  · exact measurable_iff_comap_le.mp
      (measurable_restrict_cylinderEvents (X := fun _ : RankLatentIndex S n => ℝ) {B | B.1 ⊆ A})
  · refine iSup₂_le fun B hB => ?_
    exact measurable_iff_comap_le.mp
      ((measurable_pi_apply (⟨B, hB⟩ : LocalLatentIndex A n)).comp
        (comap_measurable (m := MeasurableSpace.pi) (localLatents (S := S) A n)))

/-- **The displaced-cylinder identity.** For a coordinate cylinder `C` and a permutation fixing
`A` that displaces the nonlocal coordinates of `C` off themselves, the mass of `C ∩ σ⁻¹C` is the
energy of the local conditional probability of `C`. -/
private theorem measureReal_inter_preimage_cylinder [Countable S.Srt]
    (A : Finset (Σ s : S.Srt, Vinfinite S s)) {F : Finset (RankLatentIndex S n)}
    {T : Set (∀ _ : F, ℝ)} (hT : MeasurableSet T)
    {σ : FinSuppPerm S} (hσ : SortwiseFixing A σ.1)
    (hdisp : ∀ B ∈ F, ¬ (B.1 ⊆ A) → rankLatentIndexEquiv σ n B ∉ F) :
    (rankLatentSource S n).real (cylinder (α := fun _ : RankLatentIndex S n => ℝ) F T ∩ rankLatentRelabel σ n ⁻¹' cylinder (α := fun _ : RankLatentIndex S n => ℝ) F T) =
      ∫ ω, (((rankLatentSource S n)⟦cylinder (α := fun _ : RankLatentIndex S n => ℝ) F T |
          MeasurableSpace.comap (localLatents A n) inferInstance⟧) ω) *
        (((rankLatentSource S n)⟦cylinder (α := fun _ : RankLatentIndex S n => ℝ) F T |
          MeasurableSpace.comap (localLatents A n) inferInstance⟧) ω) ∂(rankLatentSource S n) := by
  classical
  set μ := rankLatentSource S n with hμ
  have hmL_le : MeasurableSpace.comap (localLatents (S := S) A n) inferInstance ≤
      MeasurableSpace.pi := (measurable_localLatents A n).comap_le
  have hCmeas : MeasurableSet (cylinder (α := fun _ : RankLatentIndex S n => ℝ) F T) := hT.cylinder
  have hTrmp : MeasurePreserving (rankLatentRelabel σ n) μ μ :=
    ⟨(rankLatentRelabel σ n).measurable, rankLatentSource_map_rankLatentRelabel σ n⟩
  -- the three coordinate families
  set Loc : Set (RankLatentIndex S n) := {B | B.1 ⊆ A} with hLoc
  set N₁ : Set (RankLatentIndex S n) := {B | B ∈ F ∧ ¬ (B.1 ⊆ A)} with hN₁
  set N₂ : Set (RankLatentIndex S n) := rankLatentIndexEquiv σ n '' N₁ with hN₂
  have hLN₁ : Disjoint Loc N₁ := Set.disjoint_left.mpr fun B hB hB' => hB'.2 hB
  have hLN₂ : Disjoint Loc N₂ := Set.disjoint_left.mpr fun B hB hB' => by
    obtain ⟨B', hB', rfl⟩ := hB'
    exact hB'.2 ((rankLatentIndexEquiv_subset_iff hσ B').mp hB)
  have hN₁N₂ : Disjoint N₁ N₂ := Set.disjoint_left.mpr fun B hB hB' => by
    obtain ⟨B', hB', rfl⟩ := hB'
    exact hdisp B' hB'.1 hB'.2 hB.1
  -- independence of the coordinate families
  have hind : iIndep (fun B : RankLatentIndex S n =>
      MeasurableSpace.comap (fun ω : RankLatentSpace S n => ω B) inferInstance) μ := by
    rw [← iIndepFun_iff_iIndep]
    exact iIndepFun_infinitePi (P := fun _ : RankLatentIndex S n => uniform01)
      (X := fun _ x => x) fun _ => measurable_id
  have hle : ∀ B : RankLatentIndex S n,
      MeasurableSpace.comap (fun ω : RankLatentSpace S n => ω B) inferInstance ≤
        MeasurableSpace.pi := fun B => (measurable_pi_apply B).comap_le
  have hI1 : Indep (cylinderEvents (X := fun _ : RankLatentIndex S n => ℝ) Loc)
      (cylinderEvents (X := fun _ : RankLatentIndex S n => ℝ) N₁ ⊔
        cylinderEvents (X := fun _ : RankLatentIndex S n => ℝ) N₂) μ := by
    have := indep_iSup_of_disjoint hle hind (S := Loc) (T := N₁ ∪ N₂)
      (Set.disjoint_union_right.mpr ⟨hLN₁, hLN₂⟩)
    simpa only [cylinderEvents, iSup_union] using this
  have hI2 : Indep (cylinderEvents (X := fun _ : RankLatentIndex S n => ℝ) N₁)
      (cylinderEvents (X := fun _ : RankLatentIndex S n => ℝ) N₂) μ :=
    indep_iSup_of_disjoint hle hind hN₁N₂
  -- conditional independence given the local window
  have hCI : CondIndep (MeasurableSpace.comap (localLatents (S := S) A n) inferInstance)
      (MeasurableSpace.comap (localLatents (S := S) A n) inferInstance ⊔
        cylinderEvents (X := fun _ : RankLatentIndex S n => ℝ) N₁)
      (MeasurableSpace.comap (localLatents (S := S) A n) inferInstance ⊔
        cylinderEvents (X := fun _ : RankLatentIndex S n => ℝ) N₂) hmL_le μ := by
    have h0 := condIndep_of_indep hmL_le cylinderEvents_le_pi cylinderEvents_le_pi hI2
      (by rw [comap_localLatents_eq_cylinderEvents]; exact hI1)
    have h1 := h0.sup_right cylinderEvents_le_pi cylinderEvents_le_pi
    exact (h1.symm.sup_right (sup_le hmL_le cylinderEvents_le_pi) cylinderEvents_le_pi).symm
  -- the two cylinders are measurable for the respective joins
  have hrestr : ∀ (φ : RankLatentIndex S n → RankLatentIndex S n)
      (m : MeasurableSpace (RankLatentSpace S n)),
      (∀ i : F, MeasurableSpace.comap (fun ω : RankLatentSpace S n => ω (φ i.1)) inferInstance ≤ m) →
      MeasurableSet[m] ((fun (ω : RankLatentSpace S n) (i : F) => ω (φ i.1)) ⁻¹' T) := by
    intro φ m hφ
    refine measurable_iff_comap_le.mpr ?_ hT
    rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
    refine iSup_le fun i => ?_
    rw [MeasurableSpace.comap_comp]
    exact hφ i
  have hlocal : ∀ B : RankLatentIndex S n, B.1 ⊆ A →
      MeasurableSpace.comap (fun ω : RankLatentSpace S n => ω B) inferInstance ≤
        MeasurableSpace.comap (localLatents (S := S) A n) inferInstance := by
    intro B hB
    rw [comap_localLatents_eq_cylinderEvents]
    exact le_iSup₂ (f := fun (B : RankLatentIndex S n) (_ : B ∈ Loc) =>
      MeasurableSpace.comap (fun ω : RankLatentSpace S n => ω B) inferInstance) B hB
  have hC1 : MeasurableSet[MeasurableSpace.comap (localLatents (S := S) A n) inferInstance ⊔
      cylinderEvents (X := fun _ : RankLatentIndex S n => ℝ) N₁]
      (cylinder (α := fun _ : RankLatentIndex S n => ℝ) F T) := by
    refine hrestr id _ fun i => ?_
    by_cases hi : i.1.1 ⊆ A
    · exact le_sup_of_le_left (hlocal i.1 hi)
    · exact le_sup_of_le_right (le_iSup₂ (f := fun (B : RankLatentIndex S n) (_ : B ∈ N₁) =>
        MeasurableSpace.comap (fun ω : RankLatentSpace S n => ω B) inferInstance) i.1 ⟨i.2, hi⟩)
  have hC2 : MeasurableSet[MeasurableSpace.comap (localLatents (S := S) A n) inferInstance ⊔
      cylinderEvents (X := fun _ : RankLatentIndex S n => ℝ) N₂]
      (rankLatentRelabel σ n ⁻¹' cylinder (α := fun _ : RankLatentIndex S n => ℝ) F T) := by
    refine hrestr (rankLatentIndexEquiv σ n) _ fun i => ?_
    by_cases hi : i.1.1 ⊆ A
    · rw [rankLatentIndexEquiv_eq_self_of_subset hσ hi]
      exact le_sup_of_le_left (hlocal i.1 hi)
    · exact le_sup_of_le_right (le_iSup₂ (f := fun (B : RankLatentIndex S n) (_ : B ∈ N₂) =>
        MeasurableSpace.comap (fun ω : RankLatentSpace S n => ω B) inferInstance)
        (rankLatentIndexEquiv σ n i.1) ⟨i.1, ⟨i.2, hi⟩, rfl⟩)
  have hprod := (condIndep_iff _ _ _ _ (sup_le hmL_le cylinderEvents_le_pi)
    (sup_le hmL_le cylinderEvents_le_pi) μ).mp hCI _ _ hC1 hC2
  -- the shifted cylinder has the same local conditional probability
  have hshift : (μ⟦rankLatentRelabel σ n ⁻¹' cylinder (α := fun _ : RankLatentIndex S n => ℝ) F T |
      MeasurableSpace.comap (localLatents (S := S) A n) inferInstance⟧) =ᵐ[μ]
      μ⟦cylinder (α := fun _ : RankLatentIndex S n => ℝ) F T |
        MeasurableSpace.comap (localLatents (S := S) A n) inferInstance⟧ := by
    have h1 := condExp_set_comp_measurePreserving hTrmp hmL_le hCmeas
    rw [MeasurableSpace.comap_comp, localLatents_comp_rankLatentRelabel hσ,
      comp_eq_self_of_measurable_comap (localLatents_comp_rankLatentRelabel hσ)
        stronglyMeasurable_condExp.measurable] at h1
    exact h1
  calc μ.real (cylinder (α := fun _ : RankLatentIndex S n => ℝ) F T ∩
        rankLatentRelabel σ n ⁻¹' cylinder (α := fun _ : RankLatentIndex S n => ℝ) F T)
      = ∫ ω, (cylinder (α := fun _ : RankLatentIndex S n => ℝ) F T ∩
          rankLatentRelabel σ n ⁻¹' cylinder (α := fun _ : RankLatentIndex S n => ℝ) F T).indicator
            (fun _ => (1 : ℝ)) ω ∂μ :=
        (integral_indicator_one (hCmeas.inter ((rankLatentRelabel σ n).measurable hCmeas))).symm
    _ = ∫ ω, (μ⟦cylinder (α := fun _ : RankLatentIndex S n => ℝ) F T ∩
          rankLatentRelabel σ n ⁻¹' cylinder (α := fun _ : RankLatentIndex S n => ℝ) F T |
          MeasurableSpace.comap (localLatents (S := S) A n) inferInstance⟧) ω ∂μ :=
        (integral_condExp hmL_le).symm
    _ = _ := by
        refine integral_congr_ae (hprod.trans ?_)
        filter_upwards [hshift] with ω h
        simp only [Pi.mul_apply, h]

/-- **Relative localization for the latent source.** An event of the latent cube that is almost
surely invariant under every finitely supported sortwise permutation fixing `A` pointwise has a
representative, modulo the source, measurable for the local window at `A`. -/
theorem rankLatentSource_exists_local_ae_eq_of_ae_invariant [Countable S.Srt]
    (A : Finset (Σ s : S.Srt, Vinfinite S s)) {D : Set (RankLatentSpace S n)}
    (hD : MeasurableSet D)
    (hinv : ∀ σ : FinSuppPerm S, SortwiseFixing A σ.1 →
      rankLatentRelabel σ n ⁻¹' D =ᵐ[rankLatentSource S n] D) :
    ∃ D', MeasurableSet[MeasurableSpace.comap (localLatents A n) inferInstance] D' ∧
      D' =ᵐ[rankLatentSource S n] D := by
  classical
  set μ := rankLatentSource S n with hμ
  have hmL_le : MeasurableSpace.comap (localLatents (S := S) A n) inferInstance ≤
      MeasurableSpace.pi := (measurable_localLatents A n).comap_le
  -- the local conditional probability of `D`
  set h : RankLatentSpace S n → ℝ :=
    μ⟦D | MeasurableSpace.comap (localLatents (S := S) A n) inferInstance⟧ with hh
  have hh_meas : StronglyMeasurable[MeasurableSpace.comap (localLatents (S := S) A n)
      inferInstance] h := stronglyMeasurable_condExp
  have hh_int : Integrable h μ := integrable_condExp
  obtain ⟨hh0, hh1⟩ := condExp_indicator_bounds (μ := μ) hmL_le hD
  rw [← hh] at hh0 hh1
  have hh_bdd : ∀ᵐ ω ∂μ, ‖h ω‖ ≤ 1 := by
    filter_upwards [hh0, hh1] with ω h0 h1
    rw [Pi.zero_apply] at h0
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith, h1⟩
  have hD_int : Integrable (D.indicator fun _ => (1 : ℝ)) μ := (integrable_const 1).indicator hD
  have hD1 : ∫ ω, D.indicator (fun _ => (1 : ℝ)) ω ∂μ = μ.real D := integral_indicator_one hD
  have hD_bdd : ∀ ω, ‖D.indicator (fun _ => (1 : ℝ)) ω‖ ≤ 1 := fun ω =>
    (norm_indicator_le_norm_self _ _).trans (by simp)
  have hh_sq : Integrable (fun ω => h ω * h ω) μ :=
    hh_int.bdd_mul (hh_meas.mono hmL_le).aestronglyMeasurable hh_bdd
  have hDh_int : Integrable (fun ω => D.indicator (fun _ => (1 : ℝ)) ω * h ω) μ :=
    hh_int.bdd_mul hD_int.aestronglyMeasurable (Filter.Eventually.of_forall hD_bdd)
  -- (i) the local conditional probability integrates to the mass of `D`
  have hi : ∫ ω, h ω ∂μ = μ.real D := by
    rw [hh, integral_condExp hmL_le]
    exact hD1
  -- (ii) orthogonality
  have hii : ∫ ω, D.indicator (fun _ => (1 : ℝ)) ω * h ω ∂μ = ∫ ω, h ω * h ω ∂μ := by
    have hpull := condExp_mul_of_stronglyMeasurable_left (μ := μ) hh_meas
      (g := D.indicator fun _ => (1 : ℝ))
      (hh_int.mul_bdd hD_int.aestronglyMeasurable (Filter.Eventually.of_forall hD_bdd)) hD_int
    calc ∫ ω, D.indicator (fun _ => (1 : ℝ)) ω * h ω ∂μ
        = ∫ ω, (h * D.indicator fun _ => (1 : ℝ)) ω ∂μ := by
          congr 1; funext ω; simp only [Pi.mul_apply, mul_comm]
      _ = ∫ ω, (μ[h * D.indicator fun _ => (1 : ℝ) |
            MeasurableSpace.comap (localLatents (S := S) A n) inferInstance]) ω ∂μ :=
          (integral_condExp hmL_le).symm
      _ = ∫ ω, h ω * h ω ∂μ := integral_congr_ae hpull
  -- (iii) the main estimate: the mass of `D` is the energy of `h`
  have hring : IsSetRing (latentCylinders S n) :=
    ⟨empty_mem_measurableCylinders _, fun _ _ hs ht => union_mem_measurableCylinders hs ht,
      fun _ _ hs ht => sdiff_mem_measurableCylinders hs ht⟩
  have hiii : μ.real D = ∫ ω, h ω * h ω ∂μ := by
    refine eq_of_forall_dist_le fun ε hε => ?_
    obtain ⟨C, hCmem, hCD⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing (μ := μ) hring
      ⟨{Set.univ}, Set.countable_singleton _,
        Set.singleton_subset_iff.mpr (univ_mem_measurableCylinders _), by simp⟩
      generateFrom_measurableCylinders.symm hD (ENNReal.ofReal_pos.mpr (by linarith : 0 < ε / 4))
    obtain ⟨F, T, hT, rfl⟩ := (mem_measurableCylinders _).mp hCmem
    obtain ⟨σ, hσ, hdisp⟩ := exists_finSuppPerm_displacing A F
    have hcore := measureReal_inter_preimage_cylinder A hT hσ hdisp
    have hCmeas : MeasurableSet (cylinder (α := fun _ : RankLatentIndex S n => ℝ) F T) :=
      hT.cylinder
    have hTrmp : MeasurePreserving (rankLatentRelabel σ n) μ μ :=
      ⟨(rankLatentRelabel σ n).measurable, rankLatentSource_map_rankLatentRelabel σ n⟩
    set C := cylinder (α := fun _ : RankLatentIndex S n => ℝ) F T with hC
    set g : RankLatentSpace S n → ℝ :=
      μ⟦C | MeasurableSpace.comap (localLatents (S := S) A n) inferInstance⟧ with hg
    have hCDr : μ.real (C ∆ D) ≤ ε / 4 :=
      ENNReal.toReal_le_of_le_ofReal (by linarith) hCD.le
    -- the mass of the displaced intersection is close to the mass of `D`
    have hE1 : |μ.real (C ∩ rankLatentRelabel σ n ⁻¹' C) - μ.real D| ≤ ε / 2 := by
      have hDD : μ.real D = μ.real (D ∩ rankLatentRelabel σ n ⁻¹' D) := by
        have hae : ((D ∩ rankLatentRelabel σ n ⁻¹' D : Set (RankLatentSpace S n))) =ᵐ[μ] D := by
          simpa only [Set.inter_self] using
            (Filter.EventuallyEq.refl (ae μ) D).inter (hinv σ hσ)
        simp only [measureReal_def, measure_congr hae]
      rw [hDD]
      refine (abs_measureReal_sub_le_symmDiff _ _).trans ?_
      have hsub : (C ∩ rankLatentRelabel σ n ⁻¹' C) ∆ (D ∩ rankLatentRelabel σ n ⁻¹' D) ⊆
          (C ∆ D) ∪ rankLatentRelabel σ n ⁻¹' (C ∆ D) := by
        intro x hx
        simp only [Set.mem_symmDiff, Set.mem_inter_iff, Set.mem_union, Set.mem_preimage] at hx ⊢
        tauto
      calc μ.real ((C ∩ rankLatentRelabel σ n ⁻¹' C) ∆ (D ∩ rankLatentRelabel σ n ⁻¹' D))
          ≤ μ.real ((C ∆ D) ∪ rankLatentRelabel σ n ⁻¹' (C ∆ D)) := measureReal_mono hsub
        _ ≤ μ.real (C ∆ D) + μ.real (rankLatentRelabel σ n ⁻¹' (C ∆ D)) :=
            measureReal_union_le _ _
        _ = μ.real (C ∆ D) + μ.real (C ∆ D) := by
            rw [hTrmp.measureReal_preimage (hCmeas.symmDiff hD).nullMeasurableSet]
        _ ≤ ε / 2 := by linarith
    -- the local conditional probabilities are close in `L¹`
    have hC_int : Integrable (C.indicator fun _ => (1 : ℝ)) μ := (integrable_const 1).indicator hCmeas
    have hgh : ∫ ω, |g ω - h ω| ∂μ ≤ ε / 4 := by
      have hsub : g - h =ᵐ[μ] μ[C.indicator (fun _ => (1 : ℝ)) - D.indicator (fun _ => (1 : ℝ)) |
          MeasurableSpace.comap (localLatents (S := S) A n) inferInstance] :=
        (condExp_sub hC_int hD_int _).symm
      calc ∫ ω, |g ω - h ω| ∂μ
          = ∫ ω, |(μ[C.indicator (fun _ => (1 : ℝ)) - D.indicator (fun _ => (1 : ℝ)) |
              MeasurableSpace.comap (localLatents (S := S) A n) inferInstance]) ω| ∂μ :=
            integral_congr_ae (hsub.mono fun ω hω => by
              simp only [Pi.sub_apply] at hω
              simp only [hω])
        _ ≤ ∫ ω, |(C.indicator (fun _ => (1 : ℝ)) - D.indicator (fun _ => (1 : ℝ))) ω| ∂μ :=
            integral_abs_condExp_le _
        _ = ∫ ω, (C ∆ D).indicator (fun _ => (1 : ℝ)) ω ∂μ := by
            congr 1
            funext ω
            by_cases hx : ω ∈ C <;> by_cases hy : ω ∈ D <;>
              simp [hx, hy, Set.mem_symmDiff]
        _ = μ.real (C ∆ D) := integral_indicator_one (hCmeas.symmDiff hD)
        _ ≤ ε / 4 := hCDr
    obtain ⟨hg0, hg1⟩ := condExp_indicator_bounds (μ := μ) hmL_le hCmeas
    rw [← hg] at hg0 hg1
    have hg_meas : StronglyMeasurable[MeasurableSpace.comap (localLatents (S := S) A n)
        inferInstance] g := stronglyMeasurable_condExp
    have hg_int : Integrable g μ := integrable_condExp
    have hg_bdd : ∀ᵐ ω ∂μ, ‖g ω‖ ≤ 1 := by
      filter_upwards [hg0, hg1] with ω h0 h1
      rw [Pi.zero_apply] at h0
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by linarith, h1⟩
    have hg_sq : Integrable (fun ω => g ω * g ω) μ :=
      hg_int.bdd_mul (hg_meas.mono hmL_le).aestronglyMeasurable hg_bdd
    have hgh_int : Integrable (fun ω => |g ω - h ω|) μ := (hg_int.sub hh_int).abs
    have hE2 : |(∫ ω, g ω * g ω ∂μ) - ∫ ω, h ω * h ω ∂μ| ≤ ε / 2 := by
      rw [← integral_sub hg_sq hh_sq]
      refine (abs_integral_le_integral_abs).trans ?_
      calc ∫ ω, |g ω * g ω - h ω * h ω| ∂μ
          ≤ ∫ ω, 2 * |g ω - h ω| ∂μ := by
            refine integral_mono_ae (hg_sq.sub hh_sq).abs (hgh_int.const_mul 2) ?_
            filter_upwards [hg0, hg1, hh0, hh1] with ω g0 g1 h0 h1
            rw [Pi.zero_apply] at g0 h0
            have hfac : g ω * g ω - h ω * h ω = (g ω - h ω) * (g ω + h ω) := by ring
            rw [hfac, abs_mul, mul_comm]
            refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
            rw [abs_le]
            constructor <;> linarith
        _ = 2 * ∫ ω, |g ω - h ω| ∂μ := integral_const_mul _ _
        _ ≤ ε / 2 := by linarith
    rw [Real.dist_eq]
    calc |μ.real D - ∫ ω, h ω * h ω ∂μ|
        ≤ |μ.real D - μ.real (C ∩ rankLatentRelabel σ n ⁻¹' C)| +
          |μ.real (C ∩ rankLatentRelabel σ n ⁻¹' C) - ∫ ω, h ω * h ω ∂μ| := abs_sub_le _ _ _
      _ = |μ.real (C ∩ rankLatentRelabel σ n ⁻¹' C) - μ.real D| +
          |(∫ ω, g ω * g ω ∂μ) - ∫ ω, h ω * h ω ∂μ| := by rw [abs_sub_comm, hcore]
      _ ≤ ε / 2 + ε / 2 := add_le_add hE1 hE2
      _ = ε := by ring
  -- the endgame: `h` is `{0,1}`-valued and agrees with the indicator of `D`
  have hA : (fun ω => D.indicator (fun _ => (1 : ℝ)) ω - D.indicator (fun _ => (1 : ℝ)) ω * h ω)
      =ᵐ[μ] 0 := by
    refine (integral_eq_zero_iff_of_nonneg_ae (f := fun ω =>
      D.indicator (fun _ => (1 : ℝ)) ω - D.indicator (fun _ => (1 : ℝ)) ω * h ω) ?_
      (hD_int.sub hDh_int)).mp ?_
    · filter_upwards [hh1] with ω h1
      have h0' : 0 ≤ D.indicator (fun _ => (1 : ℝ)) ω :=
        Set.indicator_nonneg (fun _ _ => zero_le_one) ω
      show (0 : ℝ) ≤ D.indicator (fun _ => (1 : ℝ)) ω - D.indicator (fun _ => (1 : ℝ)) ω * h ω
      nlinarith
    · refine (integral_sub hD_int hDh_int).trans ?_
      rw [hD1, hii, hiii, sub_self]
  have hB : (fun ω => h ω - D.indicator (fun _ => (1 : ℝ)) ω * h ω) =ᵐ[μ] 0 := by
    refine (integral_eq_zero_iff_of_nonneg_ae (f := fun ω =>
      h ω - D.indicator (fun _ => (1 : ℝ)) ω * h ω) ?_ (hh_int.sub hDh_int)).mp ?_
    · filter_upwards [hh0] with ω h0
      rw [Pi.zero_apply] at h0
      have h1' : D.indicator (fun _ => (1 : ℝ)) ω ≤ 1 :=
        Set.indicator_le_self' (fun _ _ => zero_le_one) ω
      show (0 : ℝ) ≤ h ω - D.indicator (fun _ => (1 : ℝ)) ω * h ω
      nlinarith
    · refine (integral_sub hh_int hDh_int).trans ?_
      rw [hi, hii, hiii, sub_self]
  refine ⟨h ⁻¹' Set.Ioi (1 / 2), hh_meas.measurable measurableSet_Ioi, ?_⟩
  refine Filter.eventuallyEq_set.mpr ?_
  filter_upwards [hA, hB] with ω hAω hBω
  simp only [Pi.zero_apply] at hAω hBω
  by_cases hω : ω ∈ D
  · simp only [Set.indicator_of_mem hω, one_mul, sub_eq_zero] at hAω
    simp only [hω, Set.mem_preimage, Set.mem_Ioi, ← hAω]
    norm_num
  · simp only [Set.indicator_of_notMem hω, zero_mul, sub_zero] at hBω
    simp [hω, Set.mem_preimage, Set.mem_Ioi, hBω]

end RelSignature

