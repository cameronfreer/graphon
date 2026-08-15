/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelationalTopology
import Graphon.SamplerSources

/-!
# Carrier-parametric latent geometry (R4 converse, #107)

Law-free latent geometry over an **arbitrary sortwise carrier** `V : S.Srt → Type*`: supports of
cardinality below the working rank, the latent cube they index, its i.i.d. uniform source, the
action of a sortwise permutation family, and restriction along a sortwise embedding of carriers.

Nothing here mentions a law, a measure on structures, a representation, recovery, screening, or a
coupling. The two intended carriers are `Vinfinite S` (the original vertices) and `PoolVertex S`
(the pooled vertices); restriction along the original embedding is what relates them.

**The action is by the full permutation family** `∀ s, Equiv.Perm (V s)`. Finite support is a
property of a particular carrier's automorphisms, not of latent cubes: any sortwise permutation
reindexes finite supports bijectively and preserves cardinality, so it acts on the index type and
preserves the i.i.d. source. Users needing a finitely supported subgroup restrict this action
rather than the other way round.
-/

open MeasureTheory

namespace RelSignature

universe u v

variable {S : RelSignature.{u}} {V W Z : S.Srt → Type v}

/-! ### Supports, the latent cube, and its source -/

/-- **Supports of cardinality below `n`** over a sortwise carrier. -/
def LatentIndexOver (S : RelSignature.{u}) (V : S.Srt → Type v) (n : ℕ) :=
  {A : Finset (Σ s : S.Srt, V s) // A.card < n}

instance [Countable S.Srt] [∀ s, Countable (V s)] (n : ℕ) :
    Countable (LatentIndexOver S V n) :=
  Subtype.countable

/-- The latent cube over a carrier: one real coordinate per support below the rank. -/
abbrev LatentSpaceOver (S : RelSignature.{u}) (V : S.Srt → Type v) (n : ℕ) :=
  LatentIndexOver S V n → ℝ

/-- The i.i.d. uniform latent source over a carrier. -/
noncomputable def latentSourceOver (S : RelSignature.{u}) (V : S.Srt → Type v) (n : ℕ) :
    Measure (LatentSpaceOver S V n) :=
  iidUniformSource (LatentIndexOver S V n)

instance (n : ℕ) : IsProbabilityMeasure (latentSourceOver S V n) := by
  rw [latentSourceOver]; infer_instance

/-! ### The action of a sortwise permutation family -/

open scoped Classical in
/-- A sortwise permutation family permutes the supports below each rank. Bijectivity of each
`ρ s` preserves cardinality, so the rank is unchanged. -/
noncomputable def latentIndexPerm (ρ : ∀ s, Equiv.Perm (V s)) (n : ℕ) :
    LatentIndexOver S V n ≃ LatentIndexOver S V n where
  toFun A := ⟨A.1.image (Sigma.map id fun s ↦ ⇑(ρ s)), by
    rw [Finset.card_image_of_injective _
      (Function.injective_id.sigma_map fun s ↦ (ρ s).injective)]
    exact A.2⟩
  invFun A := ⟨A.1.image (Sigma.map id fun s ↦ ⇑(ρ s)⁻¹), by
    rw [Finset.card_image_of_injective _
      (Function.injective_id.sigma_map fun s ↦ ((ρ s)⁻¹).injective)]
    exact A.2⟩
  left_inv A := Subtype.ext (by
    show (A.1.image (Sigma.map id fun s ↦ ⇑(ρ s))).image (Sigma.map id fun s ↦ ⇑(ρ s)⁻¹) = A.1
    rw [Finset.image_image]
    refine (Finset.image_congr fun v _ ↦ ?_).trans A.1.image_id
    obtain ⟨s, x⟩ := v
    show (⟨s, (ρ s)⁻¹ ((ρ s) x)⟩ : Σ s : S.Srt, V s) = ⟨s, x⟩
    rw [show (ρ s)⁻¹ ((ρ s) x) = x from (ρ s).symm_apply_apply x])
  right_inv A := Subtype.ext (by
    show (A.1.image (Sigma.map id fun s ↦ ⇑(ρ s)⁻¹)).image (Sigma.map id fun s ↦ ⇑(ρ s)) = A.1
    rw [Finset.image_image]
    refine (Finset.image_congr fun v _ ↦ ?_).trans A.1.image_id
    obtain ⟨s, x⟩ := v
    show (⟨s, (ρ s) ((ρ s)⁻¹ x)⟩ : Σ s : S.Srt, V s) = ⟨s, x⟩
    rw [show (ρ s) ((ρ s)⁻¹ x) = x from (ρ s).apply_symm_apply x])

open scoped Classical in
@[simp] theorem latentIndexPerm_apply_coe (ρ : ∀ s, Equiv.Perm (V s)) (n : ℕ)
    (A : LatentIndexOver S V n) :
    (latentIndexPerm ρ n A).1 = A.1.image (Sigma.map id fun s ↦ ⇑(ρ s)) := rfl

open scoped Classical in
@[simp] theorem latentIndexPerm_one (n : ℕ) :
    latentIndexPerm (S := S) (V := V) (fun _ ↦ 1) n = Equiv.refl _ :=
  Equiv.ext fun A ↦ Subtype.ext (by
    show A.1.image (Sigma.map id fun s ↦ ⇑(1 : Equiv.Perm (V s))) = A.1
    refine (Finset.image_congr fun v _ ↦ ?_).trans A.1.image_id
    obtain ⟨s, x⟩ := v
    rfl)

open scoped Classical in
@[simp] theorem latentIndexPerm_comp (ρ τ : ∀ s, Equiv.Perm (V s)) (n : ℕ) :
    latentIndexPerm (S := S) (fun s ↦ ρ s * τ s) n =
      (latentIndexPerm τ n).trans (latentIndexPerm ρ n) :=
  Equiv.ext fun A ↦ Subtype.ext (by
    show A.1.image (Sigma.map id fun s ↦ ⇑(ρ s * τ s)) =
      (A.1.image (Sigma.map id fun s ↦ ⇑(τ s))).image
        (Sigma.map id fun s ↦ ⇑(ρ s) : (Σ s : S.Srt, V s) → Σ s : S.Srt, V s)
    rw [Finset.image_image]
    refine Finset.image_congr fun v _ ↦ ?_
    obtain ⟨s, x⟩ := v
    rfl)

open scoped Classical in
/-- The action on the latent cube: reindex the coordinates. -/
noncomputable def latentRelabelOver (ρ : ∀ s, Equiv.Perm (V s)) (n : ℕ) :
    LatentSpaceOver S V n ≃ᵐ LatentSpaceOver S V n where
  toEquiv := Equiv.arrowCongr (latentIndexPerm ρ n).symm (Equiv.refl ℝ)
  measurable_toFun := measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _
  measurable_invFun := measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

@[simp] theorem latentRelabelOver_apply (ρ : ∀ s, Equiv.Perm (V s)) (n : ℕ)
    (ω : LatentSpaceOver S V n) (A : LatentIndexOver S V n) :
    latentRelabelOver ρ n ω A = ω (latentIndexPerm ρ n A) := rfl

/-- **Exact invariance of the source.** The action permutes coordinates of an i.i.d. cube. -/
theorem latentSourceOver_map_latentRelabelOver [Countable S.Srt] [∀ s, Countable (V s)]
    (ρ : ∀ s, Equiv.Perm (V s)) (n : ℕ) :
    (latentSourceOver S V n).map (latentRelabelOver ρ n) = latentSourceOver S V n := by
  rw [latentSourceOver, iidUniformSource]
  exact Measure.infinitePi_map_comp_equiv _ (latentIndexPerm ρ n)

/-! ### Restriction along a sortwise embedding of carriers -/

open scoped Classical in
/-- A sortwise embedding of carriers pushes supports forward, preserving the rank. -/
noncomputable def latentIndexEmbed (e : ∀ s, V s ↪ W s) (n : ℕ) :
    LatentIndexOver S V n → LatentIndexOver S W n := fun A =>
  ⟨A.1.image (Sigma.map id fun s ↦ ⇑(e s)), by
    rw [Finset.card_image_of_injective _
      (Function.injective_id.sigma_map fun s ↦ (e s).injective)]
    exact A.2⟩

open scoped Classical in
@[simp] theorem latentIndexEmbed_coe (e : ∀ s, V s ↪ W s) (n : ℕ) (A : LatentIndexOver S V n) :
    (latentIndexEmbed e n A).1 = A.1.image (Sigma.map id fun s ↦ ⇑(e s)) := rfl

/-- **Restriction of a latent assignment** along a sortwise embedding of carriers: read the
coordinates indexed by the embedded supports. -/
noncomputable def latentRestrictOver (e : ∀ s, V s ↪ W s) (n : ℕ) :
    LatentSpaceOver S W n → LatentSpaceOver S V n := fun ω A => ω (latentIndexEmbed e n A)

theorem measurable_latentRestrictOver (e : ∀ s, V s ↪ W s) (n : ℕ) :
    Measurable (latentRestrictOver (S := S) e n) :=
  measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

@[simp] theorem latentRestrictOver_apply (e : ∀ s, V s ↪ W s) (n : ℕ)
    (ω : LatentSpaceOver S W n) (A : LatentIndexOver S V n) :
    latentRestrictOver e n ω A = ω (latentIndexEmbed e n A) := rfl

/-- **The moved-window law**, the honest naturality for a carrier permutation: restricting after
relabeling the larger carrier is restriction along the *moved* embedding. A permutation that
crosses the image of `e` does not commute with restriction along `e` — no such law is stated,
and this one holds for every permutation, mixed ones included. -/
theorem latentRestrictOver_latentRelabelOver (e : ∀ s, V s ↪ W s)
    (ρ : ∀ s, Equiv.Perm (W s)) (n : ℕ) :
    latentRestrictOver (S := S) e n ∘ latentRelabelOver ρ n =
      latentRestrictOver (fun s => (e s).trans (ρ s).toEmbedding) n := by
  classical
  funext ω A
  show ω (latentIndexPerm ρ n (latentIndexEmbed e n A))
    = ω (latentIndexEmbed (fun s => (e s).trans (ρ s).toEmbedding) n A)
  refine congrArg ω (Subtype.ext ?_)
  rw [latentIndexPerm_apply_coe, latentIndexEmbed_coe, latentIndexEmbed_coe,
    Finset.image_image]
  refine Finset.image_congr fun v _ ↦ ?_
  obtain ⟨s, x⟩ := v
  rfl

open scoped Classical in
/-- **Naturality of the index maps**: an embedding of carriers intertwining two permutation
families intertwines the induced index actions. Stated here, with abstract carriers, so that
instantiating at a concrete carrier never has to manipulate `Finset.image` under a derived
`DecidableEq`. -/
theorem latentIndexPerm_latentIndexEmbed (e : ∀ s, V s ↪ W s)
    (ρ : ∀ s, Equiv.Perm (W s)) (τ : ∀ s, Equiv.Perm (V s))
    (h : ∀ s x, ρ s (e s x) = e s (τ s x)) (n : ℕ) (A : LatentIndexOver S V n) :
    latentIndexPerm ρ n (latentIndexEmbed e n A)
      = latentIndexEmbed e n (latentIndexPerm τ n A) := by
  refine Subtype.ext ?_
  rw [latentIndexPerm_apply_coe, latentIndexEmbed_coe, latentIndexEmbed_coe,
    latentIndexPerm_apply_coe, Finset.image_image, Finset.image_image]
  refine Finset.image_congr fun v _ => ?_
  obtain ⟨s, x⟩ := v
  exact Sigma.ext rfl (heq_of_eq (h s x))

/-- The cube-level form of `latentIndexPerm_latentIndexEmbed`. -/
theorem latentRestrictOver_latentRelabelOver_of_intertwines (e : ∀ s, V s ↪ W s)
    (ρ : ∀ s, Equiv.Perm (W s)) (τ : ∀ s, Equiv.Perm (V s))
    (h : ∀ s x, ρ s (e s x) = e s (τ s x)) (n : ℕ) :
    latentRestrictOver (S := S) e n ∘ latentRelabelOver ρ n =
      latentRelabelOver τ n ∘ latentRestrictOver e n := by
  funext ω A
  show ω (latentIndexPerm ρ n (latentIndexEmbed e n A))
    = ω (latentIndexEmbed e n (latentIndexPerm τ n A))
  exact congrArg ω (latentIndexPerm_latentIndexEmbed e ρ τ h n A)

open scoped Classical in
/-- Index-level functoriality of restriction along carrier embeddings. -/
theorem latentIndexEmbed_comp (e : ∀ s, V s ↪ W s) (f : ∀ s, W s ↪ Z s) (n : ℕ)
    (A : LatentIndexOver S V n) :
    latentIndexEmbed f n (latentIndexEmbed e n A)
      = latentIndexEmbed (fun s => (e s).trans (f s)) n A := by
  refine Subtype.ext ?_
  rw [latentIndexEmbed_coe, latentIndexEmbed_coe, latentIndexEmbed_coe, Finset.image_image]
  refine Finset.image_congr fun v _ => ?_
  obtain ⟨s, x⟩ := v
  rfl

/-- **Functoriality of restriction**: restricting along `f` and then along `e` is restricting
along the composite embedding. -/
theorem latentRestrictOver_comp (e : ∀ s, V s ↪ W s) (f : ∀ s, W s ↪ Z s) (n : ℕ) :
    latentRestrictOver (S := S) e n ∘ latentRestrictOver f n =
      latentRestrictOver (fun s => (e s).trans (f s)) n := by
  funext ω A
  show ω (latentIndexEmbed f n (latentIndexEmbed e n A))
    = ω (latentIndexEmbed (fun s => (e s).trans (f s)) n A)
  rw [latentIndexEmbed_comp]

/-- Restriction along a permutation-as-embedding is that permutation's action. -/
theorem latentRestrictOver_toEmbedding (ρ : ∀ s, Equiv.Perm (V s)) (n : ℕ) :
    latentRestrictOver (S := S) (fun s => (ρ s).toEmbedding) n = latentRelabelOver ρ n := by
  classical
  funext ω A
  show ω (latentIndexEmbed (fun s => (ρ s).toEmbedding) n A) = ω (latentIndexPerm ρ n A)
  refine congrArg ω (Subtype.ext ?_)
  rw [latentIndexEmbed_coe, latentIndexPerm_apply_coe]
  refine Finset.ext fun v => ?_
  simp [Finset.mem_image]

open scoped Classical in
/-- **Support-wise agreement**: if a permutation of the target carrier carries one embedding to
another on every vertex of a support, the two induced index maps agree there. Stated with
abstract carriers, so instantiating never manipulates `Finset.image` under a derived
`DecidableEq`. -/
theorem latentIndexEmbed_eq_of_agree {e f : ∀ s, V s ↪ W s} {ρ : ∀ s, Equiv.Perm (W s)} {n : ℕ}
    {A : LatentIndexOver S V n} (h : ∀ v ∈ A.1, ρ v.1 (e v.1 v.2) = f v.1 v.2) :
    latentIndexEmbed f n A = latentIndexPerm ρ n (latentIndexEmbed e n A) := by
  refine Subtype.ext ?_
  rw [latentIndexEmbed_coe, latentIndexPerm_apply_coe, latentIndexEmbed_coe, Finset.image_image]
  refine Finset.image_congr fun v hv => ?_
  obtain ⟨s, x⟩ := v
  show (⟨s, f s x⟩ : Σ s : S.Srt, W s) = ⟨s, ρ s (e s x)⟩
  rw [h ⟨s, x⟩ hv]

/-- **The conjugation square for a carrier equivalence** — the latent-side mirror of
`RelStructure.congrCarrier_relabel`. Transporting along `e` intertwines a permutation of the
source carrier with its conjugate on the target. Proved carrier-generically, so instantiating at
a concrete carrier never manipulates `Finset.image` under a derived `DecidableEq`. -/
theorem latentRestrictOver_latentRelabelOver_conj (e : ∀ s, V s ≃ W s)
    (ρ : ∀ s, Equiv.Perm (V s)) (n : ℕ) :
    latentRestrictOver (S := S) (fun s => (e s).toEmbedding) n ∘
        latentRelabelOver (fun s => (e s).symm.trans ((ρ s).trans (e s))) n =
      latentRelabelOver ρ n ∘ latentRestrictOver (fun s => (e s).toEmbedding) n :=
  latentRestrictOver_latentRelabelOver_of_intertwines _ _ ρ
    (fun s x => by simp) n

end RelSignature
