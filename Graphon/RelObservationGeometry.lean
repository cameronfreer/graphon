/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelLatentGeometry
import Graphon.RelEqualityPattern

/-!
# Carrier-parametric observation layer (R4 converse, #107)

The observations used by recovery and screening — local latents, blocks of raw relation
coordinates, and the rank-truncated remainder — over an **arbitrary sortwise carrier**. The
`Vinfinite`-indexed originals become compatibility aliases, and the pooled statements instantiate
this core rather than introducing parallel pooled definitions.

## The transport boundary

The three observations do **not** transport equally well, and the difference is a matter of truth,
not of proof effort:

* `localLatentsOver` and `blockMapOver` are **local** — they read only coordinates supported inside
  a given finite set — so they admit naturality along an arbitrary sortwise **embedding** of
  carriers: an embedding restricts to a bijection between the supports inside `A` and those inside
  its image.
* `restObservationOver` is **global**: its remainder ranges over *every* rank-`≤ n` coordinate of
  the ambient carrier other than the one at `A`. Along an embedding into a larger carrier the
  target remainder sees coordinates outside the image, which the source remainder cannot, so an
  embedding-level commuting law would be **false**. It transports only along a carrier
  **equivalence**.

Screening therefore transports along the canonical `poolVertexEquiv`, which the pooled uniqueness
identity makes available; recovery, being local, is free to use embeddings.
-/

open MeasureTheory

namespace RelSignature

universe u v

variable {S : RelSignature.{u}} {V W : S.Srt → Type v}

/-! ### Local latents -/

/-- The latent coordinates visible at `A`: supports contained in `A`. -/
def LocalLatentIndexOver (V : S.Srt → Type v) (A : Finset (Σ s : S.Srt, V s)) (n : ℕ) :=
  {B : LatentIndexOver S V n // B.1 ⊆ A}

instance [Countable S.Srt] [∀ s, Countable (V s)] (A : Finset (Σ s : S.Srt, V s)) (n : ℕ) :
    Countable (LocalLatentIndexOver V A n) := Subtype.countable

/-- The local latent space at `A`. -/
abbrev LocalLatentSpaceOver (V : S.Srt → Type v) (A : Finset (Σ s : S.Srt, V s)) (n : ℕ) :=
  LocalLatentIndexOver V A n → ℝ

/-- Restriction of the latent array to the coordinates visible at `A`. -/
def localLatentsOver (A : Finset (Σ s : S.Srt, V s)) (n : ℕ) :
    LatentSpaceOver S V n → LocalLatentSpaceOver V A n := fun ω B => ω B.1

theorem measurable_localLatentsOver (A : Finset (Σ s : S.Srt, V s)) (n : ℕ) :
    Measurable (localLatentsOver (S := S) A n) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

/-! ### Blocks of raw relation coordinates -/

open scoped Classical in
/-- Raw relation coordinates whose tagged support is exactly `A`. -/
def BlockIndexOver (V : S.Srt → Type v) (A : Finset (Σ s : S.Srt, V s)) :=
  {c : RelCoord S V // c.support = A}

open scoped Classical in
instance [Countable S.Rel] [∀ s, Countable (V s)] (A : Finset (Σ s : S.Srt, V s)) :
    Countable (BlockIndexOver V A) := Subtype.countable

open scoped Classical in
/-- The block of the structure at `A`. -/
abbrev BlockSpaceOver (V : S.Srt → Type v) (A : Finset (Σ s : S.Srt, V s)) :=
  BlockIndexOver V A → Bool

open scoped Classical in
/-- Read the block at `A` off a structure. -/
def blockMapOver (A : Finset (Σ s : S.Srt, V s)) :
    RelStructure S V → BlockSpaceOver V A := fun X c => X c.1

open scoped Classical in
theorem measurable_blockMapOver [Countable S.Rel] [∀ s, Countable (V s)]
    (A : Finset (Σ s : S.Srt, V s)) :
    Measurable (blockMapOver (S := S) A) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

/-! ### The rank-truncated remainder

Global, hence transportable only along carrier equivalences — see the module header. -/

open scoped Classical in
/-- Coordinates of rank at most `n` other than those at `A`. -/
def RestIndexOver (V : S.Srt → Type v) (n : ℕ) (A : Finset (Σ s : S.Srt, V s)) :=
  {c : RelCoord S V // c.support.card ≤ n ∧ c.support ≠ A}

open scoped Classical in
instance [Countable S.Rel] [∀ s, Countable (V s)] (n : ℕ) (A : Finset (Σ s : S.Srt, V s)) :
    Countable (RestIndexOver V n A) := Subtype.countable

open scoped Classical in
/-- The remaining rank-`≤ n` structure. -/
abbrev RestSpaceOver (V : S.Srt → Type v) (n : ℕ) (A : Finset (Σ s : S.Srt, V s)) :=
  RestIndexOver V n A → Bool

open scoped Classical in
/-- **The rank-truncated remainder observation** over a carrier: the other blocks of rank at most
`n`, together with the whole latent array. -/
def restObservationOver (n : ℕ) (A : Finset (Σ s : S.Srt, V s)) :
    RelStructure S V × LatentSpaceOver S V n →
      RestSpaceOver V n A × LatentSpaceOver S V n :=
  fun p => (fun c => p.1 c.1, p.2)

open scoped Classical in
theorem measurable_restObservationOver [Countable S.Rel] [∀ s, Countable (V s)] (n : ℕ)
    (A : Finset (Σ s : S.Srt, V s)) :
    Measurable (restObservationOver (S := S) n A) :=
  (measurable_pi_lambda _ fun _ => measurable_fst.eval).prodMk measurable_snd

/-! ### Coordinate transport along a carrier equivalence

The coordinate mirror of `RelStructure.congrCarrier`, bundled once here: the remainder index is
global, so its transport needs a genuine equivalence of coordinates rather than an embedding. -/

/-- **Transport of relation coordinates along a sortwise equivalence of carriers**, bundled. -/
def RelCoord.congrCarrier (e : ∀ s, V s ≃ W s) : RelCoord S V ≃ RelCoord S W where
  toFun := RelCoord.map fun s => ⇑(e s)
  invFun := RelCoord.map fun s => ⇑(e s).symm
  left_inv c := by
    refine congrArg (fun w => (⟨c.1, w⟩ : RelCoord S V)) (funext fun i => ?_)
    exact (e _).symm_apply_apply (c.2 i)
  right_inv c := by
    refine congrArg (fun w => (⟨c.1, w⟩ : RelCoord S W)) (funext fun i => ?_)
    exact (e _).apply_symm_apply (c.2 i)

@[simp] theorem RelCoord.congrCarrier_apply (e : ∀ s, V s ≃ W s) (c : RelCoord S V) :
    RelCoord.congrCarrier e c = RelCoord.map (fun s => ⇑(e s)) c := rfl

@[simp] theorem RelCoord.congrCarrier_symm_apply (e : ∀ s, V s ≃ W s) (c : RelCoord S W) :
    (RelCoord.congrCarrier e).symm c = RelCoord.map (fun s => ⇑(e s).symm) c := rfl

/-! ### Support and index transport

Equivalences first, with pointwise `_apply` lemmas; the function-level naturality laws are derived
from these. Keeping the bijections primitive is what limits coercion and `DecidableEq` friction. -/

open scoped Classical in
/-- The image of a support under a sortwise embedding of carriers. -/
noncomputable def supportImage (e : ∀ s, V s ↪ W s) (A : Finset (Σ s : S.Srt, V s)) :
    Finset (Σ s : S.Srt, W s) :=
  A.image (Sigma.map id fun s => ⇑(e s))

theorem injective_sigmaMap (e : ∀ s, V s ↪ W s) :
    Function.Injective (Sigma.map id fun s => ⇑(e s) : (Σ s : S.Srt, V s) → Σ s : S.Srt, W s) :=
  Function.injective_id.sigma_map fun s => (e s).injective

open scoped Classical in
@[simp] theorem mem_supportImage_map {e : ∀ s, V s ↪ W s} {A : Finset (Σ s : S.Srt, V s)}
    {v : Σ s : S.Srt, V s} :
    Sigma.map id (fun s => ⇑(e s)) v ∈ supportImage e A ↔ v ∈ A :=
  (injective_sigmaMap e).mem_finset_image

open scoped Classical in
/-- **A support lies inside `A` exactly when its image lies inside the image of `A`.** This is the
bijection underlying local naturality: an embedding restricts to a bijection between the supports
inside `A` and those inside its image. -/
theorem latentIndexEmbed_subset_supportImage_iff (e : ∀ s, V s ↪ W s)
    {A : Finset (Σ s : S.Srt, V s)} {n : ℕ} (B : LatentIndexOver S V n) :
    (latentIndexEmbed e n B).1 ⊆ supportImage e A ↔ B.1 ⊆ A := by
  classical
  rw [latentIndexEmbed_coe, supportImage]
  constructor
  · intro h v hv
    have hmem := h (Finset.mem_image_of_mem (Sigma.map id fun s => ⇑(e s)) hv)
    rwa [(injective_sigmaMap e).mem_finset_image] at hmem
  · intro h w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    exact Finset.mem_image_of_mem _ (h hv)

open scoped Classical in
/-- Transporting a coordinate carries its support to the image of that support. -/
theorem RelCoord.support_congrCarrier (e : ∀ s, V s ≃ W s) (c : RelCoord S V) :
    (RelCoord.congrCarrier e c).support =
      supportImage (fun s => (e s).toEmbedding) c.support := by
  rw [RelCoord.congrCarrier_apply, RelCoord.support_map, supportImage]
  rfl

end RelSignature
