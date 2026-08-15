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

end RelSignature
