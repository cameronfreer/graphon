/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelationalTopology

/-!
# The auxiliary vertex pool (R4 converse, #107)

Law-free geometry for the stationary extension: each sort's carrier is enlarged by a fresh
pool copy,

`PoolVertex S s := Vinfinite S s ⊕ Vinfinite S s`,

with the original and pool embeddings, definitional disjointness and exhaustivity, a fixed
sortwise identification with `ℕ`, structure transport along sortwise equivalences as a
measurable equivalence, the two restriction maps, and the naturality laws between restriction,
transport, and relabeling.

**There is deliberately no "mixed permutation" subtype.** The relabeling action on the
extension quantifies over the raw full permutation family `∀ s, Equiv.Perm (PoolVertex S s)` —
permutations may move vertices between the two summands, and that freedom is load-bearing for
the polling argument. Split permutations (`Equiv.sumCongr`) appear only in the naturality law
for restriction, which is exactly the setting where the split hypothesis is honest: restriction
does not commute with a permutation that crosses the boundary, and no such law is stated.

No law, no measure, no basis appears in this file.
-/

open MeasureTheory

namespace RelSignature

universe u

variable {S : RelSignature.{u}}

/-! ### The pooled carrier -/

/-- The enlarged carrier: an original copy and a fresh pool copy of the vertices, per sort. -/
abbrev PoolVertex (S : RelSignature.{u}) : S.Srt → Type := fun s =>
  Vinfinite S s ⊕ Vinfinite S s

/-- The original-vertex embedding. -/
def originalVertex (S : RelSignature.{u}) (s : S.Srt) : Vinfinite S s ↪ PoolVertex S s :=
  ⟨Sum.inl, Sum.inl_injective⟩

/-- The pool-vertex embedding. -/
def poolVertex (S : RelSignature.{u}) (s : S.Srt) : Vinfinite S s ↪ PoolVertex S s :=
  ⟨Sum.inr, Sum.inr_injective⟩

/-- The two embeddings have disjoint images — definitionally, from `Sum`. -/
theorem originalVertex_ne_poolVertex (s : S.Srt) (v w : Vinfinite S s) :
    originalVertex S s v ≠ poolVertex S s w :=
  Sum.inl_ne_inr

/-- Every pooled vertex is an original vertex or a pool vertex — definitionally, from `Sum`. -/
theorem originalVertex_or_poolVertex (s : S.Srt) (x : PoolVertex S s) :
    (∃ v, x = originalVertex S s v) ∨ ∃ w, x = poolVertex S s w := by
  cases x with
  | inl v => exact Or.inl ⟨v, rfl⟩
  | inr w => exact Or.inr ⟨w, rfl⟩

/-- The fixed sortwise identification of the pooled carrier with the vertex set: both summands
together are again a countably infinite carrier. This is what transports the law in the cheap
existence theorem. -/
def poolVertexEquiv (S : RelSignature.{u}) (s : S.Srt) : PoolVertex S s ≃ Vinfinite S s :=
  Equiv.natSumNatEquivNat

/-! ### Structure transport along sortwise equivalences -/

/-- **Transport of structures along a sortwise family of equivalences**, as a measurable
equivalence: the forward map carries a structure on `V` to a structure on `W`, reading each
`W`-coordinate through `e⁻¹`. Both directions are `comap`s — the forward map is `comap` of the
inverse family — so the inverse laws reduce to `comap_comp` and the equivalence
cancellations. -/
def RelStructure.congrCarrier {V W : S.Srt → Type*} (e : ∀ s, V s ≃ W s) :
    RelStructure S V ≃ᵐ RelStructure S W where
  toEquiv :=
    { toFun := RelStructure.comap fun s => ((e s).symm : W s → V s)
      invFun := RelStructure.comap fun s => ((e s) : V s → W s)
      left_inv := fun X => by
        rw [← RelStructure.comap_comp]
        convert RelStructure.comap_id X using 2
        funext s x
        exact (e s).symm_apply_apply x
      right_inv := fun X => by
        rw [← RelStructure.comap_comp]
        convert RelStructure.comap_id X using 2
        funext s x
        exact (e s).apply_symm_apply x }
  measurable_toFun := measurable_pi_lambda _ fun _ => measurable_pi_apply _
  measurable_invFun := measurable_pi_lambda _ fun _ => measurable_pi_apply _

@[simp] theorem RelStructure.congrCarrier_apply {V W : S.Srt → Type*} (e : ∀ s, V s ≃ W s)
    (X : RelStructure S V) :
    RelStructure.congrCarrier (S := S) e X =
      RelStructure.comap (fun s => ((e s).symm : W s → V s)) X := rfl

/-- **Transport–relabel naturality**: relabeling by `σ` before transport is relabeling by the
conjugated family after transport. -/
theorem RelStructure.congrCarrier_relabel {V W : S.Srt → Type*} (e : ∀ s, V s ≃ W s)
    (σ : ∀ s, Equiv.Perm (V s)) (X : RelStructure S V) :
    RelStructure.congrCarrier (S := S) e (RelStructure.relabel σ X) =
      RelStructure.relabel (fun s => (e s).symm.trans ((σ s).trans (e s)))
        (RelStructure.congrCarrier (S := S) e X) := by
  show RelStructure.comap _ (RelStructure.comap _ X) = RelStructure.comap _ (RelStructure.comap _ X)
  rw [← RelStructure.comap_comp, ← RelStructure.comap_comp]
  congr 1
  funext s x
  simp

/-! ### Restriction to the two halves -/

/-- Restriction of an extended structure to the original vertices. -/
def restrictOriginal (S : RelSignature.{u}) :
    RelStructure S (PoolVertex S) → RelStructure S (Vinfinite S) :=
  RelStructure.restrict (originalVertex S)

/-- Restriction of an extended structure to the pool vertices. -/
def restrictPool (S : RelSignature.{u}) :
    RelStructure S (PoolVertex S) → RelStructure S (Vinfinite S) :=
  RelStructure.restrict (poolVertex S)

theorem measurable_restrictOriginal : Measurable (restrictOriginal S) :=
  measurable_restrict _

theorem measurable_restrictPool : Measurable (restrictPool S) :=
  measurable_restrict _

/-- **Restriction–relabel naturality, split case**: a permutation that respects the
original/pool split commutes with restriction to the original half — the original component
acts before restriction. Definitional. Stated only for split permutations: restriction does
not commute with a permutation crossing the boundary, and no such law holds or is claimed. -/
theorem restrictOriginal_relabel_sumCongr (σ τ : ∀ s, Equiv.Perm (Vinfinite S s))
    (X : RelStructure S (PoolVertex S)) :
    restrictOriginal S (RelStructure.relabel (fun s => Equiv.sumCongr (σ s) (τ s)) X) =
      RelStructure.relabel σ (restrictOriginal S X) := rfl

/-- The pool half of the split naturality law. Definitional. -/
theorem restrictPool_relabel_sumCongr (σ τ : ∀ s, Equiv.Perm (Vinfinite S s))
    (X : RelStructure S (PoolVertex S)) :
    restrictPool S (RelStructure.relabel (fun s => Equiv.sumCongr (σ s) (τ s)) X) =
      RelStructure.relabel τ (restrictPool S X) := rfl

end RelSignature
