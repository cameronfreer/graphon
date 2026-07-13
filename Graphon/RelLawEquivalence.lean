/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelInfiniteLaw

/-!
# The finite/infinite exchangeable relational law equivalence (AHK umbrella #103, R2c)

The exchangeability, uniqueness, and finite/infinite-law equivalence completing R2 (issue
#105), the multi-sorted analogue of `Graphon.InfiniteExchangeability`. Assumptions
`[Fintype S.Srt] [Countable S.Rel]`.

* `RelExchangeableLaw.infiniteLaw_map_restrict` — the **arbitrary sortwise injection** marginal
  theorem: `map (restrict e) infiniteLaw = marginal n` for any `e : ∀ s, Fin (n s) ↪ ℕ` (each
  finite range factors through a large size vector);
* `RelSignature.InfiniteRelExchangeableLaw` — a probability law on the infinite structure
  space invariant under every sortwise `Equiv.Perm ℕ`;
* `RelExchangeableLaw.infiniteLaw_map_relabel` / `toInfinite` — the infinite law is
  exchangeable, giving the forward map;
* `RelSignature.exists_perm_extend` — every `Fin k ↪ ℕ` extends to a permutation of `ℕ`;
* `InfiniteRelExchangeableLaw.toFinite` — the reverse map (finite marginals of an
  exchangeable infinite law, consistent by the permutation extension);
* `RelSignature.relExchangeableLawEquiv` — the equivalence
  `RelExchangeableLaw S ≃ InfiniteRelExchangeableLaw S`.
-/

open MeasureTheory Filter Topology

namespace RelSignature

variable {S : RelSignature}

/-- **Relabelling is measurable** (over the product σ-algebra; no countability needed). -/
theorem measurable_relabel {V : S.Srt → Type*} (σ : ∀ s, Equiv.Perm (V s)) :
    Measurable (RelStructure.relabel σ) := by
  apply measurable_pi_iff.mpr
  intro c
  exact measurable_pi_apply _

/-- **Every injection `Fin k ↪ ℕ` extends to a permutation of `ℕ`** (the complements are
cofinite, hence equivalent). -/
theorem exists_perm_extend {k : ℕ} (g : Fin k ↪ ℕ) :
    ∃ σ : Equiv.Perm ℕ, ∀ a : Fin k, σ ↑a = g a := by
  classical
  let e₀ : (Set.range ((↑) : Fin k → ℕ) : Set ℕ) ≃ (Set.range g : Set ℕ) :=
    (Equiv.ofInjective _ Fin.val_injective).symm.trans (Equiv.ofInjective g g.injective)
  have hsc : ((Set.range ((↑) : Fin k → ℕ))ᶜ : Set ℕ).Infinite :=
    (Set.finite_range _).infinite_compl
  have htc : ((Set.range g)ᶜ : Set ℕ).Infinite := (Set.finite_range _).infinite_compl
  haveI := hsc.to_subtype
  haveI := htc.to_subtype
  haveI : Denumerable ((Set.range ((↑) : Fin k → ℕ))ᶜ : Set ℕ) :=
    Denumerable.ofEncodableOfInfinite _
  haveI : Denumerable ((Set.range g)ᶜ : Set ℕ) := Denumerable.ofEncodableOfInfinite _
  obtain ⟨σ, hσ⟩ := (Equiv.Set.compl e₀).symm
    ((Denumerable.eqv _).trans (Denumerable.eqv _).symm)
  refine ⟨σ, fun a => ?_⟩
  have h := hσ ⟨(↑a : ℕ), ⟨a, rfl⟩⟩
  rw [h]
  have h1 : (Equiv.ofInjective _ Fin.val_injective).symm ⟨(↑a : ℕ), ⟨a, rfl⟩⟩ = a := by
    rw [Equiv.symm_apply_eq]; rfl
  show ((Equiv.ofInjective g g.injective)
    ((Equiv.ofInjective _ Fin.val_injective).symm ⟨(↑a : ℕ), ⟨a, rfl⟩⟩) : ℕ) = g a
  rw [h1]; rfl

/-- **A probability law on the infinite structure space invariant under every sortwise
permutation of `ℕ`.** -/
@[ext] structure InfiniteRelExchangeableLaw (S : RelSignature) where
  /-- The law on the infinite structure space. -/
  law : ProbabilityMeasure (RelStructure S (Vinfinite S))
  /-- Invariance under every sortwise relabelling. -/
  exchangeable : ∀ σ : ∀ _ : S.Srt, Equiv.Perm ℕ,
    (law : Measure (RelStructure S (Vinfinite S))).map (RelStructure.relabel σ) = law

namespace RelExchangeableLaw

variable [Fintype S.Srt] [Countable S.Rel] (L : RelExchangeableLaw S)

/-- **The arbitrary-injection marginal theorem**: for any sortwise injection into `ℕ`, the
pushforward of the infinite law is the finite marginal (each finite range factors through a
large enough diagonal size vector). -/
theorem infiniteLaw_map_restrict {n : S.Srt → ℕ} (e : ∀ s, Fin (n s) ↪ ℕ) :
    (L.infiniteLaw : Measure (RelStructure S (Vinfinite S))).map (RelStructure.restrict e) =
      (L.marginal n : Measure (RelStructure S (Vfinite n))) := by
  classical
  set N := (Finset.univ.sup fun p : Σ s : S.Srt, Fin (n s) => e p.1 p.2) + 1 with hN
  have hlt : ∀ s (i : Fin (n s)), e s i < N := fun s i =>
    Nat.lt_succ_of_le (Finset.le_sup
      (f := fun p : Σ s : S.Srt, Fin (n s) => e p.1 p.2) (Finset.mem_univ ⟨s, i⟩))
  let e' : ∀ s, Fin (n s) ↪ Fin N := fun s =>
    ⟨fun i => ⟨e s i, hlt s i⟩, fun i j h => (e s).injective (by simpa using h)⟩
  have hcomp : RelStructure.restrict e
      = RelStructure.restrict e' ∘ RelStructure.restrictFin (fun _ => N) := by
    show RelStructure.comap (fun s => (e s : Fin (n s) → ℕ)) = _
    rfl
  rw [hcomp, ← Measure.map_map (measurable_restrict e') (measurable_restrictFin (fun _ => N)),
    L.infiniteLaw_map_restrictFin, L.consistent e']

/-- **Exchangeability of the infinite law**: it is invariant under every sortwise permutation
of `ℕ`. Each finite restriction of the relabelled law is a restriction along an injection
into `ℕ`, identified with the marginal by `infiniteLaw_map_restrict`; uniqueness concludes. -/
theorem infiniteLaw_map_relabel (σ : ∀ _ : S.Srt, Equiv.Perm ℕ) :
    (L.infiniteLaw : Measure (RelStructure S (Vinfinite S))).map (RelStructure.relabel σ) =
      (L.infiniteLaw : Measure (RelStructure S (Vinfinite S))) := by
  refine RelStructure.ext_of_map_restrictFin (fun n => ?_)
  rw [Measure.map_map (measurable_restrictFin n) (measurable_relabel σ),
    show RelStructure.restrictFin n ∘ RelStructure.relabel σ =
        RelStructure.restrict (fun s =>
          (Fin.valEmbedding : Fin (n s) ↪ ℕ).trans (σ s).toEmbedding) from rfl,
    L.infiniteLaw_map_restrict, L.infiniteLaw_map_restrictFin]

/-- **The forward map**: the infinite exchangeable relational law of an exchangeable law. -/
noncomputable def toInfinite : InfiniteRelExchangeableLaw S where
  law := L.infiniteLaw
  exchangeable := L.infiniteLaw_map_relabel

@[simp] theorem toInfinite_law_map_restrictFin (n : S.Srt → ℕ) :
    (L.toInfinite.law : Measure (RelStructure S (Vinfinite S))).map (RelStructure.restrictFin n) =
      (L.marginal n : Measure (RelStructure S (Vfinite n))) :=
  L.infiniteLaw_map_restrictFin n

end RelExchangeableLaw

namespace InfiniteRelExchangeableLaw

variable [Fintype S.Srt] [Countable S.Rel] (M : InfiniteRelExchangeableLaw S)

/-- The finite `n`-marginal of an infinite exchangeable law. -/
noncomputable def marginal (n : S.Srt → ℕ) : ProbabilityMeasure (RelStructure S (Vfinite n)) :=
  ⟨(M.law : Measure (RelStructure S (Vinfinite S))).map (RelStructure.restrictFin n),
    Measure.isProbabilityMeasure_map (measurable_restrictFin n).aemeasurable⟩

omit [Fintype S.Srt] [Countable S.Rel] in
@[simp] theorem marginal_coe (n : S.Srt → ℕ) :
    (M.marginal n : Measure (RelStructure S (Vfinite n))) =
      (M.law : Measure (RelStructure S (Vinfinite S))).map (RelStructure.restrictFin n) := rfl

/-- **The reverse map**: the finite marginals of an exchangeable infinite law form an
exchangeable law. Consistency under a sortwise injection follows from exchangeability: the
injection extends (per sort) to a permutation of `ℕ`, and invariance under it identifies the
restricted marginal. -/
noncomputable def toFinite : RelExchangeableLaw S where
  marginal := M.marginal
  consistent := by
    classical
    intro n m e
    show ((M.law : Measure (RelStructure S (Vinfinite S))).map (RelStructure.restrictFin m)).map
        (RelStructure.restrict e) =
      (M.law : Measure (RelStructure S (Vinfinite S))).map (RelStructure.restrictFin n)
    choose σ hσ using fun s => exists_perm_extend
      ((e s).trans (Fin.valEmbedding : Fin (m s) ↪ ℕ))
    have hkey : RelStructure.restrict (fun s => (Fin.valEmbedding : Fin (n s) ↪ ℕ))
        ∘ RelStructure.relabel σ
        = RelStructure.restrict (fun s => (e s).trans (Fin.valEmbedding : Fin (m s) ↪ ℕ)) := by
      show RelStructure.comap (fun s => (fun a : ℕ => σ s a) ∘ (Fin.val : Fin (n s) → ℕ))
        = RelStructure.comap _
      congr 1; funext s x; exact hσ s x
    rw [Measure.map_map (measurable_restrict e) (measurable_restrictFin m),
      show RelStructure.restrict e ∘ RelStructure.restrictFin m
        = RelStructure.restrict (fun s => (e s).trans (Fin.valEmbedding : Fin (m s) ↪ ℕ)) from rfl,
      ← hkey, ← Measure.map_map
        (measurable_restrict (fun s => (Fin.valEmbedding : Fin (n s) ↪ ℕ))) (measurable_relabel σ),
      M.exchangeable σ]
    rfl

end InfiniteRelExchangeableLaw

/-- **The finite/infinite exchangeable relational law equivalence** (R2c): exchangeable
size-vector marginal families correspond exactly to probability laws on the infinite
structure space invariant under sortwise relabelling. -/
noncomputable def relExchangeableLawEquiv [Fintype S.Srt] [Countable S.Rel] :
    RelExchangeableLaw S ≃ InfiniteRelExchangeableLaw S where
  toFun := RelExchangeableLaw.toInfinite
  invFun := InfiniteRelExchangeableLaw.toFinite
  left_inv L := by
    apply RelExchangeableLaw.ext
    funext n
    apply ProbabilityMeasure.toMeasure_injective
    exact L.infiniteLaw_map_restrictFin n
  right_inv M := by
    apply InfiniteRelExchangeableLaw.ext
    apply ProbabilityMeasure.toMeasure_injective
    refine RelStructure.ext_of_map_restrictFin (fun n => ?_)
    exact M.toFinite.infiniteLaw_map_restrictFin n

end RelSignature
