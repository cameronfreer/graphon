/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelationalTopology
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Exchangeable relational laws: size-vector marginals and consistency (AHK umbrella #103, R2a)

The finite-marginal layer of the generic exchangeable-law theory (issue #105). A generic
exchangeable law is given by a **size-vector-indexed family of probability marginals** that
is **consistent under arbitrary sortwise injections** — the multi-sorted, arbitrary-arity
analogue of `Graphon.ExchangeableGraphLaw`.

Crucially the finite marginals are `ProbabilityMeasure (RelStructure S (Vfinite n))`, **not
`PMF`**: with countably many relation symbols a finite vertex carrier still has infinitely
many Boolean coordinates, so `RelStructure S (Vfinite n)` can be an (uncountable) standard-Borel
space and the law can be non-atomic. (D2 recovers `PMF`s in the finite-signature case.)

* `RelSignature.exists_const_ge` — because `S.Srt` is finite, the **diagonal** size vectors
  are cofinal (every size vector is bounded by a constant one);
* `RelSignature.RelExchangeableLaw` — the structure: probability marginals + arbitrary
  sortwise-injection consistency;
* `RelExchangeableLaw.marginal_map_restrictLE` / `marginal_map_perm` — consistency under the
  standard size-vector inclusion, and finite exchangeability (permutation invariance) of the
  marginals, both special cases.

The compactness-based extension to an infinite law is **R2b**; uniqueness (via
`ext_of_map_restrictFin`) and the finite/infinite equivalence are **R2c**.
-/

open MeasureTheory

namespace RelSignature

variable {S : RelSignature}

/-- **Diagonal cofinality**: since `S.Srt` is finite, every size vector is bounded above by
a constant (diagonal) size vector — so diagonal marginals suffice for the extension. -/
theorem exists_const_ge [Fintype S.Srt] (n : S.Srt → ℕ) : ∃ N : ℕ, ∀ s, n s ≤ N :=
  ⟨Finset.univ.sup n, fun s => Finset.le_sup (Finset.mem_univ s)⟩

/-- **An exchangeable relational law**: a size-vector-indexed family of probability marginals
on the finite structure spaces, consistent under every **sortwise injection**
`∀ s, Fin (n s) ↪ Fin (m s)` (the `m`-marginal restricts to the `n`-marginal). -/
structure RelExchangeableLaw (S : RelSignature) where
  /-- The probability marginal on structures over the size vector `n`. -/
  marginal : (n : S.Srt → ℕ) → ProbabilityMeasure (RelStructure S (Vfinite n))
  /-- Consistency under every sortwise injection. -/
  consistent : ∀ {n m : S.Srt → ℕ} (e : ∀ s, Fin (n s) ↪ Fin (m s)),
    (marginal m : Measure (RelStructure S (Vfinite m))).map (RelStructure.restrict e) =
      (marginal n : Measure (RelStructure S (Vfinite n)))

namespace RelExchangeableLaw

variable (L : RelExchangeableLaw S)

/-- **Consistency under the standard size-vector inclusion** `n ≤ m`. -/
theorem marginal_map_restrictLE {n m : S.Srt → ℕ} (h : ∀ s, n s ≤ m s) :
    (L.marginal m : Measure (RelStructure S (Vfinite m))).map (RelStructure.restrictLE h) =
      (L.marginal n : Measure (RelStructure S (Vfinite n))) :=
  L.consistent fun s => Fin.castLEEmb (h s)

/-- **Finite exchangeability**: each marginal is invariant under the sortwise permutations of
its finite vertex sets — the special case `n = m`, `e` a permutation. -/
theorem marginal_map_perm {n : S.Srt → ℕ} (σ : ∀ s, Equiv.Perm (Fin (n s))) :
    (L.marginal n : Measure (RelStructure S (Vfinite n))).map (RelStructure.relabel σ) =
      (L.marginal n : Measure (RelStructure S (Vfinite n))) := by
  simpa [RelStructure.relabel, RelStructure.restrict] using
    L.consistent (fun s => (σ s).toEmbedding)

end RelExchangeableLaw

end RelSignature
