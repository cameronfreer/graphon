/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Denumerable
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Fintype.Card

/-!
# Extending a finite injection into `ℕ` to a permutation

A small graph-independent lemma, reused by both the graph exchangeability API
(`Graphon.InfiniteGraph.exists_perm_extend`) and the generic relational one
(AHK R2c). A candidate for upstreaming to Mathlib.
-/

/-- **Every injection `Fin k ↪ ℕ` extends to a permutation of `ℕ`**: the ranges are finite so
their complements are countably infinite, hence equivalent, and `Equiv.Set.compl` assembles
the permutation. -/
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

/-- **Every finite partial injection of `ℕ` extends to a permutation**: the domain and its image
are finite, so their complements are countably infinite and hence equivalent, and
`Equiv.Set.compl` assembles the permutation. Generalizes `exists_perm_extend` from an initial
segment to an arbitrary finite domain. -/
theorem exists_perm_extend_of_injOn {A : Finset ℕ} {g : ℕ → ℕ} (hg : Set.InjOn g ↑A) :
    ∃ σ : Equiv.Perm ℕ, ∀ a ∈ A, σ a = g a := by
  classical
  let e₀ : (↑A : Set ℕ) ≃ (g '' ↑A : Set ℕ) := Equiv.Set.imageOfInjOn g (↑A : Set ℕ) hg
  have hsc : ((↑A : Set ℕ)ᶜ).Infinite := (A.finite_toSet).infinite_compl
  have htc : ((g '' ↑A : Set ℕ)ᶜ).Infinite :=
    ((A.finite_toSet).image g).infinite_compl
  haveI := hsc.to_subtype
  haveI := htc.to_subtype
  haveI : Denumerable ((↑A : Set ℕ)ᶜ : Set ℕ) := Denumerable.ofEncodableOfInfinite _
  haveI : Denumerable ((g '' ↑A : Set ℕ)ᶜ : Set ℕ) := Denumerable.ofEncodableOfInfinite _
  obtain ⟨σ, hσ⟩ := (Equiv.Set.compl e₀).symm
    ((Denumerable.eqv _).trans (Denumerable.eqv _).symm)
  refine ⟨σ, fun a ha => ?_⟩
  have h := hσ ⟨a, ha⟩
  rw [h]
  rfl
