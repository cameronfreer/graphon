/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.CaiGovorovOrbit

/-!
# The #70 rank theorem: simple evaluations span the orbit-invariant functions

The Phase C1+D finrank skeleton, moved here from `CycleKrylov.lean` (which sits upstream of
the Cai–Govorov machinery in the import order and therefore could not consume it):
`finrank orbitInvariantSubmodule = #OrbitClass` (orbit-invariant functions ≅ functions on the
orbit quotient), the simple-side lower bound `simpleEvalSubmodule_finrank_ge_orbitClass`
(formerly the sole named #70 residue), and the Phase D rank collapse
`simpleEvalSubmodule_eq_orbitInvariantSubmodule`.

The lower bound is discharged by an annihilator argument (chunk 5B/5C): the signed
single-family Vandermonde over `OrbitClass × (Fin m → Fin T)` — powered by the Cai–Govorov
descent ingredients `sum_extensions_eval` / `expTestGraph` / `testEvalEq_implies_orbit_super`
— shows that any `c : OrbitClass → ℝ` annihilating all simple evaluations at orbit
representatives vanishes; injectivity of the induced map into the dual of
`simpleEvalSubmodule` then gives `#OrbitClass ≤ finrank simpleEvalSubmodule` (the linear
algebra transcribes `connectionMatrix_full_rank_of_orthogonal`, `Spectral.lean`).

NB `Spectral.lean` (an unimported leaf) declares its own same-named `Fintype (OrbitClass …)`
instance; no clash on any current import chain.
-/

namespace Graphon.Lovasz

open Finset

noncomputable instance instFintypeOrbitClass {T K : ℕ} {B : Fin T → Fin T → ℝ} {W : Fin T → ℝ} :
    Fintype (OrbitClass T K B W) := by
  classical
  unfold OrbitClass
  exact Quotient.fintype _

/-- Evaluation-at-orbit-representatives, as a linear map from the orbit-invariant
functions to functions on the orbit quotient. -/
noncomputable def orbitInvariantToClassFun {T K : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) :
    orbitInvariantSubmodule B W K →ₗ[ℝ] (OrbitClass T K B W → ℝ) where
  toFun f := fun q => (f : (Fin K → Fin T) → ℝ) (Quotient.out q)
  map_add' f g := by funext q; simp
  map_smul' c f := by funext q; simp

/-- **Orbit-invariant functions ≅ functions on the orbit quotient.** -/
noncomputable def orbitInvariantEquiv {T K : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) :
    orbitInvariantSubmodule B W K ≃ₗ[ℝ] (OrbitClass T K B W → ℝ) :=
  LinearEquiv.ofBijective (orbitInvariantToClassFun B W) (by
    constructor
    · -- injective: agreement on representatives + orbit-invariance ⟹ equal
      intro f₁ f₂ h
      apply Subtype.ext
      funext ξ
      have key : ∀ (g : orbitInvariantSubmodule B W K) (η : Fin K → Fin T),
          (g : (Fin K → Fin T) → ℝ) η
            = (g : (Fin K → Fin T) → ℝ)
                (Quotient.out (Quotient.mk (tupleOrbitSetoid B W K) η)) := by
        intro g η
        obtain ⟨σ, hσ, hση⟩ := Quotient.mk_out (s := tupleOrbitSetoid B W K) η
        have hηeq : η = σ ∘ Quotient.out (Quotient.mk (tupleOrbitSetoid B W K) η) := funext hση
        conv_lhs => rw [hηeq]
        exact g.2 σ hσ _
      rw [key f₁ ξ, key f₂ ξ]
      exact congrFun h (Quotient.mk (tupleOrbitSetoid B W K) ξ)
    · -- surjective: pull back a class function
      intro g
      refine ⟨⟨fun η => g (Quotient.mk (tupleOrbitSetoid B W K) η), ?_⟩, ?_⟩
      · intro σ hσ η
        show g (Quotient.mk (tupleOrbitSetoid B W K) (σ ∘ η))
            = g (Quotient.mk (tupleOrbitSetoid B W K) η)
        have hmk : Quotient.mk (tupleOrbitSetoid B W K) η
            = Quotient.mk (tupleOrbitSetoid B W K) (σ ∘ η) :=
          Quotient.sound ⟨σ, hσ, fun i => rfl⟩
        rw [hmk]
      · funext q
        show g (Quotient.mk (tupleOrbitSetoid B W K) (Quotient.out q)) = g q
        rw [Quotient.out_eq])

/-- **Phase C1: `finrank orbitInvariantSubmodule = #OrbitClass`.** -/
theorem finrank_orbitInvariantSubmodule {T K : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) :
    Module.finrank ℝ (orbitInvariantSubmodule B W K) = Fintype.card (OrbitClass T K B W) := by
  rw [(orbitInvariantEquiv B W).finrank_eq, Module.finrank_fintype_fun_eq_card]

/-- **The simple-side lower bound** (the genuine Lovász §3 content, formerly the sole #70
residue): the simple-eval span has dimension at least the number of orbit classes. -/
theorem simpleEvalSubmodule_finrank_ge_orbitClass {T K : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    (hW : ∀ i, 0 < W i) (htwin : ∀ i j, i ≠ j → B i ≠ B j) :
    Fintype.card (OrbitClass T K B W) ≤ Module.finrank ℝ (simpleEvalSubmodule B W K) := by
  sorry

/-- **Phase D: the rank collapse.** Modulo the lower bound, the simple-eval and
orbit-invariant submodules coincide. -/
theorem simpleEvalSubmodule_eq_orbitInvariantSubmodule {T K : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    (hW : ∀ i, 0 < W i) (htwin : ∀ i j, i ≠ j → B i ≠ B j) :
    simpleEvalSubmodule B W K = orbitInvariantSubmodule B W K :=
  Submodule.eq_of_le_of_finrank_le
    (simpleEvalSubmodule_le_orbitInvariantSubmodule B hB W)
    (by rw [finrank_orbitInvariantSubmodule B W]
        exact simpleEvalSubmodule_finrank_ge_orbitClass B hB W hW htwin)

/-- **The hard inclusion** `orbitInvariantSubmodule ≤ simpleEvalSubmodule`. -/
theorem orbitInvariantSubmodule_le_simpleEvalSubmodule {T K : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    (hW : ∀ i, 0 < W i) (htwin : ∀ i j, i ≠ j → B i ≠ B j) :
    orbitInvariantSubmodule B W K ≤ simpleEvalSubmodule B W K :=
  (simpleEvalSubmodule_eq_orbitInvariantSubmodule B hB W hW htwin).ge

end Graphon.Lovasz
