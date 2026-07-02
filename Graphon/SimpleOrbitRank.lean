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

/-! ### The annihilator lemma (chunk 5B)

Any `c : OrbitClass → ℝ` that annihilates every simple evaluation at orbit representatives is
zero. This is STRICTLY stronger than point-separation of the orbit classes (distinct rows can
still be linearly dependent); the signed single-family Vandermonde over
`OrbitClass × (Fin m → Fin T)` does the real work, powered by the Cai–Govorov descent
ingredients (`sum_extensions_eval`, `expTestGraph`, `testEvalEq_implies_orbit_super`). -/

/-- Reindexing the test-moment power product along `Fintype.equivFin` (profile form). -/
private theorem prod_profile_pow {T L : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (μ : Fin L → Fin T) (k : Fin (Fintype.card (TestCoord L)) → ℕ) :
    ∏ c : TestCoord L, (testMoment B W c μ) ^ k (Fintype.equivFin (TestCoord L) c)
      = ∏ c, (testProfile B W μ c) ^ k c := by
  calc ∏ c : TestCoord L, (testMoment B W c μ) ^ k (Fintype.equivFin (TestCoord L) c)
      = ∏ c : TestCoord L, (testProfile B W μ (Fintype.equivFin (TestCoord L) c))
          ^ k (Fintype.equivFin (TestCoord L) c) := by
        refine Finset.prod_congr rfl fun c _ => ?_
        congr 1
        show testMoment B W c μ
          = testMoment B W ((Fintype.equivFin (TestCoord L)).symm
              (Fintype.equivFin (TestCoord L) c)) μ
        rw [Equiv.symm_apply_apply]
    _ = ∏ c, (testProfile B W μ c) ^ k c :=
        Equiv.prod_comp (Fintype.equivFin (TestCoord L))
          (fun c => (testProfile B W μ c) ^ k c)

/-- **The annihilator lemma.** If `∑ q, c q · simpleEvalAt F (out q) = 0` for every simple
graph `F`, then `c = 0`. Signed Vandermonde over `OrbitClass × (Fin m → Fin T)` with the
test-moment profile of `Fin.append (out q) ρ` as classifier: the class of the profile of
`superExt (out q₀)` consists exactly of pairs `(q₀, ρ)` (chunk 4A at level `K + m` forces
`q = q₀`), and its `W`-mass is positive, so the class-sum `c q₀ · (positive) = 0` kills
`c q₀`. -/
theorem eval_rep_annihilator_zero {T K : ℕ} (B : Fin T → Fin T → ℝ)
    (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ) (hW : ∀ i, 0 < W i)
    (htwin : ∀ i j, i ≠ j → B i ≠ B j) (c : OrbitClass T K B W → ℝ)
    (hc : ∀ (n : ℕ) (F : SimpleGraph (Fin (n + K))) (inst : DecidableRel F.Adj),
      ∑ q, c q * @simpleEvalAt T K n B W F inst (Quotient.out q) = 0) :
    c = 0 := by
  classical
  funext q₀
  show c q₀ = 0
  -- ρ-form of the extension-sum collapse (eq. (10), one side).
  have hρsum : ∀ (n : ℕ) (G : SimpleGraph (Fin (n + (K + T * (2 * T ^ 2)))))
      (_ : DecidableRel G.Adj) (ζ : Fin K → Fin T),
      ∑ ρ : Fin (T * (2 * T ^ 2)) → Fin T,
          (∏ j, W (ρ j)) * simpleEvalAt B W G (Fin.append ζ ρ)
        = simpleEvalAt B W (unlabelExtras G) ζ := fun n G _ ζ =>
    (sum_extensions_eq_sum_rho B W G ζ).symm.trans (sum_extensions_eval B hB W G ζ)
  -- Moment vanishing for the signed family over `OrbitClass × (Fin m → Fin T)`.
  have hmom : ∀ ℓ : Fin (Fintype.card (TestCoord (K + T * (2 * T ^ 2)))) → ℕ,
      (∀ j, ℓ j < Fintype.card (OrbitClass T K B W × (Fin (T * (2 * T ^ 2)) → Fin T))) →
      ∑ i : OrbitClass T K B W × (Fin (T * (2 * T ^ 2)) → Fin T),
          (c i.1 * ∏ j, W (i.2 j))
            * ∏ j, (testProfile B W (Fin.append (Quotient.out i.1) i.2) j) ^ ℓ j = 0 := by
    intro ℓ _
    rw [Fintype.sum_prod_type]
    have hterm : ∀ q : OrbitClass T K B W,
        ∑ ρ : Fin (T * (2 * T ^ 2)) → Fin T,
            (c q * ∏ j, W (ρ j))
              * ∏ j, (testProfile B W (Fin.append (Quotient.out q) ρ) j) ^ ℓ j
          = c q * simpleEvalAt B W
              (unlabelExtras (expTestGraph
                (fun c' => ℓ (Fintype.equivFin (TestCoord (K + T * (2 * T ^ 2))) c'))))
              (Quotient.out q) := by
      intro q
      rw [← hρsum _ (expTestGraph
          (fun c' => ℓ (Fintype.equivFin (TestCoord (K + T * (2 * T ^ 2))) c')))
        inferInstance (Quotient.out q), Finset.mul_sum]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      rw [simpleEvalAt_expTestGraph B hB W _ (Fin.append (Quotient.out q) ρ),
        prod_profile_pow B W (Fin.append (Quotient.out q) ρ) ℓ]
      ring
    rw [Finset.sum_congr rfl fun q _ => hterm q]
    exact hc _ _ inferInstance
  -- Class-sum at the profile of `superExt (out q₀)`.
  have hclass := CaiGovorov.multivariate_vandermonde_class_sums_zero
    (fun i : OrbitClass T K B W × (Fin (T * (2 * T ^ 2)) → Fin T) =>
      testProfile B W (Fin.append (Quotient.out i.1) i.2))
    (fun i => c i.1 * ∏ j, W (i.2 j)) hmom
    (testProfile B W (superExt (Quotient.out q₀)))
  -- The class forces `q = q₀` (chunk 4A at level K + m).
  have hq_eq : ∀ (q : OrbitClass T K B W) (ρ : Fin (T * (2 * T ^ 2)) → Fin T),
      testProfile B W (Fin.append (Quotient.out q) ρ)
        = testProfile B W (superExt (Quotient.out q₀)) → q = q₀ := by
    intro q ρ hprof
    have hTE : TestEvalEq B W (superExt (Quotient.out q₀)) (Fin.append (Quotient.out q) ρ) :=
      (testEvalEq_iff_moments B hB W).mpr fun c' => (testProfile_eq_iff.mp hprof c').symm
    obtain ⟨σ, hσ_aut, hσ⟩ := testEvalEq_implies_orbit_super B hB W hW htwin _ _
      (superExt_superSurjective (Quotient.out q₀)) hTE
    have horb : tupleOrbitRel B W (Quotient.out q₀) (Quotient.out q) := by
      refine ⟨σ, hσ_aut, fun i => ?_⟩
      have hi := hσ (Fin.castAdd (T * (2 * T ^ 2)) i)
      rw [Fin.append_left, superExt_extends (Quotient.out q₀) i] at hi
      exact hi
    have hmk : Quotient.mk (tupleOrbitSetoid B W K) (Quotient.out q₀)
        = Quotient.mk (tupleOrbitSetoid B W K) (Quotient.out q) := Quotient.sound horb
    rw [Quotient.out_eq, Quotient.out_eq] at hmk
    exact hmk.symm
  -- The class is exactly `{q₀} ×ˢ P` for the ρ-side class `P`.
  have hfilter_eq : (univ.filter
      (fun i : OrbitClass T K B W × (Fin (T * (2 * T ^ 2)) → Fin T) =>
        testProfile B W (Fin.append (Quotient.out i.1) i.2)
          = testProfile B W (superExt (Quotient.out q₀))))
      = {q₀} ×ˢ (univ.filter (fun ρ : Fin (T * (2 * T ^ 2)) → Fin T =>
          testProfile B W (Fin.append (Quotient.out q₀) ρ)
            = testProfile B W (superExt (Quotient.out q₀)))) := by
    ext ⟨q, ρ⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      Finset.mem_singleton]
    constructor
    · intro hprof
      obtain rfl := hq_eq q ρ hprof
      exact ⟨rfl, hprof⟩
    · rintro ⟨rfl, hprof⟩
      exact hprof
  -- Collapse the class-sum to `c q₀ · (positive W-mass)`.
  have hmass : c q₀ * ∑ ρ ∈ univ.filter (fun ρ : Fin (T * (2 * T ^ 2)) → Fin T =>
      testProfile B W (Fin.append (Quotient.out q₀) ρ)
        = testProfile B W (superExt (Quotient.out q₀))), ∏ j, W (ρ j) = 0 := by
    rw [Finset.mul_sum, ← hclass, hfilter_eq, Finset.sum_product, Finset.sum_singleton]
  have hpos : (0 : ℝ) < ∑ ρ ∈ univ.filter (fun ρ : Fin (T * (2 * T ^ 2)) → Fin T =>
      testProfile B W (Fin.append (Quotient.out q₀) ρ)
        = testProfile B W (superExt (Quotient.out q₀))), ∏ j, W (ρ j) :=
    Finset.sum_pos (fun ρ _ => Finset.prod_pos fun j _ => hW _)
      ⟨coverExtra T, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  exact (mul_eq_zero.mp hmass).resolve_right (ne_of_gt hpos)

/-! ### The dual-pairing endgame (chunk 5C)

The representative pairing turns the annihilator lemma into injectivity of a map into the
dual of `simpleEvalSubmodule`; comparing dimensions gives the lower bound. Transcribes the
`hle1` half of `connectionMatrix_full_rank_of_orthogonal` (`Spectral.lean`). -/

/-- The representative pairing `⟨c, f⟩ := ∑ q, c q · f (Quotient.out q)` as a bilinear map
(mirrors `orbitInnerBil`). -/
noncomputable def evalRepPairing {T K : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ) :
    (OrbitClass T K B W → ℝ) →ₗ[ℝ] ((Fin K → Fin T) → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun c f => ∑ q, c q * f (Quotient.out q))
    (fun c₁ c₂ f => by
      simp only [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [Pi.add_apply]; ring)
    (fun r c f => by
      simp only [Finset.smul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (fun c f₁ f₂ => by
      simp only [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [Pi.add_apply]; ring)
    (fun r c f => by
      simp only [Finset.smul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]; ring)

@[simp] lemma evalRepPairing_apply {T K : ℕ} (B : Fin T → Fin T → ℝ) (W : Fin T → ℝ)
    (c : OrbitClass T K B W → ℝ) (f : (Fin K → Fin T) → ℝ) :
    evalRepPairing B W c f = ∑ q, c q * f (Quotient.out q) := rfl

/-- **The simple-side lower bound** (the genuine Lovász §3 content, formerly the sole #70
residue): the simple-eval span has dimension at least the number of orbit classes. The
composite `Ψ := subtype.dualMap ∘ evalRepPairing` is injective by the annihilator lemma, so
`#OrbitClass = finrank (OrbitClass → ℝ) ≤ finrank (Dual simpleEvalSubmodule)
= finrank simpleEvalSubmodule`. -/
theorem simpleEvalSubmodule_finrank_ge_orbitClass {T K : ℕ}
    (B : Fin T → Fin T → ℝ) (hB : ∀ i j, B i j = B j i) (W : Fin T → ℝ)
    (hW : ∀ i, 0 < W i) (htwin : ∀ i j, i ≠ j → B i ≠ B j) :
    Fintype.card (OrbitClass T K B W) ≤ Module.finrank ℝ (simpleEvalSubmodule B W K) := by
  classical
  set Ψ : (OrbitClass T K B W → ℝ) →ₗ[ℝ] Module.Dual ℝ (simpleEvalSubmodule B W K) :=
    (simpleEvalSubmodule B W K).subtype.dualMap ∘ₗ evalRepPairing B W with hΨ
  have hΨinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hcker
    refine eval_rep_annihilator_zero B hB W hW htwin c fun n F inst => ?_
    have hgen := LinearMap.congr_fun hcker
      (⟨fun ξ => @simpleEvalAt T K n B W F inst ξ,
        Submodule.subset_span ⟨⟨n, F, inst⟩, rfl⟩⟩ : simpleEvalSubmodule B W K)
    simpa only [hΨ, LinearMap.comp_apply, LinearMap.dualMap_apply, Submodule.subtype_apply,
      evalRepPairing_apply, LinearMap.zero_apply] using hgen
  have h1 : Module.finrank ℝ (OrbitClass T K B W → ℝ)
      ≤ Module.finrank ℝ (Module.Dual ℝ (simpleEvalSubmodule B W K)) :=
    LinearMap.finrank_le_finrank_of_injective hΨinj
  rw [Subspace.dual_finrank_eq] at h1
  rw [← Module.finrank_pi (ι := OrbitClass T K B W) ℝ]
  exact h1

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
