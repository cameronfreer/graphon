/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelLowerFactor
import Graphon.RelRankRepresentation
import Graphon.RelSingletonPeel

/-!
# Rank-one local recovery (R4 converse piece 3, #107)

The `lower_recovers` field of a rank-one `RankRepresentation`: the block strictly below rank one
— the **nullary block**, at support `∅` — is almost everywhere a measurable function of the
latents visible at `∅`.

The argument is coordinatewise and countable. Each nullary relation coordinate is an event of
`fixingAlgebra ∅ = invariantAlgebra`; the eventwise generation of the rank-one factor
(`exists_comap_lowerFactorMap_one_ae_eq`, #157) supplies, per coordinate, a factor event agreeing
with it modulo the law; a `decide`-indicator coding turns the chosen factor events into a
measurable map `LowerFactorSpace 1 → BlockSpace ∅`; and the resolution identity of the coupling
replaces the factor read of the structure by the latent read. Countably many null coordinate
disagreements combine by `ae_all_iff`, and the latent read factors *exactly* through
`localLatents ∅ 1`, which at rank one is a bijective reindexing.

Stated over an abstract coupling with the two clauses it consumes — the structure marginal and
the resolution identity — rather than over `rankOneLatentCoupling` itself, so the final assembly
passes the clauses it destructured. Everything is modulo the coupling measure: no claim is made
that the nullary block is a strict function of the latent, and none is available.
-/

open MeasureTheory ProbabilityTheory

namespace RelSignature

namespace CoherentBasis

universe u

variable {S : RelSignature.{u}} {M : InfiniteRelExchangeableLaw S} (B : CoherentBasis M)

open scoped Classical in
/-- **Rank-one local recovery.** Under any coupling of the law with the rank-one latents whose
structure marginal is the law and which resolves the rank-one factor through a measurable latent
read, every block of rank strictly below one — the nullary block — is almost everywhere a
measurable function of the latents visible at its own support. -/
theorem exists_blockMap_recovery_of_card_lt_one [Countable S.Srt] [Countable S.Rel]
    {P : Measure (RelStructure S (Vinfinite S) × RankLatentSpace S 1)}
    (hfst : P.map Prod.fst = (M.law : Measure (RelStructure S (Vinfinite S))))
    {g : RankLatentSpace S 1 → B.LowerFactorSpace 1} (hg : Measurable g)
    (hres : B.lowerFactorMap 1 ∘ Prod.fst =ᵐ[P] g ∘ Prod.snd)
    (A : Finset (Σ s : S.Srt, Vinfinite S s)) (hA : A.card < 1) :
    ∃ g₀ : LocalLatentSpace A 1 → BlockSpace A, Measurable g₀ ∧
      blockMap A ∘ Prod.fst =ᵐ[P] g₀ ∘ localLatents A 1 ∘ Prod.snd := by
  classical
  haveI : IsProbabilityMeasure (M.law : Measure (RelStructure S (Vinfinite S))) := M.law.2
  obtain rfl : A = ∅ := Finset.card_eq_zero.mp (Nat.lt_one_iff.mp hA)
  -- each nullary coordinate is an invariant event
  have hEmeas : ∀ c : BlockIndex (∅ : Finset (Σ s : S.Srt, Vinfinite S s)),
      MeasurableSet[RelStructure.invariantAlgebra]
        ((fun X : RelStructure S (Vinfinite S) => blockMap ∅ X c) ⁻¹' {true}) := by
    intro c
    have hb := measurable_blockMap_fixingAlgebra (S := S)
      (∅ : Finset (Σ s : S.Srt, Vinfinite S s))
    rw [RelStructure.fixingAlgebra_empty] at hb
    exact ((measurable_pi_apply c).comp hb) (measurableSet_singleton true)
  -- choose a factor event representing each coordinate modulo the law
  have hrep : ∀ c : BlockIndex (∅ : Finset (Σ s : S.Srt, Vinfinite S s)),
      ∃ D : Set (B.LowerFactorSpace 1), MeasurableSet D ∧
        B.lowerFactorMap 1 ⁻¹' D =ᵐ[(M.law : Measure (RelStructure S (Vinfinite S)))]
          (fun X : RelStructure S (Vinfinite S) => blockMap ∅ X c) ⁻¹' {true} := by
    intro c
    obtain ⟨E', hE'meas, hE'ae⟩ := B.exists_comap_lowerFactorMap_one_ae_eq (hEmeas c)
    obtain ⟨D, hD, rfl⟩ := hE'meas
    exact ⟨D, hD, hE'ae⟩
  choose D hDmeas hDae using hrep
  -- the coding of the factor space by the chosen events
  set φ : B.LowerFactorSpace 1 → BlockSpace (∅ : Finset (Σ s : S.Srt, Vinfinite S s)) :=
    fun y c => decide (y ∈ D c) with hφdef
  have hφmeas : Measurable φ := by
    refine measurable_pi_lambda _ fun c => measurable_to_bool ?_
    convert hDmeas c using 1
    ext y
    simp [hφdef]
  -- the exact reindexing through the local latents at `∅`
  have hsub : ∀ Bi : RankLatentIndex S 1,
      Bi.1 ⊆ (∅ : Finset (Σ s : S.Srt, Vinfinite S s)) := fun Bi => by
    rw [Finset.card_eq_zero.mp (Nat.lt_one_iff.mp Bi.2)]
  set ρ : LocalLatentSpace (∅ : Finset (Σ s : S.Srt, Vinfinite S s)) 1 → RankLatentSpace S 1 :=
    fun ω Bi => ω ⟨Bi, hsub Bi⟩ with hρdef
  have hρmeas : Measurable ρ := measurable_pi_lambda _ fun _ => measurable_pi_apply _
  refine ⟨φ ∘ g ∘ ρ, hφmeas.comp (hg.comp hρmeas), ?_⟩
  -- coordinatewise agreement under the law, transported along `fst`
  have hqmp : Measure.QuasiMeasurePreserving Prod.fst P
      (M.law : Measure (RelStructure S (Vinfinite S))) :=
    (⟨measurable_fst, hfst⟩ : MeasurePreserving Prod.fst P _).quasiMeasurePreserving
  have hall : ∀ᵐ p ∂P, ∀ c : BlockIndex (∅ : Finset (Σ s : S.Srt, Vinfinite S s)),
      blockMap ∅ p.1 c = φ (B.lowerFactorMap 1 p.1) c := by
    rw [ae_all_iff]
    intro c
    have hae : ∀ᵐ X ∂(M.law : Measure (RelStructure S (Vinfinite S))),
        blockMap ∅ X c = φ (B.lowerFactorMap 1 X) c := by
      filter_upwards [Filter.eventuallyEq_set.mp (hDae c)] with X hX
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hX
      by_cases hb : blockMap ∅ X c = true
      · simp [hφdef, hb, hX.mpr hb]
      · rw [Bool.not_eq_true] at hb
        have hmem : B.lowerFactorMap 1 X ∉ D c := fun hm => by
          rw [hX.mp hm] at hb
          exact Bool.true_eq_false.mp hb
        simp [hφdef, hb, hmem]
    exact hqmp.tendsto_ae.eventually hae
  filter_upwards [hall, hres] with p hp hpres
  funext c
  show blockMap ∅ p.1 c = φ (g (ρ (localLatents ∅ 1 p.2))) c
  rw [show ρ (localLatents (∅ : Finset (Σ s : S.Srt, Vinfinite S s)) 1 p.2) = p.2 from rfl,
    hp c, show B.lowerFactorMap 1 p.1 = g p.2 from hpres]

end CoherentBasis

end RelSignature
