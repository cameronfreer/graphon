/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelLawEquivalence
import Graphon.InfiniteDigraph
import Graphon.DigraphMaps
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Exchangeable directed-graph laws: the PMF-based finite API (directed umbrella #84, D2 / #86)

The directed specialization of the generic exchangeable-law theory (R2, issue #105). Because
`digraphSig` has finitely many relation symbols, a finite directed law over `Fin k` is a
genuine **probability mass function** `PMF (Digraph (Fin k))` — the conventional
combinatorial object — rather than a `ProbabilityMeasure` on the (uncountable) relational
carrier. This file provides that user-facing `PMF`-based API and bridges it to the measure-side
`RelExchangeableLaw digraphSig`, then composes with the R2c equivalence to obtain the headline
finite/infinite directed equivalence.

* `finiteDigraphEquiv_restrict` / `finiteDigraphEquiv_symm_restrict` — the finite carrier
  equivalence commutes with restriction: `Digraph.comap` on the combinatorial side matches
  `RelStructure.restrict` on the relational side (via `digraphStructureEquiv_comap`);
* `ExchangeableDigraphLaw` — the `PMF`-based finite directed law: a `PMF (Digraph (Fin k))`
  for each `k`, consistent under `Digraph.comap` along every `Fin k ↪ Fin l`;
* `digraphLawEquiv` — the finite bridge `ExchangeableDigraphLaw ≃ RelExchangeableLaw digraphSig`,
  transporting via `finiteDigraphEquiv` and the `PMF.toMeasure` / `Measure.toPMF` correspondence;
* `InfiniteExchangeableDigraphLaw` — the infinite directed law (a relabelling-invariant law on
  the infinite digraph space `InfiniteDigraph`, where the measurable structure lives);
* `exchangeableDigraphLawEquiv` — **the headline directed equivalence**
  `ExchangeableDigraphLaw ≃ InfiniteExchangeableDigraphLaw`, the composite of the finite bridge
  with the R2c relational equivalence.

The measurable / topological structure is used **only** on the relational carrier
(`InfiniteDigraph` / `FiniteDigraph`); Mathlib's `Digraph` carries no measurable-space instance.
The finite `PMF` ↔ `ProbabilityMeasure` conversions are localized to the bridge maps.
-/

open MeasureTheory RelSignature

-- The finite `PMF` ↔ `ProbabilityMeasure` conversions unfold instance-heavy product-space
-- structure on the relational carrier; give the elaborator generous headroom.
set_option maxHeartbeats 1000000

/-- **`toPMF` transports `map` to `Measure.map`** (finite-conversion helper, stated over abstract
countable spaces so that instance resolution stays cheap): the measure of the pushed-forward PMF
is the pushed-forward measure. -/
theorem MeasureTheory.toPMF_map_toMeasure {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] [MeasurableSingletonClass α] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → β) (hf : Measurable f) : (μ.toPMF.map f).toMeasure = μ.map f := by
  rw [← PMF.toMeasure_map _ _ hf, Measure.toPMF_toMeasure]

/-! ### The finite carrier equivalence commutes with restriction -/

/-- **The carrier equivalence commutes with `comap`**: pulling a relational structure back along a
constant sortwise map and then reading it as a digraph is the same as reading it as a digraph and
pulling that back. The directed analogue of `SimpleGraph.comap` naturality. -/
theorem digraphStructureEquiv_comap {V W : Type*} (f : V → W)
    (X : RelStructure digraphSig (fun _ => W)) :
    digraphStructureEquiv V (RelStructure.comap (fun _ => f) X)
      = (digraphStructureEquiv W X).comap f := by
  ext a b
  simp only [digraphStructureEquiv_adj, Digraph.comap_adj, RelStructure.comap]
  have : RelCoord.map (fun _ : Unit => f) (digraphCoord a b) = digraphCoord (f a) (f b) := by
    refine Sigma.ext rfl (heq_of_eq ?_); funext i; fin_cases i <;> rfl
  rw [this]

/-- **Restriction commutes with the finite carrier equivalence** (forward form): reading a digraph
off a relational structure and then `Digraph.comap`-ping is the same as `RelStructure.restrict`-ing
and then reading it off. -/
theorem finiteDigraphEquiv_restrict {k l : ℕ} (e : Fin k ↪ Fin l) :
    (fun G : Digraph (Fin l) => G.comap e) ∘ finiteDigraphEquiv l
      = finiteDigraphEquiv k ∘ RelStructure.restrict (fun _ : Unit => e) :=
  funext fun X => (digraphStructureEquiv_comap (e : Fin k → Fin l) X).symm

/-- **Restriction commutes with the finite carrier equivalence** (inverse form): the shape needed
to transport `PMF`-marginals along `finiteDigraphEquiv.symm`. -/
theorem finiteDigraphEquiv_symm_restrict {n m : Unit → ℕ} (e : ∀ s, Fin (n s) ↪ Fin (m s)) :
    RelStructure.restrict e ∘ (finiteDigraphEquiv (m ())).symm
      = (finiteDigraphEquiv (n ())).symm ∘ (fun G : Digraph (Fin (m ())) => G.comap (e ())) := by
  funext G
  apply (finiteDigraphEquiv (n ())).injective
  rw [Function.comp_apply, Function.comp_apply, Equiv.apply_symm_apply]
  set Y := (finiteDigraphEquiv (m ())).symm G with hY
  show finiteDigraphEquiv (n ()) (RelStructure.restrict e Y) = G.comap (e ())
  have hG : finiteDigraphEquiv (m ()) Y = G := by rw [hY, Equiv.apply_symm_apply]
  rw [← hG]
  exact digraphStructureEquiv_comap (e () : Fin (n ()) → Fin (m ())) Y

/-! ### The PMF-based finite directed law -/

/-- **An exchangeable directed-graph law**, presented by its consistent finite marginals: a
`PMF (Digraph (Fin k))` for every `k`, consistent under `Digraph.comap` along every injection of
labels. The directed analogue of `Graphon.ExchangeableGraphLaw`; the marginals are `PMF`s because
`digraphSig` is a finite signature. -/
structure ExchangeableDigraphLaw where
  /-- The `k`-vertex directed-graph marginal. -/
  law : ∀ k, PMF (Digraph (Fin k))
  /-- Consistency under `Digraph.comap` along every injection of labels. -/
  consistent : ∀ {k l : ℕ} (e : Fin k ↪ Fin l), (law l).map (fun G => G.comap e) = law k

@[ext] theorem ExchangeableDigraphLaw.ext {L M : ExchangeableDigraphLaw}
    (h : ∀ k, L.law k = M.law k) : L = M := by
  cases L; cases M; simp only [ExchangeableDigraphLaw.mk.injEq]; exact funext h

/-- The measure-side marginals of a `PMF`-based directed law: transport each `PMF (Digraph (Fin k))`
across `finiteDigraphEquiv.symm` and read it as a probability measure on the relational carrier. -/
noncomputable def ExchangeableDigraphLaw.toRel (D : ExchangeableDigraphLaw) :
    RelExchangeableLaw digraphSig where
  marginal n := ⟨((D.law (n ())).map (finiteDigraphEquiv (n ())).symm).toMeasure, inferInstance⟩
  consistent {n m} e := by
    show (((D.law (m ())).map (finiteDigraphEquiv (m ())).symm).toMeasure).map
        (RelStructure.restrict e) = ((D.law (n ())).map (finiteDigraphEquiv (n ())).symm).toMeasure
    rw [PMF.toMeasure_map _ _ (RelSignature.measurable_restrict e),
        PMF.map_comp, finiteDigraphEquiv_symm_restrict, ← PMF.map_comp, D.consistent (e ())]

@[simp] theorem ExchangeableDigraphLaw.toRel_coe_marginal (D : ExchangeableDigraphLaw)
    (n : Unit → ℕ) :
    (D.toRel.marginal n : Measure (RelStructure digraphSig (Vfinite n)))
      = ((D.law (n ())).map (finiteDigraphEquiv (n ())).symm).toMeasure := rfl

namespace RelSignature

/-- The `PMF`-marginals of a measure-side directed law: read each relational marginal as a PMF
(`Measure.toPMF`, the carrier is finite) and transport it across `finiteDigraphEquiv`. -/
noncomputable def RelExchangeableLaw.toDigraph (L : RelExchangeableLaw digraphSig) :
    ExchangeableDigraphLaw where
  law k := (L.marginal (fun _ => k) : Measure _).toPMF.map (finiteDigraphEquiv k)
  consistent {k l} e := by
    have hinner : ((L.marginal (fun _ => l) : Measure (FiniteDigraph l)).toPMF).map
          (RelStructure.restrict (fun _ : Unit => e))
        = (L.marginal (fun _ => k) : Measure (FiniteDigraph k)).toPMF := by
      refine PMF.toMeasure_injective ?_
      exact (toPMF_map_toMeasure (L.marginal (fun _ => l) : Measure (FiniteDigraph l)) _
          (RelSignature.measurable_restrict _)).trans
        ((L.consistent (fun _ : Unit => e)).trans (Measure.toPMF_toMeasure _).symm)
    calc ((L.marginal (fun _ => l) : Measure _).toPMF.map (finiteDigraphEquiv l)).map
            (fun G => G.comap e)
        = (L.marginal (fun _ => l) : Measure _).toPMF.map
            ((fun G => G.comap e) ∘ finiteDigraphEquiv l) := PMF.map_comp _ _ _
      _ = (L.marginal (fun _ => l) : Measure _).toPMF.map
            (finiteDigraphEquiv k ∘ RelStructure.restrict (fun _ : Unit => e)) :=
          congrArg (fun φ => (L.marginal (fun _ => l) : Measure _).toPMF.map φ)
            (finiteDigraphEquiv_restrict e)
      _ = ((L.marginal (fun _ => l) : Measure _).toPMF.map
            (RelStructure.restrict (fun _ : Unit => e))).map (finiteDigraphEquiv k) :=
          (PMF.map_comp _ _ _).symm
      _ = (L.marginal (fun _ => k) : Measure _).toPMF.map (finiteDigraphEquiv k) :=
          congrArg (fun p => p.map (finiteDigraphEquiv k)) hinner

@[simp] theorem RelExchangeableLaw.toDigraph_law (L : RelExchangeableLaw digraphSig) (k : ℕ) :
    L.toDigraph.law k = (L.marginal (fun _ => k) : Measure _).toPMF.map (finiteDigraphEquiv k) :=
  rfl

end RelSignature

/-- **The finite directed bridge**: `PMF`-based exchangeable directed-graph laws are the same data
as measure-side exchangeable relational laws over `digraphSig`, with `finiteDigraphEquiv` and the
`PMF` ↔ `ProbabilityMeasure` correspondence as inverse transports. -/
noncomputable def digraphLawEquiv : ExchangeableDigraphLaw ≃ RelExchangeableLaw digraphSig where
  toFun := ExchangeableDigraphLaw.toRel
  invFun := RelExchangeableLaw.toDigraph
  left_inv D := by
    apply ExchangeableDigraphLaw.ext; intro k
    show (((D.law k).map (finiteDigraphEquiv k).symm).toMeasure).toPMF.map (finiteDigraphEquiv k)
        = D.law k
    calc (((D.law k).map (finiteDigraphEquiv k).symm).toMeasure).toPMF.map (finiteDigraphEquiv k)
        = ((D.law k).map (finiteDigraphEquiv k).symm).map (finiteDigraphEquiv k) :=
          congrArg (fun p => p.map (finiteDigraphEquiv k))
            (PMF.toMeasure_toPMF ((D.law k).map (finiteDigraphEquiv k).symm))
      _ = (D.law k).map (⇑(finiteDigraphEquiv k) ∘ ⇑(finiteDigraphEquiv k).symm) := PMF.map_comp _ _ _
      _ = (D.law k).map id := congrArg (fun φ => (D.law k).map φ) (Equiv.self_comp_symm _)
      _ = D.law k := PMF.map_id _
  right_inv L := by
    apply RelExchangeableLaw.ext; funext n
    apply ProbabilityMeasure.toMeasure_injective
    have hn : (fun _ : Unit => n ()) = n := funext (fun u => by cases u; rfl)
    have hPMF : ((L.marginal (fun _ => n ()) : Measure _).toPMF.map (finiteDigraphEquiv (n ()))).map
          (finiteDigraphEquiv (n ())).symm = (L.marginal (fun _ => n ()) : Measure _).toPMF := by
      rw [PMF.map_comp, Equiv.symm_comp_self, PMF.map_id]
    simp only [ExchangeableDigraphLaw.toRel_coe_marginal, RelExchangeableLaw.toDigraph_law]
    calc (((L.marginal (fun _ => n ()) : Measure _).toPMF.map (finiteDigraphEquiv (n ()))).map
            (finiteDigraphEquiv (n ())).symm).toMeasure
        = ((L.marginal (fun _ => n ()) : Measure _).toPMF).toMeasure := congrArg PMF.toMeasure hPMF
      _ = (L.marginal (fun _ => n ()) : Measure _) := Measure.toPMF_toMeasure _
      _ = (L.marginal n : Measure _) := hn ▸ rfl

@[simp] theorem digraphLawEquiv_apply (D : ExchangeableDigraphLaw) :
    digraphLawEquiv D = D.toRel := rfl

@[simp] theorem digraphLawEquiv_symm_apply (L : RelExchangeableLaw digraphSig) :
    digraphLawEquiv.symm L = L.toDigraph := rfl

/-! ### The infinite directed law and the headline equivalence -/

/-- **An infinite exchangeable directed-graph law**: a probability law on the infinite digraph
space `InfiniteDigraph` invariant under every relabelling of `ℕ`. The measurable structure lives
on the relational carrier, so this is the `digraphSig` specialization of
`InfiniteRelExchangeableLaw`. -/
abbrev InfiniteExchangeableDigraphLaw : Type := InfiniteRelExchangeableLaw digraphSig

/-- **The headline directed equivalence** (Aldous–Hoover–Kallenberg, directed case): `PMF`-based
exchangeable directed-graph laws are the same data as relabelling-invariant laws on the infinite
digraph space — the finite bridge `digraphLawEquiv` composed with the R2c relational equivalence
`relExchangeableLawEquiv`. -/
noncomputable def exchangeableDigraphLawEquiv :
    ExchangeableDigraphLaw ≃ InfiniteExchangeableDigraphLaw :=
  digraphLawEquiv.trans relExchangeableLawEquiv

@[simp] theorem exchangeableDigraphLawEquiv_apply_law (D : ExchangeableDigraphLaw) :
    (exchangeableDigraphLawEquiv D).law = D.toRel.infiniteLaw := rfl

/-- The infinite directed law realizes the finite `PMF`-marginals: restricting to the first `k`
vertices and reading off the finite digraph recovers `D.law k`. -/
theorem exchangeableDigraphLawEquiv_law_map_restrictFin (D : ExchangeableDigraphLaw) (k : ℕ) :
    ((exchangeableDigraphLawEquiv D).law : Measure (RelStructure digraphSig (Vinfinite digraphSig))).map
        (RelStructure.restrictFin (fun _ => k))
      = (D.toRel.marginal (fun _ => k) : Measure (RelStructure digraphSig (Vfinite (fun _ => k)))) :=
  D.toRel.infiniteLaw_map_restrictFin (fun _ => k)
