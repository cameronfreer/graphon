/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Architect
import Graphon.SamplingLaw
import Graphon.InverseCounting
import Graphon.GraphonSpace

/-!
# The sample laws determine the graphon (S2–S3 joining theorem)

Two graphons have the same finite sample laws at every size iff they are weakly
isomorphic — equivalently, iff they define the same point of the graphon space:

* `Graphon.samplePMF_eq_all_iff_weaklyIsomorphic` — sample laws ↔ weak isomorphism.
  Forward: equal laws have equal upper masses, which are the homomorphism densities
  (`upperSum_samplePMF`), and densities determine the graphon
  (`weaklyIsomorphic_of_homDensity_eq`, the inverse-counting headline). Reverse:
  cut distance zero forces equal densities (`homDensity_eq_of_cutDistance_zero`, the
  counting lemma), hence equal upper masses, hence equal PMFs (`pmf_ext_of_upperSum`).
* `Graphon.samplePMF_eq_all_iff_mk_eq_mk` — the quotient-facing form: same sample laws
  iff the same point of `GraphonSpace`.

This joins the S2 finite-marginal API to the S3 state space: the maps
`GraphonSpace.mk W ↦ samplePMF W k` are well-defined coordinates on the graphon space
that separate points — the Lovász-style bridge toward exchangeable infinite graph laws.

This file sits above both `SamplingLaw` and `InverseCounting` so that the foundational
sample-law module does not import the inverse-counting machinery.
-/

open MeasureTheory

namespace Graphon

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  [IsProbabilityMeasure μ] [StandardBorelSpace α] [NoAtoms μ]

/-- **The sample laws determine the graphon**: two graphons have the same `k`-vertex
sample law for every `k` iff they are weakly isomorphic. -/
@[blueprint "thm:sample-determination"
  (title := /-- Sample laws determine the graphon -/)]
theorem samplePMF_eq_all_iff_weaklyIsomorphic (U W : Graphon α μ) :
    (∀ k, samplePMF U k = samplePMF W k) ↔ WeaklyIsomorphic U W := by
  classical
  constructor
  · intro h
    apply weaklyIsomorphic_of_homDensity_eq U W
    intro k F _
    have hk := congrArg
      (fun p : PMF (SimpleGraph (Fin k)) =>
        upperSum (fun G => (p G).toReal) F)
      (h k)
    simpa only [upperSum_samplePMF] using hk
  · intro h k
    apply pmf_ext_of_upperSum
    intro F
    rw [upperSum_samplePMF, upperSum_samplePMF]
    exact homDensity_eq_of_cutDistance_zero F U W h

/-- The quotient-facing form: two graphons have the same sample laws iff they define the
same point of the graphon space. The maps `mk W ↦ samplePMF W k` are therefore
point-separating coordinates on `GraphonSpace`. -/
theorem samplePMF_eq_all_iff_mk_eq_mk (U W : Graphon α μ) :
    (∀ k, samplePMF U k = samplePMF W k) ↔ GraphonSpace.mk U = GraphonSpace.mk W := by
  rw [GraphonSpace.mk_eq_mk_iff]
  exact samplePMF_eq_all_iff_weaklyIsomorphic U W

end Graphon
