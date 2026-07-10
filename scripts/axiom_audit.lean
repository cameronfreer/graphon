import Graphon
/-! CI axiom audit: the load-bearing declarations below must use only axioms from the
allowed set {propext, Classical.choice, Quot.sound} — in particular no `sorryAx` and no
custom axioms. Target list and policy: `scripts/check_census_and_axioms.py`
(and `docs/post-r3-mainline-completion-plan.md` §4.4). -/
#print axioms Graphon.MeasureIso.atomless_standardBorel_mod0MeasureIso_unitInterval
#print axioms Graphon.MeasureIso.Mod0MeasureIso.toMeasurableEquiv
#print axioms Graphon.MeasurePreserving.exists_common_coupling_maps
#print axioms Graphon.cutNormDiff_pullback_le
#print axioms Graphon.MeasurePreserving.exists_controlled_cell_alignment
#print axioms Graphon.exists_mpEquiv_cutNormDiff_lt_add
#print axioms Graphon.cutDistance_triangle
#print axioms Graphon.totallyBounded
#print axioms Graphon.complete
#print axioms Graphon.compact
#print axioms Graphon.first_sampling_lemma
#print axioms Graphon.cutDistance_zero_of_homDensity_eq
#print axioms Graphon.homDensity_eq_sum_sampleMass
#print axioms Graphon.sampleMass_map_perm
#print axioms Graphon.samplePMF_map_comap
#print axioms Graphon.sampleLaw_map_comap
#print axioms Graphon.sampleLaw_const_eq_binomial
#print axioms GraphonSpace.mk_eq_mk_iff
#print axioms GraphonSpace.instCompactSpace
#print axioms Graphon.samplePMF_eq_all_iff_weaklyIsomorphic
