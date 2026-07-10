import Graphon
/-! CI axiom audit: the six headline theorems must use only the standard axioms.
Checked by `scripts/check_census_and_axioms.sh`. -/
#print axioms Graphon.exists_mpEquiv_cutNormDiff_lt_add
#print axioms Graphon.complete
#print axioms Graphon.compact
#print axioms Graphon.cutDistance_triangle
#print axioms Graphon.first_sampling_lemma
#print axioms Graphon.cutDistance_zero_of_homDensity_eq
