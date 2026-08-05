/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Graphon.RelFixingCondIndep
import Graphon.RelSingletonPeel
import Graphon.RelFactorLaws

/-!
# The rank-one mutual conditional independence (R4 converse piece 3, #107)

The rank-one instance of the target: the exact-anchor layers at the *singletons* are **mutually**
conditionally independent given the invariant σ-algebra,

`iCondIndepFun (fun v => exactMap {v}) invariantAlgebra M.law`.

At rank one the conditioning factor is `lowerRankAlgebra 1 = invariantAlgebra`, so this is the
conditional-independence half of the multi-sorted de Finetti statement, for an arbitrary
exchangeable law — no dissociation, no `NoNullary`. Sort-orbit equality of the conditional
kernels is the other half and is deliberately absent here; it is provable separately from
exchangeability and uniqueness of conditional distributions.

The peel itself is `InfiniteRelExchangeableLaw.iCondIndepFun_of_fixingAlgebra_singleton`, stated
for an arbitrary vertex-indexed family measurable for its own singleton fixing algebra. This
theorem is one instance of it; the raw relation blocks are another. Neither is more fundamental,
and the argument never needed the basis.

## Why no de Finetti machinery is needed

Mutual conditional independence does not follow from pairwise conditional independence in
general, and this is exactly the higher-rank obstruction recorded in `Graphon.RelRankAlgebra`.
At rank one it can nevertheless be obtained from the *two-set* theorem
`InfiniteRelExchangeableLaw.condIndep_fixingAlgebra` by peeling one vertex at a time:

* peel a vertex `v` off the finite family;
* bundle the remaining events into a single event measurable for `fixingAlgebra s`, where `s` is
  the set of remaining vertices — legitimate because `fixingAlgebra` is monotone;
* `{v} ∩ s = ∅`, so the two-set theorem conditions on `fixingAlgebra ∅ = invariantAlgebra`,
  which is the conditioning algebra we want and does not change as the peel proceeds;
* multiply by the induction hypothesis.

The step that fails at higher rank is the third: for supports of rank `n > 1` the peeled support
*need not be disjoint* from the accumulated union, and where it is not, the two-set theorem
conditions on a different — and larger — algebra at that stage. Since conditional independence
is not preserved under enlarging the conditioning, the stages no longer compose. A positive-rank
intersection is not inevitable for every family, but it is possible, and that is enough to break
the induction. At rank one the remaining union stays disjoint from the peeled singleton for
*every* family, so the conditioning algebra is the same throughout and the products compose.

Consequently the rank-one case needs no de Finetti representation, no mixing measure, and no
identification of a mixing measure with an invariant conditional distribution.
-/

open MeasureTheory MeasurableSpace ProbabilityTheory

namespace RelSignature

namespace CoherentBasis

universe u

variable {S : RelSignature.{u}} {M : InfiniteRelExchangeableLaw S} (B : CoherentBasis M)

open scoped Classical in
/-- **Mutual conditional independence of the singleton exact layers given the invariant
σ-algebra** — the rank-one instance of the rankwise theorem, for an arbitrary exchangeable law.

Stated over the whole vertex index rather than for a fixed finite family: `iCondIndepFun` already
quantifies over finite subfamilies, so finite families are a corollary. -/
theorem iCondIndepFun_exactMap_singleton [Fintype S.Srt] [Countable S.Rel] :
    iCondIndepFun RelStructure.invariantAlgebra (RelStructure.invariantAlgebra_le (S := S))
      (fun v : Σ s : S.Srt, Vinfinite S s => B.exactMap {v})
      (M.law : Measure (RelStructure S (Vinfinite S))) :=
  M.iCondIndepFun_of_fixingAlgebra_singleton fun _ => B.measurable_exactMap_fixingAlgebra _

end CoherentBasis

end RelSignature
