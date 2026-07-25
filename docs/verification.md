# Verification status and project history

This page records *how* the formalization is checked and what was resolved along the way. The
landing pages state the current status; the details and the history live here so they do not
crowd out the mathematics.

## What CI enforces

Every change runs `scripts/check_census_and_axioms.py`, which applies two gates:

1. **Sorry census.** The project contains zero `sorry`/`admit` tokens. The allowlist of permitted
   stubs is empty (`ALLOWED_STUBS = set()`), so any reintroduction fails the build.
2. **Axiom audit.** A fixed list of load-bearing declarations is checked with `#print axioms`, and
   each must depend only on `propext`, `Classical.choice`, and `Quot.sound`.

   Note the scope precisely: this gate proves that the *audited* declarations use no custom
   axioms. It does not scan every declaration in the repository. The project introduces no custom
   axioms today, but that is a fact about the current source, not something the gate enforces —
   which is why the audited list is extended whenever a new load-bearing result lands.

The audited declaration list is maintained in **two** places that must stay in sync:
`scripts/axiom_audit.lean` (the `#print axioms` lines) and the intended-set literal inside
`scripts/check_census_and_axioms.py`. Adding a declaration to only one of them fails the gate with
`printed declaration set differs from the intended audit list`.

CI coverage differs by trigger: **every PR** builds the Lean project and the blueprint (web and
PDF) and runs both gates above; the **`master` deployment** additionally builds the API
documentation and the Jekyll homepage before assembling and publishing the site.

## History

### Rokhlin-style alignment (closed 2026-07-09)

The triangle inequality for cut distance originally rested on a single monolithic statement,
`exists_common_extension`, which was **shown to be unprovable as stated**. It was replaced by four
corrected coupling cores, all proved from the atomless standard-Borel measure-isomorphism theorem
developed graphon-independently in `Graphon/MeasureIso.lean`. Three cores live in
`Graphon/CutDistance.lean`; the fourth, the overlay theorem
`exists_mpEquiv_cutNormDiff_lt_add`, is proved in `Graphon/Overlay.lean` — the coupling matrix is
realized exactly by a measure-preserving bijection, with no appeal to Birkhoff.

### First Sampling Lemma (proved 2026-07-08)

`first_sampling_lemma` (Lovász Lemma 10.16 / BCLSV Theorem 4.6): for every ε and η there is a
sample size `k` that works for *every* graphon simultaneously. Proved by recombining two
independently established concentration events — the pointwise AFKK cut-guessing bound
(`Graphon/SamplingPointwise.lean`, using McDiarmid-at-MGF and soft-max infrastructure) with the
finite rounding certificate (`Graphon/SamplingRounding.lean`).

### Algebraic determination (proved 2026-07-06)

`matrix_quotient_of_weightedHomSum_eq` (Lovász Theorem 5.30, the k ≥ 2 positive-weight case), via
the twin-free bijection `twinfree_bijection_of_weightedHomSum_eq` and the cross-matrix
super-surjective transfer in `Graphon/CrossSuper.lean`.

### Removal of the last stubs (issue #19, completed 2026-07-11)

Several statements in `MatrixDetermination.lean`, `Lovasz.lean`, and `Spectral.lean` had been
retained as `sorry`-carrying stubs after being discovered to be **false**. All were deleted, along
with a dead 66-declaration private subtree, and their refutations were kept as prose notes at the
original sites — including the C₅ ⊔ C₆ and identity-matrix automorphism counterexamples. The
census gate was tightened to strictly zero at the same time.

`Graphon/Spectral.lean` remains in the tree as documentation of the refuted closed-walk
conjectures (issue #77) and is deliberately outside the root import tree.
