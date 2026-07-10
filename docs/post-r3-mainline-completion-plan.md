# Post-R3 mainline completion plan

**Status:** execution plan, 2026-07-10; **PR #14 was merged the same day**
(merge commit `4cec913`), so §3's pre-merge gates are historical — they were satisfied.
The docs-closeout/CI work package is implemented in PR #15 (`docs-closeout-ci`).  
**Execution base:** `master` after PR #14 is merged (now current `master`)  
**Purpose:** finish and harden the work already in progress; do not start a new graphon-theory
campaign under the cover of “cleanup.”

## 1. Target state

PRs #13 and #14 close the mathematical program advertised by the repository: the corrected
Rokhlin/measure-isomorphism route, compactness, the First Sampling Lemma, inverse counting, and
the convergence equivalence are all proved. The remaining work is therefore a mainline
completion campaign, not another proof campaign.

The repository is finished for a first release when all of the following are true:

1. Every public status surface (root module documentation, README, homepage, blueprint, API
   inventory, and historical scoping notes) states the same proved result.
2. There is no literal `sorry` or `admit` anywhere in `Graphon/`. The seven known-false
   declarations are removed rather than “proved”; their counterexamples remain documented.
3. The root library and the deliberately non-root `Graphon.Spectral` module both build.
4. The headline declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
5. CI enforces the build, placeholder census, axiom audit, blueprint consistency, and public
   documentation build, so the closed state cannot silently regress.
6. Reusable measure-theory results have a realistic Mathlib upstreaming path, but upstream
   acceptance is not a prerequisite for the project release.
7. A reproducible release commit is tagged and its generated website reflects that commit.

## 2. Explicit non-goals

The following should not be mixed into this campaign:

- extending `Graphon.Operations` or the `Graphon.Operator` L² API;
- adding new graphon results beyond the currently advertised theorem set;
- trying to prove any of the seven refuted statements;
- redesigning the two-sided definition of `cutDistance`;
- a Lean/Mathlib toolchain migration;
- large proof golfing or file-wide stylistic rewrites;
- making Mathlib accept the upstream pieces before declaring this repository complete.

Those are valid later projects, but each changes the risk profile and obscures the closeout.

## 3. Baseline immediately around PR #14

### 3.1 What should land in PR #14

The six-file narrative closeout is committed and pushed as `d196786`. Before merging #14, make
one last small follow-up commit; at the time this plan was written the following current-tense
remnants remained:

- `Graphon/InverseCounting.lean`: the discharged sampling argument still says “modulo the
  single analytic sorry `first_sampling_lemma`” near `headline_parameter_selection`.
- `Graphon/SamplingConcentration.lean`: the module header and the
  `sampleGoodMassOn_of_events` docstring still say that proving the two events “remains”; the
  `RoundingEvent` docstring still calls its proof future work.
- `Graphon.lean`: the `Graphon.Sampling` inventory row still says concentration bounds are
  future work.

Do not broaden this last PR commit into the blueprint/homepage rewrite described below unless
there is a strong reason to delay the merge. The important thing is that the PR description
must describe what is actually committed at its head.

### 3.2 Final PR #14 gates

Run these on the final pushed head:

```bash
git diff --check
lake build
lake build :blueprint :blueprintJson
lake exe checkdecls blueprint/lean_decls
rg -n '^\s*sorry\s*$' Graphon/*.lean
```

The expected census before the later refuted-stub cleanup is exactly:

- `Graphon/MatrixDetermination.lean`: 3;
- `Graphon/Spectral.lean`: 2;
- `Graphon/Lovasz.lean`: 2;
- every other file: 0.

Recheck the axioms of at least:

- `Graphon.MeasurePreserving.exists_common_coupling_maps`;
- `Graphon.MeasurePreserving.exists_controlled_cell_alignment`;
- `Graphon.cutNormDiff_pullback_le`;
- `Graphon.exists_mpEquiv_cutNormDiff_lt_add`;
- `Graphon.cutDistance_triangle`;
- `Graphon.totallyBounded`;
- `Graphon.complete`;
- `Graphon.compact`;
- `Graphon.first_sampling_lemma`;
- `Graphon.cutDistance_zero_of_homDensity_eq`;
- `Graphon.cutDistance_le_of_homDensity_close`;
- `Graphon.cutDistance_tendsto_iff_homDensity_tendsto`.

The accepted list is exactly the three standard axioms above. A declaration mentioning
`sorryAx` is a release blocker even if its file contains no new literal `sorry`.

### 3.3 Merge and establish the real mainline baseline

Merge #14 with a merge commit, then start subsequent work from the updated remote `master`:

```bash
git switch master
git pull --ff-only
git status --short
git log --oneline --decorate -5
```

The worktree must be clean before creating the first post-R3 branch. Wait for the `master`
Actions run, including Pages deployment, rather than treating the PR run as the deployment
check. Record the merge SHA in the first closeout PR description and in any release notes.

Do not merge `master` back into the old R1–R3 branch merely to absorb #13's merge commit. Once
#14 is merged, the stacked branches have served their purpose.

## 4. Work package A — make every public surface true

Create a short-lived branch from post-#14 `master`, for example
`post-r3-public-status`. This should be the first mainline follow-up.

### 4.1 Root module documentation

Update `Graphon.lean` so its stable-core inventory includes `MeasureIso`, `Overlay`,
`SamplingPointwise`, and the proved status of the sampling chain. In particular, separate the
base random-graph distribution in `Graphon.Sampling` from the concentration results that now
live in `SamplingRounding`, `SamplingPointwise`, and `SamplingLemma`.

This is documentation only; do not reorder imports unless a measured dependency reason is
found.

### 4.2 Homepage

`home_page/index.md` is currently the most visible stale artifact. Replace the two-live-blocker
table with the same closed-status summary used by the README:

- explain that the old `exists_common_extension` statement was false and was replaced by four
  corrected consumer-shaped results;
- describe `MeasureIso.lean` and `Overlay.lean` separately;
- mark the First Sampling Lemma and determination theorem proved;
- list all newly added sampling and measure-isomorphism files;
- describe the seven remaining placeholders as refuted/dead declarations only until work
  package B removes them.

Avoid copying dates and counts into many independent paragraphs. Prefer one canonical status
paragraph and a compact component table, reducing future drift.

### 4.3 Blueprint source

`blueprint/src/content.tex` still describes three pending declarations, the deleted Rokhlin
monolith, and an unproved inverse-counting chain. Rewrite its proof-status and theorem chapters
from the proved architecture:

1. **Measure-isomorphism layer:** CDF continuity, probability integral transform, quantile
   mod-0 inverse, transport from a standard Borel space, null-reservoir patch, and the
   mod-0-to-everywhere upgrade.
2. **Three CutDistance cores:** common coupling maps, pullback contraction, and controlled
   cell alignment.
3. **Overlay core:** exact realization for step graphons followed by the `5ε/8` regularity
   budget.
4. **Sampling layer:** point sampling, rounding, recombination, and the K-independent
   quantitative inverse-counting route.
5. **Determination and convergence:** explicitly state that the entire chain is now
   axiom-clean.

The blueprint should explain the important distinction between measure-preserving maps and
measure-preserving bijections. Do not resurrect the false “common extension by automorphisms”
form in prose.

### 4.4 Blueprint nodes and declaration inventory

Add LeanArchitect nodes, where useful, for the new load-bearing results rather than merely
mentioning them in free text. Candidate declarations are:

- `Graphon.MeasureIso.atomless_standardBorel_mod0MeasureIso_unitInterval`;
- `Graphon.MeasureIso.Mod0MeasureIso.toMeasurableEquiv`;
- `Graphon.MeasurePreserving.exists_common_coupling_maps`;
- `Graphon.cutNormDiff_pullback_le`;
- `Graphon.MeasurePreserving.exists_controlled_cell_alignment`;
- `Graphon.exists_mpEquiv_cutNormDiff_lt_add`;
- `Graphon.first_sampling_lemma`;
- `Graphon.cutDistance_zero_of_homDensity_eq`.

Use stable node IDs and add the declarations to `blueprint/lean_decls`. Keep the existing
headline nodes. The dependency graph should show the four-core architecture rather than one
fictional Rokhlin node.

### 4.5 References and paper alignment

Audit theorem numbers and add missing bibliography entries for the sampling proof and the
standard-probability-space isomorphism. The blueprint should distinguish:

- results directly following Lovász;
- the BCLSV sampling formulation;
- the AFKK cut-guessing input used by the point-sampling proof;
- standard descriptive-set/measure-theory facts used for the null patch;
- project-specific proof choices, especially exact coupling-matrix carving and the
  `5ε/8` assembly.

Do not cite the project-specific exact-overlay proof as though it appeared verbatim in a
source. Say explicitly when the formal proof is a derived implementation of a classical fact.

### 4.6 Build only source artifacts

Edit `blueprint/src/content.tex`, `blueprint/src/refs.bib`, `blueprint/lean_decls`, and the
homepage source. Do not hand-edit generated files under `blueprint/web`, `blueprint/print`, or
the deployed site.

Local gates for this package:

```bash
lake build :blueprint :blueprintJson
lake exe checkdecls blueprint/lean_decls
leanblueprint web
leanblueprint pdf
cd home_page && bundle exec jekyll build
```

CI remains authoritative if the local machine lacks the full TeX/Ruby toolchain.

## 5. Work package B — remove all seven refuted `sorryAx` declarations

This is the main logical-hygiene package. “No headline theorem depends on them” is useful, but
it is weaker than having a theory that never declares false propositions. A false theorem kept
with `sorry` is also dangerously discoverable by automation.

Make this a dedicated PR. The governing rule is:

> Preserve the counterexample and architectural lesson; delete the false proposition from the
> Lean environment.

### 5.1 Mechanical safety procedure

For every candidate declaration:

1. Use LSP references and repository search to confirm all consumers.
2. Classify consumers as live/public, private dead-route, or documentation-only.
3. Delete the false declaration and every theorem whose proof depends on it.
4. Retain independent definitions and proved lemmas only when they have plausible reuse or make
   the counterexample intelligible.
5. Build the affected module immediately.
6. Re-run the public axiom audit after each file, not only at the end.

Do not weaken hypotheses opportunistically just to make a nearby theorem true. A corrected
statement belongs in a separate, mathematically scoped campaign.

### 5.2 `Graphon/Spectral.lean` — two refuted public declarations

The two literal placeholders are:

- `same_diag_powers_imp_vertex_orbit` (double-pin cospectral-vertex counterexample);
- `stable_imp_vertexOrbitRel` (1-WL/fractional automorphism versus true orbit, e.g. the Frucht
  graph).

`Spectral.lean` is outside the root import tree, but it must still be consistent and buildable.
Delete the theorem declarations, convert their long docstrings into section-level historical
notes, and keep the true one-way/refinement and spectral-translation lemmas.

Optional follow-up, not a blocker: formalize one concrete counterexample in Lean. This is more
valuable than retaining a false theorem, but it may require substantial finite-graph
computation and should not delay removal.

### 5.3 `Graphon/Lovasz.lean` — two refuted closed-walk declarations

Remove:

- `vertex_orbit_of_closed_walks_eq`;
- `closed_walk_profiles_separate_vertex_orbits`.

They are public declarations in a root-imported module but repository search currently finds no
code consumers. Preserve the double-pin-tree explanation and the true bridge lemmas translating
rooted cycles to closed-walk/symmetric-adjacency data. Update the module documentation so it no
longer advertises a “spectral closing” theorem.

This is an intentional API break: the removed API was false. Call it out plainly in release
notes rather than adding deprecated aliases.

### 5.4 `Graphon/MatrixDetermination.lean` — three private refuted declarations

There are two independent dead routes.

**Route M1:** `labeledEvalK_separates` is false when two unused colors are exchanged by an
automorphism. It is private and has no code consumers. Delete the whole declaration; retain its
counterexample as a short section note if it still helps explain why the successful
super-surjective route was chosen.

**Route M2:** the five-motif pair-profile route is false for `C₅ ⊔ C₆`. Its literal
placeholders are `vertexOrbit_of_star0_tri0_eq` and
`pairOrbit_of_vertexOrbits_and_path`; the mirrored right theorem and the assembled
`pairOrbitRel_of_pairProfile_eq` depend on them. The later private CT-1 chain, beginning with
`pairOrbit_separated_by_edgeFreeEval` and ending at
`eval2Span_eq_pairInvariantSubspace`, also depends on the false pair-profile conclusion and is
not used by the successful cross-super proof. Delete that dependent chain.

The explicit motif graph definitions and their evaluation lemmas are true. Keep them only if
they are useful independently; otherwise removing the entire abandoned block will make the
successful proof architecture substantially easier to read.

### 5.5 Zero-placeholder completion gate

After the three file passes:

```bash
rg -n '^\s*(sorry|admit)\s*$' Graphon
lake build
lake build Graphon.Spectral
```

The search must return no matches. Then rerun every axiom check listed in §3.2. The README,
homepage, and blueprint can now say simply “zero sorries,” with a historical note that seven
refuted declarations were removed.

## 6. Work package C — turn the successful audit into CI policy

The project reached a clean state through manual campaigns; encode the important invariants so
future work cannot accidentally reverse them.

### 6.1 Add a repository verification script

Create a small, readable script (for example `scripts/verify_release.sh`) that:

1. rejects literal `sorry` and `admit` in `Graphon/`;
2. builds the root target;
3. builds `Graphon.Spectral` explicitly because it is not imported by `Graphon.lean`;
4. runs the headline axiom checks and rejects `sorryAx` or any non-standard custom axiom;
5. runs `lake exe checkdecls blueprint/lean_decls`;
6. optionally checks `git diff --check` when run from a worktree.

Keep the theorem list explicit. A short audited allowlist is safer than a heuristic that can
silently stop checking renamed declarations.

### 6.2 Extend GitHub Actions

Add a fast “logical hygiene” step after the Lean build and before the expensive TeX/Ruby work.
This gives failures early and makes it obvious whether a PR broke logic, documentation, or site
generation.

Also consider a scheduled or manually dispatched full build without caches. Cache-backed PR
builds remain the normal path; a periodic cold build catches undeclared/transitive-import leaks.

### 6.3 Prevent narrative drift

Do not attempt to grep every occurrence of words such as “remaining” or “sorry”; historical
design notes legitimately contain them. Instead:

- keep one canonical current-status paragraph in README/homepage/blueprint;
- mark historical notes with a prominent outcome banner;
- have code docstrings say “uses” or “rests on,” not campaign-era status;
- include public-status surfaces in the release checklist.

## 7. Work package D — stabilize the new measure-theory API

Do this after the repository is zero-sorry and publicly truthful. It is preparation for
upstreaming, not a prerequisite for logical completion.

### 7.1 Re-audit Mathlib before changing the API

On the currently pinned Mathlib, local declaration search finds no existing mod-0 measure
isomorphism structure; only the project’s `Graphon.MeasureIso.Mod0MeasureIso` appears. Re-run
that search against the Mathlib revision used for upstream work, because the answer may change.

### 7.2 Give `Mod0MeasureIso` the minimal categorical API

Before exporting it, consider adding and proving:

- `refl` and `symm` (the project currently constructs symmetric instances by hand);
- `[simp]` a.e.-inverse lemmas in both directions;
- composition laws stated at the useful level, without attempting literal structure equality;
- direct `MeasurePreserving` projections for `toFun` and `invFun`;
- a clear namespace and name suitable for Mathlib (for example, a measure-theory rather than
  graphon namespace).

Avoid changing all graphon consumers in the same commit. Introduce compatibility aliases, move
consumers, then remove project-only names after the migration builds.

### 7.3 Split `MeasureIso.lean` by mathematical responsibility

The current roughly 1,000-line file naturally separates into:

1. atomless-CDF continuity and the probability integral transform;
2. quantile measurability, pushforward, and a.e. inverse results;
3. the mod-0 isomorphism structure and standard-Borel transport;
4. null-reservoir construction via a Cantor scheme;
5. mod-0-to-everywhere measurable-equivalence patching.

Split only when it improves import boundaries. Preserve the already measured targeted import
closure; do not trade a clean conceptual split for a new `import Mathlib` umbrella.

### 7.4 Separate project-local overlay plumbing from reusable carving

`Graphon.exists_disjoint_subsets_of_measures` is a plausible general measure-theory lemma.
Before upstreaming it:

- determine the truly minimal hypotheses of `exists_measurable_subset_of_measure`;
- generalize from `Fin n` only if a finite-indexed formulation is clearer in Mathlib;
- decide whether the result should return a `Finset`/indexed family or an inductive partition;
- add edge-case tests for `n = 0`, zero masses, and total requested mass exactly `μ C`.

`MeasurablePartition.ofCells` and the exact step-overlay theorem are graphon-project APIs and
should remain here unless a genuine independent Mathlib consumer appears.

## 8. Work package E — upstream in small, reviewable pieces

Do not send the whole `MeasureIso.lean` file as one Mathlib PR. A practical dependency stack is:

1. **U1 — atomless CDF:** continuity and the CDF pushforward to restricted Lebesgue measure.
2. **U2 — quantile:** measurability, reverse pushforward, and the two a.e.-inverse identities.
3. **U3 — mod-0 API:** the abstraction, symmetry/composition, real-line instance, and
   `embeddingReal` transport.
4. **U4 — standard-Borel upgrade:** uncountable null reservoir and null-set patching to an
   everywhere `MeasurableEquiv`.
5. **U5 — finite prescribed-mass carving:** independent of graphons and separable from U1–U4.

For each upstream PR:

- first search current Mathlib for the intended statement and naming convention;
- move from `Graphon.MeasureIso` into the appropriate Mathlib namespace;
- add docstrings and a source citation;
- reduce hypotheses with `lean_minimal_hypotheses` or a manual audit;
- use the narrowest imports;
- keep a compatibility layer in this repository until the pinned Mathlib contains the result.

Upstream review may request a different abstraction or may split the theorem differently. Keep
the project’s proved implementation intact until the replacement is available at the pinned
revision.

## 9. Work package F — release and maintenance baseline

### 9.1 Toolchain policy

As of this plan, the project is pinned to Lean/Mathlib `v4.32.0-rc1`, while the latest stable
release is `v4.31.0`. Do not downgrade during closeout. Wait for stable `v4.32.0`, then perform a
separate migration PR with a cold build, deprecation sweep, blueprint build, and axiom audit.

### 9.2 Release metadata

After packages A–C are merged and green:

- add a concise `CHANGELOG.md` describing the completed theorem chain and removal of the seven
  false declarations;
- consider `CITATION.cff` matching the existing BibTeX citation;
- confirm license and author metadata;
- verify the deployed homepage, blueprint web/PDF, API docs, and dependency graph;
- tag the release matching `lakefile.toml` (currently `0.1.0`) and create a GitHub release from
  the exact green commit.

### 9.3 Branch cleanup

Only after the release tag exists, inventory the campaign branches. Delete remote branches only
when their commits are reachable from the release or intentionally superseded, and retain any
branch containing unique research notes until those notes are archived in `docs/`.

Branch deletion is housekeeping, not a release blocker.

## 10. Recommended PR/commit sequence

Keep the mainline history easy to review:

1. **PR #14 final closeout follow-up:** after `d196786`, remove the few remaining current-tense
   traces in §3.1; merge #14.
2. **PR A — public truth:** `Graphon.lean`, homepage, blueprint source/nodes/references.
3. **PR B1 — remove Spectral/Lovasz refuted declarations:** public false-API removal and docs.
4. **PR B2 — remove MatrixDetermination dead routes:** private false chain and dead-code trim.
5. **PR C — integrity gates:** zero-placeholder and axiom CI automation.
6. **PR D — measure-theory API stabilization:** only after the clean baseline is protected.
7. **Upstream PRs U1–U5:** independent review cadence; do not block the project release.
8. **Release PR/tag:** changelog, citation metadata, final generated-site verification.

Splitting B1 and B2 is deliberate: the first removes false public declarations; the second can
be a large private-code deletion and deserves its own diff.

## 11. Stop conditions and decision gates

Stop and reassess rather than expanding scope if any of these occur:

- a supposedly dead false declaration has a live public consumer;
- deleting the CT-1 route changes the axioms or type of the successful determination theorem;
- a blueprint node forces a new import cycle;
- upstreaming requires a foundational Mathlib abstraction whose design is unsettled;
- stable Lean `v4.32.0` introduces repairs large enough to obscure the closeout;
- a paper citation does not actually support the exact formal statement being attributed to it.

In each case, preserve the last green commit and open a narrowly scoped design note before
continuing.

## 12. Final acceptance checklist

- [x] PR #14 merged and the `master` build/Pages deployment is green (2026-07-10, `4cec913`).
- [ ] Root module docs, README, homepage, blueprint, and API inventory agree.
- [ ] Blueprint includes the measure-isomorphism, coupling, overlay, sampling, and determination
      dependencies.
- [ ] `rg -n '^\s*(sorry|admit)\s*$' Graphon` returns no matches.
- [ ] `lake build` succeeds.
- [ ] `lake build Graphon.Spectral` succeeds independently.
- [ ] Blueprint targets and `checkdecls` succeed.
- [ ] Every headline theorem passes the standard-axioms-only audit.
- [ ] CI enforces the zero-placeholder and axiom policies.
- [ ] Generated homepage, blueprint, API docs, and dependency graph are checked from the release
      commit.
- [ ] Release notes explicitly record removal of the seven false declarations.
- [ ] A release tag is created from the green commit.
- [ ] Upstreaming is tracked separately and does not hold the release hostage.
